%%% @author Thomas Arts <thomas@SpaceGrey.lan>
%%% @copyright (C) 2019, Thomas Arts
%%% @doc
%%%
%%%      Start a second epoch node with old code using something like:
%%%            ./rebar3 as test shell --sname oldepoch@localhost --apps ""
%%%            we need the test profile to assure that the cookie is set to aeternity_cookie
%%%            The test profile has a name and a cookie set in {dist_node, ...}
%%% @end
%%% Created : 23 Jan 2019 by Thomas Arts <thomas@SpaceGrey.lan>

-module(tx_primops_eqc).

-include_lib("eqc/include/eqc.hrl").
-include_lib("eqc/include/eqc_statem.hrl").

-compile([export_all, nowarn_export_all]).
-define(REMOTE_NODE, 'oldepoch@localhost').
-define(Patron, <<1, 1, 0:240>>).

-record(account, {key, amount, nonce}).

%% -- State and state functions ----------------------------------------------
initial_state() ->
    #{}.

%% -- Generators -------------------------------------------------------------

%% -- Common pre-/post-conditions --------------------------------------------
command_precondition_common(_S, _Cmd) ->
    true.

precondition_common(_S, _Call) ->
    true.

postcondition_common(_S, _Call, _Res) ->
    true.

%% -- Operations -------------------------------------------------------------

%% --- Operation: init ---
init_pre(S) ->
    not maps:is_key(accounts, S).

init_args(_S) ->
    [aetx_env:tx_env(0, 1)].

init(_) ->
    Trees = rpc(aec_trees, new_without_backend, [], fun hash_equal/2),
    EmptyAccountTree = rpc(aec_trees, accounts, [Trees]),
    Account = rpc(aec_accounts, new, [?Patron, 1200000]), 
    AccountTree = rpc(aec_accounts_trees, enter, [Account, EmptyAccountTree]),
    InitialTrees = rpc(aec_trees, set_accounts, [Trees, AccountTree], fun hash_equal/2),
    put(trees, InitialTrees),
    InitialTrees, 
    ok.

init_next(S, _Value, [TxEnv]) ->
    S#{tx_env => TxEnv, 
       accounts => [#account{key = ?Patron, amount = 1200000, nonce = 1}]}.

%% --- Operation: mine ---
mine_pre(S) ->
    maps:is_key(accounts, S).

mine_args(#{tx_env := TxEnv}) ->
    Height = aetx_env:height(TxEnv),
    [Height].

mine_pre(#{tx_env := TxEnv}, [H]) ->
    aetx_env:height(TxEnv) == H.

mine(Height) ->
    Trees = get(trees),
    NewTrees = rpc(aec_trees, perform_pre_transformations, [Trees, Height + 1], fun hash_equal/2),
    put(trees, NewTrees),
    NewTrees,
    ok.

mine_next(#{tx_env := TxEnv} = S, _Value, [H]) ->
    S#{tx_env => aetx_env:set_height(TxEnv, H + 1)}.

%% --- Operation: spend ---
spend_pre(S) ->
    maps:is_key(accounts, S).

spend_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args, 
    ?LET([{SenderTag, Sender}, {ReceiverTag, Receiver}], 
         vector(2, gen_account_pubkey(Accounts)),
         ?LET([Amount, Nonce], [nat(), oneof([0, 1, Sender#account.nonce, 100])],
              [Env, {SenderTag, Sender#account.key}, {ReceiverTag, Receiver#account.key},
               #{sender_id => aec_id:create(account, Sender#account.key), 
                 recipient_id => aec_id:create(account, Receiver#account.key), 
                 amount => Amount, 
                 fee => choose(1, 10), 
                 nonce => Nonce,
                 payload => utf8()}])),
         Args ++ [spend_valid(Accounts, [lists:nth(2, Args), lists:last(Args)])]).

spend_pre(#{accounts := Accounts}, [_Env, Sender, {ReceiverTag, Receiver}, Tx, Correct]) ->
    Valid = spend_valid(Accounts, [Sender, Tx]),
    ReceiverOk = 
        case ReceiverTag of 
            new -> lists:keyfind(Receiver, #account.key, Accounts) == false;
            existing -> lists:keyfind(Receiver, #account.key, Accounts) =/= false
        end,
    ReceiverOk andalso Correct == Valid.

spend_valid(Accounts, [{_, Sender}, Tx]) ->
    case lists:keyfind(Sender, #account.key, Accounts) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(amount, Tx) + maps:get(fee, Tx) andalso
                maps:get(fee, Tx) >= 0   %% it seems fee == 0 does not return error
    end.


%% Don't get adapt to work! Needs investigation.
%% spend_adapt(_S, [Env, Sender, Receiver, Tx, Correct]) ->
%%     %% We only get here if spend is not Correct
%%     [Env, Sender, Receiver, Tx, not Correct].
    

spend(Env, _Sender, _Receiver, Tx, _Correct) ->
    Trees = get(trees),
    {ok, AeTx} = rpc(aec_spend_tx, new, [Tx]),
    {_, SpendTx} = aetx:specialize_type(AeTx),

    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE, aec_spend_tx, check, [SpendTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aec_spend_tx, process, [SpendTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aec_spend_tx, process, [SpendTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.


spend_next(#{accounts := Accounts} = S, _Value, 
           [_Env, {_SenderTag, Sender}, {ReceiverTag, Receiver}, Tx, Correct]) ->
    if Correct ->
            %% Classical mistake if sender and receiver are the same! Update carefully
            SAccount = lists:keyfind(Sender, #account.key, Accounts),
            RAccount = 
                case ReceiverTag of
                    new -> #account{key = Receiver, amount = 0, nonce = 1};
                    existing ->
                        lists:keyfind(Receiver, #account.key, Accounts)
                end,
            case Sender == Receiver of
                false ->
                    S#{accounts => 
                           (Accounts -- [RAccount, SAccount]) ++
                           [SAccount#account{amount = SAccount#account.amount - maps:get(amount,Tx) - maps:get(fee, Tx), 
                                             nonce = maps:get(nonce, Tx) + 1},
                            RAccount#account{amount = maps:get(amount,Tx) + RAccount#account.amount}]};  %% add to end of list
                true ->
                    S#{accounts => 
                           (Accounts -- [SAccount]) ++
                           [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx), 
                                             nonce = maps:get(nonce, Tx) + 1}]}
            end;
       not Correct -> 
            S
    end.

spend_post(_S, [_Env, _, _, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        {'EXIT',
         {different, {error, account_nonce_too_low},
          {error, insufficient_funds}}} -> not Correct;
        {'EXIT',
         {different, {error, account_nonce_too_high},
          {error, insufficient_funds}}} -> not Correct;
        _ -> false
    end.


spend_features(S, [_Env, {_, Sender}, {_, Receiver}, Tx, Correct], Res) ->
    [{spend_accounts, length(maps:get(accounts, S))}, 
     {spend_correct, Correct}] ++
        [ spend_to_self || Sender == Receiver andalso Correct] ++
             [ {spend, zero} || maps:get(amount, Tx) == 0 andalso Correct] ++
             [ {spend, zero_fee} ||  maps:get(fee, Tx) == 0 ] ++
        [{spend_error, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: register_oracle ---
register_oracle_pre(S) ->
    length(maps:get(accounts, S, [])) > 1.

register_oracle_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args, 
         ?LET({SenderTag, Sender}, gen_account_pubkey(lists:keydelete(?Patron, #account.key, Accounts)),
              ?LET([Amount, Nonce], [nat(), oneof([0, 1, Sender#account.nonce, 100])],
                   [Env, {SenderTag, Sender#account.key},
                    #{account_id => aec_id:create(account, Sender#account.key), 
                      query_format    => <<"{foo: bar}"/utf8>>,
                      response_format => <<"boolean()"/utf8>>,
                      query_fee       => Amount,
                      fee => choose(1, 10), 
                      nonce => Nonce,
                      oracle_ttl => {delta, 100}}])),
         Args ++ [register_oracle_valid(S, [lists:nth(2, Args), lists:last(Args)])]).

register_oracle_pre(S, [_Env, Sender, Tx, Correct]) ->
    %% Sender /= ?Patron andalso
    Correct == register_oracle_valid(S, [Sender, Tx]).

register_oracle_valid(S, [{_, Sender}, Tx]) ->
    case lists:keyfind(Sender, #account.key, maps:get(accounts, S, [])) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(fee, Tx) andalso
                not lists:member(Sender, maps:get(oracles, S, []))
    end.

register_oracle(Env, Sender, Tx, Correct) ->
    Trees = get(trees),
    {ok, AeTx} = rpc(aeo_register_tx, new, [Tx]),
    {oracle_register_tx, OracleTx} = aetx:specialize_type(AeTx),
    
    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE,aeo_register_tx, check, [OracleTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aeo_register_tx, process, [OracleTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aeo_register_tx, process, [OracleTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.
    

register_oracle_next(#{accounts := Accounts} = S, _Value, [_Env, {_, Sender}, Tx, Correct]) ->
    if Correct ->
            SAccount = lists:keyfind(Sender, #account.key, Accounts),
            S#{accounts => 
                   (Accounts -- [SAccount]) ++
                   [SAccount#account{amount = SAccount#account.amount - maps:get(fee, Tx), 
                                     nonce = maps:get(nonce, Tx) + 1}],
               oracles =>
                   maps:get(oracles, S, []) ++ [Sender]};
       not Correct -> 
            S
    end.

register_oracle_post(_S, [_Env, _Sender, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        {'EXIT',
         {different, {error, account_nonce_too_low},
          {error, insufficient_funds}}} -> not Correct;
        {'EXIT',
         {different, {error, account_nonce_too_high},
          {error, insufficient_funds}}} -> not Correct;
        _ -> false
    end.

register_oracle_features(S, [_Env, {_, Sender}, Tx, Correct], Res) ->
    [{register_oracle_correct, Correct}] ++
             [ {oracle_query_fee, zero} || maps:get(query_fee, Tx) == 0 andalso Correct] ++
             [ {oracle, zero_fee} ||  maps:get(fee, Tx) == 0 ] ++
        [{register_oracle_error, Res} || is_tuple(Res) andalso element(1, Res) == error].

%% -- Property ---------------------------------------------------------------
prop_tx_primops() ->
    ?FORALL(Cmds, commands(?MODULE),
    ?TIMEOUT(3000,
    begin
        %% io:format("Pinging ~p~n", [?REMOTE_NODE]),

        pong = net_adm:ping(?REMOTE_NODE),
        %% io:format("Start run test ~p~n", [Cmds]),

        {H, S, Res} = run_commands(Cmds),
        Height = 
            case maps:get(tx_env, S, undefined) of
                undefined -> 0;
                TxEnv -> aetx_env:height(TxEnv)
            end,
        %% io:format("Did run test"),
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            measure(height, Height,
            aggregate(call_features(H),
                pretty_commands(?MODULE, Cmds, {H, S, Res},
                                Res == ok)))))
    end)).

bugs() -> bugs(10).

bugs(N) -> bugs(N, []).

bugs(Time, Bugs) ->
    more_bugs(eqc:testing_time(Time, prop_tx_primops()), 20, Bugs).


%% --- local helpers ------

strict_equal(X, Y) ->
     case X == Y of 
         true -> X; 
         false -> exit({different, X, Y}) 
     end.

hash_equal(X, Y) ->
     case {X, Y} of 
         {{ok, L}, {ok, R}} -> 
             case aec_trees:hash(L) == aec_trees:hash(R) of
                 true -> X;
                 false -> exit({hash_differs, X, Y})
             end;
         {E, E} -> E;
         _ -> exit({different, X, Y}) 
     end.
 
rpc(Module, Fun, Args) ->
    rpc(Module, Fun, Args, fun(X,Y) -> strict_equal(X, Y) end).

rpc(Module, Fun, Args, InterpretResult) ->
    Local = rpc:call(node(), Module, Fun, Args, 1000),
    Remote = rpc:call(?REMOTE_NODE, Module, Fun, Args, 1000),
    eq_rpc(Local, Remote, InterpretResult).

eq_rpc(Local, Remote, InterpretResult) ->
    case {Local, Remote} of
        {{badrpc, {'EXIT', {E1, _}}},{badrpc, {'EXIT', {E2, _}}}} when E1 == E2 ->
            Local;
        _ ->
            InterpretResult(Local, Remote)
    end.
    
%% -- Generators -------------------------------------------------------------


gen_account_pubkey(Accounts) ->
    oneof([?LAZY({existing, elements(Accounts)}), 
           ?LAZY({new, #account{key = noshrink(binary(32)), amount = 0, nonce = 0 }})]).

unique_name(List) ->
    ?LET([W], 
         noshrink(?SUCHTHAT([Word], 
                            eqc_erlang_program:words(1), not lists:member(Word, List))), 
         W).


