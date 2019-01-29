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
-record(query, {sender, id, fee, response_ttl}).

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

mine_adapt(#{tx_env := TxEnv}, [_]) ->
    [aetx_env:height(TxEnv)];
mine_adapt(_, _) ->
    false.


mine(Height) ->
    Trees = get(trees),
    NewTrees = rpc(aec_trees, perform_pre_transformations, [Trees, Height + 1], fun hash_equal/2),
    put(trees, NewTrees),
    NewTrees,
    ok.

mine_next(#{tx_env := TxEnv} = S, _Value, [H]) ->
    Payback = [ Query || Query <- maps:get(queries, S, []), Query#query.response_ttl =< H],
    Accounts = [ case lists:keyfind(Account#account.key, #query.sender, Payback) of
                     false -> Account;
                     Query -> Account#account{amount = Account#account.amount + Query#query.fee}
                 end || Account <- maps:get(accounts, S, [])],
    S#{tx_env => aetx_env:set_height(TxEnv, H + 1),
       accounts => Accounts,
       queries =>  maps:get(queries, S, []) -- Payback
      }.

mine_features(S, [H], _Res) ->
    [mine_response_ttl || [ true || Query <- maps:get(queries, S, []), Query#query.response_ttl =< H ] =/= [] ] ++
        [mine].


%% --- Operation: spend ---
spend_pre(S) ->
    maps:is_key(accounts, S).

spend_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args, 
    ?LET([{SenderTag, Sender}, {ReceiverTag, Receiver}], 
         vector(2, gen_account_pubkey(Accounts)),
         ?LET([Amount, Nonce], [nat(), gen_nonce(Sender)],
              [Env, {SenderTag, Sender#account.key}, {ReceiverTag, Receiver#account.key},
               #{sender_id => aec_id:create(account, Sender#account.key), 
                 recipient_id => aec_id:create(account, Receiver#account.key), 
                 amount => Amount, 
                 fee => choose(1, 10), 
                 nonce => Nonce,
                 payload => utf8()}])),
         Args ++ [spend_valid(S, [Env, lists:nth(2, Args), lists:last(Args)])]).

spend_pre(#{accounts := Accounts} = S, [Env, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx, Correct]) ->
    Valid = spend_valid(S, [Env, {SenderTag, Sender}, Tx]),
    ReceiverOk = 
        case ReceiverTag of 
            new -> lists:keyfind(Receiver, #account.key, Accounts) == false;
            existing -> lists:keyfind(Receiver, #account.key, Accounts) =/= false
        end,
    ReceiverOk andalso Correct == Valid
        andalso correct_height(S, Env).

spend_valid(#{accounts := Accounts}, [_Env, {_, Sender}, Tx]) ->
    case lists:keyfind(Sender, #account.key, Accounts) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(amount, Tx) + maps:get(fee, Tx) andalso
                maps:get(fee, Tx) >= 0   %% it seems fee == 0 does not return error
    end.

spend_adapt(#{tx_env := TxEnv} = S, [_, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx, _Correct]) ->
    [TxEnv, {SenderTag, Sender}, {ReceiverTag, Receiver}, Tx, spend_valid(S, [TxEnv, {SenderTag, Sender}, Tx])];
spend_adapt(_, _) ->
    false.

    
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
        _ -> not Correct andalso valid_mismatch(Res)
    end.


spend_features(S, [_Env, {_, Sender}, {_, Receiver}, Tx, Correct], Res) ->
    [{spend_accounts, length(maps:get(accounts, S))}, 
     {correct,  if Correct -> spend; true -> false end}] ++
        [ spend_to_self || Sender == Receiver andalso Correct] ++
             [ {spend, zero} || maps:get(amount, Tx) == 0 andalso Correct] ++
             [ {spend, zero_fee} ||  maps:get(fee, Tx) == 0 ] ++
        [{spend, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: register_oracle ---
register_oracle_pre(S) ->
    length(maps:get(accounts, S, [])) > 1.

register_oracle_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args, 
         ?LET({SenderTag, Sender}, gen_account_pubkey(lists:keydelete(?Patron, #account.key, Accounts)),
              [Env, {SenderTag, Sender#account.key},
                    #{account_id => aec_id:create(account, Sender#account.key), 
                      query_format    => <<"send me any string"/utf8>>,
                      response_format => <<"boolean()"/utf8>>,
                      query_fee       => nat(),
                      fee => choose(1, 10), 
                      nonce => gen_nonce(Sender),
                      oracle_ttl => {delta, 100}}]),
         Args ++ [register_oracle_valid(S, [lists:nth(2, Args), lists:last(Args)])]).

register_oracle_pre(S, [Env, Sender, Tx, Correct]) ->
    Correct == register_oracle_valid(S, [Sender, Tx]) andalso correct_height(S, Env).

register_oracle_valid(S, [{_, Sender}, Tx]) ->
    case lists:keyfind(Sender, #account.key, maps:get(accounts, S, [])) of
        false -> false;
        SenderAccount ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(fee, Tx) andalso
                not lists:keymember(Sender, 1, maps:get(oracles, S, []))
    end.

register_oracle_adapt(#{tx_env := TxEnv} = S, [_, Sender, Tx, _Correct]) ->
    [TxEnv, Sender, Tx, register_oracle_valid(S, [Sender, Tx])];
register_oracle_adapt(_, _) ->
    %% in case we don't even have a TxEnv
    false.

register_oracle(Env, _Sender, Tx, _Correct) ->
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
                   maps:get(oracles, S, []) ++ [{Sender, maps:get(query_fee, Tx)}]};
       not Correct -> 
            S
    end.

register_oracle_post(_S, [_Env, _Sender,_Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        _ -> not Correct andalso valid_mismatch(Res)
    end.

register_oracle_features(_S, [_Env, {_, _Sender}, Tx, Correct], Res) ->
    [{correct, if Correct -> register_oracle; true -> false end} ] ++
             [ {oracle_query_fee, zero} || maps:get(query_fee, Tx) == 0 andalso Correct] ++
             [ {oracle, zero_fee} ||  maps:get(fee, Tx) == 0 ] ++
        [{register_oracle, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% --- Operation: query_oracle ---
query_oracle_pre(S) ->
     maps:is_key(accounts, S).

query_oracle_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args, 
         ?LET([{SenderTag, Sender}, {_, Oracle}], 
              vector(2, gen_account_pubkey(Accounts)),
                   [Env, {SenderTag, Sender#account.key}, Oracle#account.key,
                    #{sender_id => aec_id:create(account, Sender#account.key), 
                      oracle_id => aec_id:create(oracle, Oracle#account.key), 
                      query => oneof([<<"{foo: bar}"/utf8>>, <<"any string"/utf8>>, <<>>]),
                      query_fee => nat(),
                      query_ttl => {delta, 3},
                      response_ttl => {delta, 3},
                      fee => choose(1, 10), 
                      nonce => gen_nonce(Sender)
                     }]),
         Args ++ [query_oracle_valid(S, Args)]).

query_oracle_pre(S, [Env, {SenderTag, Sender}, Oracle, Tx, Correct]) ->
    Correct == query_oracle_valid(S, [Env, {SenderTag, Sender}, Oracle, Tx]) andalso correct_height(S, Env).

query_oracle_valid(S, [_Env, {_SenderTag, Sender}, Oracle, Tx]) ->
    case {lists:keyfind(Sender, #account.key, maps:get(accounts, S, [])),
          lists:keyfind(Oracle, 1, maps:get(oracles, S, []))}
          of
        {false, _} -> false;
        {_, false} -> false;
        {SenderAccount, {_, QueryFee}} ->
            SenderAccount#account.nonce == maps:get(nonce, Tx) andalso
                SenderAccount#account.amount >= maps:get(fee, Tx) + maps:get(query_fee, Tx) andalso
                maps:get(query_fee, Tx) >= QueryFee
    end.

query_oracle_adapt(#{tx_env := TxEnv} = S, [_Env, Sender, Oracle, Tx, _Correct]) ->
    [TxEnv, Sender, Oracle, Tx, query_oracle_valid(S, [TxEnv, Sender, Oracle, Tx])];
query_oracle_adapt(_, _) ->
    false.


query_oracle(Env, _Sender, _Oracle, Tx, _Correct) ->
    Trees = get(trees),
    {ok, AeTx} = rpc(aeo_query_tx, new, [Tx]),
    {oracle_query_tx, OracleTx} = aetx:specialize_type(AeTx),
    
    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE,aeo_query_tx, check, [OracleTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aeo_query_tx, process, [OracleTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aeo_query_tx, process, [OracleTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

query_oracle_next(#{accounts := Accounts} = S, _Value, [Env, {_, Sender}, Oracle, Tx, Correct]) ->
    if Correct ->
            {delta, Delta} = maps:get(response_ttl, Tx),
            SAccount = lists:keyfind(Sender, #account.key, Accounts),
            S#{accounts => 
                   (Accounts -- [SAccount]) ++
                   [SAccount#account{
                      amount = SAccount#account.amount - maps:get(fee, Tx) - maps:get(query_fee, Tx), 
                      nonce = maps:get(nonce, Tx) + 1}],
              queries => maps:get(queries, S, []) ++
                   [#query{sender = Sender, 
                           id = {Sender, maps:get(nonce, Tx), Oracle}, 
                           response_ttl = Delta + aetx_env:height(Env), 
                           fee = maps:get(query_fee, Tx)}]};
       not Correct -> 
            S
    end.

query_oracle_post(_S, [_Env, _Sender, _Oracle, _Tx, Correct], Res) ->
     case Res of
        {error, _} -> not Correct;
        ok -> Correct;
         _ -> not Correct andalso valid_mismatch(Res)
    end.

query_oracle_features(_S, [_Env, _, _, Tx, Correct], Res) ->
    [{correct, if Correct -> query_oracle; true -> false end} ] ++
             [ {query_query_fee, zero} || maps:get(query_fee, Tx) == 0 andalso Correct] ++
             [ {query_oracle, zero_fee} ||  maps:get(fee, Tx) == 0 ] ++
        [{query_oracle, Res} || is_tuple(Res) andalso element(1, Res) == error].

%% --- Operation: response_oracle ---
response_oracle_pre(S) ->
     maps:get(queries, S, []) =/= [].

%% Only responses to existing query tested for the moment, no fault injection
response_oracle_args(#{accounts := Accounts, tx_env := Env} = S) ->
    ?LET(Args, 
         ?LET({Sender, Nonce, Oracle}, 
               frequency([{99, ?LET(Query, elements(maps:get(queries, S)), Query#query.id)},
                          {1, {?Patron, 2, ?Patron}}]),
              [Env, {Sender, Nonce, Oracle},
               #{oracle_id => aec_id:create(oracle, Oracle), 
                 query_id => aeo_query:id(Sender, Nonce, Oracle),
                 response => <<"yes, you can">>,
                 response_ttl => {delta, 3},
                 fee => choose(1, 10), 
                 nonce => case lists:keyfind(Oracle, #account.key, Accounts) of
                              false -> 1;
                              Account -> Account#account.nonce
                          end
                }]),
         Args ++ [response_oracle_valid(S, Args)]).

response_oracle_pre(S, [Env, QueryId, Tx, Correct]) ->
    Correct == response_oracle_valid(S, [Env, QueryId, Tx]) 
        andalso correct_height(S, Env).

response_oracle_valid(S, [_Env, {_, _, Oracle} = QueryId, Tx]) ->
    case lists:keyfind(Oracle, #account.key, maps:get(accounts, S)) of
        false -> false;
        OracleAccount ->
            Query = lists:keyfind(QueryId, #query.id, maps:get(queries, S, [])),
            OracleAccount#account.nonce == maps:get(nonce, Tx) andalso
                OracleAccount#account.amount >= maps:get(fee, Tx) andalso 
                Query =/= false
    end.

response_oracle(Env, _QueryId, Tx, _Correct) ->
    Trees = get(trees),
    {ok, AeTx} = rpc(aeo_response_tx, new, [Tx]),
    {oracle_response_tx, OracleTx} = aetx:specialize_type(AeTx),
    
    %% old version
    Remote = 
        case rpc:call(?REMOTE_NODE,aeo_response_tx, check, [OracleTx, Trees, Env], 1000) of
            {ok, Ts} ->
                rpc:call(?REMOTE_NODE, aeo_response_tx, process, [OracleTx, Ts, Env], 1000);
            OldError ->
                OldError
        end,

    Local = rpc:call(node(), aeo_response_tx, process, [OracleTx, Trees, Env], 1000),
    case catch eq_rpc(Local, Remote, fun hash_equal/2) of
        {ok, NewTrees} ->
            put(trees, NewTrees),
            ok;
        Other -> Other
    end.

response_oracle_next(#{accounts := Accounts} = S, _Value, [_Env, QueryId, Tx, Correct]) ->
    if Correct ->
            {_, _, Oracle} = QueryId, 
            OracleAccount = lists:keyfind(Oracle, #account.key, Accounts),
            Query = lists:keyfind(QueryId, #query.id, maps:get(queries, S, [])),
            QueryFee = Query#query.fee,
            {delta, Delta} = maps:get(response_ttl, Tx),

            S#{accounts => 
                   (Accounts -- [OracleAccount]) ++
                   [OracleAccount#account{
                      amount = OracleAccount#account.amount - maps:get(fee, Tx) + QueryFee, 
                      nonce = maps:get(nonce, Tx) + 1}],
              queries => maps:get(queries, S, []) -- [Query]};
       not Correct -> 
            S
    end.

response_oracle_post(_S, [_Env, _Oracle, _Tx, Correct], Res) ->
    case Res of
        {error, _} -> not Correct;
        ok -> Correct;
        _ -> not Correct andalso valid_mismatch(Res)
    end.

response_oracle_features(_S, [_Env, _, _Tx, Correct], Res) ->
    [{correct, if Correct -> response_oracle; true -> false end} ] ++
        [{response_oracle, Res} || is_tuple(Res) andalso element(1, Res) == error].


%% -- Property ---------------------------------------------------------------
prop_tx_primops() ->
    eqc:dont_print_counterexample(
    ?FORALL(Cmds, commands(?MODULE),
    begin
        pong = net_adm:ping(?REMOTE_NODE),

        {H, S, Res} = run_commands(Cmds),
        Height = 
            case maps:get(tx_env, S, undefined) of
                undefined -> 0;
                TxEnv -> aetx_env:height(TxEnv)
            end,
        check_command_names(Cmds,
            measure(length, commands_length(Cmds),
            measure(height, Height,
            features(call_features(H),
            aggregate(call_features(H),
                pretty_commands(?MODULE, Cmds, {H, S, Res},
                                Res == ok))))))
    end)).

bugs() -> bugs(10).

bugs(N) -> bugs(N, []).

bugs(Time, Bugs) ->
    more_bugs(eqc:testing_time(Time, prop_tx_primops()), 20, Bugs).



%% --- local helpers ------

correct_height(#{tx_env := TxEnv}, Env) ->
    aetx_env:height(TxEnv) == aetx_env:height(Env).

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


valid_mismatch({'EXIT',{different, {error, account_nonce_too_low},
                        {error, insufficient_funds}}}) -> true;
valid_mismatch({'EXIT', {different, {error, account_nonce_too_high},
                         {error, insufficient_funds}}}) -> true;
valid_mismatch(_) -> false.
%% -- Generators -------------------------------------------------------------


gen_account_pubkey(Accounts) ->
    oneof([?LAZY({existing, elements(Accounts)}), 
           ?LAZY({new, #account{key = noshrink(binary(32)), amount = 0, nonce = 0 }})]).

unique_name(List) ->
    ?LET([W], 
         noshrink(?SUCHTHAT([Word], 
                            eqc_erlang_program:words(1), not lists:member(Word, List))), 
         W).

gen_nonce(Account) ->
    %% 0 is always wrong, 1 is often too low and 100 is often too high
    frequency([{1, 0}, {1, 1}, {97, Account#account.nonce}, {1, 100}]).




