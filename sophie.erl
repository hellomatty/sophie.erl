-module(sophie).

%% A (partial) solution to Facebook's Find Sophie puzzle, in erlang
%%   see http://www.facebook.com/careers/puzzles.php?puzzle_id=11
%%
%% hellomatty@gmail.com

-export([start/1]).

-define(INDEX(I, J, G), ((I - 1) * G#graph.n + J)).
-define(CORES, 2).

-record(graph, {
  n,
  nodes,
  costs,
  probabilities
}).

-record(step, {
  node,
  probability = 1.0,
  elapsed = 0.0,
  expected = 0.0
}).

start(Filename) ->
%%  fprof:trace(start),
  G = new_graph(with_file(Filename, fun(Fd) ->
    {map_n_lines(Fd, fun(L) ->
      [Name, Probability] = string:tokens(L, " "),
      {node, Name, list_to_float(fix_decimal(Probability))}
    end), map_n_lines(Fd, fun(L) ->
      [From, To, Cost] = string:tokens(L, " "),
      {edge, From, To, list_to_integer(Cost)}
    end)}
  end)),
  P = local_optimal_path(G),
  S = walk_path(P, G),
  io:format("local optimal path: ~w~n", [P]),
  Best = backtrack(P, S, G),
  io:format("best: ~w~n", [Best]).
%%  fprof:trace(stop),
%%  fprof:profile(),
%%  fprof:analyse([{callers, false}, {details, false}, {totals, true}]).

local_optimal_path(G) ->
  [H|T] = lists:seq(1, G#graph.n),
  local_optimal_path([H], T, local_optimals(G), G).
local_optimal_path(P, [], _, _) ->
   P;
local_optimal_path([H|_] = P, Remaining, O, G) ->
  case dict:find(H, O) of
    {ok, Scores} ->
      Next = first_from(Scores, Remaining),
      local_optimal_path([Next|P], lists:delete(Next, Remaining), O, G);
    _ ->
      exit({optimals_not_known_for, H})
  end.

first_from([{score, H, _}|T], L) ->
  case lists:member(H, L) of
    true ->
      H;
    _ ->
      first_from(T, L)
  end.

local_optimals(G) ->
  local_optimals(G#graph.n, G#graph.n, dict:new(), G, []).
local_optimals(0, _, D, _, _) ->
%%io:format("optimals ~w~n", [dict:to_list(D)]),
  D;
local_optimals(I, 0, D, G, Scores) ->
  NewDict = dict:store(I, lists:sort(fun({score, _, Ascore}, {score, _, Bscore}) ->
    Ascore < Bscore
  end, Scores), D),
  local_optimals(I - 1, G#graph.n, NewDict, G, []);
local_optimals(I, I, D, G, Scores) ->
  local_optimals(I, I - 1, D, G, Scores); 
local_optimals(I, J, D, G, Scores) ->
%%io:format("optimals i ~w j ~w ", [I, J]),
  S = {score, J, cost(I, J, G) * (1.0 - probability(J, G))},
%%io:format("~w~n", [S]),
  local_optimals(I, J - 1, D, G, [S|Scores]).
  
walk_path(P, G) ->
  [H|T] = lists:reverse(P),
  walk_path(T, [#step{node = H, probability = 1.0 - probability(H, G)}], G).
walk_path([], S, _) ->
  S;
walk_path([H|T], [Hs|_] = S, G) ->
  walk_path(T, [step(Hs, H, G)|S], G).

backtrack(P, [Hs|_] = S, G) ->
  backtrack(P, lists:reverse(S), length(P) - 1, Hs#step.expected, G, []).
backtrack(_, _, 1, L, G, Q) ->
  loop(Q, [], L, G);
backtrack(P, [Hs|Ts], Depth, Limit, G, Q) ->
  {Branches, Root} = lists:split(Depth, P),
%%io:format("backtrack ~w ~w ~w~n", [Root, Branches, Hs]),
  backtrack(P, Ts, Depth - 1, Limit, G, [{backtrack, Root, Branches, Hs}|Q]).

loop([], [], L, _) ->
  L;
loop([{backtrack, Root, Branches, S}|T], Children, Limit, G) when
    length(Children) < ?CORES ->
  Master = self(),
  Pid = spawn(fun() ->
    io:format("~w backtracking ~w ~w limit ~w~n", [self(), Root, Branches, Limit]),
    breadth_first(Master, Root, Branches, S#step.probability, S#step.elapsed, S#step.expected, Limit, G),
    io:format("~w backtrack done~n", [self() ]),
    Master ! {done, self()}
  end),
  loop(T, [Pid|Children], Limit, G);
loop(Q, Children, Limit, G) ->
   receive
    {done, Pid} ->
      loop(Q, lists:delete(Pid, Children), Limit, G);
    {limit, L} ->
      lists:foreach(fun(C) ->
        C ! {limit, L}
      end, Children),
      loop(Q, Children, L, G);
    _ ->
      loop(Q, Children, Limit, G)
  end.

breadth_first(Master, R, B, P, El, Ex, L, G) ->
%%io:format("~w bf start ~w p ~w el ~w ex ~w~n", [self(), R, P, El, Ex]),
%%io:format("~w   on to ~w~n", [self(), B]),
  breadth_first(Master, R, B, B, P, El, Ex, L, G).
breadth_first(_, _, [], _, _, _, _, L, _) ->
  L;
breadth_first(Master, [Hr|_] = R, [Hn|Tn], B, P, El, Ex, L, G) ->
  HnP = probability(Hn, G),
  HnC = cost(Hr, Hn, G),
  PDelta = P - HnP,
  ElDelta = El + HnC,
  ExDelta = Ex + (ElDelta * HnP),
%%io:format("~w     at ~w p ~w el ~w ex ~w)~n", [self(), Hn, PDelta, ElDelta, ExDelta]),
  NewLimit = if
    (ExDelta + (PDelta * ElDelta)) >= L ->
%%  ExDelta >= L ->
%%    io:format("~w prune ~w > ~w~n", [self(), ExDelta, L]),
      L;
    PDelta < 0.001 ->
      io:format("~w solution ~w ~w~n", [self(), ExDelta, [Hn|R]]),
      Master ! {limit, ExDelta},
      ExDelta;
    true ->
      Remaining = lists:delete(Hn, B),
%%    io:format("~w       on to ~w~n", [self(), Remaining]),
      breadth_first(Master, [Hn|R], Remaining, PDelta, ElDelta, ExDelta, update_limit(L), G)
  end,
%%io:format("~w result ~w limit ~w~n", [self(), NewLimit, L]),
  breadth_first(Master, R, Tn, B, P, El, Ex, NewLimit, G).

update_limit(L) ->
  receive
    {limit, Limit} ->
      update_limit(Limit)
    after
      0 ->
        L
  end.

step(Last, To, G) ->
  P = probability(To, G),
  C = cost(Last#step.node, To, G),
  E = Last#step.elapsed + C,
  #step{
    node = To,
    probability = Last#step.probability - P,
    elapsed = E,
    expected = Last#step.expected + E * P
  }.

new_graph({Nodes, Edges}) ->
  N = length(Nodes),
  G = join(Edges, #graph{
    n = N,
    nodes = Nodes,
    costs = list_to_tuple([infinity || _ <- lists:seq(1, N * N)]),
    probabilities = list_to_tuple([P || {node, _, P} <- Nodes])
  }),
  floyd_warshall(initialise_costs(G)).

initialise_costs(G) ->
  initialise_costs(G#graph.n, G).
initialise_costs(0, G) ->
  G;
initialise_costs(N, G) ->
  initialise_costs(N - 1, set_cost(N, N, 0.0, G)).

join([], G) ->
  G;
join([{edge, From, To, Cost}|T], G) ->
  FromIndex = lookup(From, G),
  ToIndex = lookup(To, G),
  join(T, set_cost(FromIndex, ToIndex, Cost, set_cost(ToIndex, FromIndex, Cost, G))).

probability(N, G) ->
  element(N, G#graph.probabilities).

cost(From, To, G) ->
  element(?INDEX(From, To, G), G#graph.costs).

cost_via(I, J, K, G) ->
  IK = cost(I, K, G),
  KJ = cost(K, J, G),
  if
    IK =:= infinity;
    KJ =:= infinity ->
      infinity;
    true ->
      IK + KJ
  end.

floyd_warshall(G) ->
  floyd_warshall(G#graph.n, G#graph.n, G#graph.n, G).
floyd_warshall(0, _, _, G) ->
%%io:format("fw costs: ~w~n", [dict:to_list(G#graph.costs)]),
  G;
floyd_warshall(K, J, 0, G) ->
  floyd_warshall(K, J - 1, G#graph.n, G);
floyd_warshall(K, 0, _, G) ->
  floyd_warshall(K - 1, G#graph.n, G#graph.n, G);
floyd_warshall(K, J, I, G) ->
  OldCost = cost(I, J, G),
  NewCost = cost_via(I, J, K, G),
%%io:format("fw i ~w j ~w k ~w old ~w new ~w~n", [I, J, K, OldCost, NewCost]),
  case NewCost =< OldCost of
    false ->
      floyd_warshall(K, J, I - 1, G);
    _ ->
      floyd_warshall(K, J, I - 1, set_cost(I, J, NewCost, G))
  end.

lookup(Name, G) ->
  lookup(Name, G#graph.nodes, 1).
lookup(Name, [{node, Name, _}|_], I) ->
  I;
lookup(Name, [_|T], I) ->
  lookup(Name, T, I + 1).

set_cost(From, To, Cost, G) ->
  G#graph{costs = setelement(?INDEX(From, To, G), G#graph.costs, Cost)}.

with_file(Filename, Fun) ->
  {ok, Fd} = file:open(Filename, [read]),
  Result = Fun(Fd),
  ok = file:close(Fd),
  Result.

map_n_lines(Fd, Fun) ->
  N = list_to_integer(read_line(Fd)),
  map_n_lines(Fd, Fun, N, []).
map_n_lines(_, _, 0, Accum) ->
  lists:reverse(Accum);
map_n_lines(Fd, Fun, N, Accum) ->
  map_n_lines(Fd, Fun, N - 1, [Fun(read_line(Fd))|Accum]).

read_line(Fd) ->
  case io:get_line(Fd, "") of
    eof  ->
      exit(eof);
    Line ->
      case lists:last(Line) of
        10 ->
          lists:sublist(Line, 1, length(Line) - 1);
        _ ->
          Line
    end
  end.

fix_decimal("0") ->
  "0.0";
fix_decimal([$.|_] = L) ->
  [$0|L];
fix_decimal(L) ->
  L.
