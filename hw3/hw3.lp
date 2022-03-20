%*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% KRR 2022, HOMEWORK ASSIGNMENT 3 %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Name:             Matteo Rosati
Student number:   13858149

Name:             Giulio Starace
Student number:   13010840

*%

%*
INPUT REPRESENTATION:
- Represent the input of the problem (the map, the trucks, etc.)
*%

% Represent the nodes and edges of the map using node/1 and edge/2.
% there are 13 nodes
node(1..13).
% and they are connected as such
edge(1,3). 
edge(1,4). 
edge(2,4). 
edge(2,5). 
edge(3,4). 
edge(3,7). 
edge(4,5). 
edge(4,7).
edge(4,8). 
edge(5,8).
edge(5,9). 
edge(5,6). 
edge(6,10). 
edge(7,8). 
edge(7,11). 
edge(8,9).
edge(9,10). 
edge(10,13). 
edge(12,13). 
edge(11,12).

% Edges are undirected, so include their reverse
edge(X,Y) :- edge(Y,X), node(Y), node(X).

#const max_charge = 10.

% truck ids and warehouse capacity
truck_id(1..3).
warehouse_capacity(0..5).

% charging station at node 1 and 2
station(1). 
station(2). 

% parking slot at nodes 11, 12, 13
parking(11). 
parking(12). 
parking(13).

% delivery locations at nodes 3 and 6
deliver_location(3;6).

% warehouse at node 10
warehouse_location(10).

%*
TIME STEPS:
- Represent the different time steps (up to some upper bound)
*%

#const t=25. % This is an upper bound on the number of time steps needed
possible_time(1..t).
{ time(T) : possible_time(T) }.
:- not time(1).
:- possible_time(T), possible_time(T+1), not time(T), time(T+1).

max_time(D) :- D = #max {T : time(T)}. % encode largest time value

%*
ACTIONS:
- Represent the possible actions that each truck can take

[EXPLAIN YOUR CODE USING SHORT INLINE COMMENTS]
*%
% here we declare the possible actions and their inputs
% the do predicate (lower) handles when and who does what
% wait is therefore 0-ary
action(wait). 
% move to a target node
action(move(N)) :- node(N).  
% unload a unit from a truck at node N
action(unload(N)) :- node(N) .
% load a unit onto a truck at node N
action(load(N)) :- node(N) .
% charge at node N
action(charge(N)) :- node(N) .

% Declare what we will treat as fluents
fluent(truck(TID, N)) :- truck_id(TID), node(N).
fluent(warehouse(N, Curr)) :- warehouse_location(N), warehouse_capacity(Curr).
fluent(cargo(TID,Curr,Max)) :- truck_id(TID), warehouse_capacity(Curr), warehouse_capacity(Max).
fluent(deliver(N,Req)) :- deliver_location(N), warehouse_capacity(Req).
fluent(battery(TID,Curr)) :- truck_id(TID),Curr = 0..max_charge.



%*
GENERATE A SEQUENCE OF ACTIONS:
- Generate a sequence of actions (for each truck)

[EXPLAIN YOUR CODE USING SHORT INLINE COMMENTS]
*%
% We perform exactly one action at each time step per truck
1 { do(A, TID, T) : action(A) } 1 :- 
    time(T), truck_id(TID), T < M, max_time(M).

% Fluents stay true, unless explicitly made false
state(T,F) :- time(T),
    fluent(F), state(T-1,F), not make_false(T,F).
% Fluents that are explicitly made true, become true
state(T,F) :- time(T),
    fluent(F), make_true(T,F).

%*
INITIAL STATE:
- Encode the initial state

[EXPLAIN YOUR CODE USING SHORT INLINE COMMENTS]
*%

% initial state of trucks
state(1, truck(TID, 10+TID)) :- truck_id(TID).
% warehouse at node 10 with 5 packages
state(1, warehouse(10, 5)).
% (position, number of packages required) of deliver goal
state(1, deliver(L, 2)) :- deliver_location(L).
% cargo of truck id, current load, max load
state(1, cargo(TID, 0, TID)) :- truck_id(TID).

% battery of truck id, initial charge level.
state(1, battery(1, 6)).
state(1, battery(2, 7)).
state(1, battery(3, 10)).


%*
SUBSEQUENT STATES OF THE WORLD:
- Encode the subsequent states, based on the actions taken

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%
% do not need to describe what happens with wait because fluents take care of it (i think)


% when we move, we move to the target node in the next time step. Make stuff that keeps node the same false.
make_true(TStep+1, truck(TID,TN)) :- 
  do(move(TN), TID, TStep), state(TStep, truck(TID, N)).
make_false(TStep+1, truck(TID,N)) :- 
  do(move(TN), TID, TStep), state(TStep, truck(TID, N)).

% when we load, our cargo increases, the node cargo decreases. Make stuff that keeps cargo the same false.
make_true(TStep+1, cargo(TID, Curr+1, Max)) :- 
  do(load(N), TID, TStep), 
  state(TStep, truck(TID, N)),
  state(TStep, cargo(TID, Curr, Max)).
make_false(TStep+1, cargo(TID, Curr, Max)) :- 
  do(load(N), TID, TStep), 
  state(TStep, truck(TID, N)),
  state(TStep, cargo(TID, Curr, Max)).
make_true(TStep+1, warehouse(N, Curr-1)) :- 
  do(load(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, warehouse(N, Curr)) .
make_false(TStep+1, warehouse(N, Curr)) :- 
  do(load(N), TID, TStep), 
  state(TStep, truck(TID, N)),
  state(TStep, warehouse(N, Curr)).

% when we unload, our cargo decreases, the node required cargo increases. Make stuff that keeps cargo the same false.
make_true(TStep+1, cargo(TID, Curr-1, Max)) :- 
  do(unload(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, cargo(TID, Curr, Max)).
make_false(TStep+1, cargo(TID, Curr, Max)) :- 
  do(unload(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, cargo(TID, Curr, Max)).
make_true(TStep+1, deliver(N, Req-1)) :- 
  do(unload(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, deliver(N, Req)) .
make_false(TStep+1, deliver(N, Req)) :- 
  do(unload(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, deliver(N, Req)) .


% when we move, battery decreases, TODO


% when we charge, battery increases, TODO


%*
RESTRICTIONS ON THE ACTIONS:
- Restrict the actions taken by the trucks, based on the state of the world

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%
% we can only move to adjacent nodes
:- do(move(TN), TID, TStep), state(TStep, truck(TID, N)), not edge(N, TN).
% we cannot move to an occupied node
:- do(move(TN), TIDA, TStep), do(move(TN), TIDB, TStep), TIDA != TIDB.
:- do(move(TN), TIDA, TStep), 
    not do(move, TIDB, TStep), 
    state(TStep, truck(TIDB, TN)),
    TIDA != TIDB.
% we cannot move through a busy edge
% helper rule
busy_edge(N, TN, TID, TStep) :- do(move(TN), TID, TStep), state(TStep, truck(TID, N)) .
:-  do(move(N), TIDA, TStep), 
    busy_edge(N, TN, TIDB, TStep), 
    TIDA != TIDB, 
    state(TStep, truck(TIDA, TN)).

% can only load at warehouse
:- do(load(N), TID, TStep), not warehouse_location(N).
% can only load when warehouse not empty
:- do(load(N), _, TStep), state(TStep, warehouse(N, C)), C < 1 .
% can only load when we have space to do so
:- do(load(_), TID, TStep), state(TStep, cargo(TID, Curr, Max)), Curr == Max .

% can only unload at deliver, this constraint breaks because there's two unload places!!
:- do(unload(N), TID, TStep), not deliver_location(N).
% can only unload when deliver needs it 
:- do(unload(N), _, TStep), state(TStep, deliver(N, R)), R < 0 .
% can only unload when we have package to unload
:- do(unload(N), TID, TStep), state(TStep, cargo(TID, Curr, _)), Curr == 0 .

% can only charge at station, TODO
% can only charge if battery is not full, TODO
% cannot move if battery == 0, TODO



%*
GOAL CONDITIONS:
- Constraints that express that the goal must be reached

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%
all_delivered(T) :- time(T), state(T, deliver(3, 0)), state(T, deliver(6, 0)) .
all_parked(T):- time(T), state(T, truck(_, N)) : parking(N) .
all_empty(T) :- time(T), state(T, cargo(TID, 0, _)) : truck_id(TID).


% helper for station reachable by truck with current charge, TODO

% all_reachable: that all trucks can reach one charging station, TODO


goal_reached(T) :- 
  time(T), 
  all_delivered(T),
  all_parked(T),
  all_empty(T) .

:- max_time(M), not goal_reached(M).
:- max_time(M), goal_reached(T), time(T), T < M .

%*
OPTIMIZATION:
- Express an optimization statement to find a solution within the smallest
  number of time steps

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%
#minimize {1, T : time(T) } .



%*
OPTIONAL: ADDITIONAL RULES
- If you add anything to your program that doesn't fit in any of the other
  headings, put it here.

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%




% tests
#show do/3.
%*
THE END
*%
