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

% trucks
#const max_charge = 10.
% truck id, node, at time
truck(1, 11, 1).
truck(2, 12, 1).
truck(3, 13, 1).

%*
TIME STEPS:
- Represent the different time steps (up to some upper bound)
*%

#const t=100. % This is an upper bound on the number of time steps needed
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


%*
GENERATE A SEQUENCE OF ACTIONS:
- Generate a sequence of actions (for each truck)

[EXPLAIN YOUR CODE USING SHORT INLINE COMMENTS]
*%
% We perform exactly one action at each time step per truck
1 { do(A, TID, T) : action(A) } 1 :- 
    time(T), truck(TID, _, _), T < M, max_time(M).

%*
INITIAL STATE:
- Encode the initial state

[EXPLAIN YOUR CODE USING SHORT INLINE COMMENTS]
*%
% charging station at node 1 and 2
station(1). 
station(2). 
% warehouse at node 10 with 5 packages at timestep 1
warehouse(10, 5, 1). 
% (position, number of packages required) of deliver goal at timestep 1
deliver(3, 2, 1).
deliver(6, 2, 1).
% parking slot at nodes 11, 12, 13
parking(11). 
parking(12). 
parking(13). 
% cargo of truck id, current load, max load, timestep
cargo(1, 0, 1, 1) .
cargo(2, 0, 2, 1) .
cargo(3, 0, 3, 1) .

%*
SUBSEQUENT STATES OF THE WORLD:
- Encode the subsequent states, based on the actions taken

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%
% when we wait, we stay in the same node in the next time step
truck(TID, N, TStep+1) :- do(wait, TID, TStep), truck(TID, N, TStep).
% when we move, we move to the target node in the next time step
truck(TID,TN, TStep+1) :- 
  do(move(TN), TID, TStep), truck(TID, N, TStep).
% when we load, our cargo increases, the node cargo decreases
cargo(TID, Curr+1, Max, TStep+1) :- 
  do(load(N), TID, TStep), 
  truck(TID, N, TStep), 
  cargo(TID, Curr, Max, TStep).
warehouse(N, Curr-1, TStep+1) :- 
  do(load(N), TID, TStep),
  truck(TID, N, TStep),
  warehouse(N, Curr, TStep) .
% when we unload, our cargo decreases, the node required cargo increases
cargo(TID, Curr-1, Max, TStep+1) :-
  do(unload(N), TID, TStep),
  truck(TID, N, TStep),
  cargo(TID, Curr, Max, TStep).
deliver(N, Req-1, TStep+1) :- 
  do(unload(N), TID, TStep),
  truck(TID, N, TStep),
  deliver(N, Req, TStep) .


%*
RESTRICTIONS ON THE ACTIONS:
- Restrict the actions taken by the trucks, based on the state of the world

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%
% we can only move to adjacent nodes
:- do(move(TN), TID, TStep), truck(TID, N, TStep), not edge(N, TN).
% we cannot move to an occupied node
:- do(move(TN), TIDA, TStep), do(move(TN), TIDB, TStep), TIDA != TIDB.
:- do(move(TN), TIDA, TStep), 
    do(wait, TIDB, TStep), 
    truck(TIDB, TN, TStep),
    TIDA != TIDB.
% we cannot move through a busy edge
% helper rule
busy_edge(N, TN, TID) :- do(move(TN), _, TID), truck(TID, N, _) .
:-  do(move(N), TIDA, TStep), 
    busy_edge(N, TN, TIDB), 
    TIDA != TIDB, 
    truck(TIDA, TN, TStep).

% can only load at warehouse
:- do(load(N), _, TStep), warehouse(M, _, TStep), N != M .
% can only load when warehouse not empty
:- do(load(_), _, TStep), warehouse(_, C, TStep), C < 1 .
% can only load when we have space to do so
:- do(load(_), TID, TStep), cargo(TID, Curr, Max, TStep), Curr + 1 > Max .

% can only unload at deliver
:- do(unload(N), _, TStep), deliver(M, _, TStep), N != M.
% can only unload when deliver needs it 
:- do(unload(N), _, TStep), deliver(N, R, TStep), R < 1 .
% can only unload when we have package to unload
:- do(unload(N), TID, TStep), cargo(TID, Curr, _, TStep), Curr < 1 .


%*
GOAL CONDITIONS:
- Constraints that express that the goal must be reached

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%
%all_delivered(T) :- time(T), deliver(3, 0, T), deliver(6, 0, T) .
all_parked(T):- time(T), truck(_, N, T) : parking(N) .

goal_reached(T) :- 
  time(T), 
%  all_delivered(T),
  all_parked(T) .

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
#show do/3 .



% tests
%*
THE END
*%
