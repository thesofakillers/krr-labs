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
% there are 13 nodes, numbered top to bottom, left to right in zig-zag fashion
#const num_nodes = 13.
node(1..num_nodes).
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

% maximum charge of any truck
#const max_charge = 10.

% truck ids and warehouse capacity
#const num_trucks = 3.
truck_id(1..num_trucks).
warehouse_capacity(0..5).

% charging station at node 1 and 2
station(1;2).

% parking slot at nodes 11, 12, 13
parking(11..13).

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
% encode largest time value
max_time(D) :- D = #max {T : time(T)}.

%*
ACTIONS:
- Represent the possible actions that each truck can take

[EXPLAIN YOUR CODE USING SHORT INLINE COMMENTS]
*%
% here we declare the possible actions and their inputs
% the do/3 predicate (lower) handles when and who does what
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
state(1, truck(TID, (num_nodes-num_trucks)+TID)) :- truck_id(TID).
% warehouse at node 10 with 5 packages
state(1, warehouse(L, 5)) :- warehouse_location(L).
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

A future state is defined by what action(s) we do at the present timestep. This
idea is encapsulated by the do/3 predicate. To save the state, we make use of
the state/2 predicate, which keeps track of fluents through time. Because we
work with fluents, for every action we must define both what a valid state and
an invalid state would be for this action. This corresponds to the usage of the
make_true/2 and make_false/2 predicates.

*%
% wait action keeps everything the same so it is taken care of by fluents
% when we move, we move to the target node in the next time step.
make_true(TStep+1, truck(TID,TN)) :-
  do(move(TN), TID, TStep), state(TStep, truck(TID, N)).
% Make states that keeps node the same false.
make_false(TStep+1, truck(TID,N)) :-
  do(move(TN), TID, TStep), state(TStep, truck(TID, N)).

% when we load, our cargo increases, the node cargo decreases.
make_true(TStep+1, cargo(TID, Curr+1, Max)) :-
  do(load(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, cargo(TID, Curr, Max)).
make_true(TStep+1, warehouse(N, Curr-1)) :-
  do(load(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, warehouse(N, Curr)) .
% Make states that keeps cargo the same false.
make_false(TStep+1, cargo(TID, Curr, Max)) :-
  do(load(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, cargo(TID, Curr, Max)).
make_false(TStep+1, warehouse(N, Curr)) :-
  do(load(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, warehouse(N, Curr)).

% when we unload, our cargo decreases, the node required cargo increases.
make_true(TStep+1, cargo(TID, Curr-1, Max)) :-
  do(unload(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, cargo(TID, Curr, Max)).
make_true(TStep+1, deliver(N, Req-1)) :-
  do(unload(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, deliver(N, Req)) .
% Make states that keeps cargo the same false.
make_false(TStep+1, cargo(TID, Curr, Max)) :-
  do(unload(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, cargo(TID, Curr, Max)).
make_false(TStep+1, deliver(N, Req)) :-
  do(unload(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, deliver(N, Req)) .


% when we charge, battery increases, TODO
make_true(TStep+1, battery(TID, Curr+1)) :-
  do(charge(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, battery(TID, Curr)).
make_false(TStep+1, battery(TID, Curr)) :-
  do(charge(N), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, battery(TID, Curr)).
% when we move, battery decreases
make_true(TStep+1, battery(TID, Curr-1)) :-
  do(move(TN), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, battery(TID, Curr)).
make_false(TStep+1, battery(TID, Curr)) :-
  do(move(TN), TID, TStep),
  state(TStep, truck(TID, N)),
  state(TStep, battery(TID, Curr)).


%*
RESTRICTIONS ON THE ACTIONS:
- Restrict the actions taken by the trucks, based on the state of the world

Explanation (max 100 words):

Here we constrain our possible actions using rules without heads. 
In particular:

- we can only _move_ to adjacent nodes
- we cannot _move_ to an occupied node or a busy edge
- we can only _load_ at a warehouse and it still has packages
- we can only _load_ if truck still has space to load
- we can only _unload_ at a delivery location and it still requires packages
- we can only _unload_ if truck has nonzero loaded packages
- we can only _charge_ at a charging station
- we cannot _move_ with an empty battery

Where the _action_ is expressed between underscores.

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
% an edge is busy when a truck is using it to move
busy_edge(N, TN, TID, TStep) :- do(move(TN), TID, TStep), state(TStep, truck(TID, N)) .
% can now use this helper rule to define our constraint.
:-  do(move(N), TIDA, TStep),
    busy_edge(N, TN, TIDB, TStep),
    TIDA != TIDB,
    state(TStep, truck(TIDA, TN)).

% can only load at warehouse
:- do(load(N), TID, TStep), not warehouse_location(N).
:- do(load(N), TID, TStep), not state(TStep, truck(TID, N)) .
% can only load when warehouse not empty
:- do(load(N), _, TStep), state(TStep, warehouse(N, C)), C < 1 .
% can only load when we have space to do so
:- do(load(_), TID, TStep), state(TStep, cargo(TID, Curr, Max)), Curr == Max .

% can only unload at deliver, this constraint breaks because there's two unload places!!
:- do(unload(N), TID, TStep), not deliver_location(N).
:- do(unload(N), TID, TStep), not state(TStep, truck(TID, N)) .
% can only unload when deliver needs it
:- do(unload(N), _, TStep), state(TStep, deliver(N, R)), R < 0 .
% can only unload when we have package to unload
:- do(unload(N), TID, TStep), state(TStep, cargo(TID, Curr, _)), Curr == 0 .

% can only charge at station
:- do(charge(N), TID, TStep), not station(N) .
:- do(charge(N), TID, TStep), not state(TStep, truck(TID, N)) .
% can only charge if battery is not full
:- do(charge(N), TID, TStep), state(TStep, battery(TID, C)), C > max_charge .
% cannot move if battery == 0
:- do(move(N), TID, TStep), state(TStep, battery(TID, C)), C == 0 . 



%*
GOAL CONDITIONS:
- Constraints that express that the goal must be reached

Explanation (max 100 words):

We have reached our goal when all the delivery requirements are met, the trucks
are all empty, they are parked in one of the parking spots and they all have
enough charge to reach the closest charging station. We make use of conditional
literals to express this "for all <instance>" notion. We resort to helper
predicates to determine the closest parking station and whether it is reachable
based on our charge. As an optimization we only check the reachability
constraint when all other constraints are satisfied, as we found this sped up
result computation.

*%
% all the delivery locations are satisfied
all_delivered(T) :- time(T), state(T, deliver(L, 0)) : deliver_location(L) .
% all the trucks are parked in one of the available parking spots
all_parked(T):- time(T), state(T, truck(_, N)) : parking(N) .
% all the trucks are empty
all_empty(T) :- time(T), state(T, cargo(TID, 0, _)) : truck_id(TID).

% almost all our constraints are satisfied except the.
goal_almost_reached(T) :-
  time(T),
  all_delivered(T),
  all_parked(T),
  all_empty(T) .

% what is the closest station for a given node
closest_station(X, X, 0) :- station(X) .
closest_station(X, Z, D+1) :- 
    node(D+1),
    closest_station(X, Y, D), 
    edge(Y, Z), 
    not closest_station(X, Z, W) : node(W), 
    W <= D .

% helper for station reachable by truck with current charge at current TStep
station_reachable(TID, TStep) :- 
    goal_almost_reached(TStep), % only compute this when close to solving
    state(TStep, battery(TID, C)), % given battery
    state(TStep, truck(TID, Z)), % of given truck
    closest_station(N, Z, D), % given station is D steps away
    C >= D . % and we have enough charge to cover this distance

% that all trucks can reach a charging station
all_reachable(T) :-
    time(T),
    station_reachable(TID, T) : truck_id(TID) .

% all our constraints are satisfied.
goal_reached(T) :-
    time(T),
    goal_almost_reached(T),
    all_reachable(T) .

% We require that we reach the goal at the end
:- max_time(M), not goal_reached(M).
% Once we reached the goal, stop the clock
:- max_time(M), goal_reached(T), time(T), T < M .

%*
OPTIMIZATION:
- Express an optimization statement to find a solution within the smallest
  number of time steps

Explanation (max 100 words):

Very simply, we want to find the shortest sequence and we can do this by
minimizing the number of time steps.

*%
#minimize {1, T : time(T) } .



%*
OPTIONAL: ADDITIONAL RULES
- If you add anything to your program that doesn't fit in any of the other
  headings, put it here.

Explanation (max 100 words):

We only care about what we do and when. The do/3 predicate captures this, so we
only show the do/3 predicate. We found that most rules fit well in the headings
provided. 

We also provide a python pretty-printing script.
Ensure to run using the provided clingo conda environment:
`conda create -n potassco -c conda-forge clingo`
You can also just comment out the #script-#end. block if you are not interested
in pretty-printing.

Our script takes approximately 150 seconds to run on a consumer laptop from
2017 and approximately 85 seconds on M1 Mac from 2020.

*%

#show do/3.

#script (python)

import clingo

def on_model(model):
    actions = dict()

    for atom in model.symbols(atoms=True):
        if atom.name == "do":
            time = atom.arguments[-1].number
            action = str(atom.arguments[0])
            truck = f"truck {atom.arguments[1]}"
            if time not in actions:
                actions[time] = dict()
            actions[time][truck] = action

    time_steps = [time for time in actions]
    time_steps.sort()
    print("Pretty printed answer set:")
    print(f"{'Time step│':10}\t{'Truck 1':12}\t{'Truck 2':12}\t{'Truck 3':12}")
    print("─────────┼"+"─"*48)
    for time in time_steps:
        truck1 = actions[time]["truck 1"]
        truck2 = actions[time]["truck 2"]
        truck3 = actions[time]["truck 3"]
        print(f"{time:9}│\t{truck1:12}\t{truck2:12}\t{truck3:12}")

def main(prg):
    prg.ground([("base", [])])
    prg.solve(on_model=on_model)
#end.
%*
THE END
*%
