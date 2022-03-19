%*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% KRR 2022, HOMEWORK ASSIGNMENT 3 %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Name:             Matteo Rosati
Student number:   13858149

Name:             Giulio Starace
Student number:   TBD

*%

%*
INPUT REPRESENTATION:
- Represent the input of the problem (the map, the trucks, etc.)
*%

% Represent the nodes and edges of the map using node/1 and edge/2.
node(1..13).
edge(1,3), edge(1,4), edge(2,4), edge(2,5), edge(3,4), edge(3,7), edge(4,5), edge(4,7).
edge(4,8), edge(5,8),edge(5,9), edge(5,6), edge(6,10), edge(7,8), edge(7,11), edge(8,9).
edge(9,10), edge(10,13), edge(12,13), edge(11,12).

% Edges are undirected, so include their reverse
edge(X,Y) :- edge(Y,X), node(Y), node(X).

% setting up special nodes
station(1), station(2). % setting the position of charging stations
warehouse(10, 5). % setting the position of the warehouse and the number of packages in it
deliver(3, 2), deliver(6, 2). % (position, number of packages) of deliver goal
parking(11). parking(12). parking(13). % parking slot position


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




%*
GENERATE A SEQUENCE OF ACTIONS:
- Generate a sequence of actions (for each truck)

[EXPLAIN YOUR CODE USING SHORT INLINE COMMENTS]
*%




%*
INITIAL STATE:
- Encode the initial state

[EXPLAIN YOUR CODE USING SHORT INLINE COMMENTS]
*%




%*
SUBSEQUENT STATES OF THE WORLD:
- Encode the subsequent states, based on the actions taken

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%




%*
RESTRICTIONS ON THE ACTIONS:
- Restrict the actions taken by the trucks, based on the state of the world

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%




%*
GOAL CONDITIONS:
- Constraints that express that the goal must be reached

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%




%*
OPTIMIZATION:
- Express an optimization statement to find a solution within the smallest
  number of time steps

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%




%*
OPTIONAL: ADDITIONAL RULES
- If you add anything to your program that doesn't fit in any of the other
  headings, put it here.

Explanation (max 100 words):
[WRITE YOUR EXPLANATION HERE]
*%




%*
THE END
*%
