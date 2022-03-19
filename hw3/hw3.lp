% setting up time
#const t=25.
possible_time(1..t).
{ time(T) : possible_time(T) }.
:- not time(1).
:- possible_time(T), possible_time(T+1), not time(T), time(T+1).

% setting up nodes and edges
node(1..13)
edge(1,3), edge(1,4), edge(2,4), edge(2,5), edge(3,4), edge(3,7), edge(4,5), edge(4,7).
edge(4,8), edge(5,8),edge(5,9), edge(5,6), edge(6,10), edge(7,8), edge(7,11), edge(8,9).
edge(9,10), edge(10,13), edge(12,13), edge(11,12).
edge(X, Y) :- edge(Y, X), node(Y), node(X).

% setting up fun slots
station(1), station(2). % setting the position of charging stations
warehouse(10, 5). % setting the position of the warehouse and the number of packages in it
deliver(3, 2), deliver(6, 2) % (postion, number of packages) of deliver goal
parking(11). parking(12). parking(13). % parking slot position

hi