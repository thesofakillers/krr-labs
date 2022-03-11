#const k=3.

row(0..k**2-1).
col(0..k**2-1).
val(1..k**2).

% current problem
place(1,1,3).
place(1,4,8).
place(3,4,4).
place(3,8,5).
place(4,8,7).
place(4,7,2).
place(5,6,3).
place(6,6,9).
place(7,5,6).
place(7,4,5).

% generate with only one value per cell
1 {place(R, C, V) : val(V)} 1 :- row(R), col(C).

% helper
valid(R, C) :- row(R), col(C).

% define when a coordinate is in a block
in_block(R, C, SR, SC) :- valid(SR, SC), valid(R, C), 
    SR \ k == 0, SC \ k = 0,
    R - SR < k, C - SC < k,
    R - SR >= 0, C - SC >= 0.

% define what is reachable with king move
kreachable(R, C, AR, AC) :- valid(R, C), valid(AR, AC), 
    |C - AC| = 1, |R - AR| <= 1.
kreachable(R, C, AR, AC) :- valid(R, C), valid(AR, AC), 
    |R - AR| = 1, |C - AC| <= 1.
kreachable(R, C, AR, AC) :- kreachable(AR, AC, R, C).

% define what is reachable with knight move
nreachable(R, C, AR, AC) :- valid(R, C), valid(AR, AC), 
    |R - AR| == 1, |C - AC| == 2.
nreachable(R, C, AR, AC) :- valid(R, C), valid(AR, AC), 
    |R - AR| == 2, |C - AC| == 1.
nreachable(R, C, AR, AC) :- nreachable(AR, AC, R, C).

% conbine king and knight reachable into one predicate
reachable(R, C, AR, AC) :- nreachable(AR, AC, R, C).
reachable(R, C, AR, AC) :- kreachable(AR, AC, R, C).


% only unique values in every row and column
:- place(R1, C, V), place(R2, C, V), R1 != R2.
:- place(R, C1, V), place(R, C2, V), C1 != C2.

% unique values in block
:- place(R, C, V), place(R1, C1, V),
    in_block(R, C, SC, EC),  in_block(R1, C1, SC, EC),
    R != R1, C != C1.

% no two reachable values the same
:- place(R, C, V), place(R1, C1, V), reachable(R, C, R1, C1).

#show place/3.