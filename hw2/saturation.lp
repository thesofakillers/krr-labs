#const k=3.
#const p=10.

row(0..k**2-1).
col(0..k**2-1).
val(1..k**2).

% generate a solution
1 {place(R, C, V) : val(V)} 1 :- row(R), col(C).

% definitions and restrictions for sudoku solutions
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

% define what is reachable with knight move
nreachable(R, C, AR, AC) :- valid(R, C), valid(AR, AC), 
    |R - AR| == 1, |C - AC| == 2.
nreachable(R, C, AR, AC) :- valid(R, C), valid(AR, AC), 
    |R - AR| == 2, |C - AC| == 1.

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


% hide empty cells
{ hide(R, C) : valid(R, C) }.
on_board(R, C, V) :- not hide(R, C), place(R, C, V).

% want exactly p numbers on board
:- not p { on_board(R, C, V) : valid(R, C), val(V) } p.


% saturation
% generate new solutions
new_place(R, C, V) : val(V) :- valid(R, C).


% incorrect new solutions if different from values on board or the same as old solution
incorrect :- on_board(R, C, V), new_place(R, C, W), V != W.
incorrect :- new_place(R, C, V) : place(R, C, V).


% incorrect new solution if same row, column, block, reachable
incorrect :- new_place(R1, C, V), new_place(R2, C, V), R1 != R2,
    valid(R1, C), valid(R2, C).
incorrect :- new_place(R, C1, V), new_place(R, C2, V), C1 != C2,
    valid(R, C1), valid(R, C2).
incorrect :- new_place(R, C, V), new_place(R1, C1, V),
    in_block(R, C, SC, EC),  in_block(R1, C1, SC, EC),
    R != R1, C != C1, valid(R, C), valid(R1, C1).
incorrect :- new_place(R, C, V), new_place(R1, C1, V), reachable(R, C, R1, C1),
    valid(R, C), valid(R1, C1).

% finish saturation
saturate :- incorrect.
incorrect :- saturate.
new_place(R, C, V) :- val(V), valid(R, C), saturate.
:- not saturate.


#show on_board/3.