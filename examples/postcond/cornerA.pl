:- style_check(-singleton).
:- ensure_loaded(progress).
:- ensure_loaded(modelGen).
:- ensure_loaded(gove).
:- ensure_loaded(sc).

typeList([num]).

constList([]).

tdomain(num, [1,2,3,4,5, const]).

predList([xpos, ypos]).
type_info(xpos, [num]).
type_info(ypos, [num]).

pred(xpos(X)) :- member(X, [1,2,3,4,5]).
pred(ypos(Y)) :- member(Y, [1,2,3,4,5]).

pred(succ(X, Y)) :-
        tdomain(num, N), member(X, N), member(Y, N).
pred(less(X, Y)) :-
        tdomain(num, N), member(X, N), member(Y, N).

pred(num(X)) :-
        tdomain(num, N), member(X, N).

:- assert(init_states([
     [xpos(4), ypos(3), num(1), num(2), num(3), num(4), num(5)]
   ])).

:- assert(sc([
    all([[x,num], [y,num], [z,num]], 
        succ(x,z) & succ(y,z) => x~y), % Useful for sc trash
    all([[x,num], [y,num], [z,num]], 
        succ(x,y) & succ(x,z) => y~z), % Useful for sc trash       
    all([x], xpos(x) => num(x)),
    all([x], ypos(x) => num(x)),
    num(const),
    all([[x,num],[y,num]], succ(x,y) => less(x,y))
    ])).

:- initall.

poss(move(left)) <=> -pos(1).
poss(move(right)) <=> -pos(5).
poss(move(up)) <=> -pos(1).
poss(move(down)) <=> -pos(5).

addList(S, move(left)) <=> 
        [xpos(XX)] :- member(xpos(X), S), XX is X-1.
delList(S, move(left)) <=>
        [xpos(X)] :- member(xpos(X), S).

addList(S, move(right)) <=>
        [xpos(XX)] :- member(xpos(X), S), XX is X+1.
delList(S, move(right)) <=>
        [xpos(X)] :- member(xpos(X), S).

addList(S, move(up)) <=>
        [ypos(YY)] :- member(ypos(Y), S), YY is Y-1.
delList(S, move(up)) <=>
        [ypos(Y)] :- member(ypos(Y), S).

addList(S, move(down)) <=>
        [ypos(YY)] :- member(ypos(Y), S), YY is Y+1.
delList(S, move(down)) <=>
        [ypos(Y)] :- member(ypos(Y), S).

perform(xpos(X), move(left)) <=> 
        some([[nx,num]], xpos(nx) & succ(X, nx)).
perform(xpos(X), move(right)) <=> 
        some([[nx,num]], xpos(nx) & succ(nx, X)).
perform(ypos(Y), move(up)) <=> 
        some([[nx,num]], ypos(nx) & succ(Y, nx)).
perform(ypos(Y), move(down)) <=> 
        some([[nx,num]], ypos(nx) & succ(nx, Y)).

sc_proc(
           while(true,
                 move(up) #
                 move(down) #
                 move(left) #
                 move(right)
                )
       ).

test1 :-
        gove(true,
             while(-ypos(1),
                   move(up)):
             while(-xpos(1),
                   move(left)),
             xpos(1) & ypos(1)).

testt1 :-
        gove_total(some([[m,num]], xpos(const) & succ(m, const)),
                   move(left),
                   some([[n,num]], xpos(n) & succ(n, const))
                  ).

testt2 :-
        gove_total(some([[m,num]], xpos(const) & succ(m, const)),
                   move(left),
                   some([[n,num]], xpos(n) & less(n, const))
                  ).

testt3 :-
        gove_total(some([[m,num]], ypos(const) & succ(m, const)),
                   move(up),
                   some([[n,num]], ypos(n) & succ(n, const))
                  ).

testt4 :-
        gove_total(some([[m,num]], ypos(const) & succ(m, const)),
                   move(up),
                   some([[n,num]], ypos(n) & less(n, const))
                  ).