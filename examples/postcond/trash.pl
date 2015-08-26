%:- style_check(-singleton).
%:- ensure_loaded(progress).
%:- ensure_loaded(modelGen).
%:- ensure_loaded(gove).
%:- ensure_loaded(sc).

typeList([obj, num, loc]).

constList([]).

tdomain(obj, [trash, can, nothing]).
tdomain(num, [1, 2, 3]).
tdomain(loc, [far, near, at]).

predList([dist_to, holding, num_trash]).

type_info(dist_to, [obj, loc]).
type_info(holding, [obj]).
type_info(num_trash, [num]).

pred(dist_to(X, Y)) :-
        member(X, [trash, can]),
        member(Y, [far, near, at]).
pred(holding(X)) :-
        member(X, [trash, nothing]).
pred(num_trash(X)) :-
        member(X, [1, 2, 3]).

pred(succ(X, Y)) :-
        tdomain(num, N), member(X, N), member(Y, N).
pred(less(X, Y)) :-
        tdomain(num, N), member(X, N), member(Y, N).

pred(obj(X)) :-
        tdomain(obj, D), member(X, D).
pred(num(X)) :-
        tdomain(num, D), member(X, D).
pred(loc(X)) :-
        tdomain(loc, D), member(X, D).

:- assert(init_states([
     [holding(nothing), dist_to(trash, far), dist_to(can, far),
      num_trash(3),
      obj(trash), obj(can), obj(nothing), 
      num(1), num(2), num(3), succ(1,2), succ(2,3),
      loc(far), loc(near), loc(at)]/*,
     [holding(nothing), dist_to(trash, far), dist_to(can, far),
      num_trash(2),
      obj(trash), obj(can), obj(nothing), 
      num(1), num(2), num(3), succ(1,2), succ(2,3),
      loc(far), loc(near), loc(at)]*/
   ])).

:- assert(sc([
       all([x], holding(x) => obj(x)),
       all([x], num_trash(x) => num(x)),
       all([x,y], dist_to(x,y) => obj(x) & loc(y)),
       all([x], -obj(x) v -num(x)),
       all([x], -obj(x) v -loc(x)),
       all([x], -num(x) v -loc(x)),
       -(1~2), -(1~3), -(2~3), 
       -(trash~can), -(trash~nothing), -(can~nothing),
       -(far~near), -(far~at), -(near~at),
%     true
       all([[x,num], [y,num]], succ(x,y) => less(x,y)),
       all([[x,num], [y,num], [z,num]], 
           succ(x,z) & succ(y,z) => x~y), % Useful for sc trash
       all([[x,num], [y,num], [z,num]], 
           succ(x,y) & succ(x,z) => y~z), % Useful for sc trash       
       num(const)
%       all([[x,num], [y,num], [z,num]], succ(x,z) & succ(y,z) =>
% (x~y))
%       some([[x,num], [y,num]], succ(x,y)) => some([[x,num],[y,num]], less(x,y))
   ])).

:- initall.

poss(wander_for(X)) <=> dist_to(X, far) & (X~trash v X~can).
poss(move_to(X)) <=> dist_to(X, near) & (X~trash v X~can).
poss(grab) <=> holding(nothing) & dist_to(trash, at).
poss(drop) <=> -holding(nothing).

addList(S, wander_for(trash)) <=>
        [dist_to(trash, near), dist_to(can, far)].
delList(S, wander_for(trash)) <=>
        [dist_to(trash, at), dist_to(trash, far),
         dist_to(can, near), dist_to(can, at)].

addList(S, wander_for(can)) <=>
        [dist_to(can, near), dist_to(trash, far)].
delList(S, wander_for(can)) <=> 
        [dist_to(can, at), dist_to(can, far),
         dist_to(trash, near), dist_to(trash, at)].

addList(S, grab) <=> [holding(trash), num_trash(X1)] :-
        member(num_trash(X), S), X1 is X-1.
delList(S, grab) <=> [holding(nothing), num_trash(X)] :-
        member(num_trash(X), S).

addList(S, move_to(trash)) <=>
        [dist_to(trash, at), dist_to(can, far)].
delList(S, move_to(trash)) <=>
        [dist_to(trash, near), dist_to(trash, far),
         dist_to(can, near), dist_to(can, at)].

addList(S, move_to(can)) <=>
        [dist_to(can, at), dist_to(trash, far)].
delList(S, move_to(can)) <=>
        [dist_to(can, near), dist_to(can, far),
         dist_to(trash, near), dist_to(trash, at)].

addList(S, drop) <=>
        [holding(nothing), num_trash(XX)] :-
        member(dist_to(can, at), S), member(num_trash(XX), S);
        not(member(dist_to(can, at), S)), 
        member(num_trash(X), S),
        XX is X + 1.
delList(S, drop) <=>
        [holding(trash), num_trash(XX)] :-
        member(num_trash(XX), S).

perform(dist_to(trash, near), wander_for(trash)) <=> true.
perform(dist_to(can, near), wander_for(can)) <=> true.
perform(dist_to(can, far), wander_for(trash)) <=> true.
perform(dist_to(trash, far), wander_for(can)) <=> true.
perform(dist_to(X, at), move_to(X)) <=> true.
perform(dist_to(can, far), move_to(trash)) <=> true.
perform(dist_to(trash, far), move_to(can)) <=> true.
perform(holding(trash), grab) <=> true.
perform(num_trash(X), grab) <=> 
        some([[nx,num]], num_trash(nx) & succ(X, nx)).
perform(holding(nothing), drop) <=> true.
perform(holding(nothing), grab) <=> false.
perform(num_trash(X), drop) <=>
        dist_to(can, at) & num_trash(X) v
        (-dist_to(can, at) & some([[nx,num]], num_trash(nx) & succ(nx,
                                                                   X))).

perform(dist_to(X, Y), wander_for(U)) <=>
        (X~trash & Y~near & U~trash) v
        (X~can & Y~near & U~can) v
        (X~can & Y~far & U~trash) v
        (X~trash & Y~far & U~can).
perform(dist_to(X, Y), move_to(U)) <=>
        (X~U & Y~at) v
        (X~can & Y~far & U~trash) v
        (X~trash & Y~far & U~can).
perform(holding(X), grab) <=> X~trash.
perform(holding(X), drop) <=> X~nothing.

sc_proc(
           while(true,
                 grab #
                 drop #
                 pi([[x,obj]], wander_for(x)) #
                 pi([[x,obj]], move_to(x))
                )
       ).

test1 :-
        gove(true,
             while(-num_trash(0),
                   wander_for(trash):
                   move_to(trash):
                   grab:
                   wander_for(can):
                   move_to(can):
                   drop),
             num_trash(0)).

test2 :-
        gove(holding(nothing),
             while(-num_trash(0),
                   wander_for(trash):
                   move_to(trash):
                   grab:
                   wander_for(can):
                   move_to(can):
                   drop),
             holding(nothing)).

testt1 :-
        gove_total(some([m], num_trash(const) & succ(m,const)),
                   wander_for(trash):
                   move_to(trash):
                   grab:
                   wander_for(can):
                   move_to(can):
                   drop,
                   some([n], num_trash(n) & succ(n, const))
                  ).

testt2 :-
        gove_total(some([[m,num]], num_trash(const) & succ(m,const)),
                   wander_for(trash):
                   move_to(trash):
                   grab:
                   wander_for(can):
                   move_to(can):
                   drop,
                   some([[n,num]], num_trash(n) & less(n, const))
                  ).