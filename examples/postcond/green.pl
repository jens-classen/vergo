:- style_check(-singleton).
:- ensure_loaded(progress).
:- ensure_loaded(modelGen).
:- ensure_loaded(gove).
:- ensure_loaded(sc).

typeList([blo]).

constList([]).

tdomain(blo, [b1, b2, b3, b4]).

predList([on, clear, holding, ontable, green, 
          collected, handempty]).
type_info(on, [blo, blo]).
type_info(clear, [blo]).
type_info(holding, [blo]).
type_info(ontable, [blo]).
type_info(green, [blo]).
type_info(collected, [blo]).
type_info(handempty, []).

pred(on(X, Y)) :-
        tdomain(blo, D), member(X, D), member(Y, D).
pred(clear(X)) :-
        tdomain(blo, D), member(X, D).
pred(holding(X)) :-
        tdomain(blo, D), member(X, D).
pred(ontable(X)) :-
        tdomain(blo, D), member(X, D).
pred(green(X)) :-
        tdomain(blo, D), member(X, D).
pred(collected(X)) :-
        tdomain(blo, D), member(X, D).
pred(handempty).

:- assert(init_states([[
     on(b1, b2), clear(b1), ontable(b2),
     on(b3, b4), clear(b3), ontable(b4),
     green(b1), green(b4), handempty,
     blo(b1), blo(b2), blo(b3), blo(b4)
   ]])).

:- assert(sc([
    true/*
    handempty => all([[x,blo]], -holding(x)),
    all([[x,blo]], holding(x) v clear(x) v 
                   some([[y,blo]], on(y,x))),        
    all([[x,blo]], ontable(x) v holding(x) v 
                   some([[y,blo]], on(x,y))),
    all([[x,blo],[y,blo],[z,blo]], on(x,y) & on(x,z) => y~z),
    all([[x,blo],[y,blo],[z,blo]], on(x,z) & on(y,z) => x~y),
    all([[x,blo],[y,blo]], holding(x) & holding(y) => x~y),
    all([[x,blo],[y,blo]], on(x,y) => -clear(y)),
    all([[x,blo]], -on(x,x)),
    all([[x,blo],[y,blo]], -on(x,y) v -on(y,x))*/
    %-(b1~b2), -(b1~b3), -(b1~b4), -(b2~b3), -(b2~b4), -(b3~b4)
   ]
  )).

:- initall.

sc_proc(
           while(true,
                 pi([[x,blo],[y,blo]], stack(x,y)) #
                 pi([[x,blo],[y,blo]], unstack(x,y)) #
                 pi([[x,blo]], pickup(x)) #
                 pi([[x,blo]], putdown(x)) #
                 pi([[x,blo]], collect(x))
                )
       ).
                

poss(stack(U, V)) <=> holding(U) & clear(V) & -(U ~ V).
poss(unstack(U, V)) <=> on(U, V) & clear(U) & handempty.
poss(pickup(U)) <=> ontable(U) & clear(U) & handempty.
poss(putdown(U)) <=> holding(U).
poss(collect(X)) <=> holding(X).

perform(clear(X), stack(U, V)) <=> (X ~ U) v (clear(X) & -(X ~ V)).
perform(clear(X), unstack(U, V)) <=> (X ~ V) v (clear(X) & -(X ~ U)).
perform(clear(X), pickup(U)) <=> clear(X) & -(X ~ U).
perform(clear(X), putdown(U)) <=> clear(X) v (X ~ U).

perform(on(X, Y), stack(U, V)) <=> ( (X ~ U) & (Y ~ V) ) v on(X, Y).
perform(on(X, Y), unstack(U, V)) <=> on(X, Y) & -( (X ~ U) & (Y ~ V)
                                                 ).
perform(on(X, Y), pickup(U)) <=> on(X, Y).
perform(on(X, Y), putdown(U)) <=> on(X, Y).

perform(ontable(X), stack(U, V)) <=> ontable(X).
perform(ontable(X), unstack(U, V)) <=> ontable(X).
perform(ontable(X), pickup(U)) <=> ontable(X) & -(X ~ U).
perform(ontable(X), putdown(U)) <=> (X ~ U) v ontable(X).

perform(holding(X), stack(U, V)) <=> holding(X) & -(X ~ U).
perform(holding(X), unstack(U, V)) <=> (X ~ U) v holding(X).
perform(holding(X), pickup(U)) <=> (X ~ U) v holding(X).
perform(holding(X), putdown(U)) <=> holding(X) & -(X ~ U).
perform(holding(X), collect(U)) <=>
        holding(X) & -(X~U).

perform(handempty, stack(U, V)) <=> true.
perform(handempty, unstack(U, V)) <=> false.
perform(handempty, pickup(U)) <=> false.
perform(handempty, putdown(U)) <=> true.
perform(handempty, collect(X)) <=> true.

perform(collected(X), collect(Y)) <=> collected(X) v (X~Y).

addList(S, pickup(X)) <=> [holding(X)].
delList(S, pickup(X)) <=> [ontable(X), clear(X), handempty].

addList(S, putdown(X)) <=> [clear(X), handempty, ontable(X)].
delList(S, putdown(X)) <=> [holding(X)].

addList(S, stack(X, Y)) <=> [clear(X), handempty, on(X,Y)].
delList(S, stack(X, Y)) <=> [holding(X), clear(Y)].

addList(S, unstack(X,Y)) <=> [holding(X), clear(Y)].
delList(S, unstack(X,Y)) <=> [clear(X), handempty, on(X,Y)].

addList(S, collect(X)) <=> [handempty, collected(X)].
delList(S, collect(X)) <=> [holding(X)].

test1 :-
        gove(all([[x,blo]], 
                -green(x) v ontable(x) v some([[y,blo]], on(x, y)))&
             handempty,
             while(some([[x,blo], [y,blo]], on(x, y)),
                   pi([[xx,blo], [yy,blo]],
                       unstack(xx, yy):
                       ( ?(green(xx)) : collect(xx) #
                         ?(-green(xx)) : putdown(xx)
                       )
                      )
                  ):
             while(some([[u,blo]], ontable(u) & green(u)),
                   pi([[uu,blo]],
                      ?(green(uu)) :
                      pickup(uu):
                      collect(uu)
                     )
                  ),
             all([[o,blo]], -green(o) v collected(o))
            ).          

test2 :-
        gove(all([[x,blo]], -collected(x) v green(x))&
             handempty,
             while(some([[x,blo], [y,blo]], on(x, y)),
                   pi([[xx,blo], [yy,blo]],
                       unstack(xx, yy):
                       ( ?(green(xx)) : collect(xx) #
                         ?(-green(xx)) : putdown(xx)
                       )
                      )
                  ):
             while(some([[u,blo]], ontable(u) & green(u)),
                   pi([[uu,blo]],
                      ?(green(uu)) :
                      pickup(uu):
                      collect(uu)
                     )
                  ),
             all([[o,blo]], -collected(o) v green(o))
            ).

test3 :-
        gove(handempty,
             while(some([[x,blo], [y,blo]], on(x, y)),
                   pi([[xx,blo], [yy,blo]],
                       unstack(xx, yy):
                       ( ?(green(xx)) : collect(xx) #
                         ?(-green(xx)) : putdown(xx)
                       )
                      )
                  ):
             while(some([[u,blo]], ontable(u) & green(u)),
                   pi([[uu,blo]],
                      ?(green(uu)) :
                      pickup(uu):
                      collect(uu)
                     )
                  ),
             handempty
            ).