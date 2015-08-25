:- style_check(-singleton).
:- ensure_loaded(progress).
:- ensure_loaded(modelGen).
:- ensure_loaded(gove).
:- ensure_loaded(sc).

typeList([loc, obj, num]).

constList([]).

tdomain(loc, [locA, locB]).
tdomain(obj, [o1, o2, o3, o4, o5]).
tdomain(num, [0,1,2]).

predList([l_at, t_at, holding, truck_on]).
type_info(l_at, [obj, loc]).
type_info(t_at, [loc]).
type_info(holding, [num]).
type_info(truck_on, [obj]).

pred(l_at(X, L)) :-
        tdomain(obj, O), member(X, O),
        tdomain(loc, LD), member(L, LD).
pred(t_at(L)) :-
        tdomain(loc, LD), member(L, LD).
pred(holding(X)) :-
        tdomain(num, O), member(X, O).
pred(truck_on(X)) :-
        tdomain(obj, O), member(X, O).

:- assert(init_states([[
     holding(0), t_at(locA), l_at(o1, locB), l_at(o2, locB),
     l_at(o3, locB), l_at(o4, locB), l_at(o5, locB),
     loc(locA), loc(locB), obj(o1), obj(o2),
     obj(o3), obj(o4), obj(o5), num(0), num(1), num(2)
   ]])).

:- assert(sc([
    -(locA~locB),
    all([x,y], l_at(x,y) => obj(x) & loc(y)),
    all([x], t_at(x) => loc(x)),
    all([x], holding(x) => num(x)),
    all([x], truck_on(x) => obj(x)),
    all([x], -obj(x) v -loc(x)),
    all([x], -obj(x) v -num(x)),
    all([x], -loc(x) v -num(x))
    /*
    -holding(0) v -holding(1), -holding(0) v -holding(2),
    -holding(1) v -holding(2),
    all([x, l], -on_truck(x) v -l_at(x,l)),
    -(locA~locB),
    holding(0) => all([x], -truck_on(x))*/
   ])).

:- initall.

poss(move_to(X, Y)) <=> t_at(X).
poss(truck_load(O, L)) <=> -holding(2) & t_at(L) & l_at(O, L).
poss(truck_unload(O, L)) <=> truck_on(O) & t_at(L).

sc_proc(
           while(true,
                 pi([[x,loc],[y,loc]], move_to(x,y)) #
                 pi([[x,obj],[y,loc]], truck_load(x,y)) #
                 pi([[x,obj],[y,loc]], truck_unload(x,y))
                )
       ).

addList(S, move_to(X, Y)) <=> [t_at(Y)].
delList(S, move_to(X, Y)) <=> [t_at(X)].

addList(S, truck_load(O, L)) <=>
        [holding(XX), truck_on(O)] :-
        member(holding(X), S), XX is X+1.
delList(S, truck_load(O, L)) <=>
        [holding(X), l_at(O, L)] :- 
        member(holding(X), S).

addList(S, truck_unload(O, L)) <=>
        [holding(XX), l_at(O, L)] :-
        member(holding(X), S), XX is X-1.
delList(S, truck_unload(O, L)) <=>
        [holding(X), truck_on(O)] :-
        member(holding(X), S).

perform(l_at(O1, L1), truck_load(O2, L2)) <=>
        l_at(O1, L1) & -(O1~O2 & L1~L2).
perform(l_at(O1, L1), truck_unload(O2, L2)) <=>
        l_at(O1, L1) v (O1~O2 & L1~L2).

perform(t_at(L1), move_to(L3, L4)) <=> L1~L4.

perform(truck_on(O1), truck_load(O2, L)) <=>
        truck_on(O1) v O1~O2.
perform(truck_on(O1), truck_unload(O2, L)) <=>
        truck_on(O1) & -(O1~O2).

perform(holding(2), truck_load(O, L)) <=> holding(1).
perform(holding(1), truck_load(O, L)) <=> holding(0).

perform(holding(0), truck_unload(O, L)) <=> holding(1).
perform(holding(1), truck_unload(O, L)) <=> holding(2).

perform(holding(X), truck_load(O, L)) <=>
        (X~2 & holding(1)) v
        (X~1 & holding(0)).
perform(holding(X), truck_unload(O, L)) <=>
        (X~0 & holding(1)) v
        (X~1 & holding(2)).

test1 :-
        gove(holding(0) & t_at(locA) & 
               all([[o, obj]], l_at(o, locB)) &
               some([[o, obj]], l_at(o, locB)),
             while(some([[x, obj]], l_at(x, locB)),
                   move_to(locA, locB):
                   while(some([[y, obj]], l_at(y, locB)) & 
                           -holding(2),
                         pi([[yy, obj]], truck_load(yy, locB))
                        ):
                   move_to(locB, locA):
                   while(some([[z, obj]], truck_on(z)),
                         pi([[zz, obj]],
                            truck_unload(zz, locA)
                           )
                        )
                  ),
             all([[o, obj]], l_at(o, locA))
            ).

test2 :-
        gove(holding(0) & t_at(locA) & 
               all([[o, obj]], l_at(o, locB)) &
               some([[o, obj]], l_at(o, locB)),
             while(some([[x, obj]], l_at(x, locB)),
                   move_to(locA, locB):
                   while(some([[y, obj]], l_at(y, locB)) & 
                           -holding(2),
                         pi([[yy, obj]], truck_load(yy, locB))
                        ):
                   move_to(locB, locA):
                   while(some([[z, obj]], truck_on(z)),
                         pi([[zz, obj]],
                            truck_unload(zz, locA)
                           )
                        )
                  ),
             holding(0)
            ).

test3 :-
        gove(holding(0) & t_at(locA) & 
               all([[o, obj]], l_at(o, locB)) &
               some([[o, obj]], l_at(o, locB)),
             while(some([[x, obj]], l_at(x, locB)),
                   move_to(locA, locB):
                   while(some([[y, obj]], l_at(y, locB)) & 
                           -holding(2),
                         pi([[yy, obj]], truck_load(yy, locB))
                        ):
                   move_to(locB, locA):
                   while(some([[z, obj]], truck_on(z)),
                         pi([[zz, obj]],
                            truck_unload(zz, locA)
                           )
                        )
                  ),
             t_at(locA)
            ).