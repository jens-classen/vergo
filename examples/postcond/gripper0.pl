%:- style_check(-singleton).
%:- ensure_loaded(progress).
%:- ensure_loaded(modelGen).
%:- ensure_loaded(gove).

typeList([loc, obj, num]).

constList([]).

tdomain(loc, [locA, locB]).
tdomain(obj, [o1, o2, o3, o4, o5]).
tdomain(num, [0,1,2]).

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
     l_at(o3, locB), l_at(o4, locB), l_at(o5, locB)
   ]])).

sc([-holding(0) v -holding(1), -holding(0) v -holding(2),
    -holding(1) v -holding(2),
    all([x, l], -on_truck(x) v -l_at(x,l)),
    -(locA~locB),
    holding(0) => all([x], -truck_on(x))]).

:- initall.

poss(move_to(X, Y)) <=> true.
poss(truck_load(O, L)) <=> -holding(2) & t_at(L) & l_at(O, L).
poss(truck_unload(O, L)) <=> truck_on(O) & t_at(L).

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

test1 :-
        gove(holding(0) & t_at(locA) & 
               all([[o, obj]], l_at(o, locB)) &
               some([[o, obj]], l_at(o, locB)),
             while(some([[x, obj]], l_at(x, locB)),
                   move_to(locA, locB):
                   pi([[xx, obj]], truck_load(xx, locB)):
                   move_to(locB, locA):
                   pi([[yy, obj]], truck_unload(yy, locA))
                  ),
             all([[o, obj]], l_at(o, locA))
            ).

test2 :-
        gove(holding(0) & t_at(locA) & 
               all([[o, obj]], l_at(o, locB)) &
               some([[o, obj]], l_at(o, locB)),
             while(some([[x, obj]], l_at(x, locB)),
                   move_to(locA, locB):
                   pi([[xx, obj]], truck_load(xx, locB)):
                   move_to(locB, locA):
                   pi([[yy, obj]], truck_unload(yy, locA))
                  ),
             holding(0)
            ).

test3 :-
        gove(holding(0) & t_at(locA) & 
               all([[o, obj]], l_at(o, locB)) &
               some([[o, obj]], l_at(o, locB)),
             while(some([[x, obj]], l_at(x, locB)),
                   move_to(locA, locB):
                   pi([[xx, obj]], truck_load(xx, locB)):
                   move_to(locB, locA):
                   pi([[yy, obj]], truck_unload(yy, locA))
                  ),
             t_at(locA)
            ).
