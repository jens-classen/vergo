:- style_check(-singleton).
:- ensure_loaded(progress).
:- ensure_loaded(modelGen).
:- ensure_loaded(gove).
:- ensure_loaded(sc).

%piArgs([[y,num]]).

typeList([num, truck, location, st, object]).

constList([[1,num],[2,num],[3,num]]).

tdomain(num, [1,2,3,const]).
tdomain(truck, [truck1, truck2]).
tdomain(location, [l1, l2, l3, d]).
tdomain(st, [nothing, both]).
tdomain(object, [monitor, server, nothing, both]).

pred(num(X)) :-  tdomain(num, N), member(X, N).
pred(truck(X)) :-  tdomain(truck, N), member(X, N).
pred(location(X)) :-  tdomain(location, N), member(X, N).
pred(object(X)) :-  tdomain(object, N), member(X, N).

predList([ loc, holding, quantity]).
type_info(loc, [truck, location]).
type_info(holding, [truck, object]).
type_info(quantity, [object, location, num]).
type_info(connected, [location, location]).

pred(loc(T, P)) :-
        member(T, [truck1, truck2]),
        member(P, [l1, l2, l3, d]).
pred(holding(T, S)) :-
        member(T, [truck1, truck2]),
        member(S, [nothing, both, monitor, server]).
%pred(num_pairs(X)) :-
%        member(X, [1, 2, 3]).
pred(quantity(O, L, X)) :-
        member(O, [monitor, server]),
        member(L, [l1, l2, l3, d]),
        member(X, [1, 2, 3, const]).
pred(connected(L1, L2)) :-
        tdomain(location, L), 
        member(L1, L),
        member(L2, L).
/*
pred(loc(T, L)) :-
        tdomain(truck, TD), member(T, TD),
        tdomain(location, LD), member(L, LD).
*/

pred(succ(X, Y)) :-
        tdomain(num, N), member(X, N), member(Y, N).
pred(less(X, Y)) :-
        tdomain(num, N), member(X, N), member(Y, N).



:- assert(init_states([
     [loc(truck1,l2), loc(truck2, l2), holding(truck1, nothing),
      holding(truck2, nothing), quantity(monitor, l1, 3),
      quantity(server, l1, 0), quantity(monitor, l2, 0),
      quantity(server, l2, 3), quantity(monitor, l3, 0),
      quantity(server, l3, 0), quantity(monitor, d, 0),
      quantity(server, d, 0),
      connected(l1,d), connected(l2,d), connected(l3,d),
      connected(d,l1), connected(d,l2), connected(d,l3),
      object(monitor), object(server), 
      object(nothng), object(both),
      truck(truck1), truck(truck2),
      location(l1), location(l2), location(l3), location(d),
      succ(0,1), succ(1,2), succ(2,3)]
   ])).

:- assert(sc([
    all([x,y], holding(x, y) => truck(x) & object(y)),
    all([x,y,z], quantity(x,y,z) => 
                 object(x) & location(y) & num(z)),
    all([x,y], connected(x,y) => location(x) & location(y)),
    all([x,y], loc(x,y) => truck(x) & location(y)),
    all([x], -truck(x) v -object(x)),
    all([x], -truck(x) v -location(x)),
    all([x], -object(x) v -location(x)),
    all([[x,num], [y,num], [z,num]], 
           succ(x,z) & succ(y,z) => x~y), % Useful for sc trash
    all([[x,num], [y,num], [z,num]], 
           succ(x,y) & succ(x,z) => y~z), % Useful for sc trash
    connected(l1,d), connected(l2,d), connected(l3,d),
    connected(d,l1), connected(d,l2), connected(d,l3),
    num(1), num(2), num(3), num(const),
%    all([x,y,z], succ(x,z) & succ(y,z) => x~y),
    /*
    all([[x,object],[y,location],[z,num],[w,num]], quantity(x,y,z) &
 quantity(x,y,w) => z~w),
    */
    all([[x,num]], -succ(x,x)),
    all([[x,num],[y,num]], succ(x,y) => less(x,y))
  ])).

:- initall.

poss(move(T, L1, L2)) <=> loc(T, L1) & connected(L1, L2).
poss(truck_load(truck1, O, L)) <=>
     loc(truck1, L) & holding(truck1, nothing) & -quantity(O, L, 0).
poss(truck_load(truck2, O, L)) <=>
     loc(truck2, L) & -quantity(O,L,0) & -holding(truck2, both) &
     -holding(truck2, O).
poss(truck_unload(truck1, O, L)) <=>
     loc(truck1, L) & holding(truck1, O).
poss(unload_all(truck2)) <=> 
     holding(truck2, both) & loc(truck2, l3).

sc_proc(
           while(true,
                 pi([[t,truck],[lx,location],[ly,location]],
                    move(t,lx,ly)) #
                 pi([[o,object],[l,location]],
                    truck_load(truck1, o, l)) #
                 pi([[o,object],[l,location]],
                    truck_load(truck2, o, l)) #
                 pi([[o,object],[l,location]],
                    truck_unload(truck1,o,l)) #
                 unload_all(truck2)
                )
       ).

addList(S, move(T, L1, L2)) <=> [loc(T, L2)].
delList(S, move(T, L1, L2)) <=> [loc(T, L1)].

addList(S, truck_load(truck1, O, L)) <=>
        [holding(truck1, O), quantity(O, L, XX)] :-
        member(quantity(O, L, X), S), XX is X - 1.
delList(S, truck_load(truck1, O, L)) <=>
        [holding(truck1, nothing), quantity(O, L, X)] :-
        member(quantity(O, L, X), S).

addList(S, truck_load(truck2, O, L)) <=>
        [holding(truck2, O), quantity(O, L, XX)] :-
        member(holding(truck2, nothing), S),
        member(quantity(O, L, X), S), XX is X - 1.
delList(S, truck_load(truck2, O, L)) <=>
        [holding(truck2, nothing), quantity(O, L, X)] :-
        member(holding(truck2, nothing), S),
        member(quantity(O, L, X), S).
addList(S, truck_load(truck2, O, L)) <=>
        [holding(truck2, both), quantity(O, L, XX)] :-
        not(member(holding(truck2, nothing), S)),
        member(quantity(O, L, X), S), XX is X - 1.
delList(S, truck_load(truck2, O, L)) <=>
        [holding(truck2, W), quantity(O, L, X)] :-
        not(member(holding(truck2, nothing), S)),
        member(holding(truck2, W), S),
        member(quantity(O, L, X), S).

addList(S, truck_unload(truck1, O, L)) <=>
        [holding(truck1, nothing), quantity(O, L, XX)] :-
        member(quantity(O, L, X), S), XX is X + 1.
delList(S, truck_unload(truck1, O, L)) <=>
        [holding(truck1, W), quantity(O, L, X)] :-
        member(holding(truck1, W), S),
        member(quantity(O, L, X), S).

addList(S, unload_all(truck2)) <=>
        [quantity(monitor, l3, XM1), quantity(server, l3, XS1),
         holding(truck2, nothing)] :-
        member(quantity(monitor, l3, XM), S), XM1 is XM + 1,
        member(quantity(server, l3, XS), S), XS1 is XS + 1.
delList(S, unload_all(truck2)) <=>
        [quantity(monitor, l3, XM), quantity(server, l3, XS),
         holding(truck2, both)] :-
        member(quantity(monitor, l3, XM), S),
        member(quantity(server, l3, XM), S).

perform(loc(T, L2), move(T, L1, L2)) <=> true.
perform(quantity(O, L, X), truck_load(T, O, L)) <=>
        some([[nx,num]], quantity(O, L, nx) & succ(X, nx)).
perform(holding(truck1, O), truck_load(truck1, O, L)) <=> true.
perform(holding(truck2, X), truck_load(truck2, O, L)) <=>
        (holding(truck2, nothing) & X~O) v
        (-holding(truck2, nothing) & X~both).
perform(holding(truck1, nothing), truck_unload(truck1, O, L)) <=> 
        true.
perform(quantity(O, L, X), truck_unload(truck1, O, L)) <=>
        some([[nx,num]], quantity(O, L, nx) & succ(nx, X)).
perform(holding(truck2, nothing), unload_all(truck2)) <=>
        true.
/*
perform(quantity(O, l3, X), unload_all(truck2)) <=>
        quantity(O, l3, X1) :- X1 is X - 1.
*/
perform(quantity(O, l3, X), unload_all(truck2)) <=>
        some([[y,num]], quantity(O, l3, y) & succ(y, X)).

perform(holding(T, O), truck_load(truck1, O1, L1)) <=>
        (T~truck2 & holding(T, O)) v
        (T~truck1 & O~O1).
perform(holding(T, O), truck_load(truck2, O1, L1)) <=>
        (T~truck1 & holding(T, O)) v
        (T~truck2 & holding(T, nothing) & O~O1) v
        (T~truck2 & -holding(T, nothing) & O~both).
perform(holding(T, O), truck_unload(truck1, O1, L1)) <=>
        (T~truck2 & holding(T, O)) v
        (T~truck1 & O~nothing).
perform(holding(T, O), unload_all(truck2)) <=>
        (T~truck1 & holding(T, O)) v
        (T~truck2 & O~nothing).

test1 :-
        N = 3,
        gove(holding(truck2, nothing) & loc(truck2, l2) &
             quantity(monitor, l1, N) & quantity(server, l1, N),
             while(-quantity(monitor,l3,N) v 
                   -quantity(server,l3,N),
                     truck_load(truck2,server,l2):
                     move(truck2,l2,d):
                     move(truck2,d,l1):
                     truck_load(truck2,monitor,l1):
                     move(truck2,l1,d):
                     move(truck2,d,l3):
                     unload_all(truck2):
                     move(truck2,l3,d):
                     move(truck2,d,l2)),
             loc(truck2, l2)).

test2 :-
        N = 3,
        gove(holding(truck2, nothing) & loc(truck2, l2) &
             quantity(monitor, l1, N) & quantity(server, l1, N) &
             quantity(monitor, l3, 0) & quantity(server, l3, 0),
             while(-quantity(monitor,l3,N),
                     truck_load(truck2,server,l2):
                     move(truck2,l2,d):
                     move(truck2,d,l1):
                     truck_load(truck2,monitor,l1):
                     move(truck2,l1,d):
                     move(truck2,d,l3):
                     unload_all(truck2):
                     move(truck2,l3,d):
                     move(truck2,d,l2)),
             quantity(server, l3, N)).


testt1 :-
        N = 3,
        gove_total(some([[n,num]], quantity(monitor, l1, const) & 
                   succ(n, const)),
                     truck_load(truck2,server,l2):
                     move(truck2,l2,d):
                     move(truck2,d,l1):
                     truck_load(truck2,monitor,l1):
                     move(truck2,l1,d):
                     move(truck2,d,l3):
                     unload_all(truck2):
                     move(truck2,l3,d):
                     move(truck2,d,l2),
             some([[n,num]], quantity(monitor, l1, n) & succ(n, const))
             ).

testt2 :-
        N = 3,
        gove_total(some([[n,num]], quantity(monitor, l1, const) & 
                   succ(n, const)),
                     truck_load(truck2,server,l2):
                     move(truck2,l2,d):
                     move(truck2,d,l1):
                     truck_load(truck2,monitor,l1):
                     move(truck2,l1,d):
                     move(truck2,d,l3):
                     unload_all(truck2):
                     move(truck2,l3,d):
                     move(truck2,d,l2),
             some([[n,num]], quantity(monitor, l1, n) & less(n, const))
             ).
