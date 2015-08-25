:- style_check(-singleton).
:- ensure_loaded(progress).
:- ensure_loaded(modelGen).
:- ensure_loaded(gove).
:- ensure_loaded(sc).

% Domain for test3 and test3_1

predList([l_in, l_at, t_at, l_in_city]).
typeList([all, obj, loc, city, l_in_city]).

%constList([[l1,loc],[l2,loc],[t1,truck],[c1,city]]).
constList([]).

tdomain(all, [o1, o2, t1, t2, p1, p2, l1, l2, c1]).
tdomain(obj, [o1, o2]).
tdomain(truck, [t1, t2]).
tdomain(plane, [p1, p2]).
tdomain(loc, [l1, l2, l3]).
tdomain(city, [c1]).
tdomain(truck_plane, [t1, t2, p1, p2]).

type_info(l_in, [obj, truck_plane]).
type_info(l_at, [obj, loc]).
type_info(t_at, [truck_plane, loc]).
type_info(l_in_city, [loc, city]).

pred(l_in(X, Y)) :- 
         member(X, [o1, o2]), member(Y, [t1, t2, p1, p2]).
pred(l_at(X, Y)) :-
         member(X, [o1, o2]),
         member(Y, [l1, l2, l3]).
pred(t_at(X, Y)) :-
         member(X, [t1, t2, p1, p2]),
         member(Y, [l1, l2, l3]).
pred(l_in_city(X, Y)) :-
         member(X, [l1, l2, l3]),
         member(Y, [c1]).

pred(obj(X)) :- tdomain(obj, D), member(X, D).
pred(truck(X)) :- tdomain(truck, D), member(X, D).
pred(plane(X)) :- tdomain(plane, D), member(X, D).
pred(loc(X)) :- tdomain(loc, D), member(X, D).
pred(city(X)) :- tdomain(city, D), member(X, D).
pred(truck_plane(X)) :- tdomain(truck_plane, D), member(X, D).

/*
pred(truck(T)) :- member(T, [t1, t2]).
pred(plane(P)) :- member(P, [p1, p2]).
pred(city(C)) :- member(C, [c1]).
pred(loc(L)) :- member(L, [l1, l2]).
pred(obj(O)) :- member(O, [o1, o2]).
*/

/*
% states for test17.
:- assert(init_states(
   [[t_at(t1, l1), t_at(t2, l2), t_at(p1, l1), t_at(p2, l1),
     l_in(o1, t1), l_in(o2, t1), 
     truck(t1), truck(t2), obj(o1), obj(o2),
     plane(p1), plane(p2), loc(l1), loc(l2),
     city(c1),
     l_in_city(l1, c1), l_in_city(l2, c1)],
    [t_at(t1, l1), t_at(t2, l2), t_at(p1, l1), t_at(p2, l1),
     l_in(o2, t2), l_at(o1, l2), 
     truck(t1), truck(t2), obj(o1), obj(o2),
     plane(p1), plane(p2), loc(l1), loc(l2),
     city(c1),
     l_in_city(l1, c1), l_in_city(l2, c1)]]
 )).
*/

% states for test18

:- assert(init_states(
   [[t_at(t1, l2), t_at(t2, l2), t_at(p1, l1), t_at(p2, l1),
     l_at(o1, l2), l_at(o2, l2),
     truck_plane(t1), truck_plane(t2),
     truck_plane(p1), truck_plane(p2),
     truck(t1), truck(t2), obj(o1), obj(o2),
     plane(p1), plane(p2), loc(l1), loc(l2), loc(l3),
     city(c1),
     l_in_city(l1, c1), l_in_city(l2, c1), l_in_city(l3, c1)]]
  )).

/*
:- assert(sc(
   [all([[x1,loc], [x2,city], [x3,city]], 
        l_in_city(x1, x2) & l_in_city(x1, x3) => x2~x3),
   l_in_city(l1, c1), l_in_city(l2, c1),
%   all([x], truck_plane(x) => (truck(x) v plane(x))),
%   all([[x,obj],[y,all]], l_in(x,y) => (truck(y) v plane(y))),
   all([[x1,obj],[x2,truck],[x3,truck]], 
       l_in(x1,x2) & l_in(x1,x3) => x2~x3),
   all([[x1,obj],[x2,truck],[x3,plane]], 
       -l_in(x1,x2) v -l_in(x1,x3)),
   all([[x1,obj],[x2,loc],[x3,loc]], 
       l_at(x1,x2) & l_at(x1,x3) => x2~x3),
   all([[x1,truck],[x2,loc],[x3,loc]], 
       t_at(x1,x2) & t_at(x1,x3) => x2~x3),
   all([[t,truck]], some([[l,loc]], t_at(t,l)))
%   all([x, l], l_at(x, l) => loc(l)),
%   all([x, y], l_in(x, y) => obj(x)),
%   all([x,y], obj(x) & truck(y) => -(x~y))
   ]
)).
*/

:- assert(sc([
       all([x, y], l_in(x, y) => obj(x) & truck_plane(y)),
       all([x, y], l_at(x, y) => obj(x) & loc(y)),
       all([x, y], t_at(x, y) => truck_plane(x) & loc(y)),
       all([x, y], l_in_city(x, y) => loc(x) & city(y)),
       all([x], truck(x) => truck_plane(x)),
       all([x], plane(x) => truck_plane(x)),
       all([x], -obj(x) v -truck(x)),
       all([x], -obj(x) v -plane(x)),
       all([x], -obj(x) v -truck_plane(x)),
       all([x], -obj(x) v -city(x)),
       all([x], -obj(x) v -loc(x)),
       all([x], -truck(x) v -plane(x)),
       all([x], -truck(x) v -loc(x)),
       all([x], -truck(x) v -city(x)),
       all([x], -plane(x) v -loc(x)),
       all([x], -plane(x) v -city(x)),
       all([x], -truck_plane(x) v -loc(x)),
       all([x], -truck_plane(x) v -city(x)),
       all([x], -loc(x) v -city(x))
   ])).

:- initall.

addList(S, load_truck(O, T, L)) <=> [l_in(O, T)].
delList(S, load_truck(O, T, L)) <=> [l_at(O, L)].

addList(S, load_plane(O, P, L)) <=> [l_in(O, P)].
delList(S, load_plane(O, P, L)) <=> [l_at(O, L)].

addList(S, unload_truck(O, T, L)) <=> [l_at(O, L)].
delList(S, unload_truck(O, T, L)) <=> [l_in(O, T)].

addList(S, unload_plane(O, A, L)) <=> [l_at(O, L)].
delList(S, unload_plane(O, A, L)) <=> [l_in(O, A)].

addList(S, drive_truck(T, LF, LT, C)) <=> [t_at(T, LT)].
delList(S, drive_truck(T, LF, LT, C)) <=> [t_at(T, LF)].

addList(S, fly_plane(A, LF, LT)) <=> [t_at(A, LT)].
delList(S, fly_plane(A, LF, LT)) <=> [t_at(A, LF)].

perform(l_in(O, T), load_truck(O1, T1, L1)) <=>
    l_in(O, T) v (O ~ O1 & T ~ T1).
perform(l_in(O, T), load_plane(O1, P1, L1)) <=>
    l_in(O, T) v (O ~ O1 & T ~ P1).
perform(l_in(O, T), unload_truck(O1, T1, L1)) <=>
    l_in(O, T) & -(O ~ O1 & T ~ T1).
perform(l_in(O, T), unload_plane(O1, A1, L1)) <=>
    l_in(O, T) & -(O ~ O1 & T ~ A1).
perform(l_in(O, T), drive_truck(T1, LF1, LT1, C1)) <=>
    l_in(O, T).
perform(l_in(O, T), fly_plane(A1, LF1, LT1)) <=>
    l_in(O, T).

perform(l_at(O, L), load_truck(O1, T1, L1)) <=>
    l_at(O, L) & -(O ~ O1 & L ~ L1).
perform(l_at(O, L), load_plane(O1, P1, L1)) <=>
    l_at(O, L) & -(O ~ O1 & L ~ L1).
perform(l_at(O, L), unload_truck(O1, T1, L1)) <=>
    l_at(O, L) v (O ~ O1 & L ~ L1).
perform(l_at(O, L), unload_plane(O1, A1, L1)) <=>
    l_at(O, L) v (O ~ O1 & L ~ L1).

perform(t_at(O, L), drive_truck(T1, LF1, LT1, C1)) <=>
    t_at(O, L) & -(O ~ T1 & L ~ LF1) v (O ~ T1 & L ~ LT1).
perform(t_at(O, L), fly_plane(A1, LF1, LT1)) <=>
    t_at(O, L) & -(O ~ A1 & L ~ LF1) v (O ~ A1 & L ~ LT1).

perform(l_in_city(A, B), load_truck(O1, T1, L1)) <=>
    l_in_city(A, B).
perform(l_in_city(A, B), load_plane(O1, T1, L1)) <=>
    l_in_city(A, B).
perform(l_in_city(A, B), unload_truck(O1, T1, L1)) <=>
    l_in_city(A, B).
perform(l_in_city(A, B), unload_plane(O1, T1, L1)) <=>
    l_in_city(A, B).
perform(l_in_city(A, B), drive_truck(T1, LF1, LT1, C1)) <=>
    l_in_city(A, B).
perform(l_in_city(A, B), fly_plane(A1, LF1, LT1)) <=>
    l_in_city(A, B).

poss(load_truck(O, T, L)) <=> t_at(T, L) & l_at(O, L) & 
                               truck(T) & obj(O) & loc(L).
poss(load_plane(O, P, L)) <=> t_at(O, L) & l_at(P, L) &
                               plane(P) & obj(O) & loc(L).
poss(unload_truck(O, T, L)) <=> t_at(T, L) & l_in(O, T) &
                                 truck(T) & obj(O) & loc(L).
poss(unload_plane(O, A, L)) <=> l_in(O, A) & t_at(A, L) &
                                plane(A) & obj(O) & loc(L).
poss(drive_truck(T, LF, LT, C)) <=>
    t_at(T, LF) & l_in_city(LF, C) & l_in_city(LT, C) &
    truck(T) & loc(LF) & loc(LT) & city(C) & -(LF~LT).
poss(fly_plane(A, LF, LT)) <=> t_at(A, LF) & 
                               plane(A) & loc(LF) & loc(LT).

test1 :-
  P =  (while(some([[x,obj],[y,truck],[l1,loc]], obj(x) & truck(y) & t_at(y,l1) & loc(l1) & l_in(x,y)),
          pi([[x,obj],[y,truck],[l1,loc]], ?(obj(x) & truck(y) & loc(l1) & t_at(y,l1)) : 
		   unload_truck(x,y,l1)))),
  toFullProg(P, P1), prettyP(P1),
  init_states(S), faprog(S, P1, P2, SS),
  prettyP(P2), prettyS(SS).

test2 :-
  f_reg(all([x,y], -(obj(x) & l_in(x,y)) v -truck(y)),
        while(some([x,y], obj(x) & truck(y) & l_in(x,y)),
              pi([x,y], ?(obj(x) & truck(y) & loc(l1) & l_at(y,l1)) : unload_truck(x,y,l1))),
        R).

test3 :-
  f_reg(all([[ob,obj],[tp,truck_plane]], -(l_in(ob,tp)) v plane(tp)),
        while(some([[x,obj],[y,truck_plane]], 
                   truck(y) & l_in(x,y)),
              pi([[xx,obj],[yy,truck_plane],[ll1,loc]], unload_truck(xx,yy,ll1))),
        R).

test3_1 :-
  f_reg(all([[ob,obj],[tp,all]], -(l_in(ob,tp)) v plane(tp)),
        while(some([[x,obj],[y,all],[l1,loc]], 
                   obj(x) & truck(y) & loc(l1) & l_at(y,l1) & l_in(x,y)),
              pi([[xx,obj],[yy,truck_plane],[ll1,loc]], unload_truck(xx,yy,ll1))),
        R).

test4 :-
        f_reg(
                 all([x,y,z], -l_in(x,y) v -l_in(x,z) v y~z),
                 while(
                          true,
                          pi([a,b,c], load_truck(a,b,c)) #
                          pi([a,b,c], load_plane(a,b,c)) #
                          pi([a,b,c], unload_truck(a,b,c)) #
                          pi([a,b,c], unload_plane(a,b,c)) #
                          pi([a,b,c,d], drive_truck(a,b,c,d)) #
                          pi([a,b,c], fly_plane(a,b,c))),
                 R).

test5 :-
        f_reg(
                 all([[x,object],[y,truck_plane],[z,truck_plane]], 
                     -l_in(x,y) v -l_in(x,z) v y~z),
                 while(
                          true,
                          pi([[a,object],[b,truck],[c,location]], 
                             load_truck(a,b,c)) #
                          pi([[a,object],[b,plane],[c,location]], 
                             load_plane(a,b,c)) #
                          pi([[a,object],[b,truck],[c,location]],
                             unload_truck(a,b,c)) #
                          pi([[a,object],[b,plane],[c,location]], 
                             unload_plane(a,b,c)) #
                          pi([[a,truck],[b,location],[c,location],[d,city]],
                             drive_truck(a,b,c,d)) #
                          pi([[a,plane],[b,location],[c,location]],
                             fly_plane(a,b,c))),
                 R).

test6 :-
        f_reg(
                 all([[x,object],[y,truck_plane],[z,truck_plane]], 
                     -l_at(x,y) v -l_at(x,z) v y~z),
                 while(
                          true,
                          pi([[a,object],[b,truck],[c,location]], 
                             load_truck(a,b,c)) #
                          pi([[a,object],[b,plane],[c,location]], 
                             load_plane(a,b,c)) #
                          pi([[a,object],[b,truck],[c,location]],
                             unload_truck(a,b,c)) #
                          pi([[a,object],[b,plane],[c,location]], 
                             unload_plane(a,b,c)) #
                          pi([[a,truck],[b,location],[c,location],[d,city]],
                             drive_truck(a,b,c,d)) #
                          pi([[a,plane],[b,location],[c,location]],
                             fly_plane(a,b,c))),
                 R).

%const_type(o2, obj).
test7 :-
  f_reg(all([[tp, truck_plane]], -(l_in(o2,tp)) v plane(tp)),
        while(some([[x,obj],[y,truck_plane],[l1,loc]], 
                   obj(x) & truck(y) & loc(l1) & l_at(y,l1) & l_in(x,y)),
              pi([[xx,obj],[yy,truck_plane],[ll1,loc]], unload_truck(xx,yy,ll1))),
        R).

constList([t1, c1, box, locA, locB, locC]).
const_type(box, obj).
const_type(locA, loc).
const_type(locB, loc).
const_type(locC, loc).
%const_type(truck, t1).
test8 :-
  f_reg(obj(box) & l_at(box, locB),
        while(some([[xx, truck]], l_at(xx, locA)),
              pi([[x, truck]],
                 drive_truck(x, locA, locB, c1):
                 while(some([[yy, obj]], l_in(yy, x)),
                       pi([[y, obj]],
                          unload_truck(y, x, locB))))),
        R).

test9 :-
  f_reg(obj(box) & l_at(box, locB),
        pi([[x, truck]],
           drive_truck(x, locA, locB, c1):
           while(some([[yy, obj]], l_in(yy, x)),
                 pi([[y, obj]],
                    unload_truck(y, x, locB)))),
        R).

test10 :-
  f_reg(obj(box) & l_at(box, locB),
           drive_truck(t1, locA, locB, c1):
           while(some([[yy, obj]], l_in(yy, t1)),
                 pi([[y, obj]],
                    unload_truck(y, t1, locB))),
        R).

test11 :-
  (Phi = all([[truck, non]], (some([[xx, truck]], l_at(xx, locA)) v l_at(box, locB) ))),
  (C = some([[xx, truck]], l_at(xx, locA))),
  f_reg(Phi,
        pi([[x, truck]], drive_truck(x, locA, locB, c1)), Reg),
  writeln(Reg),
  fol_imply(Phi & C, Reg, Imply),
  writeln(Imply).

test12 :-
  f_reg(some([[t, truck]], l_at(t, locA)) v 
        obj(box) & l_at(box, locB),
        pi([[x, truck]],
        while(some([[yy, obj]], l_in(yy, x)),
              pi([[y, obj]],
                 unload_truck(y, x, locB)))),
        R).

tempArgs([[t, truck], [l,loc]]).
test13 :-
        f_reg(all([[x, obj]], l_at(x, locA)),
              while(some([[tt, truck]], -t_at(tt, locA)),
                    pi([[t, truck], [l, loc]],
                       drive_truck(t, l, locA, c1):
                       while(some([[oo, obj]], l_in(oo, t)),
                             pi([[o, obj]],
                                unload_truck(o, t, locA))))),
              R).
			  
test14 :-
  P =  (while(some([[tt, truck]], -t_at(tt, l2)),
                    pi([[t, truck], [l, loc]],
                       drive_truck(t, l, l2, c1):
                       while(some([[oo, obj]], l_in(oo, t)),
                             pi([[o, obj]],
                                unload_truck(o, t, l2)))))),
  toFullProg(P, P1), prettyP(P1),
  init_states(S), faprog(S, P1, P2, SS, Flag),
  prettyP(P2), prettyS(SS), writeln(Flag).
  
test15 :-
  P =  (while(
                          true,
                          pi([[a,obj],[b,truck],[c,loc]], 
                             load_truck(a,b,c)) #
                          pi([[a,obj],[b,plane],[c,loc]], 
                             load_plane(a,b,c)) #
                          pi([[a,obj],[b,truck],[c,loc]],
                             unload_truck(a,b,c)) #
                          pi([[a,obj],[b,plane],[c,loc]], 
                             unload_plane(a,b,c)) #
                          pi([[a,truck],[b,loc],[c,loc],[d,city]],
                             drive_truck(a,b,c,d)) #
                          pi([[a,plane],[b,loc],[c,loc]],
                             fly_plane(a,b,c)))),
  toFullProg(P, P1), prettyP(P1),
  init_states(S), faprog(S, P1, P2, SS),
  prettyP(P2), prettyS(SS).

test16 :-
        getModel(all([[o,obj]], some([[t,truck]], l_in(o,t))),
                 [[l_in(o1, t2), l_in(o2, t1)],
                  [l_in(o1, t2), l_in(o2, t2)],
                  [l_in(o1, t1), l_in(o2, t2)],
                  [l_in(o1,t2),l_in(o2,t1),t_at(t1,l1),t_at(t2,l1),
                   l_in_city(l1,c1),l_in_city(l2,c1)],
                  [l_in(o1,t2),l_in(o2,t2),t_at(t1,l1),t_at(t2,l1),
                   l_in_city(l1,c1),l_in_city(l2,c1)]], S), write(S).

test17 :-
        gove(all([[x,obj]], some([[lo,loc],[t,truck]],
                                 l_at(x,lo) v l_in(x, t))),
             while(some([[xx,obj],[tt,truck]], l_in(xx,tt)),
                   pi([[x,obj],[t,truck],[lo,loc]], unload_truck(x, t, lo))),
             all([[x,obj]], some([[lo,loc]], l_at(x,lo)))).

test18 :-
        gove(all([[x, obj]], l_at(x, l2)),
             while(some([[xa, obj]], l_at(xa, l2)),
                   pi([[x, obj]], 
                      load_truck(x, t1, l2))):
             drive_truck(t1, l2, l1, c1):
             while(some([[ya, obj]], l_in(ya, t1)),
                   pi([[y, obj]], 
                      unload_truck(y, t1, l1))),
             all([[x, obj]], l_at(x, l1))).

sc_proc(
           while(true,
                 pi([[x, obj], [t, truck], [l, loc]],
                    load_truck(x, t, l)) #
                 pi([[x, obj], [t, truck], [l, loc]],
                    unload_truck(x, t, l)) #
                 pi([[x, obj], [p, plane], [l, loc]],
                    load_plane(x, p, l)) #
                 pi([[x, obj], [p, plane], [l, loc]],
                    unload_plane(x, p, l)) #
                 pi([[t, truck], [l1, loc], [l2, loc], [c, city]],
                    drive_truck(t, l1, l2, c)) #
                 pi([[p, plane], [l1, loc], [l2, loc]],
                    fly_plane(p, l1, l2))
                )
       ).