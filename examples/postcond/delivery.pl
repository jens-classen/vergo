%:- style_check(-singleton).
%:- ensure_loaded(progress).
%:- ensure_loaded(modelGen).
%:- ensure_loaded(gove).
%:- ensure_loaded(sc).

typeList([obj, location]).

constList([[home,location]]).

tdomain(obj, [o1, o2, o3, o4]).
tdomain(location, [home, office, factory, dock]).

predList([truck_on, l_at, t_at, dest, empty]).
type_info(truck_on, [obj]).
type_info(l_at, [obj, location]).
type_info(t_at, [location]).
type_info(dest, [obj, location]).
type_info(empty, []).

pred(truck_on(O)) :- 
        tdomain(obj, D), member(O, D).
pred(l_at(O, L)) :-
        tdomain(obj, OD), member(O, OD),
        tdomain(location, LD), member(L, LD).
pred(t_at(L)) :-
        tdomain(location, LD), member(L, LD).
pred(dest(O, L)) :-
        tdomain(obj, OD), member(O, OD),
        tdomain(location, LD), member(L, LD).
pred(location(L)) :-
        tdomain(location, LD), member(L, LD).
pred(empty).

:- assert(init_states([[
     l_at(o1, dock), l_at(o2, dock), l_at(o3, dock),
     l_at(o4, dock), 
     dest(o1, home), dest(o2, factory), dest(o3, office),
     dest(o4, home),
     empty, t_at(dock),
     obj(o1), obj(o2), obj(o3), obj(o4),
     location(home), location(office), 
     location(factory), location(dock)
   ]])).

:- assert(sc([
    /*
    all([[o,obj],[l1,location],[l2,location]],
        l_at(o,l1) & l_at(o,l2) => l1~l2),
    */
    all([x], truck_on(x) => obj(x)),
    all([x,y], l_at(x,y) => obj(x) & location(y)),
    all([x], t_at(x) => location(x)),
    all([x,y], dest(x,y) => obj(x) & location(y)),
    all([x], -obj(x) v -location(x)),
    location(dock), location(home), location(office),
    -(home~dock), -(home~office), -(home~factory),
    -(dock~office), -(dock~factory), -(office~factory)
   ])).

:- initall.

poss(truck_load(O, L)) <=> empty & l_at(O, L) & t_at(L).
poss(truck_unload(O, L)) <=> truck_on(O) & t_at(L).
poss(moveto(L1, L2)) <=> t_at(L1).

sc_proc(
           while(true,
                 pi([[x,obj],[y,location]], truck_load(x,y)) #
                 pi([[x,obj],[y,location]], truck_unload(x,y)) #
                 pi([[x,location],[y,location]], moveto(x,y))
                )
       ).

addList(S, truck_load(O, L)) <=> [truck_on(O)].
delList(S, truck_load(O, L)) <=> [l_at(O, L), empty].

addList(S, truck_unload(O, L)) <=> [l_at(O, L), empty].
delList(S, truck_unload(O, L)) <=> [truck_on(O)].

addList(S, moveto(L1, L2)) <=> [t_at(L2)].
delList(S, moveto(L1, L2)) <=> [t_at(L1)].

perform(truck_on(O), truck_load(O1, L1)) <=> 
        truck_on(O) v O~O1.
perform(truck_on(O), truck_unload(O1, L1)) <=>
        truck_on(O) & -(O~O1).

perform(l_at(O1, L1), truck_load(O2, L2)) <=>
        l_at(O1, L1) & -(O1~O2 & L1~L2).
perform(l_at(O1, L1), truck_unload(O2, L2)) <=>
        l_at(O1, L1) v (O1~O2 & L1~L2).

perform(empty, truck_load(O, L)) <=> false.
perform(empty, truck_unload(O, L)) <=> true.

perform(t_at(L), moveto(L1, L2)) <=> L~L2.

test1 :-
        gove(all([[o,obj]], l_at(o, dock)) & empty & t_at(dock),
             while(some([[x,obj]], l_at(x, dock)),
                   pi([[xx, obj]], 
                      truck_load(xx, dock) :
                      ( ?(dest(xx, factory)) :
                          moveto(dock, factory) :
                          truck_unload(xx, factory) :
                          moveto(factory, dock) #
                        ?(dest(xx, home)) :
                          moveto(dock, home) :
                          truck_unload(xx, home) :
                          moveto(home, dock) #
                        ?(dest(xx, office)) :
                          moveto(dock, office) :
                          truck_unload(xx, office) :
                          moveto(office, dock)
                      )
                     )
                  ),
             all([[o,obj], [l,location]], -l_at(o,l) v dest(o,l))
            ).
                

test2 :-
        gove(all([[o,obj]], l_at(o, dock)) & empty & t_at(dock),
             while(some([[x,obj]], l_at(x, dock)),
                   pi([[xx, obj]], 
                      truck_load(xx, dock) :
                      ( ?(dest(xx, factory)) :
                          moveto(dock, factory) :
                          truck_unload(xx, factory) :
                          moveto(factory, dock) #
                        ?(dest(xx, home)) :
                          moveto(dock, home) :
                          truck_unload(xx, home) :
                          moveto(home, dock) #
                        ?(dest(xx, office)) :
                          moveto(dock, office) :
                          truck_unload(xx, office) :
                          moveto(office, dock)
                      )
                     )
                  ),
             all([[o,obj]], -l_at(o,home) v dest(o,home))
            ).

test3 :-
        gove(all([[o,obj]], l_at(o, dock)) & empty & t_at(dock),
             while(some([[x,obj]], l_at(x, dock)),
                   pi([[xx, obj]], 
                      truck_load(xx, dock) :
                      ( ?(dest(xx, factory)) :
                          moveto(dock, factory) :
                          truck_unload(xx, factory) :
                          moveto(factory, dock) #
                        ?(dest(xx, home)) :
                          moveto(dock, home) :
                          truck_unload(xx, home) :
                          moveto(home, dock) #
                        ?(dest(xx, office)) :
                          moveto(dock, office) :
                          truck_unload(xx, office) :
                          moveto(office, dock)
                      )
                     )
                  ),
             empty
            ).

test4 :-
        gove(all([[o,obj]], l_at(o, dock)) & empty & t_at(dock),
             while(some([[x,obj]], l_at(x, dock)),
                   pi([[xx, obj]], 
                      truck_load(xx, dock) :
                      ( ?(dest(xx, factory)) :
                          moveto(dock, factory) :
                          truck_unload(xx, factory) :
                          moveto(factory, dock) #
                        ?(dest(xx, home)) :
                          moveto(dock, home) :
                          truck_unload(xx, home) :
                          moveto(home, dock) #
                        ?(dest(xx, office)) :
                          moveto(dock, office) :
                          truck_unload(xx, office) :
                          moveto(office, dock)
                      )
                     )
                  ),
             t_at(dock)
            ).