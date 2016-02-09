:- dynamic(initially/1).
:- dynamic(domain/2).

:- ['main_cgraphs'].

experiment(Rooms,Dishes,InitialTheory) :- 
        retractall(domain(room,_)),
        assert_domain_atoms(room,r,Rooms),
        retractall(domain(dish,_)),
        assert_domain_atoms(dish,d,Dishes),
        (InitialTheory = false -> 
            retractall(initially(_));true),
        time(construct_characteristic_graph(main)),
        time(verify(main,prop1)),
        time(verify(main,prop2)),
        time(verify(main,prop3)),
        time(verify(main,prop4)),
        time(verify(main,prop5)).        

assert_domain_atoms(Domain,Prefix,N) :-
        N > 0, !,
        atom_number(NAtom,N),
        atom_concat(Prefix,NAtom,Atom),
        asserta(domain(Domain,Atom)),
        N1 is N-1,
        assert_domain_atoms(Domain,Prefix,N1).
assert_domain_atoms(_Domain,_Prefix,0).
