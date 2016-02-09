:- dynamic(initially/1).
:- dynamic(domain/2).

:- ['main_abstraction'].

experiment(Rooms,Dishes,InitialTheory) :- 
        retractall(domain(room,_)),
        assert_domain_atoms(room,r,Rooms),
        retractall(domain(dish,_)),
        assert_domain_atoms(dish,d,Dishes),
        (InitialTheory = false -> 
            retractall(initially(_));true),
        time(compute_abstraction(main)),
        time(verify(prop1)),
        time(verify(prop2)),
        time(verify(prop3)),
        time(verify(prop4)),
        time(verify(prop5)).        

assert_domain_atoms(Domain,Prefix,N) :-
        N > 0, !,
        atom_number(NAtom,N),
        atom_concat(Prefix,NAtom,Atom),
        asserta(domain(Domain,Atom)),
        N1 is N-1,
        assert_domain_atoms(Domain,Prefix,N1).
assert_domain_atoms(_Domain,_Prefix,0).
