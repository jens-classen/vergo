:- dynamic(initially/1).
:- dynamic(domain/2).

:- use_module('../../lib/utils').

:- ['main_cgraphs'].

% Runs one experiment, i.e. _all_ 5 properties tested on _one_
% conbination of rooms, dishes and initial theory. To avoid
% side effects, each new experiment should be started in a fresh
% instance of Prolog.
experiment(Rooms,Dishes,InitialTheory,FileName,TimeOutC,TimeOutP) :- 
        local_time_and_date_as_string(TimeS),
        atom_string(Time,TimeS),
        retractall(domain(room,_)),
        assert_domain_atoms(room,'r',Rooms),
        retractall(domain(dish,_)),
        assert_domain_atoms(dish,'d',Dishes),
        (InitialTheory = false -> 
            retractall(initially(_));true),
        measure_time_with_limit(construct_characteristic_graph(main),
                                TimeOutC,TWC,TCC),
        (TWC = timeout ->
            (Nodes = 'n/a', Edges = 'n/a', 
             TW1 = 'n/a', TW2 = 'n/a', TW3 = 'n/a', TW4 = 'n/a', TW5 = 'n/a',
             TC1 = 'n/a', TC2 = 'n/a', TC3 = 'n/a', TC4 = 'n/a', TC5 = 'n/a');
            (number_of_nodes(Nodes),
             number_of_edges(Edges),
             measure_time_with_limit(verify(main,prop1),TimeOutP,TW1,TC1),
             measure_time_with_limit(verify(main,prop2),TimeOutP,TW2,TC2),
             measure_time_with_limit(verify(main,prop3),TimeOutP,TW3,TC3),
             measure_time_with_limit(verify(main,prop4),TimeOutP,TW4,TC4),
             measure_time_with_limit(verify(main,prop5),TimeOutP,TW5,TC5))),
        Row = [Time,
               Rooms,
               Dishes,
               InitialTheory,
               Nodes,
               Edges,
               TWC,TCC,
               TW1,TC1,
               TW2,TC2,
               TW3,TC3,
               TW4,TC4,
               TW5,TC5],
        append_to_csv(FileName,Row).

number_of_nodes(Nodes) :-
        cg_number_of_nodes(main,Nodes).
number_of_edges(Edges) :-
        count(cg_edge(main,_,_,_,_), Edges).

/**
 * assert_domain_atoms(+Domain,+Prefix,+N) is det
 *
 * Creates a finite domain (type) of name Domain with N consecutively 
 * numbered elements (standard names) prefixed with Prefix. For example,
 * 
 * assert_domain_atoms(test,t,3)
 * 
 * yields
 * 
 * domain(test,'#t1').
 * domain(test,'#t2').
 * domain(test,'#t3').
 *
 **/
assert_domain_atoms(Domain,Prefix,N) :-
        N > 0, !,
        atom_number(NAtom,N),
        atom_concat('#',Prefix,Prefix2),
        atom_concat(Prefix2,NAtom,Atom),
        asserta(domain(Domain,Atom)),
        N1 is N-1,
        assert_domain_atoms(Domain,Prefix,N1).
assert_domain_atoms(_Domain,_Prefix,0).
