:- ['dish_robot_bat_syn'].

:- use_module('../../verification/synthesis_acyclic').
:- use_module('../../lib/utils').
:- use_module('../../logic/l').

% Runs one experiment, modifies the BAT to use the specified numbers
% of rooms and dishes, then calls synthesize/2 on the specified
% program and property. To avoid side effects, each new experiment
% should be started in a fresh instance of Prolog.
experiment(Rooms,Dishes,Program,Property,FileName,TimeOut) :- 
        local_time_and_date_as_string(TimeS),
        atom_string(Time,TimeS),
        retractall(domain(dish,_)),
        retractall(domain(room,_)),
        assert_domain_atoms(dish,'d',Dishes),
        assert_domain_atoms(room,'r',Rooms),
        measure_time_with_limit(synthesize(Program,Property,Strategy),
                                TimeOut,TWC,TCC),
        (TWC = timeout ->
            (Nodes = 'n/a', Edges = 'n/a',
             StNodes = 'n/a', StEdges = 'n/a');
            (number_of_nodes(Nodes),
             number_of_edges(Edges),
             strategy_size(Strategy,StNodes,StEdges))),
        Row = [Time,
               Rooms,
               Dishes,
               Program,
               Property,
               Nodes,
               Edges,
               StNodes,
               StEdges,
               TWC,
               TCC],
        append_to_csv(FileName,Row).

number_of_nodes(Nodes) :-
        count('synthesis_acyclic':abstract_state(_,_),Nodes).
number_of_edges(Edges) :-
        count('synthesis_acyclic':abstract_trans(_,_,_),Edges).
strategy_size([],0,0) :- !.
strategy_size([(_,S)|Strat],N,E) :-
        strategy_size(Strat,N1,E1),
        N is N1+1,
        length(S,E2),
        E is E1+E2.

assert_domain_atoms(Domain,Prefix,N) :-
        N > 0, !,
        atom_number(NAtom,N),
        atom_concat('#',Prefix,Prefix2),
        atom_concat(Prefix2,NAtom,Atom),
        asserta(domain(Domain,Atom)),
        N1 is N-1,
        assert_domain_atoms(Domain,Prefix,N1).
assert_domain_atoms(_Domain,_Prefix,0).
