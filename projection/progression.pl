:- ['regression'].

:- discontiguous progress/2.

progress(Action) :-
        progression_style(Style),
        progress(Action,Style).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Closed-World STRIPS progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

progress(Action,strips(closed)) :-
        ground(Action), !,
        findall(Fluent,causes_false(Action,Fluent,true),Dels),
        findall(Fluent,causes_true(Action,Fluent,true),Adds),
        del_facts_closed(Dels),
        add_facts_closed(Adds).

del_facts_closed([Fact|Facts]) :- 
        retractall(initially(Fact)),
        del_facts_closed(Facts).
del_facts_closed([]).

add_facts_closed([Fact|Facts]) :- 
        assert(initially(Fact)),
        add_facts_closed(Facts).
add_facts_closed([]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Open-World STRIPS progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

progress(Action,strips(open)) :-
        ground(Action), !,
        findall(Fluent,causes_false(Action,Fluent,true),Dels),
        findall(Fluent,causes_true(Action,Fluent,true),Adds),
        del_facts_open(Dels),
        add_facts_open(Adds).

del_facts_open([Fact|Facts]) :- 
        retractall(initially(Fact)),
        assert(initially(-Fact)),
        del_facts_open(Facts).
del_facts_open([]).

add_facts_open([Fact|Facts]) :-
        retractall(initially(-Fact)),
        assert(initially(Fact)),
        add_facts_open(Facts).
add_facts_open([]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ADL (PDDL subset, i.e. CWA + domain closure)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: Cond may contain non-CWA atoms => need reasoning!
%       (example: Wumpus shoot action)

progress(Action,adl) :-
        ground(Action), !,
        findall(Fluent,(causes_false(Action,Fluent,Cond),
                        adl_holds(Cond)),Dels),
        findall(Fluent,(causes_true(Action,Fluent,Cond),
                        adl_holds(Cond)),Adds),
        del_facts_closed(Dels),
        add_facts_closed(Adds).

adl_holds(Atom) :-
        cwa(Atom),
        initially(Atom).
adl_holds(true).
adl_holds(false) :-
        fail.
adl_holds(F1*F2) :-
        adl_holds(F1),
        adl_holds(F2).
adl_holds(F1+F2) :-
        adl_holds(F1);
        adl_holds(F2).
adl_holds(-F) :-
        not(adl_holds(F)).
adl_holds(F1<=>F2) :-
        adl_holds((F1=>F2)*(F2=>F1)).
adl_holds(F1=>F2) :-
        adl_holds((-F1)+F2).
adl_holds(F1<=F2) :-
        adl_holds(F2=>F1).
adl_holds(some(_V,F)) :-
        adl_holds(F). %succeed if able to instantiate _V
adl_holds(all(V,F)) :-
        not(adl_holds(some(V,-F))).
adl_holds(F) :-
        def(F,FD),
        adl_holds(FD).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Progression for local-effect theories
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% progress(Action,local_effect) :-
%         ground(Action), !,
%         findall(Fluent,
%                 (causes_false(Action,Fluent,_Cond1);
%                  causes_true(Action,Fluent,_Cond2)),
%                 CharacteristicSet).
%         % generate all combinations / truth assignment
%         % generate all instantiated SSAs
%         % unify each with initial theory
%         % apply regression from verification/abstraction_local-effect to each
%         % disjoin them all = result
