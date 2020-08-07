%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(progression, [progress/1,
                        progress/2]).

:- use_module('regression').
:- use_module('../lib/utils').
:- use_module('../logic/cwa').
:- use_module('../logic/fol').
:- use_module('../logic/una').

:- multifile user:progression_style/1.
:- multifile user:causes_true/3.
:- multifile user:causes_false/3.

:- discontiguous progress/2.

:- dynamic user:initially/1.

progress(Action) :-
        user:progression_style(Style),
        progress(Action,Style).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Closed-World STRIPS progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: make sure CWA applies to fluents and all actions are STRIPS
%       (produce warning when not)

progress(Action,strips(closed)) :-
        ground(Action), !,
        findall(Fluent,user:causes_false(Action,Fluent,true),Dels),
        findall(Fluent,user:causes_true(Action,Fluent,true),Adds),
        del_facts_closed(Dels),
        add_facts_closed(Adds).

del_facts_closed([Fact|Facts]) :- 
        retractall(user:initially(Fact)),
        del_facts_closed(Facts).
del_facts_closed([]).

add_facts_closed([Fact|Facts]) :- 
        assert(user:initially(Fact)),
        add_facts_closed(Facts).
add_facts_closed([]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Open-World STRIPS progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: make sure CWA applies to fluents and all actions are STRIPS
%       (produce warning when not)

progress(Action,strips(open)) :-
        ground(Action), !,
        findall(Fluent,user:causes_false(Action,Fluent,true),Dels),
        findall(Fluent,user:causes_true(Action,Fluent,true),Adds),
        del_facts_open(Dels),
        add_facts_open(Adds).

del_facts_open([Fact|Facts]) :- 
        retractall(user:initially(Fact)),
        assert(user:initially(-Fact)),
        del_facts_open(Facts).
del_facts_open([]).

add_facts_open([Fact|Facts]) :-
        retractall(user:initially(-Fact)),
        assert(user:initially(Fact)),
        add_facts_open(Facts).
add_facts_open([]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ADL (PDDL subset, i.e. CWA + domain closure)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: make sure CWA applies to fluents and effect conditions are
%       just-in-time CWA (produce warning when not)
%       e.g. shoot action in Wumpus world

progress(Action,adl) :-
        ground(Action), !,
        findall(Fluent,(user:causes_false(Action,Fluent,Cond),
                        eval_cwa(Cond)),Dels),
        findall(Fluent,(user:causes_true(Action,Fluent,Cond),
                        eval_cwa(Cond)),Adds),
        del_facts_closed(Dels),
        add_facts_closed(Adds).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Progression for local-effect theories
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% progress(Action,local_effect) :-
%         ground(Action), !,
%         findall(Fluent,
%                 (user:causes_false(Action,Fluent,_Cond1);
%                  user:causes_true(Action,Fluent,_Cond2)),
%                 CharacteristicSet).
%         % generate all combinations / truth assignment
%         % generate all instantiated SSAs
%         % unify each with initial theory
%         % apply regression from verification/abstraction_local-effect to each
%         % disjoin them all = result
