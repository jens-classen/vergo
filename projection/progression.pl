%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(progression, [progress/3,
                        progress/4]).

:- use_module('regression').
:- use_module('../kbs/l_kb').
:- use_module('../lib/utils').
:- use_module('../logic/cwa').
:- use_module('../logic/fol').
:- use_module('../logic/una').

:- multifile user:progression_style/1.
:- multifile user:causes_true/3.
:- multifile user:causes_false/3.

:- discontiguous progress/2.

progress(KB1,Action,KB2) :-
        user:progression_style(Style),
        progress(Style,KB1,Action,KB2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Closed-World STRIPS progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: make sure CWA applies to fluents and all actions are STRIPS
%       (produce warning when not)

progress(strips(closed),KB1,Action,KB2) :-
        ground(Action), !,
        findall(del(Fluent),user:causes_false(Action,Fluent,true),Dels),
        findall(add(Fluent),user:causes_true(Action,Fluent,true),Adds),
        append([Dels,Adds],Mods),
        update_kb(KB1,Mods,KB2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Open-World STRIPS progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: make sure CWA applies to fluents and all actions are STRIPS
%       (produce warning when not)

progress(strips(open),KB1,Action,KB2) :-
        ground(Action), !,
        findall(del(Fluent),user:causes_false(Action,Fluent,true),DelsF),
        findall(add(-Fluent),user:causes_false(Action,Fluent,true),AddsF),
        findall(add(Fluent),user:causes_true(Action,Fluent,true),AddsA),
        findall(del(-Fluent),user:causes_true(Action,Fluent,true),DelsA),
        append([DelsF,DelsA,AddsF,AddsA],Mods),
        update_kb(KB1,Mods,KB2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ADL (PDDL subset, i.e. CWA + domain closure)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: make sure CWA applies to fluents and effect conditions are
%       just-in-time CWA (produce warning when not)
%       e.g. shoot action in Wumpus world

progress(adl,KB1,Action,KB2) :-
        ground(Action), !,
        findall(del(Fluent),(user:causes_false(Action,Fluent,Cond),
                        eval_cwa(Cond)),Dels),
        findall(add(Fluent),(user:causes_true(Action,Fluent,Cond),
                        eval_cwa(Cond)),Adds),
        append([Dels,Adds],Mods),
        update_kb(KB1,Mods,KB2).

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
