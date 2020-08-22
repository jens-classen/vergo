%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(progression, [progress/3,
                        progress/4,
                        can_progress/3]).

:- use_module('regression').
:- use_module('../kbs/l_kb').
:- use_module('../lib/utils').
:- use_module('../logic/cwa').
:- use_module('../logic/fol').
:- use_module('../logic/una').

:- multifile user:progression_style/3.
:- multifile user:causes_true/3.
:- multifile user:causes_false/3.

:- discontiguous progress/4.
:- discontiguous can_progress/3.

progress(KB1,Action,KB2) :-
        % user-determined progression style
        user:progression_style(Style,KB1,Action), !,
        progress(Style,KB1,Action,KB2).

progress(KB1,Action,KB2) :-
        % automatically determined progression style
        can_progress(Style,KB1,Action), !,
        progress(Style,KB1,Action,KB2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Closed-World STRIPS progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

progress(strips(closed),KB1,Action,KB2) :-
        ground(Action), !,
        findall(del(Fluent),user:causes_false(Action,Fluent,true),Dels),
        findall(add(Fluent),user:causes_true(Action,Fluent,true),Adds),
        append([Dels,Adds],Mods),
        update_kb(KB1,Mods,KB2).

can_progress(strips(closed),_KB,Action) :-
        forall(user:causes_false(Action,Fluent,Cond),
               (Cond = true, cwa(Fluent))),
        forall(user:causes_true(Action,Fluent,Cond),
               (Cond = true, cwa(Fluent))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Open-World STRIPS progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

progress(strips(open),KB1,Action,KB2) :-
        ground(Action), !,
        findall(del(Fluent),user:causes_false(Action,Fluent,true),DelsF),
        findall(add(-Fluent),user:causes_false(Action,Fluent,true),AddsF),
        findall(add(Fluent),user:causes_true(Action,Fluent,true),AddsA),
        findall(del(-Fluent),user:causes_true(Action,Fluent,true),DelsA),
        append([DelsF,DelsA,AddsF,AddsA],Mods),
        update_kb(KB1,Mods,KB2).

can_progress(strips(closed),_KB,_Action) :-
        fail.

% todo: We need to check whether the KB mentions all involved fluents
%       only in literals. It may be too expensive to do this every
%       time on-the-fly.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ADL (PDDL subset, i.e. CWA + domain closure)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

progress(adl,KB1,Action,KB2) :-
        ground(Action), !,
        findall(del(Fluent),(user:causes_false(Action,Fluent,Cond),
                        eval_cwa(KB1,Cond)),Dels),
        findall(add(Fluent),(user:causes_true(Action,Fluent,Cond),
                        eval_cwa(KB1,Cond)),Adds),
        append([Dels,Adds],Mods),
        update_kb(KB1,Mods,KB2).

can_progress(adl,_KB,Action) :-
        forall(user:causes_false(Action,Fluent,Cond),
               (cwa_fml(Cond), cwa(Fluent))),
        forall(user:causes_true(Action,Fluent,Cond),
               (cwa_fml(Cond), cwa(Fluent))).

% todo: Here we ignore the case that fluent values may become known
%       "just in time" (e.g. the shoot action in the Wumpus world),
%       which could be tested using ask(kwhether(...)) (but may be too
%       expensive to do before every action). Instead we simply
%       require that the CWA applies to all involved fluents.

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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Default Progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

can_progress(adl,_KB,_Action) :-
        report_message(warn,
                       ['Warning: No suitable progression ',
                        'style! Using ADL progression nonetheless...']).
