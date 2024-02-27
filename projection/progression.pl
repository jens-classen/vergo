%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(progression, [progress/3,
                        progress/4,
                        can_progress/3,
                        mentions_fluent/2]).

:- use_module('ligression').
:- use_module('regression').
:- use_module('../kbs/l_kb').
:- use_module('../lib/utils').
:- use_module('../logic/cwa').
:- use_module('../logic/def').
:- use_module('../logic/fobdd').
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
        report_message(debug,
                       ['Applying ',Style,' progression to action ',
                        Action,'.']),
        progress(Style,KB1,Action,KB2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Empty progression for actions with no effects (e.g. sensing)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

progress(empty,KB1,Action,KB2) :-
        ground(Action), !,
        copy_kb(KB1,KB2).

can_progress(empty,_KB,Action) :-
        not(causes_true(Action,_,_)),
        not(causes_false(Action,_,_)),
        not(causes(Action,_,_,_)).

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

can_progress(strips(open),_KB,_Action) :-
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
%       "just in time" (e.g. the pick action in the Wumpus world),
%       which could be tested using ask(kwhether(...)) (but may be too
%       expensive to do before every action). Instead we simply
%       require that the CWA applies to all involved fluents.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Progression for local-effect theories
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Local-effect progression (for arbitrary KBs) as described in:
%
% Yongmei Liu and Gerhard Lakemeyer: "On First-Order Definability and
% Computability of Progression for Local-Effect Actions and
% Beyond". In: Proc. IJCAI 2009, AAAI Press, pp. 860–866.

progress(local_effect,KB1,Action,KB2) :-
        ground(Action), !,
        characteristic_set(Action,Omega),
        affected_kb_axioms(KB1,Omega,Axioms),
        findall(Disjunct,
                (is_model(Theta,Omega),
                 consistent_with_kb(KB1,Theta),
                 apply_model_axioms(Theta,KB1,Axioms,InstAxioms),
                 apply_model_ssa(Theta,KB1,Action,InstSSA),
                 append([InstAxioms,InstSSA],DisjunctFmls),
                 conjoin(DisjunctFmls,DisjunctC),
                 minimize(DisjunctC,Disjunct),
                 consistent_l(Disjunct,true)),
                Disjuncts),
        disjoin(Disjuncts,Fml1),
        minimize(Fml1,Fml2),
        conjuncts(Fml2,Fmls),
        findall(del(Axiom),member(Axiom,Axioms),DelAxioms),
        findall(add(Axiom),member(Axiom,Fmls),AddAxioms),
        append([DelAxioms,AddAxioms],AddDelAxioms),
        update_kb(KB1,AddDelAxioms,KB2).

% char. set: ground fluent atoms the action (might) have an effect on
characteristic_set(Action,CharSet) :-
        findall(Fluent,
                (causes_true(Action,Fluent,_);
                 causes_false(Action,Fluent,_)),
                CharSet1),
        sort(CharSet1,CharSet). % remove duplicates

% affected KB axioms: only those that mention some affected fluent
affected_kb_axioms(KB,Atoms,Axioms) :-
        kb_as_list(KB,Fmls),
        affected_kb_axioms2(Fmls,Atoms,Axioms).
affected_kb_axioms2([],_Atoms,[]) :- !.
affected_kb_axioms2([Fml|Fmls],Atoms,[Fml|Axioms]) :-
        mentions_fluent(Fml,Atoms), !,
        affected_kb_axioms2(Fmls,Atoms,Axioms).
affected_kb_axioms2([_Fml|Fmls],Atoms,Axioms) :- !,
        affected_kb_axioms2(Fmls,Atoms,Axioms).

% check whether given formula mentions any fluent from given atoms
mentions_fluent(F,Atoms) :-
        (rel_fluent(F);rel_fluent(F,_)), !,
        member(A,Atoms),
        F =.. [P|FArgs],
        A =.. [P|AArgs],
        length(FArgs,N),
        length(AArgs,N).
mentions_fluent(true,_) :- !, fail.
mentions_fluent(false,_) :- !, fail.
mentions_fluent((_=_),_) :- !, fail.
mentions_fluent(F1*F2,Atoms) :- !,
        (mentions_fluent(F1,Atoms);
         mentions_fluent(F2,Atoms)).
mentions_fluent(F1+F2,Atoms) :- !,
        (mentions_fluent(F1,Atoms);
         mentions_fluent(F2,Atoms)).
mentions_fluent(-F,Atoms) :- !,
        mentions_fluent(F,Atoms).
mentions_fluent(F1<=>F2,Atoms) :- !,
        (mentions_fluent(F1,Atoms);
         mentions_fluent(F2,Atoms)).
mentions_fluent(F1=>F2,Atoms) :- !,
        (mentions_fluent(F1,Atoms);
         mentions_fluent(F2,Atoms)).
mentions_fluent(F1<=F2,Atoms) :- !,
        (mentions_fluent(F1,Atoms);
         mentions_fluent(F2,Atoms)).
mentions_fluent(some(_Vars,F),Atoms) :- !,
        mentions_fluent(F,Atoms).
mentions_fluent(all(_Vars,F),Atoms) :- !,
        mentions_fluent(F,Atoms).
mentions_fluent(some_t(_Vars,F),Atoms) :- !,
        mentions_fluent(F,Atoms).
mentions_fluent(all_t(_Vars,F),Atoms) :- !,
        mentions_fluent(F,Atoms).
mentions_fluent(F,Atoms) :-
        user:def(F,D), !,
        mentions_fluent(D,Atoms).
mentions_fluent(_,_) :- !, fail.

% model: consistent set of literals over some set of atoms
is_model(Lits,Atoms) :-
        is_model2(Lits,Atoms),
        consistent_l(Lits,true).
is_model2([],[]).
is_model2([Atom|Lits],[Atom|Atoms]) :-
        is_model2(Lits,Atoms).
is_model2([-Atom|Lits],[Atom|Atoms]) :-
        is_model2(Lits,Atoms).

% consistent with KB: negation not entailed
consistent_with_kb(KB,Fmls) :-
        conjoin(Fmls,Fml),
        entails_kb(KB,-Fml,false).

% apply ligression to all formulas and minimize
apply_model_axioms(Theta,KB,Axioms,Fmls) :-
        findall(Fml,
                (member(Axiom,Axioms),
                 ligress(Axiom,Theta,Fml1),
                 apply_cwa(KB,Fml1,Fml2),
                 minimize(Fml2,Fml)),
                Fmls).

% create instantiated SSAs, apply ligression and minimize
apply_model_ssa(Theta,KB,Action,Fmls) :-
        findall(Fml,
                ((rel_fluent(Fluent);rel_fluent(Fluent,_)),
                 mentions_fluent(Fluent,Theta),
                 regression:ssa(Fluent,Action,Condition),
                 free_variables(Fluent,Vars),
                 ligress(Condition,Theta,LCondition),
                 apply_cwa(KB,LCondition,LCCondition),
                 minimize(all(Vars,(Fluent <=> LCCondition)),Fml),
                 valid_l(Fml,false)),
                Fmls).

% all actions must be local-effect
can_progress(local_effect,_KB,Action) :-
        % no effect on functional fluents
        not(causes(Action,_,_,_)),
        % action arguments contain all fluent arguments
        forall((causes_true(Action,Fluent,_);
                causes_false(Action,Fluent,_)),
               (Action =.. [_Op|ArgsA],
                Fluent =.. [_Pr|ArgsF],
                subset2(ArgsF,ArgsA))).

% todo: using minimize/2 instead of simplify/2 makes this slower, yet
%       keeps formulas at a more manageable size (e.g. Wumpus world).
%       Maybe make it optional?

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Default Progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

can_progress(adl,_KB,_Action) :-
        report_message(warn,
                       ['Warning: No suitable progression ',
                        'style! Using ADL progression nonetheless...']).
