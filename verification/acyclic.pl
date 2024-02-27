/**
 
<module> acyclic

This module provides functionality for reasoning with so-called
acyclic action theories, to be used for verification, as described in
the paper

Benjamin Zarrieß and Jens Claßen:
Decidable Verification of Golog Programs over Non-Local Effect Actions.
In Proceedings of the 13th AAAI Conference on Artificial Intelligence (AAAI 2016),
pages 1109-1115, AAAI Press, 2016.

@author  Jens Claßen
@license GPLv2

 **/
:- module('acyclic', [preprocess_actions/1,
                      effect_description/5,
                      determine_effects/4,
                      apply_effects/3,
                      simplify_fml/2,
                      regression/3,
                      is_entailed/2,
                      is_inconsistent/1]).

:- use_module('../lib/utils').

:- use_module('../logic/cwa').
:- use_module('../logic/l', [entails_l/3, inconsistent_l/2, simplify_l/2,
                             conjoin/2, conjuncts/2, free_variables/2,
                             op(1130, xfy, <=>),
                             op(1110, xfy, <=),
                             op(1110, xfy, =>)]).

:- use_module('../logic/dl', [entails_dl/3, inconsistent_dl/2,
                              simplify/2 as simplify_dl]).

:- use_module('../logic/fobdd').

:- use_module('../projection/ligression').

:- use_module('../projection/progression').

:- use_module('characteristic_graphs_guards').

:- multifile user:base_logic/1.
:- multifile user:causes_true/3.
:- multifile user:causes_false/3.
:- multifile user:causes_true/4.
:- multifile user:causes_false/4.

:- discontiguous(is_entailed/3).
:- discontiguous(is_inconsistent/2).

:- dynamic
   is_entailed_cached/3,
   is_inconsistent_cached/2,
   effect_description/5.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Preprocess Actions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

preprocess_actions(Program) :-
        determine_eff_con(Program),
        check_acyclicity.                  

determine_eff_con(Program) :- % untyped fluent, positive effect
        cg_edge(Program,_NodeID,_Guard,Action,_NewNodeID),
        action_template(Action,ActionT,Vars),
        causes_true(ActionT,Fluent,Condition),
        user:rel_fluent(Fluent),
        eff_con(Condition,Vars,Eff,Con),
        not(effect_description(+,Fluent,ActionT,Eff,Con)),
        assert(effect_description(+,Fluent,ActionT,Eff,Con)),
        fail.
determine_eff_con(Program) :- % typed fluent, positive effect
        cg_edge(Program,_NodeID,_Guard,Action,_NewNodeID),
        action_template(Action,ActionT,Vars),
        causes_true(ActionT,Fluent,Condition),
        user:rel_fluent(Fluent,Types),
        types_cons(Types,TyCons),
        eff_con(Condition,Vars,Eff,Con),
        conjoin([Eff|TyCons],Eff2),
        not(effect_description(+,Fluent,ActionT,Eff2,Con)),
        assert(effect_description(+,Fluent,ActionT,Eff2,Con)),
        fail.
determine_eff_con(Program) :- % untyped fluent, negative effect
        cg_edge(Program,_NodeID,_Guard,Action,_NewNodeID),
        action_template(Action,ActionT,Vars),
        causes_false(ActionT,Fluent,Condition),
        eff_con(Condition,Vars,Eff,Con),
        not(effect_description(-,Fluent,ActionT,Eff,Con)),
        assert(effect_description(-,Fluent,ActionT,Eff,Con)),
        fail.
determine_eff_con(Program) :- % typed fluent, negative effect
        cg_edge(Program,_NodeID,_Guard,Action,_NewNodeID),
        action_template(Action,ActionT,Vars),
        causes_false(ActionT,Fluent,Condition),
        user:rel_fluent(Fluent,Types),
        types_cons(Types,TyCons),
        eff_con(Condition,Vars,Eff,Con),
        conjoin([Eff|TyCons],Eff2),
        not(effect_description(+,Fluent,ActionT,Eff2,Con)),
        assert(effect_description(+,Fluent,ActionT,Eff2,Con)),
        fail.
determine_eff_con(_Program).

action_template(Action,ActionT,Vars) :-
        Action =.. [A|Args],
        generate_fresh_variables(Args,Vars),
        ActionT =.. [A|Vars], !.

generate_fresh_variables([_|Args],[_X|Vars]) :- !,
        generate_fresh_variables(Args,Vars).
generate_fresh_variables([],[]) :- !.

eff_con(Condition,Vars,Eff,Con) :- !,
        conjuncts(Condition,Conjuncts),
        eff_con2(Conjuncts,Vars,EffC,ConC),
        conjoin(EffC,Eff),
        conjoin(ConC,Con).
eff_con2([Conj|Conjuncts],Vars,EffC,[Conj|ConC]) :-
        free_variables(Conj,CVars),
        subset2(CVars,Vars), !,
        eff_con2(Conjuncts,Vars,EffC,ConC).
eff_con2([Conj|Conjuncts],Vars,[Conj|EffC],ConC) :- !,
        eff_con2(Conjuncts,Vars,EffC,ConC).
eff_con2([],_Vars,[],[]) :- !.

check_acyclicity :-
        not(dg_cycle), !,
        report_message_r(['Action theory is acyclic. Proceeding...']).
check_acyclicity :-
        report_message_r(err,
                         ['Action theory is NOT acyclic! Aborting...']),
        fail.
dg_cycle :-
        dg_edge(F1,F2),
        dg_path(F2,F1).
dg_edge(F1,F2) :-
        effect_description(_S1,F1,_A1,Eff1,_C1),
        effect_description(_S2,F2,_A2,_Eff2,_C2),
        mentions_fluent(Eff1,[F2]), !.
dg_path(F1,F1).
dg_path(F1,F2) :-
        dg_edge(F1,F3),
        dg_path(F3,F2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Regression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

determine_effects(Formulas,Effects,Action,NewEffects) :-
        findall(Effect,is_effect(Formulas,Effects,Action,Effect),NewEffects).

is_effect(Formulas,Effects,Action,Effect) :-
        effect_description(Sign,Fluent,Action,Eff,Con),
        regression(Con,Effects,RCon),
        is_entailed(Formulas,RCon),
        Effect=(Sign,Fluent,Eff).

apply_effects(CurEffects,NewEffects,ResEffects) :- !,
        findall(Effect,is_res_effect(CurEffects,NewEffects,Effect),
                ResEffects2),
        variant_sort(ResEffects2,ResEffects).

is_res_effect(CurEffects,NewEffects,Effect) :-
        member((Sign,Fluent,Eff),NewEffects),
        regression(Eff,CurEffects,REff),
        simplify_fml(REff,REffS),
        REffS \= false,
        Effect = (Sign,Fluent,REffS).
is_res_effect(CurEffects,NewEffects,Effect) :-
        member((+,Fluent,Eff),CurEffects),
        neg_new_effects(Fluent,CurEffects,NewEffects,NegRPhiPs),
        conjoin([Eff|NegRPhiPs],REff),
        simplify_fml(REff,REffS),
        REffS \= false,
        Effect = (+,Fluent,REffS).
is_res_effect(CurEffects,_NewEffects,Effect) :-
        member((-,Fluent,Eff),CurEffects),
        Effect = (-,Fluent,Eff).

neg_new_effects(Fluent,CurEffects,NewEffects,NegRPhiPs) :-
        % need bagof to avoid copying Fluent with new variables
        bagof(NegRPhiP,
              (member((-,Fluent,PhiP),NewEffects),
               regression(PhiP,CurEffects,RPhiP),
               NegRPhiP=(-RPhiP)),
              NegRPhiPs), !.
% bagof fails if there are no solutions
neg_new_effects(_,_,_,[]) :- !.

% regression: use "ligression" and simplify
regression(F,E,R) :- !,
        ligress(F,E,R1),
        simplify_fml(R1,R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Formula Simplification
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simplify_fml(F,R) :-
        user:base_logic(L), !,
        simplify_fml(L,F,R).
simplify_fml(F,R) :- !,
        simplify_fml(l,F,R).
simplify_fml(l,F,R) :- !,
        % required to eliminate equivalent effect descriptors
        minimize(F,R). 
simplify_fml(dl,F,R) :- !,
        % TODO: need a corresponding minimize/2 for DLs for acyclic case
        simplify_dl(F,R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Reasoning: Use L or DL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_entailed(Formulas,Formula) :-
        user:base_logic(L), !,
        is_entailed(L,Formulas,Formula).
is_entailed(Formulas,Formula) :- !,
        is_entailed(l,Formulas,Formula). % default

is_inconsistent(Formulas) :-
        user:base_logic(L), !,
        is_inconsistent(L,Formulas).
is_inconsistent(Formulas) :- !,
        is_inconsistent(l,Formulas). % default

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% L reasoning with caching
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_entailed(l,Formulas,Formula) :-
        is_entailed_cached(Formulas,Formula,true), !.
is_entailed(l,Formulas,Formula) :-
        is_entailed_cached(Formulas,Formula,false), !, fail.
is_entailed(l,Formulas,Formula) :-
        entails_l(Formulas,Formula,Truth), !,
        assert(is_entailed_cached(Formulas,Formula,Truth)),
        Truth = true.

is_inconsistent(l,Formulas) :-
        is_inconsistent_cached(Formulas,true), !.
is_inconsistent(l,Formulas) :-
        is_inconsistent_cached(Formulas,false), !, fail.
is_inconsistent(l,Formulas) :-
        inconsistent_l(Formulas,Truth), !,
        assert(is_inconsistent_cached(Formulas,Truth)),
        Truth = true.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% DL reasoning with caching
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_entailed(dl,Formulas,Formula) :-
        is_entailed_cached(Formulas,Formula,true), !.
is_entailed(dl,Formulas,Formula) :-
        is_entailed_cached(Formulas,Formula,false), !, fail.
is_entailed(dl,Formulas,Formula) :-
        entails_dl(Formulas,Formula,Truth), !,
        assert(is_entailed_cached(Formulas,Formula,Truth)),
        Truth = true.

is_inconsistent(dl,Formulas) :-
        is_inconsistent_cached(Formulas,true), !.
is_inconsistent(dl,Formulas) :-
        is_inconsistent_cached(Formulas,false), !, fail.
is_inconsistent(dl,Formulas) :-
        inconsistent_dl(Formulas,Truth), !,
        assert(is_inconsistent_cached(Formulas,Truth)),
        Truth = true.
