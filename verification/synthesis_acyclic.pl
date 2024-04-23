/**
 
<module> synthesis_acyclic

This module implements a method for synthesizing a solution strategy
in the presence of "angelic" and "demonic" non-determinism, given a
Golog program and a temporal property.

Parts of the construction used here are described in the paper

Benjamin Zarrieß and Jens Claßen:
Decidable Verification of Golog Programs over Non-Local Effect Actions.
In Proceedings of the 13th AAAI Conference on Artificial Intelligence (AAAI 2016),
pages 1109-1115, AAAI Press, 2016.

@author  Jens Claßen
@license GPLv2

 **/
:- module('synthesis_acyclic', [synthesize/2]).

:- use_module('../lib/utils').
:- use_module('../lib/env').

:- use_module('../logic/cwa').
:- use_module('../logic/l', [conjoin/2,
                             op(1130, xfy, <=>),
                             op(1110, xfy, <=),
                             op(1110, xfy, =>)]).

:- use_module('../logic/fobdd').

:- use_module('../projection/ligression').

:- use_module('../projection/progression').

:- use_module('acyclic').
:- use_module('characteristic_graphs_guards').

:- dynamic   
   abstract_state/2,
   abstract_trans/3,
   strategy_node/2.

:- multifile user:exo/2.
:- multifile user:initially/1.
:- multifile user:property/2.

% TODO: include support for closed-world assumption?

/**
  * synthesize(+Program,+Property) is det.
  *
  * Synthesizes a strategy given a temporal property.
  *
  * @arg Program  the name of a program, defined by the user via a
  *               fact over the predicate program/2
  * @arg Property the name of a property, defined by the user via a
  *               fact over the predicate property/2
 **/
synthesize(Program,Property) :-
        init_construction(Program,Property),
        iterate_construction(Program,Property),
        build_strategy(Program,Property).

% iterate construction steps as long as possible
iterate_construction(Program,Property) :-
        construction_step(Program,Property), !,
        iterate_construction(Program,Property).
iterate_construction(_Program,_Property).

% initial setup
init_construction(Program,Property) :-
        
        % materialize the characteristic graph
        construct_characteristic_graph(Program),

        % preprocess actions
        preprocess_actions(Program),
        
        % determine the KB (initial theory)
        findall(F,user:initially(F),KB),
        
        % remove old instances of dynamic predicates
        retractall(abstract_state(_,_)),
        retractall(abstract_trans(_,_,_)),
        
        % determine atoms for temporal property
        prop2tnf(Property,TNF),
        tnf2xnf(TNF,XNF),
        
        create_initial_states(Program,Property,KB,XNF).

% create one initial state per satisfying assignment
create_initial_states(P,F,KB,XNF) :-
        xnf_ass(XNF,Ls,Xs,Tail),
        union2(KB,Ls,Fmls),
        not(is_inconsistent(Fmls)),
        
        State = (P,F,Fmls,[],Xs,Tail,0),
        
        report_message_r(['Creating initial state: \n']),
        report_state(State),

        create_state_if_not_exists(State,_),
        fail.
create_initial_states(_,_,_,_).

% construction step: remove non-tail node from fringe
construction_step(P,F) :-
        
        % if there is an abstract state at the fringe...
        abstract_state(State,true),
        State = (P,F,Formulas,Effects,Next,Tail,NodeID),
        
        % where none of the cases below applies...
        not(can_expand(State,_,_)),
        not(can_split_transition(P,F,Formulas,Effect,NodeID,_,_)),
        not(can_split_finality(P,F,Formulas,Effects,NodeID,_)),
        not(can_split_effectcond(P,F,Formulas,Effect,NodeID,_,_,_,_,_)),
        not(can_split_tempsubfml(P,F,Formulas,Effect,Next,NodeID,_,_,_)),
        
        % then
        !,
        
        % this state is not a fringe state anymore
        retract(abstract_state((P,F,Formulas,Effects,Next,Tail,NodeID),true)),
        assert(abstract_state((P,F,Formulas,Effects,Next,Tail,NodeID),false)).

% construction step: split over transition condition
construction_step(P,F) :-

        % if there is an abstract state...        
        abstract_state((P,F,Formulas,Effects,_Next,_Tail,NodeID),true),
        
        % where we can split over a transition condition...
        can_split_transition(P,F,Formulas,Effects,NodeID,Action,
                             RegressedCondition),
        
        % then
        !,
        
        report_message_r(['Doing split over transition condition: \n',
                        '\t action             : ', Action, '\n',
                        '\t regressed condition: ', RegressedCondition, '\n',
                        '\t type               : ', Formulas, '\n',
                        '\t effects            : ', Effects, '\n',
                        '\t node               : ', NodeID, '\n']),
        
        % split states and transitions over this condition
        split(P,F,Formulas,RegressedCondition).

% construction step: split over finality condition
construction_step(P,F) :-

        % TODO: perhaps this is only required in some states,
        % depending on Tail?
        
        % if there is an abstract state...        
        abstract_state((P,F,Formulas,Effects,_Next,_Tail,NodeID),true),
        
        % where we can split over a finality condition...
        can_split_finality(P,F,Formulas,Effects,NodeID,RegressedFinal),
        
        % then
        !,
        
        report_message_r(['Doing split over finality condition: \n',
                        '\t node               : ', NodeID, '\n',
                        '\t regressed condition: ', RegressedFinal, '\n',
                        '\t type               : ', Formulas, '\n',
                        '\t effects            : ', Effects, '\n']),
        
        % split states and transitions over this condition
        split(P,F,Formulas,RegressedFinal).

% construction step: split over effect condition
construction_step(P,F) :-
        
        % if there is an abstract state...
        abstract_state((P,F,Formulas,Effects,_Next,_Tail,NodeID),true),
        
        % where we can split over a transition's effect conditions...
        can_split_effectcond(P,F,Formulas,Effects,NodeID,
                             Action,Sign,Fluent,Eff,
                             RegressedEffCondition),
        
        % then
        !,
        
        report_message_r(['Doing split over effect condition: \n',
                        '\t action           : ', Action, '\n',
                        '\t sign             : ', Sign, '\n',
                        '\t fluent           : ', Fluent, '\n',
                        '\t effect descriptor: ', Eff, '\n',
                        '\t regressed context: ', RegressedEffCondition, '\n',
                        '\t type             : ', Formulas, '\n',
                        '\t effects          : ', Effects, '\n',
                        '\t node             : ', NodeID, '\n']),
        
        % split state and transitions over this condition
        split(P,F,Formulas,RegressedEffCondition).

% construction step: split over temporal subformula
construction_step(P,F) :-
        
        % if there is an abstract state...
        abstract_state((P,F,Formulas,Effects,Next,_Tail,NodeID),true),
        
        % where we can split over a temporal subformula...
        can_split_tempsubfml(P,F,Formulas,Effects,Next,NodeID,
                             Atom,RegressedAtom,ResEffects),
                             
        % then
        !,
        
        report_message_r(['Doing split over temporal subformula: \n',
                        '\t atom             : ', Atom, '\n',
                        '\t regressed atom   : ', RegressedAtom, '\n',
                        '\t type             : ', Formulas, '\n',
                        '\t new effects      : ', ResEffects, '\n',
                        '\t node             : ', NodeID, '\n']),
        
        % split state and transitions over this condition
        split(P,F,Formulas,RegressedAtom).

% construction step: create transition
construction_step(P,F) :-
        
        % if there is an abstract state...
        abstract_state(State,true),
        State = (P,F,_,_,_,_,_),
        
        % that can be expanded
        can_expand(State,Action,NewState),
        
        % then
        !,

        report_message_r(['Expanding action: ', Action, '\n',
                          '\t From:']),
        report_state(State),
        report_message_r(['\t To:']),
        report_state(NewState),

        % create resulting state (if not exists already)
        create_state_if_not_exists(NewState,_),
        
        % and resulting transition
        assert(abstract_trans(State,Action,NewState)).

report_state((_P,_F,Formulas,Effects,Next,Tail,NodeID)) :-

        report_message_r(['\t type       : ', Formulas, '\n',
                          '\t effects    : ', Effects, '\n',
                          '\t next       : ', Next, '\n',
                          '\t tail       : ', Tail, '\n',
                          '\t node       : ', NodeID, '\n']).

% is it possible to create a new transition?
can_expand(State,Action,NewState) :-

        % State is a state where...
        State = (P,F,Formulas,Effects,Next,Tail,NodeID),

        % tail does not hold,...
        Tail = false,

        % there is a possible outgoing transition...
        cg_edge(P,NodeID,Guard,Action,NewNodeID),
        guardcond(Guard,Condition),

        % whose regressed condition is entailed...
        regression(Condition,Effects,RegressedCondition),
        is_entailed(Formulas,RegressedCondition),

        % that has certain effects...
        determine_effects(Formulas,Effects,Action,NewEffects),
        apply_effects(Effects,NewEffects,ResEffects),

        % whose next formulas have an assignment...
        tnf2xnf(Next,XNF),
        xnf_ass(XNF,Ls,NewNext,NewTail),

        % whose regression is satisfied...
        conjoin(Ls,LsF),
        regression(LsF,ResEffects,RLsF),
        is_entailed(Formulas,RLsF),

        NewState = (P,F,Formulas,ResEffects,NewNext,NewTail,NewNodeID),

        % and where the corresponding transition(s) do not yet exist
        not(abstract_trans(State,Action,NewState)).

% is it possible to split over a transition condition?
can_split_transition(P,_F,Formulas,Effects,NodeID,Action,
                     RegressedCondition) :-

        % there is a possible outgoing transition...
        cg_edge(P,NodeID,Guard,Action,_NewNodeID),
        guardcond(Guard,Condition),
        
        % whose (negated) regressed condition is not yet entailed
        % by the type formulas
        regression(Condition,Effects,RegressedCondition),
        not(is_entailed(Formulas,RegressedCondition)),
        not(is_entailed(Formulas,-RegressedCondition)).

% is it possible to split over a finality condition?
can_split_finality(P,_F,Formulas,Effects,NodeID,RegressedFinal) :-

        % the node has a finality condition
        cg_node(P,_,Final,NodeID),

        % whose (negated) regressed version is not yet entailed
        % by the type formulas
        regression(Final,Effects,RegressedFinal),
        not(is_entailed(Formulas,RegressedFinal)),
        not(is_entailed(Formulas,-RegressedFinal)).

% is it possible to split over an effect condition?
can_split_effectcond(P,_F,Formulas,Effects,NodeID,Action,Sign,Fluent,
                     Eff,RegressedEffCondition) :-
        
        % there is a possible outgoing transition...
        cg_edge(P,NodeID,Guard,Action,_NewNodeID),
        guardcond(Guard,Condition),
        
        % whose regressed condition is entailed by the type formula...
        regression(Condition,Effects,RegressedCondition),
        is_entailed(Formulas,RegressedCondition),

        % whose action has an effect...
        effect_description(Sign,Fluent,Action,Eff,Con),
        
        % whose (negated) regressed condition is not yet entailed by
        % the type formulas
        regression(Con,Effects,RegressedEffCondition),
        not(is_entailed(Formulas,RegressedEffCondition)),
        not(is_entailed(Formulas,-RegressedEffCondition)).

% is it possible to split over an atom of a temporal subformula?
can_split_tempsubfml(P,_F,Formulas,Effects,Next,NodeID,Atom,RegressedAtom,
                     ResEffects) :-
                             
        % there is a possible outgoing transition...
        cg_edge(P,NodeID,Guard,Action,_NewNodeID),
        guardcond(Guard,Condition),
        
        % whose regressed condition is entailed by the type formula...
        regression(Condition,Effects,RegressedCondition),
        is_entailed(Formulas,RegressedCondition),

        % and that results in the new effect set 'ResEffects'
        determine_effects(Formulas,Effects,Action,NewEffects),
        apply_effects(Effects,NewEffects,ResEffects),
                        
        % and where there is a propositional assignment of the XNF
        % version of the temporal formulas
        tnf2xnf(Next,XNF),
        xnf_ass(XNF,Ls,_,_),
        
        % that contains an atom...
        member2(Atom,Ls),

        % whose (negated) regressed version is not yet entailed by the
        % type formulas
        regression(Atom,ResEffects,RegressedAtom),
        not(is_entailed(Formulas,RegressedAtom)),
        not(is_entailed(Formulas,-RegressedAtom)).

% split Formulas over RegressedCondition
split(P,F,Formulas,RegressedCondition) :-
        simplify_fml(-RegressedCondition,NegRegressedCondition),
        retract(abstract_state((P,F,Formulas,Effects,Next,Tail,NodeID),
                                Fringe)),
        assert(abstract_state((P,F,[RegressedCondition|Formulas],Effects,
                               Next,Tail,NodeID),Fringe)),
        assert(abstract_state((P,F,[NegRegressedCondition|Formulas],Effects,
                               Next,Tail,NodeID),Fringe)),
        fail.

split(P,F,Formulas,RegressedCondition) :-
        simplify_fml(-RegressedCondition,NegRegressedCondition),
        retract(abstract_trans((P,F,Formulas,Effects,Next,Tail,NodeID),
                               Action,
                               (P,F,Formulas,NewEffects,NewNext,
                                NewTail,NewNodeID))),
        assert(abstract_trans((P,F,[RegressedCondition|Formulas],
                               Effects,Next,Tail,NodeID),
                              Action,
                              (P,F,[RegressedCondition|Formulas],
                               NewEffects,NewNext,NewTail,NewNodeID))),
        assert(abstract_trans((P,F,[NegRegressedCondition|Formulas],
                               Effects,Next,Tail,NodeID),
                              Action,
                              (P,F,[NegRegressedCondition|Formulas],
                               NewEffects,NewNext,NewTail,NewNodeID))),
        fail.
        
split(P,F,Formulas,RegressedCondition) :-
        is_inconsistent([RegressedCondition|Formulas]),
        retractall(abstract_state((P,F,[RegressedCondition|Formulas],_,
                                   _,_,_),_)),
        retractall(abstract_trans((P,F,[RegressedCondition|Formulas],_,
                                   _,_,_),_,_)),
        fail.
        
split(P,F,Formulas,RegressedCondition) :-
        simplify_fml(-RegressedCondition,NegRegressedCondition),
        is_inconsistent([NegRegressedCondition|Formulas]),
        retractall(abstract_state((P,F,
                                   [NegRegressedCondition|Formulas],_,
                                   _,_,_),_)),
        retractall(abstract_trans((P,F,
                                   [NegRegressedCondition|Formulas],_,
                                   _,_,_),_,_)),
        fail.

split(_,_,_,_).

% create a new abstract state if it does not exist already
create_state_if_not_exists(State,Fringe) :-
        abstract_state(State,Fringe), !.
create_state_if_not_exists(State,true) :- !,
        assert(abstract_state(State,true)).
% is the abstract state final?
is_final(State) :-

        State = (P,_F,Formulas,Effects,_Next,_Tail,NodeID),
        
        % determine the finality condition Final for NodeID
        cg_node(P,_SubProg,Final,NodeID),
        
        % and check whether its regression holds.
        regression(Final,Effects,RegressedFinal),
        is_entailed(Formulas,RegressedFinal).

% is the abstract state accepting?
is_accepting(State) :-

        State = (_P,_F,_Formulas,_Effects,Next,Tail,_NodeID),

        % this is a tail state
        Tail = true,
        
        % next is empty
        Next = [].

% build strategy from existing transition system
build_strategy(P,F) :-
        label_leaves(P,F),
        label_inductively(P,F).

% label good leaves
label_leaves(P,F) :-
        State = (P,F,_,_,_,_,_),
        abstract_state(State,false),
        not(strategy_node(State,_)),
        is_final(State),
        is_accepting(State),
        assert(strategy_node(State,good)),
        fail.

% label bad leaves
label_leaves(P,F) :-
        State = (P,F,_,_,_,_,_),
        abstract_state(State,false),
        not(abstract_trans(State,_,_)),
        not(strategy_node(State,good)),
        assert(strategy_node(State,bad)),
        fail.

% finish labelling leaves
label_leaves(_,_).

% label bad state due to environment action
label_inductively(P,F) :-
        State = (P,F,_,_,_,_,_),
        abstract_state(State,false),
        strategy_node(NewState,bad),
        abstract_trans(State,Action,NewState),
        not(strategy_node(State,_)),
        env_action(Action,State),
        assert(strategy_node(State,bad)),
        fail.

% label bad state due to control actions
label_inductively(P,F) :-
        State = (P,F,_,_,_,_,_),
        abstract_state(State,false),
        not(strategy_node(State,_)),
        forall((abstract_trans(State,Action,NewState),
                ctl_action(Action,State)),
               strategy_node(NewState,bad)),
        assert(strategy_node(State,bad)),
        fail.

% label remaining states as good states
label_inductively(P,F) :-
        State = (P,F,_,_,_,_,_),
        abstract_state(State,false),
        not(strategy_node(State,_)),
        assert(strategy_node(State,good)),
        fail.

% finish induction
label_inductively(_,_).

% control action = non-environment action
ctl_action(A,State) :-
        not(env_action(A,State)).

% environment action = exogenous actions defined in BAT
env_action(A,State) :-
        user:exo(A,F),
        State = (_,_,T,E,_,_,_),
        regression(F,E,R),
        is_entailed(T,R).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Process temporal properties
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Convert a (named) property into tail normal form (TNF),
% pushing negations inside (but treating quantified formulas as atoms).
% Also replaces always, eventually, wnext, =>, <=, <=> by their
% definitions.
prop2tnf(Name,T) :-
        user:property(Name,Prop), !,
        prop2tnf(Prop*eventually(tail),T).
prop2tnf(always(P),T) :- !,
        prop2tnf(release(false,P),T).
prop2tnf(eventually(P),T) :- !,
        prop2tnf(until(true,P),T).
prop2tnf(until(P1,P2),T) :- !,
        prop2tnf(P1,T1),
        prop2tnf(P2,T2),
        simplify_fml((-tail)*T1,T3),
        simplify_fml(T2,T4),
        T = until(T3,T4).
prop2tnf(release(P1,P2),T) :- !,
        prop2tnf(P1,T1),
        prop2tnf(P2,T2),
        simplify_fml(tail+T1,T3),
        simplify_fml(T2,T4),
        T = release(T3,T4).
prop2tnf(next(P),T) :- !,
        prop2tnf(P,T1),
        simplify_fml(T1,T2),
        T = (-tail)*next(T2).
prop2tnf(wnext(P),T) :- !,
        prop2tnf(P,T1),
        simplify_fml(T1,T2),
        T = tail+next(T2).
prop2tnf(F1*F2,T1*T2) :- !,
        prop2tnf(F1,T1),
        prop2tnf(F2,T2).
prop2tnf(F1+F2,T1+T2) :- !,
        prop2tnf(F1,T1),
        prop2tnf(F2,T2).
prop2tnf(F1=>F2,T) :- !,
        prop2tnf(-F1+F2,T).
prop2tnf(F1<=F2,T) :- !,
        prop2tnf(F1+(-F2),T).
prop2tnf(F1<=>F2,T) :- !,
        prop2tnf(F1*F2+(-F1)*(-F2),T).

prop2tnf(-always(P),T) :- !,
        prop2tnf(until(true,-P),T).
prop2tnf(-eventually(P),T) :- !,
        prop2tnf(release(false,-P),T).
prop2tnf(-until(P1,P2),T) :- !,
        prop2tnf(release(-P1,-P2),T).
prop2tnf(-release(P1,P2),T) :- !,
        prop2tnf(until(-P1,-P2),T).
prop2tnf(-next(P),T) :- !,
        prop2tnf(wnext(-P),T).
prop2tnf(-wnext(P),T) :- !,
        prop2tnf(next(-P),T).

prop2tnf(-(-F),T) :- !,
        prop2tnf(F,T).
prop2tnf(-(F1*F2),T) :- !,
        prop2tnf((-F1)+(-F2),T).
prop2tnf(-(F1+F2),T) :- !,
        prop2tnf((-F1)*(-F2),T).
prop2tnf(-(F1=>F2),T) :- !,
        prop2tnf(F1*(-F2),T).
prop2tnf(-(F1<=F2),T) :- !,
        prop2tnf((-F1)*F2,T).
prop2tnf(-(F1<=>F2),T) :- !,
        prop2tnf((F1*(-F2))+((-F1)*F2),T).
prop2tnf(-all(X,F),some(X,NF)) :- !, % treat quantified formulas as atoms
        simplify_fml(-F,NF).
prop2tnf(-some(X,F),all(X,NF)) :- !, % treat quantified formulas as atoms
        simplify_fml(-F,NF).
prop2tnf(F,F2) :- !,
        simplify_fml(F,F2).

% Given a formula in TNF, convert it into "next normal form" (XNF).
tnf2xnf(L,R) :-
        is_list(L), !,
        conjoin(L,F),
        tnf2xnf(F,R).
tnf2xnf(until(P1,P2),R) :- !,
        tnf2xnf(P2+(P1*next(until(P1,P2))),R).
tnf2xnf(release(P1,P2),R) :- !,
        tnf2xnf(P2*(P1+next(release(P1,P2))),R).
tnf2xnf(next(P),next(P)) :- !.
tnf2xnf(F1*F2,R1*R2) :- !,
        tnf2xnf(F1,R1),
        tnf2xnf(F2,R2).
tnf2xnf(F1+F2,R1+R2) :- !,
        tnf2xnf(F1,R1),
        tnf2xnf(F2,R2).
tnf2xnf(F,F) :- !.

% propositional assignments satisfying a formula in XNF, split up into
% "literals" Ls, "next formulas" Xs, and the truth value Tail for the
% special 'tail' atom.
xnf_ass(F,Ls,Xs,Tail) :-
        not(is_list(F)), !,
        xnf_ass([F],Ls,Xs,Tail).
xnf_ass([F1*F2|Fs],Ls,Xs,Tail) :-
        xnf_ass([F1,F2|Fs],Ls,Xs,Tail).
xnf_ass([F1+F2|Fs],Ls,Xs,Tail) :-
        xnf_ass([F1|Fs],Ls,Xs,Tail);
        xnf_ass([F2|Fs],Ls,Xs,Tail).
xnf_ass([-(F1*F2)|Fs],Ls,Xs,Tail) :-
        xnf_ass([(-F1)+(-F2)|Fs],Ls,Xs,Tail).
xnf_ass([-(F1+F2)|Fs],Ls,Xs,Tail) :-
        xnf_ass([(-F1)*(-F2)|Fs],Ls,Xs,Tail).
xnf_ass([-(-F)|Fs],Ls,Xs,Tail) :-
        xnf_ass([F|Fs],Ls,Xs,Tail).
xnf_ass([next(P)|Fs],Ls,NXs,Tail) :-
        xnf_ass(Fs,Ls,Xs,Tail),
        (member2(P,Xs) -> NXs = Xs; NXs = [P|Xs]).
xnf_ass([-next(_)|Fs],Ls,Xs,Tail) :- % TODO: is it correct to ignore negated nexts?
        xnf_ass(Fs,Ls,Xs,Tail).
xnf_ass([tail|Fs],Ls,Xs,true) :-
        xnf_ass(Fs,Ls,Xs,true).
xnf_ass([-tail|Fs],Ls,Xs,false) :-
        xnf_ass(Fs,Ls,Xs,false).
xnf_ass([F|Fs],NLs,Xs,Tail) :-
        F \= _*_, F \= _+_, F \= -_, F \= next(_), F \= tail,
        xnf_ass(Fs,Ls,Xs,Tail),
        not(member2(-F,Ls)),
        (member2(F,Ls) -> NLs = Ls; NLs = [F|Ls]).
xnf_ass([-F|Fs],NLs,Xs,Tail) :-
        F \= _*_, F \= _+_, F \= -_, F \= next(_), F \= tail,
        xnf_ass(Fs,Ls,Xs,Tail),
        not(member2(F,Ls)),
        (member2(-F,Ls) -> NLs = Ls; NLs = [-F|Ls]).
xnf_ass([],[],[],true).
xnf_ass([],[],[],false).
