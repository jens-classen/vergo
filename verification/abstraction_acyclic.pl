/**
 
<module> abstraction_acyclic

This module implements a verification algorithm for Golog programs
based on the construction described in the paper

Benjamin Zarrieß and Jens Claßen:
Decidable Verification of Golog Programs over Non-Local Effect Actions.
In Proceedings of the 13th AAAI Conference on Artificial Intelligence (AAAI 2016),
pages 1109-1115, AAAI Press, 2016.

It also subsumes the methods presented in

Benjamin Zarrieß and Jens Claßen:
Verification of Knowledge-Based Programs over Description Logic Actions.
In Proceedings of the Twenty-Fourth International Joint Conference on Artificial Intelligence (IJCAI 2015),
AAAI Press, 2015.

Benjamin Zarrieß and Jens Claßen:
Decidable Verification of Knowledge-Based Programs over Description Logic Actions with Sensing.
In Proceedings of the Twenty-Eighth International Workshop on Description Logics (DL 2015),
CEUR-WS.org, 2015.

Benjamin Zarrieß and Jens Claßen:
Verifying CTL* Properties of Golog Programs over Local-Effect Actions.
In Proceedings of the Twenty-First European Conference on Artificial Intelligence (ECAI 2014),
IOS Press, 2014.

Benjamin Zarrieß and Jens Claßen:
On the Decidability of Verifying LTL Properties of Golog Programs. 
Technical Report 13-10, Chair of Automata Theory, TU Dresden, Dresden, Germany, 2013.

By default, an internal implementation of the standard CTL model
checking algorithm is applied to the propositionalized, abstract
transition system. It is possible to use an external model checking
tool in the form of NuSMV instead. For this purpose, have the 'nusmv'
executable visible in PATH, and set the model checker via
set_modelchecker/1. However, note that there is no significant
performance advantage to be expected due to the fact that the states
and transitions of the abstract transition system need to be
enumerated explicitly, so a fast symbolic model checker cannot really
play to its strengths here.

@author  Jens Claßen
@license GPLv2

 **/
:- module('abstraction_acyclic', [compute_abstraction/1,
                                  verify/3,
                                  get_modelchecker/1,
                                  set_modelchecker/1]).

:- use_module('../lib/utils').
:- use_module('../lib/env').

:- use_module('../logic/cwa').
:- use_module('../logic/l', [op(1130, xfy, <=>),
                             op(1110, xfy, <=),
                             op(1110, xfy, =>)]).

:- use_module('../logic/fobdd').

:- use_module('../projection/ligression').

:- use_module('../projection/progression').

:- use_module('acyclic').
:- use_module('characteristic_graphs_guards').

:- dynamic
   map_property/4,
   map_subformula/3,
   map_action/3,
   map_state/5,
   map_trans/4,
   map_number_of_properties/2,
   map_number_of_subformulas/2,
   map_number_of_actions/2,
   map_number_of_states/2,
   map_holds_subformula/3,
   abstract_state/5,
   abstract_trans/7,
   property_subformula/2,
   modelchecker/1.

% use_sink_states.

% TODO: include support for closed-world assumption

/**
  * compute_abstraction(+ProgramName) is det.
  *
  * Computes the abstract transition system for the program of the
  * given name. Nodes and transitions will be generated in the form of
  * newly created facts for the dynamic predicates abstract_state/5
  * and abstract_trans/7.
  *
  * @arg ProgramName the name of a program, defined by the user via a
  *                  fact over the predicate program/2
 **/
compute_abstraction(ProgramName) :-
        modelchecker(nusmv),
        construct_abstract_transition_system(ProgramName),
        construct_propositional_mapping(ProgramName),
        translate_to_smv(ProgramName), !.

compute_abstraction(ProgramName) :-
        modelchecker(internal),
        construct_abstract_transition_system(ProgramName),
        construct_propositional_mapping(ProgramName), !.

/**
  * verify(+ProgramName,+PropertyName,-TruthValue) is det.
  *
  * Verifies the property of the given name on the previously created
  * abstract transition system by means of translating the
  * corresponding propositional mapping to the model checker NuSMV.
  * Verification results (truth value and counterexample) will be
  * printed to standard output.
  *
  * @arg ProgramName  the name of a program, defined by the user via a
  *                   fact over the predicate program/2
  * @arg PropertyName the name of a property, defined by the user via a
  *                   fact over the predicate property/3
  * @arg TruthValue   'true' if the property is satisfied,
  *                   'false' if not
 **/
verify(ProgramName,PropertyName,TruthValue) :-
        modelchecker(nusmv),
        map_property(ProgramName,N,PropertyName,_),
        property(PropertyName,ProgramName,Property),
        call_smv(ProgramName, N, TruthValue, Type, Actions),
        report_message_r(['Verified: \n',
                          '\t Property            : ', Property, '\n',
                          '\t Truth Value         : ', TruthValue, '\n',
                          '\t Counterexample Type : ', Type, '\n',
                          '\t Counterexample Trace: ', Actions, '\n']).

verify(ProgramName,PropertyName,TruthValue) :-
        modelchecker(internal),
        property(PropertyName,ProgramName,Property),
        check_ctl(ProgramName,PropertyName,StateSet),
        stateset_initial(ProgramName,Initial),
        (subset(Initial,StateSet) ->
            TruthValue = true; TruthValue = false),
        report_message_r(['Verified: \n',
                          '\t Property            : ', Property, '\n',
                          '\t Truth Value         : ', TruthValue, '\n']).

construct_abstract_transition_system(P) :-
        init_construction(P),
        iterate_construction(P).

iterate_construction(P) :-
        construction_step(P), !,
        iterate_construction(P).
iterate_construction(_P).

init_construction(ProgramName) :-
        
        % materialize the characteristic graph
        construct_characteristic_graph(ProgramName),

        % preprocess actions
        preprocess_actions(ProgramName),
        
        % determine relevant formulas from property
        determine_property_subformulas(ProgramName),
        
        % determine the KB (initial theory)
        findall(F,user:initially(F),KB),
        
        % remove old instances of dynamic predicates
        retractall(abstract_state(_,_,_,_,_)),
        retractall(abstract_trans(_,_,_,_,_,_,_)),
        
        % initialize with first abstract state
        create_state_if_not_exists(ProgramName,KB,[],0).
        
% construction step: expand transition(s)
construction_step(P) :-
        
        % if there is an abstract state at the fringe...
        abstract_state(P,Formulas,Effects,NodeID,true),
        
        % where none of the three cases below applies...
        not(can_expand(P,Formulas,Effects,NodeID,_,_,_)),
        not(can_split_transition(P,Formulas,Effects,NodeID,_,_)),
        not(can_split_property(P,Formulas,Effects,_)),

        % then
        !,
        
        % this state is not a fringe state anymore
        retract(abstract_state(P,Formulas,Effects,NodeID,true)),
        assert(abstract_state(P,Formulas,Effects,NodeID,false)).
        
% construction step: expand transition(s)
construction_step(P) :-
        
        % if there is an abstract state...
        abstract_state(P,Formulas,Effects,NodeID,true),
        
        % where it is possible to expand an action...
        can_expand(P,Formulas,Effects,NodeID,Action,RegressedCondition,
                   NewNodeID),
        
        % then
        !,
        
        % create the corresponding transition(s)
        create_transitions(P,Formulas,Effects,NodeID,Action,
                           RegressedCondition,NewNodeID).

% construction step: split types by some transition condition
construction_step(P) :-
        
        % if there is an abstract state...
        abstract_state(P,Formulas,Effects,NodeID,true),
        
        % where we can split over a transition condition...
        can_split_transition(P,Formulas,Effects,NodeID,Action,
                             RegressedCondition),
        
        % then
        !,
        
        report_message_r(['Doing split over transition condition: \n',
                        '\t action   : ', Action, '\n',
                        '\t condition: ', RegressedCondition, '\n',
                        '\t type     : ', Formulas, '\n',
                        '\t effects  : ', Effects, '\n',
                        '\t node     : ', NodeID, '\n']),
        
        % split states and transitions over this condition
        split(P,Formulas,RegressedCondition).

% construction step: split types by some property subformula
construction_step(P) :-
        
        % if there is an abstract state...
        abstract_state(P,Formulas,Effects,NodeID,true),
        
        % where we can split over a property subformula...
        can_split_property(P,Formulas,Effects,RegressedFormula),
        
        % then
        !,
        
        report_message_r(['Doing split over property subformula: \n',
                        '\t property : ', RegressedFormula, '\n',
                        '\t type     : ', Formulas, '\n',
                        '\t effects  : ', Effects, '\n',
                        '\t node     : ', NodeID, '\n']),
        
        % split states and transitions over this formula
        split(P,Formulas,RegressedFormula).

% is it possible to expand a transition?
can_expand(P,Formulas,Effects,NodeID,Action,RegressedCondition,
           NewNodeID) :- 
        
        % there is a possible outgoing transition...
        cg_edge(P,NodeID,Guard,Action,NewNodeID),
        guardcond(Guard,Condition),

        % whose regressed condition is entailed...
        regression(Condition,Effects,RegressedCondition),
        is_entailed(Formulas,RegressedCondition),
        
        % and where the corresponding transition(s) do not yet exist
        not(abstract_trans(P,Formulas,Effects,NodeID,Action,
                           _NewEffects,NewNodeID)).
        
% is it possible to split over a transition condition?
can_split_transition(P,Formulas,Effects,NodeID,Action,
                     RegressedCondition) :-

        % there is a possible outgoing transition...
        cg_edge(P,NodeID,Guard,Action,_NewNodeID),
        guardcond(Guard,Condition),
        
        % whose (negated) regressed condition is not yet entailed
        % by the type formulas
        regression(Condition,Effects,RegressedCondition),
        not(is_entailed(Formulas,RegressedCondition)),
        not(is_entailed(Formulas,-RegressedCondition)).
        
% is it possible to split over a property subformula?
can_split_property(P,Formulas,Effects,RegressedFormula) :-
        
        % there is a property subformula
        property_subformula(P,Formula),
        
        % whose (negated) regressed condition is not yet entailed
        % by the type formulas
        regression(Formula,Effects,RegressedFormula),
        not(is_entailed(Formulas,RegressedFormula)),
        not(is_entailed(Formulas,-RegressedFormula)).
        
% split Formulas over RegressedCondition
split(P,Formulas,RegressedCondition) :-
        simplify_fml(-RegressedCondition,NegRegressedCondition),
        retract(abstract_state(P,Formulas,Effects,NodeID,Fringe)),
        assert(abstract_state(P,[RegressedCondition|Formulas],Effects,
                              NodeID,Fringe)),
        assert(abstract_state(P,[NegRegressedCondition|Formulas],Effects,
                              NodeID,Fringe)),
        fail.

split(P,Formulas,RegressedCondition) :-
        simplify_fml(-RegressedCondition,NegRegressedCondition),
        retract(abstract_trans(P,Formulas,Effects,NodeID,Action,
                               NewEffects,NewNodeID)),
        assert(abstract_trans(P,[RegressedCondition|Formulas],Effects,
                              NodeID,Action,NewEffects,NewNodeID)),
        assert(abstract_trans(P,[NegRegressedCondition|Formulas],Effects,
                              NodeID,Action,NewEffects,NewNodeID)),
        fail.
        
split(P,Formulas,RegressedCondition) :-
        is_inconsistent([RegressedCondition|Formulas]),
        retractall(abstract_state(P,[RegressedCondition|Formulas],_,_,_)),
        retractall(abstract_trans(P,[RegressedCondition|Formulas],_,_,_,_)), 
        fail.
        
split(P,Formulas,RegressedCondition) :-
        simplify_fml(-RegressedCondition,NegRegressedCondition),
        is_inconsistent([NegRegressedCondition|Formulas]),
        retractall(abstract_state(P,[NegRegressedCondition|Formulas],_,_,_)),
        retractall(abstract_trans(P,[NegRegressedCondition|Formulas],_,_,_,_)), 
        fail.

split(_,_,_).


% split over effect conditions
create_transitions(P,Formulas,Effects,NodeID,Action,Cond,NewNodeID) :-
        
        effect_description(Sign,Fluent,Action,Eff,Con),
        regression(Con,Effects,RegressedCondition),
        
        not(is_entailed(Formulas,RegressedCondition)),
        not(is_entailed(Formulas,-RegressedCondition)),
        
        !,
        
        report_message_r(['Doing split over effect condition: \n',
                        '\t action           : ', Action, '\n',
                        '\t sign             : ', Sign, '\n',
                        '\t fluent           : ', Fluent, '\n',
                        '\t effect descriptor: ', Eff, '\n',
                        '\t regressed context: ', RegressedCondition, '\n',
                        '\t type             : ', Formulas, '\n',
                        '\t effects          : ', Effects, '\n',
                        '\t node             : ', NodeID, '\n']),
        
        split(P,Formulas,RegressedCondition),
        simplify_fml(-RegressedCondition,NegRegressedCondition),
        
        create_transitions(P,[RegressedCondition|Formulas],Effects,
                           NodeID,Action,Cond,NewNodeID),
        create_transitions(P,[NegRegressedCondition|Formulas],Effects,
                           NodeID,Action,Cond,NewNodeID).

% actually create transition
create_transitions(P,Formulas,Effects,NodeID,Action,Cond,NewNodeID) :-
        
        determine_effects(Formulas,Effects,Action,NewEffects),
        apply_effects(Effects,NewEffects,ResEffects),
        
        !,

        report_message_r(['Expanding action: \n',
                        '\t action     : ', Action, '\n',
                        '\t condition  : ', Cond, '\n',
                        '\t type       : ', Formulas, '\n',
                        '\t effects    : ', Effects, '\n',
                        '\t new effects: ', NewEffects, '\n',
                        '\t res effects: ', ResEffects, '\n',
                        '\t node       : ', NodeID, '\n',
                        '\t new node   : ', NewNodeID, '\n']),

        assert(abstract_trans(P,Formulas,Effects,NodeID,Action,
                              ResEffects,NewNodeID)),
        create_state_if_not_exists(P,Formulas,ResEffects,NewNodeID).

% create a new abstract state if it does not exist already
create_state_if_not_exists(P,Formulas,Effects,NodeID) :-
        abstract_state(P,Formulas,Effects,NodeID,_Fringe), !.
create_state_if_not_exists(P,Formulas,Effects,NodeID) :- !,
        assert(abstract_state(P,Formulas,Effects,NodeID,true)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Model Checker
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% default: internal model checker
modelchecker(internal).
% modelchecker(nusmv).

set_modelchecker(X) :-
        member(X,[internal,nusmv]), !,
        retract(modelchecker(_)),
        assert(modelchecker(X)).

get_modelchecker(X) :-
        modelchecker(X).

% TODO: counterexamples

/**
  * check_ctl(+Program,+Property,-StateSet)
  *
  * Performs the classical CTL model checking on Program (whose
  * transition system and propositional mapping must have been
  * constructed) and Property. Result is a list of IDs of satisfying
  * abstract states.
  **/
check_ctl(Program,PropertyName,StateSet) :-
        map_property(Program,_,PropertyName,Property), !,
        check_ctl(Program,Property,StateSet).

check_ctl(Program,Fml,StateSet) :-
        map_subformula(Program,Fml,_), !,
        findall(State,map_holds_subformula(Program,State,Fml),StateSet).

check_ctl(_Program,false,[]) :- !.
check_ctl(Program,true,StateSet) :- !,
        findall(State,map_state(Program,State,_,_,_),StateSet).

check_ctl(Program,-Fml,StateSet) :- !,
        check_ctl(Program,Fml,StateSet1),
        findall(State,(map_state(Program,State,_,_,_),
                       not(member(State,StateSet1))),StateSet).

check_ctl(Program,Fml1*Fml2,StateSet) :- !,
        check_ctl(Program,Fml1,StateSet1),
        check_ctl(Program,Fml2,StateSet2),
        intersection(StateSet1,StateSet2,StateSet).

check_ctl(Program,Fml1+Fml2,StateSet) :- !,
        check_ctl(Program,Fml1,StateSet1),
        check_ctl(Program,Fml2,StateSet2),
        union(StateSet1,StateSet2,StateSet).

check_ctl(Program,Fml1=>Fml2,StateSet) :- !,
        check_ctl(Program,(-Fml1)+Fml2,StateSet).

check_ctl(Program,Fml2<=Fml1,StateSet) :- !,
        check_ctl(Program,(-Fml1)+Fml2,StateSet).

check_ctl(Program,Fml1<=>Fml2,StateSet) :- !,
        check_ctl(Program,(Fml1=>Fml2)*(Fml2=>Fml1),StateSet).

check_ctl(Program,somepath(next(Fml)),StateSet) :- !,
        check_ctl(Program,Fml,StateSet1),
        check_ex(Program,StateSet1,StateSet).

check_ctl(Program,somepath(always(Fml)),StateSet) :- !,
        check_ctl(Program,Fml,StateSet1),
        check_eg(Program,StateSet1,StateSet).

check_ctl(Program,somepath(until(Fml1,Fml2)),StateSet) :- !,
        check_ctl(Program,Fml1,StateSet1),
        check_ctl(Program,Fml2,StateSet2),
        check_eu(Program,StateSet1,StateSet2,StateSet).

check_ctl(Program,somepath(eventually(Fml)),StateSet) :- !,
        check_ctl(Program,somepath(until(true,Fml)),StateSet).

check_ctl(Program,allpaths(next(Fml)),StateSet) :- !,
        check_ctl(Program,-somepath(next(-Fml)),StateSet).

check_ctl(Program,allpaths(always(Fml)),StateSet) :- !,
        check_ctl(Program,-somepath(until(true,-Fml)),StateSet).

check_ctl(Program,allpaths(eventually(Fml)),StateSet) :- !,
        check_ctl(Program,allpaths(until(true,Fml)),StateSet).

check_ctl(Program,allpaths(until(Fml1,Fml2)),StateSet) :- !,
        check_ctl(Program,
                  -somepath(until(-Fml2,(-Fml1)*(-Fml2))),
                  StateSet1),
        check_ctl(Program,
                  -somepath(always(-Fml2)),
                  StateSet2),
        intersection(StateSet1,StateSet2,StateSet).

preimage(Program,StateSet1,StateSet) :- !,
        findall(S,
                (member(S1,StateSet1),
                 map_trans(Program,S,_,S1)),
                StateSet).

statesets_not_equivalent(StateSet1,StateSet2) :-
        sort(StateSet1,S1),
        sort(StateSet2,S2),
        S1 \= S2.

stateset_initial(Program,StateSet) :- !,
        findall(S,map_state(Program,S,_,[],0),StateSet).

check_ex(Program,StateSet1,StateSet) :- !,
        preimage(Program,StateSet1,StateSet).

check_eg(Program,StateSet1,StateSet) :- !,
        False = [],
        check_eg_iterate(Program,False,StateSet1,StateSet).
check_eg_iterate(Program,Sold,Scur,Sres) :-
        statesets_not_equivalent(Sold,Scur), !,
        preimage(Program,Scur,Spre),
        intersection(Scur,Spre,Snew),
        check_eg_iterate(Program,Scur,Snew,Sres).
check_eg_iterate(_Program,_Sold,Scur,Scur) :- !.

check_eu(Program,StateSet1,StateSet2,StateSet) :- !,
        findall(State,map_state(Program,State,_,_,_),True),
        check_eu_iterate(Program,StateSet1,True,StateSet2,StateSet).
check_eu_iterate(Program,S1,Sold,Scur,Sres) :-
        statesets_not_equivalent(Sold,Scur), !,
        preimage(Program,Scur,Spre),
        intersection(S1,Spre,Stmp),
        union(Scur,Stmp,Snew),
        check_eu_iterate(Program,S1,Scur,Snew,Sres).
check_eu_iterate(_Program,_S1,_Sold,Scur,Scur) :- !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Graphical Representation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% draw transition system using dot
% TODO: doesn't work, need node labels w/o brackets etc.
%       ==> use pt_draw_graph instead for now
draw_graph :-
        trans_file(TransFile),
        open(TransFile, write, Stream),
        write(Stream, 'digraph G {\n'),
        write_nodes(Stream),
        write_edges(Stream),
        write(Stream, '}\n'),
        close(Stream).

write_nodes(Stream) :-
        abstract_state(Formulas,Effects,NodeID,_Fringe),
        write(Stream, '\t'),
        write(Stream, (Formulas,Effects,NodeID)),
        write(Stream, ';\n'),
        fail.
write_nodes(_Stream).

write_edges(Stream) :-
        abstract_trans(Formulas,Effects,NodeID,Action,NewEffects,NewNodeID),
        write(Stream, '\t'),
        write(Stream, (Formulas,Effects,NodeID)),
        write(Stream, ' -> '),
        write(Stream, (Formulas,NewEffects,NewNodeID)),
        write(Stream, ' [label=\"'),
        write(Stream, Action),
        % write(Stream, ' / '),
        % write(Stream, Condition),
        write(Stream, '\"];\n'),
        fail.
write_edges(_Stream).

trans_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/trans.dot', File).
        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Parse temporal property
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

determine_property_subformulas(ProgramName) :-
        retractall(property_subformula(ProgramName,_)),
        determine_property_subformulas2(ProgramName).
determine_property_subformulas2(ProgramName) :-
        property(_PropertyName,ProgramName,Property),
        extract_subformulas(ProgramName,Property),
        fail.
determine_property_subformulas2(_ProgramName).

extract_subformulas(Pr,somepath(P)) :- !,
        extract_subformulas(Pr,P).
extract_subformulas(Pr,allpaths(P)) :- !,
        extract_subformulas(Pr,P).
extract_subformulas(Pr,always(P)) :- !,
        extract_subformulas(Pr,P).
extract_subformulas(Pr,eventually(P)) :- !,
        extract_subformulas(Pr,P).
extract_subformulas(Pr,until(P1,P2)) :- !,
        extract_subformulas(Pr,P1),
        extract_subformulas(Pr,P2).
extract_subformulas(Pr,next(P)) :- !,
        extract_subformulas(Pr,P).

extract_subformulas(Pr,F) :-
        no_temporal_operators(F), !,
        simplify_fml(F,FS),
        (not(property_subformula(Pr,FS)) ->
            assert(property_subformula(Pr,FS));
            true).

extract_subformulas(Pr,F1*F2) :- !,
        extract_subformulas(Pr,F1),
        extract_subformulas(Pr,F2).
extract_subformulas(Pr,F1+F2) :- !,
        extract_subformulas(Pr,F1),
        extract_subformulas(Pr,F2).
extract_subformulas(Pr,F1=>F2) :- !,
        extract_subformulas(Pr,F1),
        extract_subformulas(Pr,F2).
extract_subformulas(Pr,F1<=F2) :- !,
        extract_subformulas(Pr,F1),
        extract_subformulas(Pr,F2).
extract_subformulas(Pr,F1<=>F2) :- !,
        extract_subformulas(Pr,F1),
        extract_subformulas(Pr,F2).
extract_subformulas(Pr,-F) :- !,
        extract_subformulas(Pr,F).
% no quantification

no_temporal_operators(F) :-
        var(F), !.
no_temporal_operators([E|Es]) :- !,
        no_temporal_operators(E),
        no_temporal_operators(Es).
no_temporal_operators([]) :- !.
no_temporal_operators(F) :-
        F =.. [somepath|_], !,
        fail.
no_temporal_operators(F) :-
        F =.. [allpaths|_], !,
        fail.
no_temporal_operators(F) :-
        F =.. [always|_], !,
        fail.
no_temporal_operators(F) :-
        F =.. [eventually|_], !,
        fail.
no_temporal_operators(F) :-
        F =.. [until|_], !,
        fail.
no_temporal_operators(F) :-
        F =.. [next|_], !,
        fail.
no_temporal_operators(F) :-
        F =.. [_|L],
        no_temporal_operators(L).
    
no_temporal_operators(F) :-
        not(compound(F)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Construct propositional mapping
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

construct_propositional_mapping(ProgramName) :-
        
        retractall(map_property(ProgramName,_,_,_)),
        retractall(map_subformula(ProgramName,_,_)),
        retractall(map_action(ProgramName,_,_)),
        retractall(map_state(ProgramName,_,_,_,_)),
        retractall(map_trans(ProgramName,_,_,_)),
        retractall(map_number_of_properties(ProgramName,_)),
        retractall(map_number_of_subformulas(ProgramName,_)),
        retractall(map_number_of_actions(ProgramName,_)),
        retractall(map_number_of_states(ProgramName,_)),
        retractall(map_holds_subformula(ProgramName,_,_)),
        
        % determine properties
        findall((Prop,PropName),
                user:property(PropName,ProgramName,Prop),
                Properties),
        memorize_properties(ProgramName,Properties,0),
        
        % determine subformulas
        findall(Subformula,property_subformula(ProgramName,Subformula),
                AllSubformulas),
        sort(AllSubformulas,Subformulas),
        memorize_subformulas(ProgramName,Subformulas,0),
        
        % determine ground actions
        findall(Action,abstract_trans(ProgramName,_,_,_,Action,_,_),
                AllActions),
        sort(AllActions,Actions),
        memorize_actions(ProgramName,Actions,0),
        
        % determine states
        assert(map_number_of_states(ProgramName,0)),
        propositionalize_states(ProgramName),
        
        % determine transitions
        propositionalize_transitions(ProgramName),

        % determine satisfied subformulas
        propositionalize_subformula_sat(ProgramName),

        % determine propositionalized properties
        propositionalize_properties(ProgramName,0).

memorize_properties(P,[(Prop,Name)|Properties],N) :-
        assert(map_property(P,N,Name,Prop)),
        N1 is N+1,
        memorize_properties(P,Properties,N1).
memorize_properties(P,[],N) :-
        assert(map_number_of_properties(P,N)).

memorize_subformulas(P,[Formula|Formulas],N) :-
        atom_number(NAtom,N),
        atom_concat(subf,NAtom,FormulaN),
        assert(map_subformula(P,FormulaN,Formula)),
        N1 is N+1,
        memorize_subformulas(P,Formulas,N1).
memorize_subformulas(P,[],N) :-
        assert(map_number_of_subformulas(P,N)).

memorize_actions(P,[Action|Actions],N) :-
        assert(map_action(P,N,Action)),
        N1 is N+1,
        memorize_actions(P,Actions,N1).
memorize_actions(P,[],N) :-
        assert(map_number_of_actions(P,N)).

propositionalize_states(P) :-
        abstract_state(P,Formulas,Effects,NodeID,_),
        retract(map_number_of_states(P,N)),
        N1 is N+1,
        assert(map_state(P,N,Formulas,Effects,NodeID)),
        assert(map_number_of_states(P,N1)),
        fail.
propositionalize_states(_P).
        
propositionalize_transitions(P) :-
        abstract_trans(P,Formulas,Effects,NodeID,Action,NewEffects,
                       NewNodeID),
        map_state(P,S1,Formulas,Effects,NodeID),
        map_state(P,S2,Formulas,NewEffects,NewNodeID),
        map_action(P,A,Action),
        assert(map_trans(P,S1,A,S2)),
        fail.
propositionalize_transitions(_P).

propositionalize_subformula_sat(P) :-
        map_state(P,N,Formulas,Effects,_NodeID),
        map_subformula(P,M,Formula),
        regression(Formula,Effects,RegressedFormula),
        is_entailed(Formulas,RegressedFormula),
        assert(map_holds_subformula(P,N,M)),
        fail.
propositionalize_subformula_sat(_P).

propositionalize_properties(P,N) :-
        retract(map_property(P,N,Name,Prop)), !,
        propositionalize_property(P,Prop,Prop2),
        assert(map_property(P,N,Name,Prop2)),
        N1 is N+1,
        propositionalize_properties(P,N1).
propositionalize_properties(_P,_N).

propositionalize_property(P,somepath(F),somepath(F1)) :- !,
        propositionalize_property(P,F,F1).
propositionalize_property(P,allpaths(F),allpaths(F1)) :- !,
        propositionalize_property(P,F,F1).
propositionalize_property(P,always(F),always(F1)) :- !,
        propositionalize_property(P,F,F1).
propositionalize_property(P,eventually(F),eventually(F1)) :- !,
        propositionalize_property(P,F,F1).
propositionalize_property(P,until(F1,F2),until(F3,F4)) :- !,
        propositionalize_property(P,F1,F3),
        propositionalize_property(P,F2,F4).
propositionalize_property(P,next(F),next(F1)) :- !,
        propositionalize_property(P,F,F1).
propositionalize_property(P,F,F1) :-
        no_temporal_operators(F), !,
        simplify_fml(F,FS),
        map_subformula(P,N,FS),
        F1 = N.
propositionalize_property(P,F1*F2,F3*F4) :- !,
        propositionalize_property(P,F1,F3),
        propositionalize_property(P,F2,F4).
propositionalize_property(P,F1+F2,F3+F4) :- !,
        propositionalize_property(P,F1,F3),
        propositionalize_property(P,F2,F4).
propositionalize_property(P,F1=>F2,F3=>F4) :- !,
        propositionalize_property(P,F1,F3),
        propositionalize_property(P,F2,F4).
propositionalize_property(P,F1<=F2,F3<=F4) :- !,
        propositionalize_property(P,F1,F3),
        propositionalize_property(P,F2,F4).
propositionalize_property(P,F1<=>F2,F3<=>F4) :- !,
        propositionalize_property(P,F1,F3),
        propositionalize_property(P,F2,F4).
propositionalize_property(P,-F,F1) :- !,
        propositionalize_property(P,F,F1).

% draw propositionalized transition system using dot
pt_draw_graph(P) :-
        ptrans_file(PTransFile),
        open(PTransFile, write, Stream),
        write(Stream, 'digraph G {\n'),
        pt_write_nodes(P,Stream),
        pt_write_edges(P,Stream),
        write(Stream, '}\n'),
        close(Stream).

pt_write_nodes(P,Stream) :-
        map_state(P,S,_Formulas,_Effects,_NodeID),
        write(Stream, '\t'),
        write(Stream, S),
        write(Stream, ';\n'),
        fail.
pt_write_nodes(_P,_Stream).

pt_write_edges(P,Stream) :-
        map_trans(P,S1,A,S2),
        map_action(P,A,Action),
        write(Stream, '\t'),
        write(Stream, S1),
        write(Stream, ' -> '),
        write(Stream, S2),
        write(Stream, ' [label=\"'),
        write(Stream, Action),
        write(Stream, '\"];\n'),
        fail.
pt_write_edges(_P,_Stream).

ptrans_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/prop_trans.dot', File).
        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Translate propositional transition system to SMV input language
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

translate_to_smv(P) :-
        temp_file(P, File),
        open(File, write, Stream),
        write(Stream, 'MODULE main\n'),
        write(Stream, ' VAR\n'),
        writeVariables(P,Stream),
        write(Stream, ' ASSIGN\n'),
        writeAssignInit(P,Stream),
        writeAssignNext(P,Stream),
        write(Stream, ' DEFINE\n'),
        writeDefine(P,Stream),
        writeSpecs(P,Stream),
        close(Stream).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

temp_file(P, File) :-
        temp_dir(TempDir),
        atomics_to_string([TempDir,'/',P,'_nusmv_problem.smv'],File).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

writeVariables(P,Stream) :-
        map_number_of_states(P,States),
        MaxState is States-1,
        write(Stream, '   state : 0..'),
        write(Stream, MaxState),
        write(Stream, ';\n').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

writeAssignInit(P,Stream) :-
        findall(N,map_state(P,N,_,[],0),InitStates),
        write(Stream, '   init(state) := {'),
        writeStateList(Stream,InitStates),
        write(Stream, '};\n').

writeAssignNext(P,Stream) :-
        write(Stream, '   next(state) := case\n'),
        writeTransStatesCases(P,Stream,0),
        write(Stream, '   esac;\n').

writeTransStatesCases(P,Stream,N) :-
        map_number_of_states(P,States),
        N < States, !,
        findall(State,
                map_trans(P,N,_,State),
                Successors),
        write(Stream, '     state = '),     
        write(Stream, N),
        write(Stream, ' : {'),
        writeStateList(Stream,Successors),
        write(Stream, '};\n'),
        N1 is N+1,
        writeTransStatesCases(P,Stream,N1).
writeTransStatesCases(_,_,_).

writeStateList(Stream,[S1,S2|L]) :-
        write(Stream, S1),
        write(Stream, ', '),
        writeStateList(Stream,[S2|L]).
writeStateList(Stream,[S]) :-
        write(Stream, S).
writeStateList(_Stream,[]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

writeDefine(P,Stream) :-
        writeDefineSubformulas(P,Stream).

writeDefineSubformulas(P,Stream) :-
        map_subformula(P,F,_Formula),
        write(Stream, '   '),
        write(Stream, F),
        write(Stream, ' :=\n'),
        writeSubformulaDefinition(P,Stream,F),
        fail.
writeDefineSubformulas(_,_).

writeSubformulaDefinition(P,Stream,F) :-
        map_holds_subformula(P,N,F),
        write(Stream, '     state = '),
        write(Stream, N),
        write(Stream, ' |\n'),
        fail.
writeSubformulaDefinition(_P,Stream,_Formula) :-
        write(Stream, '     FALSE;\n').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

writeSpecs(P,Stream) :-
        map_property(P,_N,PropertyName,Property),
        write(Stream, ' SPEC NAME '),
        write(Stream, PropertyName),
        write(Stream, ' := '),
        writeSpecProperty(Stream,Property),
        write(Stream, ';\n'),
        fail.
writeSpecs(_,_).

writeSpecProperty(Stream,F) :-
        atom(F),
        write(Stream, F).
writeSpecProperty(Stream,P1*P2) :- !,
        write(Stream,'('),
        writeSpecProperty(Stream,P1),
        write(Stream,' & '),
        writeSpecProperty(Stream,P2),
        write(Stream, ')').
writeSpecProperty(Stream,P1+P2) :- !,
        write(Stream,'('),
        writeSpecProperty(Stream,P1),
        write(Stream,' | '),
        writeSpecProperty(Stream,P2),
        write(Stream, ')').
writeSpecProperty(Stream,P1=>P2) :- !,
        write(Stream,'('),
        writeSpecProperty(Stream,P1),
        write(Stream,' -> '),
        writeSpecProperty(Stream,P2),
        write(Stream, ')').
writeSpecProperty(Stream,P1<=P2) :- !,
        write(Stream,'('),
        writeSpecProperty(Stream,P2),
        write(Stream,' -> '),
        writeSpecProperty(Stream,P1),
        write(Stream, ')').
writeSpecProperty(Stream,P1<=>P2) :- !,
        write(Stream,'('),
        writeSpecProperty(Stream,P1),
        write(Stream,' <-> '),
        writeSpecProperty(Stream,P2),
        write(Stream, ')').
writeSpecProperty(Stream,-P1) :- !,
        write(Stream,'!('),
        writeSpecProperty(Stream,P1),
        write(Stream, ')').
writeSpecProperty(Stream,somepath(P1)) :- !,
        write(Stream,'E'),
        writeSpecProperty(Stream,P1).
writeSpecProperty(Stream,allpaths(P1)) :- !,
        write(Stream,'A'),
        writeSpecProperty(Stream,P1).
writeSpecProperty(Stream,always(P1)) :- !,
        write(Stream,'G('),
        writeSpecProperty(Stream,P1),
        write(Stream, ')').
writeSpecProperty(Stream,eventually(P1)) :- !,
        write(Stream,'F('),
        writeSpecProperty(Stream,P1),
        write(Stream, ')').
writeSpecProperty(Stream,until(P1,P2)) :- !,
        write(Stream,' [ '),
        writeSpecProperty(Stream,P1),
        write(Stream,' U '),
        writeSpecProperty(Stream,P2),
        write(Stream,' ] ').
writeSpecProperty(Stream,next(P1)) :- !,
        write(Stream,'X('),
        writeSpecProperty(Stream,P1),
        write(Stream, ')').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Call SMV and parse output
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
        
call_smv(ProgramN, PropertyN, TruthValue, Type, Actions) :-
        temp_file(ProgramN, File),
        process_create(path('NuSMV'), 
                       ['-n', PropertyN,      % property index
                        File],                % input file
                       [stdout(pipe(Stream)), % completely silent
                        process(PID)]),       % need PID for exit status
        process_wait(PID, _Status), !,        % wait for completion
        % Status=exit(0),
        get_result(ProgramN, Stream, TruthValue, Type, Actions).

get_result(P, Stream, TruthValue, Type, Actions) :-
        read_lines(Stream,Lines),
        get_truth_value(Lines,TruthValue),
        get_counterexample(P,Lines,TruthValue,Type,Actions).

read_lines(Stream, Lines) :-
        read_line_to_codes(Stream, Line1),
        read_lines(Line1, Stream, Lines).

read_lines(end_of_file, _, []) :- !.
read_lines(Codes, Stream, [Line|Lines]) :-
        string_codes(Line, Codes),
        read_line_to_codes(Stream, Line2),
        read_lines(Line2, Stream, Lines).

get_truth_value([Line|_], true) :-
        sub_string(Line,_,_,_,'is true'), !.
get_truth_value([Line|_], false) :-
        sub_string(Line,_,_,_,'is false'), !.
get_truth_value([_|Lines], Value) :- !,
        get_truth_value(Lines, Value).

get_counterexample(_P, _Lines, true, nil, nil).

get_counterexample(P, Lines, false, Type, Actions) :-
        skip_to_counterexample(Lines,Lines2),
        get_counterexample2(Lines2,States),
        translate_counterexample(P,States,Type,Actions).

get_counterexample2([Line|Lines],[State|States]) :-
        sub_string(Line,_,_,After,'  state = '), !,
        sub_string(Line,_,After,0,StateStr),
        atom_string(StateAtom,StateStr),
        atom_number(StateAtom,State),
        get_counterexample2(Lines,States).
get_counterexample2([Line|Lines],[loop|States]) :-
        sub_string(Line,_,_,_,'-- Loop starts here'), !,
        get_counterexample2(Lines,States).        
get_counterexample2([_Line|Lines],States) :-
        get_counterexample2(Lines,States).        
get_counterexample2([],[]).

skip_to_counterexample([Line|Lines],Lines2) :-
        \+ sub_string(Line,_,_,_,'Trace Type: Counterexample'), !,
        skip_to_counterexample(Lines,Lines2).
skip_to_counterexample([_|Lines],Lines).

% single state counterexample = initial state without such a path
translate_counterexample(P,[State],Formulas,[]) :- !,
        map_state(P,State,Formulas,_Effects,_NodeID).

% multiple states counterexample = execution trace
translate_counterexample(P,States,Type,Trace) :-
        translate_counterexample2(P,States,Type,Trace).

translate_counterexample2(P,[S1,loop,S2|States],Type,[Action|Trace]) :-
        !,
        map_trans(P,S1,A,S2),
        map_action(P,A,Action),
        translate_counterexample2(P,[loop,S2|States],Type,Trace).
        
translate_counterexample2(P,[loop,S],Type,[loop(Action)]) :- !,
        map_state(P,S,Type,_,_),
        map_trans(P,S,A,S),
        map_action(P,A,Action).

translate_counterexample2(P,[loop,S2|States],Type,[loop(Trace)]) :- !,
        translate_counterexample2(P,[S2|States],Type,Trace).
        
translate_counterexample2(P,[S1,S2|States],Type,[Action|Trace]) :-
        map_trans(P,S1,A,S2),
        map_action(P,A,Action),
        translate_counterexample2(P,[S2|States],Type,Trace).
        
translate_counterexample2(P,[State],Type,[]) :-
        map_state(P,State,Type,_,_).
