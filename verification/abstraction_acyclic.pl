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

@author  Jens Claßen
@license GPLv2

 **/
:- module('abstraction_acyclic', [compute_abstraction/1,
                                  verify/1, verify/2]).

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
   map_property/3,
   map_subformula/2,
   map_action/2,  
   map_state/4,
   map_trans/3,
   map_number_of_properties/1,
   map_number_of_subformulas/1,
   map_number_of_actions/1,
   map_number_of_states/1,
   abstract_state/4,
   abstract_trans/6,
   program_to_verify/1,
   property_subformula/1.

% use_sink_states.

% TODO: include support for closed-world assumption

/**
  * compute_abstraction(+ProgramName) is det.
  *
  * Computes the abstract transition system for the program of the
  * given name. Nodes and transitions will be generated in the form of
  * newly created facts for the dynamic predicates abstract_state/4
  * and abstract_trans/6.
  *
  * @arg ProgramName the name of a program, defined by the user via a
  *                  fact over the predicate program/2
 **/
compute_abstraction(ProgramName) :-
        
        retractall(program_to_verify(ProgramName)),
        assert(program_to_verify(ProgramName)),

        construct_abstract_transition_system,
        construct_propositional_mapping,
        translate_to_smv, !.

/**
  * verify(+PropertyName) is det.
  *
  * Verifies the property of the given name on the previously created
  * abstract transition system by means of translating the
  * corresponding propositional mapping to the model checker NuSMV.
  * Verification results (truth value and counterexample) will be
  * printed to standard output.
  *
  * @arg PropertyName the name of a property, defined by the user via a
  *                   fact over the predicate property/3
 **/
verify(PropertyName) :-
        verify(PropertyName,_).

/**
  * verify(+PropertyName,-TruthValue) is det.
  *
  * Same as verify/1, but additionally returns the truth value of
  * whether the program for which the abstract transition system was
  * constructed satisfies the property (true) or not (false).
  *
  * @arg PropertyName the name of a property, defined by the user via a
  *                   fact over the predicate property/3
  * @arg TruthValue   'true' if the property is satisfied,
  *                   'false' if not
 **/
verify(PropertyName,TruthValue) :-
       map_property(N,PropertyName,Property),
       call_smv(N, TruthValue, Type, Actions),
       report_message_r(['Verified: \n',
                       '\t Property            : ', Property, '\n',
                       '\t Truth Value         : ', TruthValue, '\n',
                       '\t Counterexample Type : ', Type, '\n',
                       '\t Counterexample Trace: ', Actions, '\n']).        

construct_abstract_transition_system :-
        init_construction,
        iterate_construction.

iterate_construction :-
        construction_step, !,
        iterate_construction.
iterate_construction.

init_construction :-
        
        program_to_verify(ProgramName),
        
        % materialize the characteristic graph
        construct_characteristic_graph(ProgramName),

        % preprocess actions
        preprocess_actions(ProgramName),
        
        % determine relevant formulas from property
        determine_property_subformulas(ProgramName),
        
        % determine the KB (initial theory)
        findall(F,user:initially(F),KB),
        
        % remove old instances of dynamic predicates
        retractall(abstract_state(_,_,_,_)),
        retractall(abstract_trans(_,_,_,_,_,_)),
        
        % initialize with first abstract state
        create_state_if_not_exists(KB,[],0).
        
% construction step: expand transition(s)
construction_step :-
        
        % if there is an abstract state at the fringe...
        abstract_state(Formulas,Effects,NodeID,true),
        
        % where none of the three cases below applies...
        not(can_expand(Formulas,Effects,NodeID,_,_,_)),
        not(can_split_transition(Formulas,Effects,NodeID,_,_)),
        not(can_split_property(Formulas,Effects,_)),

        % then
        !,
        
        % this state is not a fringe state anymore
        retract(abstract_state(Formulas,Effects,NodeID,true)),
        assert(abstract_state(Formulas,Effects,NodeID,false)).
        
% construction step: expand transition(s)
construction_step :-
        
        % if there is an abstract state...
        abstract_state(Formulas,Effects,NodeID,true),
        
        % where it is possible to expand an action...
        can_expand(Formulas,Effects,NodeID,Action,RegressedCondition,
                   NewNodeID),
        
        % then
        !,
        
        % create the corresponding transition(s)
        create_transitions(Formulas,Effects,NodeID,Action,
                           RegressedCondition,NewNodeID).

% construction step: split types by some transition condition
construction_step :-
        
        % if there is an abstract state...
        abstract_state(Formulas,Effects,NodeID,true),
        
        % where we can split over a transition condition...
        can_split_transition(Formulas,Effects,NodeID,Action,
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
        split(Formulas,RegressedCondition).

% construction step: split types by some property subformula
construction_step :-
        
        % if there is an abstract state...
        abstract_state(Formulas,Effects,NodeID,true),
        
        % where we can split over a property subformula...
        can_split_property(Formulas,Effects,RegressedFormula),
        
        % then
        !,
        
        report_message_r(['Doing split over property subformula: \n',
                        '\t property : ', RegressedFormula, '\n',
                        '\t type     : ', Formulas, '\n',
                        '\t effects  : ', Effects, '\n',
                        '\t node     : ', NodeID, '\n']),
        
        % split states and transitions over this formula
        split(Formulas,RegressedFormula).

% is it possible to expand a transition?
can_expand(Formulas,Effects,NodeID,Action,RegressedCondition,
           NewNodeID) :- 
        
        % there is a possible outgoing transition...
        cg_edge(_Program,NodeID,Guard,Action,NewNodeID),
        guardcond(Guard,Condition),

        % whose regressed condition is entailed...
        regression(Condition,Effects,RegressedCondition),
        is_entailed(Formulas,RegressedCondition),
        
        % and where the corresponding transition(s) do not yet exist
        not(abstract_trans(Formulas,Effects,NodeID,Action,
                           _NewEffects,NewNodeID)).
        
% is it possible to split over a transition condition?
can_split_transition(Formulas,Effects,NodeID,Action,
                     RegressedCondition) :-

        % there is a possible outgoing transition...
        cg_edge(_Program,NodeID,Guard,Action,_NewNodeID),
        guardcond(Guard,Condition),
        
        % whose (negated) regressed condition is not yet entailed
        % by the type formulas
        regression(Condition,Effects,RegressedCondition),
        not(is_entailed(Formulas,RegressedCondition)),
        not(is_entailed(Formulas,-RegressedCondition)).
        
% is it possible to split over a property subformula?
can_split_property(Formulas,Effects,RegressedFormula) :-
        
        % there is a property subformula
        property_subformula(Formula),
        
        % whose (negated) regressed condition is not yet entailed
        % by the type formulas
        regression(Formula,Effects,RegressedFormula),
        not(is_entailed(Formulas,RegressedFormula)),
        not(is_entailed(Formulas,-RegressedFormula)).
        
% split Formulas over RegressedCondition
split(Formulas,RegressedCondition) :-
        simplify_fml(-RegressedCondition,NegRegressedCondition),
        retract(abstract_state(Formulas,Effects,NodeID,Fringe)),
        assert(abstract_state([RegressedCondition|Formulas],Effects,
                              NodeID,Fringe)),
        assert(abstract_state([NegRegressedCondition|Formulas],Effects,
                              NodeID,Fringe)),
        fail.

split(Formulas,RegressedCondition) :-
        simplify_fml(-RegressedCondition,NegRegressedCondition),
        retract(abstract_trans(Formulas,Effects,NodeID,Action,
                               NewEffects,NewNodeID)),
        assert(abstract_trans([RegressedCondition|Formulas],Effects,
                              NodeID,Action,NewEffects,NewNodeID)),
        assert(abstract_trans([NegRegressedCondition|Formulas],Effects,
                              NodeID,Action,NewEffects,NewNodeID)),
        fail.
        
split(Formulas,RegressedCondition) :-
        is_inconsistent([RegressedCondition|Formulas]),
        retractall(abstract_state([RegressedCondition|Formulas],_,_,_)),
        retractall(abstract_trans([RegressedCondition|Formulas],_,_,_,_)), 
        fail.
        
split(Formulas,RegressedCondition) :-
        simplify_fml(-RegressedCondition,NegRegressedCondition),
        is_inconsistent([NegRegressedCondition|Formulas]),
        retractall(abstract_state([NegRegressedCondition|Formulas],_,_,_)),
        retractall(abstract_trans([NegRegressedCondition|Formulas],_,_,_,_)), 
        fail.

split(_,_).


% split over effect conditions
create_transitions(Formulas,Effects,NodeID,Action,Cond,NewNodeID) :-
        
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
        
        split(Formulas,RegressedCondition),
        simplify_fml(-RegressedCondition,NegRegressedCondition),
        
        create_transitions([RegressedCondition|Formulas],Effects,
                           NodeID,Action,Cond,NewNodeID),
        create_transitions([NegRegressedCondition|Formulas],Effects,
                           NodeID,Action,Cond,NewNodeID).

% actually create transition
create_transitions(Formulas,Effects,NodeID,Action,Cond,NewNodeID) :-
        
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

        assert(abstract_trans(Formulas,Effects,NodeID,Action,
                              ResEffects,NewNodeID)),
        create_state_if_not_exists(Formulas,ResEffects,NewNodeID).

% create a new abstract state if it does not exist already
create_state_if_not_exists(Formulas,Effects,NodeID) :-
        abstract_state(Formulas,Effects,NodeID,_Fringe), !.
create_state_if_not_exists(Formulas,Effects,NodeID) :- !,
        assert(abstract_state(Formulas,Effects,NodeID,true)).

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
        retractall(property_subformula(_)),
        determine_property_subformulas2(ProgramName).
determine_property_subformulas2(ProgramName) :-
        property(_PropertyName,ProgramName,Property),
        extract_subformulas(Property),
        fail.
determine_property_subformulas2(_ProgramName).

extract_subformulas(somepath(P)) :- !,
        extract_subformulas(P).
extract_subformulas(allpaths(P)) :- !,
        extract_subformulas(P).
extract_subformulas(always(P)) :- !,
        extract_subformulas(P).
extract_subformulas(eventually(P)) :- !,
        extract_subformulas(P).
extract_subformulas(until(P1,P2)) :- !,
        extract_subformulas(P1),
        extract_subformulas(P2).        
extract_subformulas(next(P)) :- !,
        extract_subformulas(P).

extract_subformulas(F) :- 
        no_temporal_operators(F), !,
        simplify_fml(F,FS),
        (not(property_subformula(FS)) ->
            assert(property_subformula(FS));
            true).

extract_subformulas(F1*F2) :- !,
        extract_subformulas(F1),
        extract_subformulas(F2).
extract_subformulas(F1+F2) :- !,
        extract_subformulas(F1),
        extract_subformulas(F2).
extract_subformulas(F1=>F2) :- !,
        extract_subformulas(F1),
        extract_subformulas(F2).
extract_subformulas(F1<=F2) :- !,
        extract_subformulas(F1),
        extract_subformulas(F2).
extract_subformulas(F1<=>F2) :- !,
        extract_subformulas(F1),
        extract_subformulas(F2).
extract_subformulas(-F) :- !,
        extract_subformulas(F).
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

construct_propositional_mapping :-
        
        retractall(map_property(_,_,_)),
        retractall(map_subformula(_,_)),
        retractall(map_action(_,_)),
        retractall(map_state(_,_,_,_)),
        retractall(map_trans(_,_,_)),
        retractall(map_number_of_properties(_)),
        retractall(map_number_of_subformulas(_)),
        retractall(map_number_of_actions(_)),
        retractall(map_number_of_states(_)),

        program_to_verify(ProgramName),
        
        % determine properties
        findall((Prop,PropName),
                user:property(PropName,ProgramName,Prop),
                Properties),
        memorize_properties(Properties,0),
        
        % determine subformulas
        findall(Subformula,property_subformula(Subformula),
                AllSubformulas),
        sort(AllSubformulas,Subformulas),
        memorize_subformulas(Subformulas,0),
        
        % determine ground actions
        findall(Action,abstract_trans(_,_,_,Action,_,_),AllActions),
        sort(AllActions,Actions),
        memorize_actions(Actions,0),
        
        % determine states
        assert(map_number_of_states(0)),
        propositionalize_states,
        
        % determine transitions
        propositionalize_transitions.

memorize_properties([(Prop,Name)|Properties],N) :-
        assert(map_property(N,Name,Prop)),
        N1 is N+1,
        memorize_properties(Properties,N1).
memorize_properties([],N) :-
        assert(map_number_of_properties(N)).

memorize_subformulas([Formula|Formulas],N) :-
        atom_number(NAtom,N),
        atom_concat(subf,NAtom,FormulaN),
        assert(map_subformula(FormulaN,Formula)),
        N1 is N+1,
        memorize_subformulas(Formulas,N1).
memorize_subformulas([],N) :-
        assert(map_number_of_subformulas(N)).

memorize_actions([Action|Actions],N) :-
        assert(map_action(N,Action)),
        N1 is N+1,
        memorize_actions(Actions,N1).
memorize_actions([],N) :-
        assert(map_number_of_actions(N)).

propositionalize_states :-
        abstract_state(Formulas,Effects,NodeID,_),
        retract(map_number_of_states(N)),
        N1 is N+1,
        assert(map_state(N,Formulas,Effects,NodeID)),
        assert(map_number_of_states(N1)),
        fail.
propositionalize_states.
        
propositionalize_transitions :-
        abstract_trans(Formulas,Effects,NodeID,Action,NewEffects,
                       NewNodeID),
        map_state(S1,Formulas,Effects,NodeID),
        map_state(S2,Formulas,NewEffects,NewNodeID),
        map_action(A,Action),
        assert(map_trans(S1,A,S2)),
        fail.
propositionalize_transitions.

% draw propositionalized transition system using dot
pt_draw_graph :-
        ptrans_file(PTransFile),
        open(PTransFile, write, Stream),
        write(Stream, 'digraph G {\n'),
        pt_write_nodes(Stream),
        pt_write_edges(Stream),
        write(Stream, '}\n'),
        close(Stream).

pt_write_nodes(Stream) :-
        map_state(S,_Formulas,_Effects,_NodeID),
        write(Stream, '\t'),
        write(Stream, S),
        write(Stream, ';\n'),
        fail.
pt_write_nodes(_Stream).

pt_write_edges(Stream) :-
        map_trans(S1,A,S2),
        map_action(A,Action),
        write(Stream, '\t'),
        write(Stream, S1),
        write(Stream, ' -> '),
        write(Stream, S2),
        write(Stream, ' [label=\"'),
        write(Stream, Action),
        write(Stream, '\"];\n'),
        fail.
pt_write_edges(_Stream).

ptrans_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/prop_trans.dot', File).
        
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Translate propositional transition system to SMV input language
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

translate_to_smv :-
        temp_file(File),
        open(File, write, Stream),
        write(Stream, 'MODULE main\n'),
        write(Stream, ' VAR\n'),
        writeVariables(Stream),
        write(Stream, ' ASSIGN\n'),
        writeAssignInit(Stream),
        writeAssignNext(Stream),
        write(Stream, ' DEFINE\n'),
        writeDefine(Stream),
        writeSpecs(Stream),
        close(Stream).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

temp_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/nusmv_problem.smv', File).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

writeVariables(Stream) :-
        map_number_of_states(States),
        MaxState is States-1,
        write(Stream, '   state : 0..'),
        write(Stream, MaxState),
        write(Stream, ';\n').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

writeAssignInit(Stream) :-
        findall(N,map_state(N,_,[],0),InitStates),
        write(Stream, '   init(state) := {'),
        writeStateList(Stream,InitStates),
        write(Stream, '};\n').

writeAssignNext(Stream) :-
        write(Stream, '   next(state) := case\n'),
        writeTransStatesCases(Stream,0),
        write(Stream, '   esac;\n').

writeTransStatesCases(Stream,N) :-
        map_number_of_states(States),
        N < States, !,
        findall(State,
                map_trans(N,_,State),
                Successors),
        write(Stream, '     state = '),     
        write(Stream, N),
        write(Stream, ' : {'),
        writeStateList(Stream,Successors),
        write(Stream, '};\n'),
        N1 is N+1,
        writeTransStatesCases(Stream,N1).
writeTransStatesCases(_,_).

writeStateList(Stream,[S1,S2|L]) :-
        write(Stream, S1),
        write(Stream, ', '),
        writeStateList(Stream,[S2|L]).
writeStateList(Stream,[S]) :-
        write(Stream, S).
writeStateList(_Stream,[]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

writeDefine(Stream) :-
        writeDefineSubformulas(Stream).

writeDefineSubformulas(Stream) :-
        map_subformula(P,Formula),
        write(Stream, '   '),
        write(Stream, P),
        write(Stream, ' :=\n'),
        writeSubformulaDefinition(Stream,Formula),
        fail.
writeDefineSubformulas(_).

writeSubformulaDefinition(Stream,Formula) :-
        map_state(N,Formulas,Effects,_NodeID),
        regression(Formula,Effects,RegressedFormula),
        is_entailed(Formulas,RegressedFormula),
        write(Stream, '     state = '),
        write(Stream, N),
        write(Stream, ' |\n'),
        fail.
writeSubformulaDefinition(Stream,_Formula) :-
        write(Stream, '     FALSE;\n').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

writeSpecs(Stream) :-
        map_property(_N,PropertyName,Property),
        write(Stream, ' SPEC NAME '),
        write(Stream, PropertyName),
        write(Stream, ' := '),
        writeSpecProperty(Stream,Property),
        write(Stream, ';\n'),
        fail.
writeSpecs(_).

writeSpecProperty(Stream, F) :-
        no_temporal_operators(F), !,
        simplify_fml(F,FS),
        property_subformula(FS),
        map_subformula(FormulaN,FM), FS =@= FM, !,
        write(Stream, FormulaN).
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
writeSpecProperty(Stream,-P) :- !,
        write(Stream,'!('),
        writeSpecProperty(Stream,P),
        write(Stream, ')').
writeSpecProperty(Stream,somepath(P)) :- !,
        write(Stream,'E'),
        writeSpecProperty(Stream,P).
writeSpecProperty(Stream,allpaths(P)) :- !,
        write(Stream,'A'),
        writeSpecProperty(Stream,P).
writeSpecProperty(Stream,always(P)) :- !,
        write(Stream,'G('),
        writeSpecProperty(Stream,P),
        write(Stream, ')').
writeSpecProperty(Stream,eventually(P)) :- !,
        write(Stream,'F('),
        writeSpecProperty(Stream,P),
        write(Stream, ')').
writeSpecProperty(Stream,until(P1,P2)) :- !,
        write(Stream,' [ '),
        writeSpecProperty(Stream,P1),
        write(Stream,' U '),
        writeSpecProperty(Stream,P2),
        write(Stream,' ] ').
writeSpecProperty(Stream,next(P)) :- !,
        write(Stream,'X('),
        writeSpecProperty(Stream,P),
        write(Stream, ')').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Call SMV and parse output
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
        
call_smv(PropertyN, TruthValue, Type, Actions) :-
        temp_file(File),
        process_create(path('NuSMV'), 
                       ['-n', PropertyN,      % property index
                        File],                % input file
                       [stdout(pipe(Stream)), % completely silent
                        process(PID)]),       % need PID for exit status
        process_wait(PID, _Status), !,        % wait for completion
        % Status=exit(0),
        get_result(Stream, TruthValue, Type, Actions).

get_result(Stream, TruthValue, Type, Actions) :-
        read_lines(Stream,Lines),
        get_truth_value(Lines,TruthValue),
        get_counterexample(Lines,TruthValue,Type,Actions).

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

get_counterexample(_Lines, true, nil, nil).

get_counterexample(Lines, false, Type, Actions) :-
        skip_to_counterexample(Lines,Lines2),
        get_counterexample2(Lines2,States),
        translate_counterexample(States,Type,Actions).

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
translate_counterexample([State],Formulas,[]) :- !,
        map_state(State,Formulas,_Effects,_NodeID).

% multiple states counterexample = execution trace
translate_counterexample(States,Type,Trace) :-
        translate_counterexample2(States,Type,Trace).

translate_counterexample2([S1,loop,S2|States],Type,[Action|Trace]) :-
        !,
        map_trans(S1,A,S2),
        map_action(A,Action),
        translate_counterexample2([loop,S2|States],Type,Trace).
        
translate_counterexample2([loop,S],Type,[loop(Action)]) :- !,
        map_state(S,Type,_,_),
        map_trans(S,A,S),
        map_action(A,Action).

translate_counterexample2([loop,S2|States],Type,[loop(Trace)]) :- !,
        translate_counterexample2([S2|States],Type,Trace).
        
translate_counterexample2([S1,S2|States],Type,[Action|Trace]) :-
        map_trans(S1,A,S2),
        map_action(A,Action),
        translate_counterexample2([S2|States],Type,Trace).
        
translate_counterexample2([State],Type,[]) :-
        map_state(State,Type,_,_).
