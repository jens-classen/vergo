/**
 
verify_abstraction

This file implements a verification algorithm for Golog programs based
on the construction described in the papers

Benjamin Zarrieß and Jens Claßen:
Verifying CTL* Properties of Golog Programs over Local-Effect Actions.
In Proceedings of the Twenty-First European Conference on Artificial Intelligence (ECAI 2014),
IOS Press, 2014.

Benjamin Zarrieß and Jens Claßen:
On the Decidability of Verifying LTL Properties of Golog Programs. 
Technical Report 13-10, Chair of Automata Theory, TU Dresden, Dresden, Germany, 2013.

Benjamin Zarrieß and Jens Claßen:
Verification of Knowledge-Based Programs over Description Logic Actions.
In Proceedings of the Twenty-Fourth International Joint Conference on Artificial Intelligence (IJCAI 2015),
AAAI Press, 2015.

Benjamin Zarrieß and Jens Claßen:
Decidable Verification of Knowledge-Based Programs over Description Logic Actions with Sensing.
In Proceedings of the Twenty-Eighth International Workshop on Description Logics (DL 2015),
CEUR-WS.org, 2015.

@author  Jens Claßen
@license GPL

 **/

:- use_module('../lib/utils').
:- use_module('../lib/env').

:- use_module('../reasoning/fol').
:- use_module('../reasoning/l').
:- use_module('../reasoning/dl', [consistent/1 as dl_consistent,
                                  inconsistent/1 as dl_inconsistent]).

:- discontiguous(stdnames_axioms/1).
:- discontiguous(is_entailed/2).
:- discontiguous(is_inconsistent/1).

% TODO: use standard names instead
% we make the UNA for constants
unique_names_assumption.

:- dynamic   
   is_entailed_cached/3,
   is_inconsistent_cached/2,
   regression_cached/3,
   map_type_formula/2,
   map_type/2,
   map_literal/2,
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
   cg_number_of_nodes/1,
   cg_node/2,
   cg_edge/4,
   program_to_verify/1,
   property_subformula/1.

compute_abstraction(ProgramName) :-
        
        retractall(program_to_verify(ProgramName)),
        assert(program_to_verify(ProgramName)),
        
        construct_abstract_transition_system,
        construct_propositional_mapping,
        translate_to_smv.

verify(PropertyName) :-
        
       map_property(N,PropertyName,Property),
       call_smv(N, TruthValue, Type, Actions),
       report_message(['Verified: \n',
                       '\t Property   : ', Property, '\n',
                       '\t Truth Value: ', TruthValue, '\n',
                       '\t Type       : ', Type, '\n',
                       '\t Trace      : ', Actions, '\n']).        

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
        
        % determine relevant formulas from property
        determine_property_subformulas(ProgramName),
        
        % determine the KB (initial theory)
        findall(F,initially(F),KB),
        
        % remove old instances of dynamic predicates
        retractall(abstract_state(_,_,_,_)),
        retractall(abstract_trans(_,_,_,_,_,_)),
        
        % initialize with first abstract state
        create_state_if_not_exists(KB,[],0).
        
% construction step: expand transition(s)
construction_step :-
        
        % if there is an abstract state at the fringe...
        abstract_state(Formulas,Literals,NodeID,true),
        
        % where none of the three cases below applies...
        not(can_expand(Formulas,Literals,NodeID,_,_,_)),
        not(can_split_transition(Formulas,Literals,NodeID,_,_)),
        not(can_split_property(Formulas,Literals,_)),

        % then
        !,
        
        % this state is not a fringe state anymore
        retract(abstract_state(Formulas,Literals,NodeID,true)),
        assert(abstract_state(Formulas,Literals,NodeID,false)).
        
% construction step: expand transition(s)
construction_step :-
        
        % if there is an abstract state...
        abstract_state(Formulas,Literals,NodeID,true),
        
        % where it is possible to expand an action...
        can_expand(Formulas,Literals,NodeID,Action,RegressedCondition,
                   NewNodeID),
        
        % then
        !,
        
        report_message(['Expanding action: \n',
                        '\t action     : ', Action, '\n',
                        '\t condition  : ', RegressedCondition, '\n',
                        '\t type       : ', Formulas, '\n',
                        '\t literals   : ', Literals, '\n',
                        '\t node       : ', NodeID, '\n',
                        '\t new node   : ', NewNodeID, '\n']),
        
        % create the corresponding transition(s)
        create_transitions(Formulas,Literals,NodeID,Action,NewNodeID).
        

% construction step: split types by some transition condition
construction_step :-
        
        % if there is an abstract state...
        abstract_state(Formulas,Literals,NodeID,true),
        
        % where we can split over a transition condition...
        can_split_transition(Formulas,Literals,NodeID,Action,
                             RegressedCondition),
        
        % then
        !,
        
        report_message(['Doing split over transition condition: \n',
                        '\t action   : ', Action, '\n',
                        '\t condition: ', RegressedCondition, '\n',
                        '\t type     : ', Formulas, '\n',
                        '\t literals : ', Literals, '\n',
                        '\t node     : ', NodeID, '\n']),
        
        % split states and transitions over this condition
        split(Formulas,RegressedCondition).


% construction step: split types by some property subformula
construction_step :-
        
        % if there is an abstract state...
        abstract_state(Formulas,Literals,NodeID,true),
        
        % where we can split over a property subformula...
        can_split_property(Formulas,Literals,RegressedFormula),
        
        % then
        !,
        
        report_message(['Doing split over property subformula: \n',
                        '\t property : ', RegressedFormula, '\n',
                        '\t type     : ', Formulas, '\n',
                        '\t literals : ', Literals, '\n',
                        '\t node     : ', NodeID, '\n']),
        
        % split states and transitions over this formula
        split(Formulas,RegressedFormula).

% is it possible to expand a transition?
can_expand(Formulas,Literals,NodeID,Action,RegressedCondition,
           NewNodeID) :- 
        
        % there is a possible outgoing transition...
        cg_edge(NodeID,Action,Condition,NewNodeID),

        % whose regressed condition is entailed...
        regression(Condition,Literals,RegressedCondition),
        is_entailed(Formulas,RegressedCondition),
        
        % and where the corresponding transition(s) do not yet exist
        not(abstract_trans(Formulas,Literals,NodeID,Action,
                           _NewLiterals,NewNodeID)).
        
% is it possible to split over a transition condition?
can_split_transition(Formulas,Literals,NodeID,Action,
                     RegressedCondition) :-

        % there is a possible outgoing transition...
        cg_edge(NodeID,Action,Condition,_NewNodeID),
        
        % whose (negated) regressed condition is not yet entailed
        % by the type formulas
        regression(Condition,Literals,RegressedCondition),
        not(is_entailed(Formulas,RegressedCondition)),
        not(is_entailed(Formulas,-RegressedCondition)).
        
% is it possible to split over a property subformula?
can_split_property(Formulas,Literals,RegressedFormula) :-
        
        % there is a property subformula
        property_subformula(Formula),
        
        % whose (negated) regressed condition is not yet entailed
        % by the type formulas
        regression(Formula,Literals,RegressedFormula),
        not(is_entailed(Formulas,RegressedFormula)),
        not(is_entailed(Formulas,-RegressedFormula)).
        
% split Formulas over RegressedCondition
split(Formulas,RegressedCondition) :-
        simplify(-RegressedCondition,NegRegressedCondition),
        retract(abstract_state(Formulas,Literals,NodeID,Fringe)),
        assert(abstract_state([RegressedCondition|Formulas],Literals,
                              NodeID,Fringe)),
        assert(abstract_state([NegRegressedCondition|Formulas],Literals,
                              NodeID,Fringe)),
        fail.

split(Formulas,RegressedCondition) :-
        simplify(-RegressedCondition,NegRegressedCondition),
        retract(abstract_trans(Formulas,Literals,NodeID,Action,
                               NewLiterals,NewNodeID)),
        assert(abstract_trans([RegressedCondition|Formulas],Literals,
                              NodeID,Action,NewLiterals,NewNodeID)), 
        assert(abstract_trans([NegRegressedCondition|Formulas],Literals,
                              NodeID,Action,NewLiterals,NewNodeID)), 
        fail.
        
split(Formulas,RegressedCondition) :-
        is_inconsistent([RegressedCondition|Formulas]),
        retractall(abstract_state([RegressedCondition|Formulas],_,_,_)),
        retractall(abstract_trans([RegressedCondition|Formulas],_,_,_,_)), 
        fail.
        
split(Formulas,RegressedCondition) :-
        simplify(-RegressedCondition,NegRegressedCondition),
        is_inconsistent([NegRegressedCondition|Formulas]),
        retractall(abstract_state([NegRegressedCondition|Formulas],_,_,_)),
        retractall(abstract_trans([NegRegressedCondition|Formulas],_,_,_,_)), 
        fail.

split(_,_).


% split over positive effect conditions
create_transitions(Formulas,Literals,NodeID,Action,NewNodeID) :-
        
        causes_true(Action,Fluent,Condition),
        regression(Condition,Literals,RegressedCondition),
        
        not(is_entailed(Formulas,RegressedCondition)),
        not(is_entailed(Formulas,-RegressedCondition)),
        
        !,
        
        report_message(['Doing split over positive action condition: \n',
                        '\t action   : ', Action, '\n',
                        '\t fluent   : ', Fluent, '\n',
                        '\t condition: ', RegressedCondition, '\n',
                        '\t type     : ', Formulas, '\n',
                        '\t literals : ', Literals, '\n',
                        '\t node     : ', NodeID, '\n']),
        
        split(Formulas,RegressedCondition),
        simplify(-RegressedCondition,NegRegressedCondition),
        
        create_transitions([RegressedCondition|Formulas],Literals,
                           NodeID,Action,NewNodeID),
        create_transitions([NegRegressedCondition|Formulas],Literals,
                           NodeID,Action,NewNodeID).

% split over negative effect conditions
create_transitions(Formulas,Literals,NodeID,Action,NewNodeID) :-
        
        causes_false(Action,Fluent,Condition),
        regression(Condition,Literals,RegressedCondition),
        
        not(is_entailed(Formulas,RegressedCondition)),
        not(is_entailed(Formulas,-RegressedCondition)),
        
        !,
        
        report_message(['Doing split over negative action condition: \n',
                        '\t action   : ', Action, '\n',
                        '\t fluent   : ', Fluent, '\n',
                        '\t condition: ', RegressedCondition, '\n',
                        '\t type     : ', Formulas, '\n',
                        '\t literals : ', Literals, '\n',
                        '\t node     : ', NodeID, '\n']),
        
        split(Formulas,RegressedCondition),
        simplify(-RegressedCondition,NegRegressedCondition),
        
        create_transitions([RegressedCondition|Formulas],Literals,
                           NodeID,Action,NewNodeID),
        create_transitions([NegRegressedCondition|Formulas],Literals,
                           NodeID,Action,NewNodeID).

% actually create transition
create_transitions(Formulas,Literals,NodeID,Action,NewNodeID) :-
        
        determine_effects(Formulas,Action,Effects),
        apply_effects(Literals,Effects,NewLiterals),
        
        !,
        
        assert(abstract_trans(Formulas,Literals,NodeID,Action,
                              NewLiterals,NewNodeID)),
        create_state_if_not_exists(Formulas,NewLiterals,NewNodeID).

% create a new abstract state if it does not exist already
create_state_if_not_exists(Formulas,Literals,NodeID) :-
        abstract_state(Formulas,Literals,NodeID,_Fringe), !.
create_state_if_not_exists(Formulas,Literals,NodeID) :- !,
        assert(abstract_state(Formulas,Literals,NodeID,true)).

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
        abstract_state(Formulas,Literals,NodeID,_Fringe),
        write(Stream, '\t'),
        write(Stream, (Formulas,Literals,NodeID)),
        write(Stream, ';\n'),
        fail.
write_nodes(_Stream).

write_edges(Stream) :-
        abstract_trans(Formulas,Literals,NodeID,Action,NewLiterals,NewNodeID),
        write(Stream, '\t'),
        write(Stream, (Formulas,Literals,NodeID)),
        write(Stream, ' -> '),
        write(Stream, (Formulas,NewLiterals,NewNodeID)),
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
%% Characteristic Graphs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


construct_characteristic_graph(ProgramName) :-
        
        % eliminate previous instances
        retractall(cg_node(_,_)),
        retractall(cg_edge(_,_,_,_)),
        retractall(cg_number_of_nodes(_)),
        
        % find the program with the given name
        program(ProgramName,Program),
        simplify_program(Program,SimplifiedProgram),
        
        % create initial node
        assert(cg_number_of_nodes(0)),
        cg_get_node_id(SimplifiedProgram,0),
        cg_draw_graph,
        
        iterate_cg_construction.
        
iterate_cg_construction :-
        cg_construction_step, 
        !,
        cg_draw_graph,
        iterate_cg_construction.
iterate_cg_construction.

cg_construction_step :-
        
        % there is some node
        cg_node(Program,ID),
        
        % whose program has a possible transition
        step(Program,Action,NewProgram,Condition),
        simplify(Condition,SimplifiedCondition),
        simplify_program(NewProgram,NewSimplifiedProgram),
        cg_get_node_id(NewSimplifiedProgram,NewID),
        
        % that is not yet in the graph
        not(cg_edge(ID,Action,SimplifiedCondition,NewID)),
        
        % then
        !,
                
        % create a new edge.
        assert(cg_edge(ID,Action,SimplifiedCondition,NewID)).

cg_get_node_id(Program,ID) :-
        cg_node(Program,ID), !.
cg_get_node_id(Program,ID) :-
        retract(cg_number_of_nodes(ID)),
        NextID is ID+1,
        assert(cg_number_of_nodes(NextID)),
        assert(cg_node(Program,ID)).

% draw characteristic graph using dot
cg_draw_graph :-
        cgraph_file(CGraphFile),
        open(CGraphFile, write, Stream),
        write(Stream, 'digraph G {\n'),
        cg_write_nodes(Stream),
        cg_write_edges(Stream),
        write(Stream, '}\n'),
        close(Stream).

cg_write_nodes(Stream) :-
        cg_node(_Program,ID),
        write(Stream, '\t'),
        write(Stream, ID),
        write(Stream, ';\n'),
        fail.
cg_write_nodes(_Stream).

cg_write_edges(Stream) :-
        cg_edge(ID,Action,_Condition,NewID),
        write(Stream, '\t'),
        write(Stream, ID),
        write(Stream, ' -> '),
        write(Stream, NewID),
        write(Stream, ' [label=\"'),
        write(Stream, Action),
        % write(Stream, ' / '),
        % write(Stream, Condition),
        write(Stream, '\"];\n'),
        fail.
cg_write_edges(_Stream).

cgraph_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/cgraph.dot', File).
        
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
        simplify(F,FS),
        assert(property_subformula(FS)).

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


% TODO: boolean combinations of CTL subformulae!

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% L reasoning with caching
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_entailed(Formulas,Formula) :-
        is_entailed_cached(Formulas,Formula,true), !.
is_entailed(Formulas,Formula) :-
        is_entailed_cached(Formulas,Formula,false), !, fail.
is_entailed(Formulas,Formula) :-
        entails_l(Formulas,Formula,Truth), !,
        assert(is_entailed_cached(Formulas,Formula,Truth)).

is_inconsistent(Formulas) :-
        is_inconsistent_cached(Formulas,true), !.
is_inconsistent(Formulas) :-
        is_inconsistent_cached(Formulas,false), !, fail.
is_inconsistent(Formulas) :-
        inconsistent_l(Formulas,Truth), !,
        assert(is_inconsistent_cached(Formulas,Truth)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% DL reasoning with caching
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TODO: incorporate standard names into dl.pl as in l.pl

stdnames_axioms(Axioms) :-
        findall(-(X=Y),
                (stdname(X),stdname(Y),not(X=Y),(X @< Y)),
                Axioms).

is_entailed(Formulas,Formula) :-
        is_entailed_cached(Formulas,Formula,true), !.
is_entailed(Formulas,Formula) :-
        is_entailed_cached(Formulas,Formula,false), !, fail.
is_entailed(Formulas,Formula) :-
        stdnames_axioms(StdAxioms),
        append(Formulas,StdAxioms,Axioms),
        dl_entails(Axioms,Formula), !,
        assert(is_entailed_cached(Formulas,Formula,true)).
is_entailed(Formulas,Formula) :-
        stdnames_axioms(StdAxioms),
        append(Formulas,StdAxioms,Axioms),
        not(dl_entails(Axioms,Formula)), !,
        assert(is_entailed_cached(Formulas,Formula,false)),
        fail.

is_inconsistent(Formulas) :-
        is_inconsistent_cached(Formulas,true), !.
is_inconsistent(Formulas) :-
        is_inconsistent_cached(Formulas,false), !, fail.
is_inconsistent(Formulas) :-
        stdnames_axioms(StdAxioms),
        append(Formulas,StdAxioms,Axioms),
        dl_inconsistent(Axioms), !,
        assert(is_inconsistent_cached(Formulas,true)).
is_inconsistent(Formulas) :-
        stdnames_axioms(StdAxioms),
        append(Formulas,StdAxioms,Axioms),
        not(dl_inconsistent(Axioms)), !,
        assert(is_inconsistent_cached(Formulas,false)),
        fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Regression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

determine_effects(Formulas,Action,Effects) :-
        findall(Effect,is_effect(Formulas,Action,Effect),Effects).

is_effect(Formulas,Action,Effect) :-
        causes_true(Action,Fluent,Condition),
        is_entailed(Formulas,Condition),
        Effect=Fluent.
is_effect(Formulas,Action,Effect) :-
        causes_false(Action,Fluent,Condition),
        is_entailed(Formulas,Condition),
        Effect=(-Fluent).

apply_effects(Literals,Effects,NewEffects) :- !,
        apply_neg_effects(Literals,Effects,Effects2),
        apply_pos_effects(Effects2,Effects,NewEffects2),
        sort(NewEffects2,NewEffects).

apply_neg_effects([-Lit|Literals],Effects,NewEffects) :-
        member(Lit,Effects), !,
        apply_neg_effects(Literals,Effects,NewEffects).
apply_neg_effects([-Lit|Literals],Effects,[-Lit|NewEffects]) :-
        apply_neg_effects(Literals,Effects,NewEffects).
apply_neg_effects([Lit|Literals],Effects,NewEffects) :-
        member(-Lit,Effects), !,
        apply_neg_effects(Literals,Effects,NewEffects).
apply_neg_effects([Lit|Literals],Effects,[Lit|NewEffects]) :-
        apply_neg_effects(Literals,Effects,NewEffects).
apply_neg_effects([],_Effects,[]).

apply_pos_effects([Lit|Literals],Effects,NewEffects) :-
        member(Lit,Effects), !,
        apply_pos_effects(Literals,Effects,NewEffects).
apply_pos_effects([Lit|Literals],Effects,[Lit|NewEffects]) :-
        apply_pos_effects(Literals,Effects,NewEffects).
apply_pos_effects([],Effects,Effects).

regression(F,E,R) :-
        regression_cached(F,E,R), !.
regression(F,E,R) :- !,
        regress(F,E,R1),
        simplify(R1,R),
        assert(regression_cached(F,E,R)).

regress(F1<=>F2,E,R1<=>R2) :- !,
        regress(F1,E,R1),
        regress(F2,E,R2).
regress(F1=>F2,E,R1=>R2) :- !,
        regress(F1,E,R1),
        regress(F2,E,R2).
regress(F1<=F2,E,R1<=R2) :- !,
        regress(F1,E,R1),
        regress(F2,E,R2).
regress(F1+F2,E,R1+R2) :- !,
        regress(F1,E,R1),
        regress(F2,E,R2).
regress(F1*F2,E,R1*R2) :- !,
        regress(F1,E,R1),
        regress(F2,E,R2).
regress(-F1,E,-R1) :- !,
        regress(F1,E,R1).
regress(some(Xs,F1),E,some(Xs,R1)) :- !,
        regress(F1,E,R1).
regress(all(Xs,F1),E,all(Xs,R1)) :- !,
        regress(F1,E,R1).
regress(X=Y,_,X=Y) :- !.
regress(true,_,true) :- !.
regress(false,_,false) :- !.

regress(concept_assertion(C,N),E,concept_assertion(CR,N)) :- !,
        regress_dl(C,E,CR).
regress(role_assertion(R,N1,N2),E,R) :- !,
        regress(concept_assertion(some(R,oneof([N2])),N1),E,R).

regress(Atom,E,(Atom+RP)*RN) :-
        regress_pos(Atom,E,RP),
        regress_neg(Atom,E,RN).

regress_pos(_Atom,[],false) :- !.
regress_pos(Atom,[L|E],(Equalities+RP)) :-
        Atom=..[F|Args],
        L=..[F|Args2],
        length(Args,N),
        length(Args2,N),!,
        pos_equalities(Args,Args2,Equalities),
        regress_pos(Atom,E,RP).
regress_pos(Atom,[_|E],RP) :-
        regress_pos(Atom,E,RP).

pos_equalities([Arg1|Args1],[Arg2|Args2],Equalities) :- 
        % same constants => true
        unique_names_assumption,
        atom(Arg1),
        atom(Arg2),
        Arg1=Arg2, !,
        pos_equalities(Args1,Args2,Equalities).
pos_equalities([Arg1|_Args1],[Arg2|_Args2],false) :- 
        % distinct constants => false
        unique_names_assumption,
        atom(Arg1),
        atom(Arg2),
        not(Arg1=Arg2), !.
pos_equalities([Arg1|Args1],[Arg2|Args2],(Arg1=Arg2)*Equalities) :-
        pos_equalities(Args1,Args2,Equalities).
pos_equalities([],[],true).

regress_neg(_Atom,[],true) :- !.
regress_neg(Atom,[-L|E],Inequalities*RN) :-
        Atom=..[F|Args],
        L=..[F|Args2],
        length(Args,N),
        length(Args2,N),!,
        neg_inequalities(Args,Args2,Inequalities),
        regress_neg(Atom,E,RN).
regress_neg(Atom,[_|E],RN) :-
        regress_neg(Atom,E,RN).

neg_inequalities([Arg1|Args1],[Arg2|Args2],Inequalities) :- 
        % same constants => false
        unique_names_assumption,
        atom(Arg1),
        atom(Arg2),
        Arg1=Arg2, !,
        neg_inequalities(Args1,Args2,Inequalities).
neg_inequalities([Arg1|_Args1],[Arg2|_Args2],true):- 
        % distinct constants => true
        unique_names_assumption,
        atom(Arg1),
        atom(Arg2),
        not(Arg1=Arg2), !.
neg_inequalities([Arg1|Args1],[Arg2|Args2],-(Arg1=Arg2)+Inequalities) :-
        neg_inequalities(Args1,Args2,Inequalities).
neg_inequalities([],[],false).

regress_dl(thing,_E,thing) :- !.
regress_dl(nothing,_E,nothing) :- !.
regress_dl(not(C),E,not(D)) :- !,
        regress_dl(C,E,D).
regress_dl(and(Cs),E,and(Rs)) :- !,
        regress_dl_list(Cs,E,Rs).
regress_dl(or(Cs),E,and(Rs)) :- !,
        regress_dl_list(Cs,E,Rs).
regress_dl(oneof(Ns),_E,oneof(Ns)) :- !.
regress_dl(some(R,C),E,Result) :- !,
        all_individuals(Ind),
        regress_dl(C,E,Res),
        findall(and([oneof([A]),some(R,and([oneof([B]),Res]))]),
                (member(A,Ind),
                 member(B,Ind),
                 not(member(role_assertion(R,A,B)),E),
                 not(member(-role_assertion(R,A,B)),E)),
                R3s),
        findall(and([oneof([A]),some(universal,and([oneof([B],Res)]))]),
                member(role_assertion(R,A,B),E),
                R4s),                    
        R1 = and([not(oneof(Ind)),some(R,Res)]),
        R2 = and([oneof(Ind),some(R,and([not(oneof(Ind)),Res]))]),
        R3 = or(R3s),
        R4 = or(R4s),
        Result = or([R1,R2,R3,R4]).
regress_dl(all(R,C),E,Result) :- !,
        all_individuals(Ind),
        regress_dl(C,E,Res),
        findall(or([not(oneof([A])),all(R,or([not(oneof([B])),Res]))]),
                (member(A,Ind),
                 member(B,Ind),
                 not(member(role_assertion(R,A,B)),E),
                 not(member(-role_assertion(R,A,B)),E)),
                R3s),
        findall(or([not(oneof([A])),some(universal,and([oneof([B],Res)]))]),
                member(role_assertion(R,A,B),E),
                R4s),                    
        R1 = or([oneof(Ind),all(R,Res)]),
        R2 = or([not(oneof(Ind)),all(R,or([oneof(Ind),Res]))]),
        R3 = or(R3s),
        R4 = and(R4s),
        Result = or([R1,R2,R3,R4]).
regress_dl(C,E,R) :- !,
        findall(A,member(-concept_assertion(C,A),E),PosInd),
        findall(B,member(concept_assertion(C,B),E),NegInd),
        R = or([and([C,not(oneof(NegInd))],oneof(PosInd))]).

regress_dl_list([C|Cs],E,[R|Rs]) :- !,
        regress_dl(C,E,R),
        regress_dl_list(Cs,E,Rs).
regress_dl_list([],_E,[]) :- !.

all_individuals(Ind) :- !,
        findall(N,stdname(N),Ind).

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
                property(PropName,ProgramName,Prop),
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
        abstract_state(Formulas,Literals,NodeID,_),
        retract(map_number_of_states(N)),
        N1 is N+1,
        assert(map_state(N,Formulas,Literals,NodeID)),
        assert(map_number_of_states(N1)),
        fail.
propositionalize_states.
        
propositionalize_transitions :-
        abstract_trans(Formulas,Literals,NodeID,Action,NewLiterals,
                       NewNodeID),
        map_state(S1,Formulas,Literals,NodeID),
        map_state(S2,Formulas,NewLiterals,NewNodeID),
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
        map_state(S,_Formulas,_Literals,_NodeID),
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
        map_state(N,Formulas,Literals,_NodeID),
        regression(Formula,Literals,RegressedFormula),
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
writeSpecProperty(Stream, F) :-
        no_temporal_operators(F),
        simplify(F,FS),
        property_subformula(FS),
        map_subformula(FormulaN,FS), !,
        write(Stream, FormulaN).

% TODO: boolean combintations of CTL formulae

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
        sub_string(Line,_,_,_,'is true').
get_truth_value([Line|_], false) :-
        sub_string(Line,_,_,_,'is false').
get_truth_value([_|Lines], Value) :-
        get_truth_value(Lines, Value).

get_counterexample(_Lines, true, [], nil).

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
        map_state(State,Formulas,_Literals,_NodeID).

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
