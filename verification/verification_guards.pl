/**
 
verification_guards

This file implements a verification algorithm for Golog programs based
on the methods described in

Jens Claßen: Planning and Verification in the Agent Language Golog.
PhD Thesis, Department of Computer Science, RWTH Aachen University,
2013.

with the difference that a new definition of characteristic graphs is
employed that uses "guards" on edges, i.e. sequences of test
 conditions and pick operators.

@author  Jens Claßen
@license GPL

 **/

:- use_module('../lib/utils').
:- use_module('../lib/env').
:- use_module('../reasoning/l_kb').
:- use_module('../reasoning/fobdd').
:- use_module('../reasoning/fol').

:- discontiguous(check_label/5).
:- discontiguous(check/3).

:- dynamic cg_node/4.
:- dynamic cg_edge/5.
:- dynamic cg_number_of_nodes/2.
:- dynamic labelset_maxid/1.
:- dynamic label/4.
:- dynamic labelset/3.

% TODO: is there a better way to do this?
% options
use_sink_states(false).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% To Do List
%% ----------
%% - todo: sink states / path labels?
%% - todo: characteristic graphs: subprograms as identifiers?
%% - todo: characteristic graphs: termconds outside of nodes
%% - todo: remove defs without call to regress
%% - todo: pretty print formulas/programs (also using defs)
%% - todo: work directly on BDDs
%% - todo: CTL*
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Verification Algorithms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * verify(+Program,+Property)
  **/
verify(Program,PropertyName) :- !,
        report_message(['Verifying property \'', PropertyName,
                        '\' for program \'', Program, '\'...']),
        property(PropertyName,Program,Property),
        check_ctl(Program,Property,LabelSet),
        labelset_initial(Program,LabelSet,Result),
        entails_initially(Result,TruthValue),
        report_message(['Verified: \n',
                        '\t Property   : ', Property, '\n',
                        '\t Result Fml : ', Result, '\n',
                        '\t Truth Value: ', TruthValue, '\n']).        

/**
  * check_ctl(+Program,+Property,-LabelSetID)
  *
  * Performs the verification procedure for CTL on Program
  * (whose characteristic graph must have been constructed)
  * and Property. Result is a numerical index that, together with
  * Program, identifies a label set.
  **/
check_ctl(Program,Psi,LabelSet) :-
        fluent_formula(Psi), !,
        labelset_create(Program,Psi,LabelSet).

check_ctl(Program,-Phi,LabelSet) :- !,
        check_ctl(Program,Phi,LabelSet1),
        labelset_negate(Program,LabelSet1,LabelSet).

check_ctl(Program,Phi1*Phi2,LabelSet) :- !,
        check_ctl(Program,Phi1,LabelSet1),
        check_ctl(Program,Phi2,LabelSet2),
        labelset_conjoin(Program,LabelSet1,LabelSet2,LabelSet).

check_ctl(Program,Phi1+Phi2,LabelSet) :- !,
        check_ctl(Program,Phi1,LabelSet1),
        check_ctl(Program,Phi2,LabelSet2),
        labelset_disjoin(Program,LabelSet1,LabelSet2,LabelSet).

check_ctl(Program,Phi1=>Phi2,LabelSet) :- !,
        check_ctl(Program,(-Phi1)+Phi2,LabelSet).

check_ctl(Program,Phi2<=Phi1,LabelSet) :- !,
        check_ctl(Program,(-Phi1)+Phi2,LabelSet).

check_ctl(Program,Phi1<=>Phi2,LabelSet) :- !,
        check_ctl(Program,(Phi1=>Phi2)*(Phi2=>Phi1),LabelSet).

check_ctl(Program,somepath(next(Phi)),LabelSet) :- !,
        check_ctl(Program,Phi,LabelSet1),
        labelset_preimage(Program,LabelSet1,LabelSet).

check_ctl(Program,somepath(always(Phi)),LabelSet) :- !,
        check_ctl(Program,Phi,LabelSet1),
        check_eg(Program,LabelSet1,LabelSet).

check_ctl(Program,somepath(until(Phi1,Phi2)),LabelSet) :- !,
        check_ctl(Program,Phi1,LabelSet1),
        check_ctl(Program,Phi2,LabelSet2),
        check_eu(Program,LabelSet1,LabelSet2,LabelSet).

check_ctl(Program,somepath(eventually(Phi)),LabelSet) :- !,
        check_ctl(Program,somepath(until(true,Phi)),LabelSet).

check_ctl(Program,allpaths(next(Phi)),LabelSet) :- !,
        check_ctl(Program,-somepath(next(-Phi)),LabelSet).

check_ctl(Program,allpaths(always(Phi)),LabelSet) :- !,
        check_ctl(Program,-somepath(until(true,-Phi)),LabelSet).

check_ctl(Program,allpaths(eventually(Phi)),LabelSet) :- !,
        check_ctl(Program,allpaths(until(true,Phi)),LabelSet).

check_ctl(Program,allpaths(until(Phi1,Phi2)),LabelSet) :- !,
        check_ctl(Program,
                  -somepath(until(-Phi2,(-Phi1)*(-Phi2))),
                  LabelSet1),
        check_ctl(Program,
                  -somepath(always(-Phi2)),
                  LabelSet2),
        labelset_conjoin(Program,LabelSet1,LabelSet2,LabelSet).

% check(Program,postcond(Phi),Result) :- !,
%         report_message(['Checking \'', postcond(Phi),
%                         '\' on program \'', Program, '\'...']),
%         check_post(Program,Phi,R),
%         simplify_fml(R,Result).

% check(Program,unipostcond(Phi),Result) :- !,
%         report_message(['Checking \'', unipostcond(Phi),
%                         '\' on program \'', Program, '\'...']),
%         check_post(Program,-Phi,R),
%         simplify_fml(-R,Result).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Label operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

labelset_create(Program,Formula,LabelSet) :-
        labelset(Program,Formula1,LabelSet),
        Formula == Formula1, !. % b/c of variables
labelset_create(Program,Formula,LabelSet) :- !,
        regress(Formula,FormulaR), % b/c of defs
        simplify_fml(FormulaR,FormulaS),
        labelset_increment(LabelSet),
        forall(cg_node(Program,_P,_F,NodeID),
               make_label(Program,NodeID,FormulaS,LabelSet)),
        assert(labelset(Program,Formula,LabelSet)).

labelset_negate(Program,LabelSet1,LabelSet) :-
        labelset(Program,-LabelSet1,LabelSet), !.
labelset_negate(Program,LabelSet1,LabelSet) :- !,
        labelset_increment(LabelSet),
        forall(cg_node(Program,_P,_F,NodeID),
               (label(Program,NodeID,Phi1,LabelSet1),
                simplify_fml(-Phi1,Fml),
                make_label(Program,NodeID,Fml,LabelSet))),
        assert(labelset(Program,-LabelSet1,LabelSet)).

labelset_conjoin(Program,LabelSet1,LabelSet2,LabelSet) :-
        labelset(Program,LabelSet1*LabelSet2,LabelSet), !.
labelset_conjoin(Program,LabelSet1,LabelSet2,LabelSet) :- !,
        labelset_increment(LabelSet),
        forall(cg_node(Program,_P,_F,NodeID),
               (label(Program,NodeID,Phi1,LabelSet1),
                label(Program,NodeID,Phi2,LabelSet2),
                simplify_fml(Phi1*Phi2,Fml),
                make_label(Program,NodeID,Fml,LabelSet))),
        assert(labelset(Program,LabelSet1*LabelSet2,LabelSet)).

labelset_disjoin(Program,LabelSet1,LabelSet2,LabelSet) :-
        labelset(Program,LabelSet1+LabelSet2,LabelSet), !.
labelset_disjoin(Program,LabelSet1,LabelSet2,LabelSet) :- !,
        labelset_increment(LabelSet),
        forall(cg_node(Program,_P,_F,NodeID),
               (label(Program,NodeID,Phi1,LabelSet1),
                label(Program,NodeID,Phi2,LabelSet2),
                simplify_fml(Phi1+Phi2,Fml),
                make_label(Program,NodeID,Fml,LabelSet))),
        assert(labelset(Program,LabelSet1+LabelSet2,LabelSet)).

labelsets_not_equivalent(Program,LabelSet1,LabelSet2) :-
        cg_node(Program,_P,_F,NodeID),
        label(Program,NodeID,Psi1,LabelSet1),
        label(Program,NodeID,Psi2,LabelSet2),
        equivalent_l(Psi1,Psi2,false).

labelset_initial(Program,LabelSet,Formula) :- !,
        label(Program,0,Formula,LabelSet).

labelset_preimage(Program,LabelSet1,LabelSet) :-
        labelset(Program,pre(LabelSet1),LabelSet), !.
labelset_preimage(Program,LabelSet1,LabelSet) :- !,
        labelset_increment(LabelSet),
        forall(cg_node(Program,_P,_F,NodeID),
               (preimage(Program,NodeID,LabelSet1,Pre),
                make_label(Program,NodeID,Pre,LabelSet))),
        assert(labelset(Program,pre(LabelSet1),LabelSet)).

preimage(Program,NodeID,LabelSet,PreimageFormula) :- !,
        findall(Pre,
                preimage_edge(Program,LabelSet,NodeID,Pre),
                PreList),
        disjoin(PreList,PreDis),
        simplify_fml(PreDis,PreimageFormula).

preimage_edge(Program,LabelSet,NodeID,Pre) :-
        cg_edge(Program,NodeID,Guard,Action,NewNodeID),
        label(Program,NewNodeID,LabelFml,LabelSet),
        guardcond(Guard,after(Action,LabelFml),GuardCond),
        regress(GuardCond,GuardCondR),
        simplify_fml(GuardCondR,Pre).

% Increments the maximal label set ID by 1 and returns the new value.
labelset_increment(ID) :-
        retract(labelset_maxid(OldMaxID)), !,
        ID is OldMaxID+1,
        assert(labelset_maxid(ID)).
labelset_increment(0) :- !,
        assert(labelset_maxid(0)).

% Make a new label, but only if it does not yet exist.
make_label(Program,Node,Formula,I) :-
        label(Program,Node,Formula,I), !. % label already exists
make_label(Program,Node,Formula,I) :- !,
        assert(label(Program,Node,Formula,I)). % create label

fluent_formula(F) :-
        F = true;
        F = false;
        isfluent(F);
        isrigid(F);
        F = poss(_);
        F = exo(_);
        F = sf(_);
        F = (_ = _).
fluent_formula(F) :-
        def(F,D), !,
        fluent_formula(D).
fluent_formula(-F) :- !,
        fluent_formula(F).
fluent_formula(F1+F2) :- !,
        fluent_formula(F1),
        fluent_formula(F2).
fluent_formula(F1*F2) :- !,
        fluent_formula(F1),
        fluent_formula(F2).
fluent_formula(F1=>F2) :- !,
        fluent_formula(F1),
        fluent_formula(F2).
fluent_formula(F1<=F2) :- !,
        fluent_formula(F1),
        fluent_formula(F2).
fluent_formula(F1<=>F2) :- !,
        fluent_formula(F1),
        fluent_formula(F2).
fluent_formula(some(_,F)) :- !,
        fluent_formula(F).
fluent_formula(all(_,F)) :- !,
        fluent_formula(F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEG
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * check_eg(+Program,+LabetSet1,-LabelSet)
  **/
check_eg(Program,LabelSet1,LabelSet) :- !,
        report_procedure(Program,'CheckEG',[LabelSet1]),
        labelset_create(Program,false,LabelSetFalse),
        check_eg_iterate(Program,0,LabelSetFalse,LabelSet1,LabelSet).

check_eg_iterate(Program,Iteration,Lold,Lcur,Lres) :-
        labelsets_not_equivalent(Program,Lold,Lcur), !,
        report_labels(Program,Lcur,Iteration),
        labelset_preimage(Program,Lcur,Lpre),
        labelset_conjoin(Program,Lcur,Lpre,Lnew),
        Iteration1 is Iteration+1,
        check_eg_iterate(Program,Iteration1,Lcur,Lnew,Lres).
check_eg_iterate(_Program,_Iteration,_Lold,Lcur,Lcur) :- !,
        report_convergence.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEU
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * check_eu(+Program,+LabelSet1,+LabelSet2,-LabelSet)
  **/
check_eu(Program,LabelSet1,LabelSet2,LabelSet) :- !,
        report_procedure(Program,'CheckEU',[LabelSet1,LabelSet2]),
        labelset_create(Program,true,LabelSetTrue),
        check_eu_iterate(Program,0,LabelSet1,LabelSetTrue,LabelSet2,LabelSet).

check_eu_iterate(Program,Iteration,L1,Lold,Lcur,Lres) :-
        labelsets_not_equivalent(Program,Lold,Lcur), !,
        report_labels(Program,Lcur,Iteration),
        labelset_preimage(Program,Lcur,Lpre),
        labelset_conjoin(Program,L1,Lpre,Ltmp),
        labelset_disjoin(Program,Lcur,Ltmp,Lnew),
        Iteration1 is Iteration+1,
        check_eu_iterate(Program,Iteration1,L1,Lcur,Lnew,Lres).
check_eu_iterate(_Program,_Iteration,_L1,_Lold,Lcur,Lcur) :- !,
        report_convergence.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Debugging output
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

report_procedure(Program,Procedure,Inputs) :-
        report_message(['--------------------------------------']),
        labelsets2fmls(Program,Inputs,Fmls),
        report_message([Procedure,'[',Program,',',Fmls,']:']).

report_convergence :-
        report_message(['--------------------------------------']),
        report_message(['Labels have converged.\n']).

report_labels(Program,LabelSet,Iteration) :-
        report_message(['--------------------------------------']),
        report_message(['Labels in iteration ', Iteration, ':\n']),
        report_labels(Program,LabelSet,Iteration,0).
report_labels(Program,LabelSet,Iteration,Node) :-
        cg_node(Program,_,_,Node),
        label(Program,Node,Formula,LabelSet), !,
        report_message([Node, ': ',Formula, '\n']),
        Node1 is Node+1,
        report_labels(Program,LabelSet,Iteration,Node1).
report_labels(_,_,_,_) :- !.        

labelsets2fmls(_Program,[],[]).
labelsets2fmls(Program,[L|Ls],[Fml|Fmls]) :-
        labelset(Program,Fml,L),
        labelsets2fmls(Program,Ls,Fmls).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Characteristic Graphs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

construct_characteristic_graph(ProgramName) :-
        
        % eliminate previous instances
        retractall(cg_node(ProgramName,_,_,_)),
        retractall(cg_edge(ProgramName,_,_,_,_)),
        retractall(cg_number_of_nodes(ProgramName,_)),
        
        % find the program with the given name
        program(ProgramName,Program),
        simplify_program(Program,SimplifiedProgram),
        
        % create initial node
        assert(cg_number_of_nodes(ProgramName,0)),
        cg_get_node_id(ProgramName,SimplifiedProgram,0), !,
        
        iterate_cg_construction(ProgramName).
        
iterate_cg_construction(ProgramName) :-
        cg_construction_step(ProgramName), !,
        iterate_cg_construction(ProgramName).
iterate_cg_construction(ProgramName) :-
        cg_print_graph(ProgramName), !.

cg_construction_step(ProgramName) :-
        
        % there is some node
        cg_node(ProgramName,Program,_Final,ID),
        
        % whose program has a possible transition
        transition(Program,Guard,Action,NewProgram),

        simplify_guard(Guard,SimplifiedGuard),
        SimplifiedGuard \= [test(false)],
        simplify_program(NewProgram,NewSimplifiedProgram),
        cg_get_node_id(ProgramName,NewSimplifiedProgram,NewID),
        
        % that is not yet in the graph
        not(cg_edge(ProgramName,ID,SimplifiedGuard,Action,NewID)),
        % then
        !,
                
        % create a new edge.
        assert(cg_edge(ProgramName,ID,SimplifiedGuard,Action,NewID)).

transition(Program,Guard,Action,NewProgram) :-
        use_sink_states(true), !,
        step(Program,Guard,Action,NewProgram).
transition(Program,Guard,Action,NewProgram) :-
        use_sink_states(false), !,
        trans(Program,Guard,Action,NewProgram).
is_final(_Program,false) :-
        use_sink_states(true), !.
is_final(Program,Final) :-
        use_sink_states(false), !,
        final(Program,Final).

simplify_guard([],[]) :- !.
simplify_guard([pick(V),test(F)|G],R) :- %push picks inwards when possible
        free_variables(F,FVs),
        not(member2(V,FVs)), !,
        simplify_guard([test(F),pick(V)|G],R).
simplify_guard([test(F1),test(F2)|G],R) :- !,
        simplify_guard([test(F1*F2)|G],R).
simplify_guard([test(F)|_],[test(false)]) :-
        simplify_fml(F,false), !.
simplify_guard([test(F)|G],[test(FS)|R]) :- !,
        simplify_fml(F,FS),
        simplify_guard(G,R).
simplify_guard([pick(V)|G],[pick(V)|R]) :- !,
        simplify_guard(G,R).

cg_get_node_id(ProgramName,Program,ID) :-
        cg_node(ProgramName,Program,_Final,ID), !.
cg_get_node_id(ProgramName,Program,ID) :-
        retract(cg_number_of_nodes(ProgramName,ID)),
        NextID is ID+1,
        assert(cg_number_of_nodes(ProgramName,NextID)),
        is_final(Program,Final),
        simplify_fml(Final,FinalS),
        assert(cg_node(ProgramName,Program,FinalS,ID)).

% print description of characteristic graph to console
cg_print_graph(ProgramName) :- !,
        write('================================================\n'),
        write('Characteristic graph for program \''),
        write(ProgramName),
        write('\':\n'),
        cg_print_nodes(ProgramName),
        cg_print_edges(ProgramName),
        write('================================================\n').

cg_print_nodes(ProgramName) :- !,
        write('------------------------------------------------\n'),
        write('Nodes:\n'),
        cg_number_of_nodes(ProgramName,N),
        cg_print_nodes(ProgramName,0,N),
        write('------------------------------------------------\n').
cg_print_nodes(ProgramName,I,N) :-
        I < N, !,
        cg_node(ProgramName,Program,Final,I),
        cg_print_node(Program,Final,I),
        I1 is I+1,
        cg_print_nodes(ProgramName,I1,N).
cg_print_nodes(_ProgramName,N,N) :- !.
cg_print_node(Program,Final,ID) :- !,
        write(ID),
        write(': '),
        write(Program),
        write('\n\t'),
        write(Final),
        write('\n').

cg_print_edges(ProgramName) :- !,
        write('Edges:\n'),
        cg_print_edges2(ProgramName).
cg_print_edges2(ProgramName) :-
        cg_edge(ProgramName,ID,Guard,Action,ID2),
        cg_print_edge(ID,Guard,Action,ID2),
        fail.
cg_print_edges2(_ProgramName).
cg_print_edge(ID,Guard,Action,ID2) :- !,
        write(ID),
        write(' --['),
        cg_print_guarded_action(Guard,Action),
        write(']--> '),
        write(ID2),
        write('\n').

cg_print_guarded_action([],Action) :- !,
        write(Action).
cg_print_guarded_action([pick(V)|Gs],Action) :- !,
        write(pick(V)),
        write(':'),
        cg_print_guarded_action(Gs,Action).
cg_print_guarded_action([test(F)|Gs],Action) :- !,
        write(F),
        write(':'),
        cg_print_guarded_action(Gs,Action).

% draw characteristic graph using dot
cg_draw_graph(ProgramName) :-
        cgraph_file(CGraphFile,ProgramName),
        open(CGraphFile, write, Stream),
        write(Stream, 'digraph G {\n'),
        cg_write_nodes(Stream,ProgramName),
        cg_write_edges(Stream,ProgramName),
        write(Stream, '}\n'),
        close(Stream).

cg_write_nodes(Stream,ProgramName) :-
        cg_node(ProgramName,_Program,_Final,ID),
        write(Stream, '\t'),
        write(Stream, ID),
        write(Stream, ';\n'),
        fail.
cg_write_nodes(_Stream,_ProgramName).

cg_write_edges(Stream,ProgramName) :-
        cg_edge(ProgramName,ID,_,Action,NewID),
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
cg_write_edges(_ProgramName,_Stream).

cgraph_file(File,ProgramName) :-
        temp_dir(TempDir),
        atom_string(ProgramName,ProgramNameS),
        string_concat('/', ProgramNameS, S),
        string_concat(S, '_cgraph.dot', FileName),
        string_concat(TempDir, FileName, File).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Formula Representation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% use fol simplification
simplify_fml(F,R) :- !,
        apply_una(F,F2),
        minimize(F2,F3),
        apply_una(F3,R).
