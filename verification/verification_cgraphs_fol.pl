/**
 
verify_cgraphs_fol

This file implements a verification algorithm for Golog programs based
on the methods described in

Jens Claßen: Planning and Verification in the Agent Language Golog.
PhD Thesis, Department of Computer Science, RWTH Aachen University,
2013.

@author  Jens Claßen
@license GPL

 **/

:- use_module('../lib/utils').
:- use_module('../lib/env').
:- ['../reasoning/bdd'].

:- discontiguous(check_label/5).
:- discontiguous(check/3).

:- dynamic cg_node/4.
:- dynamic cg_edge/7.
:- dynamic cg_number_of_nodes/2.
:- dynamic cached_label/5.
:- dynamic cg_max_iteration/3.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Verification Algorithms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
        
check(Program,Property,Result) :-
        property(Property,Program,somepath(next(Phi))), !,
        check_ex(Program,Phi,Result).
        
check(Program,Property,Result) :-
        property(Property,Program,somepath(always(Phi))), !,
        check_eg(Program,Phi,Result).

check(Program,Property,Result) :-
        property(Property,Program,somepath(until(Phi1,Phi2))), !,
        check_eu(Program,Phi1,Phi2,Result).

check(Program,Property,Result) :-
        property(Property,Program,somepath(eventually(Phi))), !,
        check_eu(Program,true,Phi,Result).
        
check(Program,Property,Result) :-
        property(Property,Program,allpaths(next(Phi))), !,
        check_ex(Program,-Phi,R),
        simplify_fml(-R,Result).
        
check(Program,Property,Result) :-
        property(Property,Program,allpaths(always(Phi))), !,
        check_eu(Program,true,-Phi,R),
        simplify_fml(-R,Result).

check(Program,Property,Result) :-
        property(Property,Program,allpaths(until(Phi1,Phi2))), !,
        check_eu(Program,-Phi2,(-Phi1)*(-Phi2),R1),
        check_eg(Program,-Phi2,R2),
        simplify_fml((-R1)*(-R2),Result).

check(Program,Property,Result) :-
        property(Property,Program,allpaths(eventually(Phi))), !,
        check_eg(Program,-Phi,R),
        simplify_fml(-R,Result).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * check(+Program,+Property,-Result)
  **/
check_ex(P,Phi,Result) :-
        cg_label(P,ex(Phi),1,0,Result).

/**
  * check_label(+Program,+Property,+Iteration,+Node,-Formula)
  **/
check_label(P,ex(Phi),0,N,F) :-
        path_label(P,N,Path),
        simplify_fml(Phi*Path,F).

check_label(P,ex(Phi),1,N,F) :-
        preimage(P,ex(Phi),0,N,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEG
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_eg(P,Phi,Result) :-
        check_iterate(P,eg(Phi),0,K),
        cg_label(P,eg(Phi),K,0,Result).

check_label(_P,eg(_Phi),-1,_N,false).

check_label(_P,eg(Phi),0,_N,F) :-
        simplify_fml(Phi,F).

check_label(P,eg(Phi),I,N,F) :-
        I > 0,
        I1 is I-1,
        cg_label(P,eg(Phi),I1,N,F1),
        preimage(P,eg(Phi),I1,F,F2),        
        simplify_fml(F1*F2,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEU
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_eu(P,Phi1,Phi2,Result) :-
        check_iterate(P,eu(Phi1,Phi2),0,K),
        cg_label(P,eu(Phi1,Phi2),K,0,Result).

check_label(_P,eu(_Phi1,_Phi2),-1,_N,true).

check_label(P,eu(_Phi1,Phi2),0,N,F) :-
        path_label(P,N,Path),
        simplify_fml(Phi2*Path,F).

check_label(P,eu(Phi1,Phi2),I,N,F) :-
        I > 0,
        I1 is I-1,
        cg_label(P,eu(Phi1,Phi2),I1,N,Old),
        preimage(P,eu(Phi1,Phi2),I1,F,Pre),        
        simplify_fml(Old+(Phi1*Pre),F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkPost
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_post(P,Phi,Result) :-
        check_iterate(P,post(Phi),0,K),
        cg_label(P,post(Phi),K,0,Result).

check_label(_P,post(_Phi),-1,_N,true).

check_label(P,post(Phi),0,N,F) :-
        simplify_fml(Phi,F).

check_label(P,post(Phi),I,N,F) :-
        I > 0,
        I1 is I-1,
        cg_label(P,post(Phi),I1,N,Old),
        preimage(P,post(Phi),I1,F,Pre),        
        simplify_fml(Old+Pre,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Path
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

path_label(P,N,L) :-
        cg_max_iteration(P,eg(true),K),
        cg_label(P,eg(true),K,N,L).

path_label(P,N,L) :-
        not(cg_max_iteration(P,eg(true),_)),
        check(P,eg(true),_),
        path_label(P,N,L).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Iteration
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: report labels, convergence

check_iterate(P,Phi,I,K) :- 
        check_not_converged(P,Phi,I), !,
        report_labels(P,Phi,I),
        I1 is I+1,
        check_labels(P,Phi,I1),
        check_iterate(P,Phi,I1,K).

check_iterate(P,Phi,I,I) :- !,
        report_message(['--------------------------------------']),
        report_message(['Labels have converged.\n']),
        assert(cg_max_iteration(P,Phi,I)).

check_not_converged(P,Phi,I) :-
        I1 is I-1,
        cg_node(P,_,_,N),
        cg_label(P,Phi,I,N,L),
        cg_label(P,Phi,I1,N,L1),
        not(equivalent(L,L1)).
        
% compute labels for all nodes
check_labels(P,Phi,I) :-
        cg_node(P,_,_,N),
        cg_label(P,Phi,I,N,_),
        fail.
check_labels(_,_,_).

report_labels(P,Phi,I) :-
        report_message(['--------------------------------------']),
        report_message(['Labels in iteration ', I, ':\n']),
        report_labels(P,Phi,I,0).
report_labels(P,Phi,I,N) :-
        cg_node(P,_,_,N),
        cg_label(P,Phi,I,N,L), !,
        report_message([N, ': ',L, '\n']),
        N1 is N+1,
        report_labels(P,Phi,I,N1).
report_labels(_,_,_,_) :- !.        

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Preimage
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

preimage(P,Phi,I,N,F) :-
        findall(Pre,
                (cg_edge(P,N,A,M,C1,V,C2),
                 cg_label(P,Phi,I,M,Psi),
                 regress(C1*some(V,C2*after(A,Psi)),R),
                 simplify_fml(R,Pre)),
                PreList),
        disjoin(PreList,PreDis),
        simplify_fml(PreDis,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Label caching
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cg_label(P,Phi,I,M,Psi) :-
        cached_label(P,Phi,I,M,Psi).

cg_label(P,Phi,I,M,Psi) :-
        check_label(P,Phi,I,M,Psi),
        not(cached_label(P,Phi,I,M,Psi)),
        assert(cached_label(P,Phi,I,M,Psi)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Characteristic Graphs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

construct_characteristic_graph(ProgramName) :-
        
        % eliminate previous instances
        retractall(cg_node(_,_,_,_)),
        retractall(cg_edge(_,_,_,_,_,_,_)),
        retractall(cg_number_of_nodes(_,_)),
        
        % find the program with the given name
        program(ProgramName,Program),
        simplify_program(Program,SimplifiedProgram),
        
        % create initial node
        assert(cg_number_of_nodes(ProgramName,0)),
        cg_get_node_id(ProgramName,SimplifiedProgram,0),
        cg_draw_graph(ProgramName), !,
        
        iterate_cg_construction(ProgramName).
        
iterate_cg_construction(ProgramName) :-
        cg_construction_step(ProgramName), 
        !,
        cg_draw_graph(ProgramName),
        iterate_cg_construction(ProgramName).
iterate_cg_construction(_ProgramName).

cg_construction_step(ProgramName) :-
        
        % there is some node
        cg_node(ProgramName,Program,_Final,ID),
        
        % whose program has a possible transition
        trans(Program,Action,NewProgram,Condition1,Vars,Condition2),
        simplify_fml(Condition1,SimplifiedCondition1),
        SimplifiedCondition1\=false,
        simplify_fml(Condition2,SimplifiedCondition2),
        SimplifiedCondition2\=false,
        simplify_program(NewProgram,NewSimplifiedProgram),
        cg_get_node_id(ProgramName,NewSimplifiedProgram,NewID),
        
        % that is not yet in the graph
        not(cg_edge(ProgramName,ID,Action,NewID,SimplifiedCondition1,
                    Vars,SimplifiedCondition2)),
        % then
        !,
                
        % create a new edge.
        assert(cg_edge(ProgramName,ID,Action,NewID,
                       SimplifiedCondition1,Vars,
                       SimplifiedCondition2)).

cg_get_node_id(ProgramName,Program,ID) :-
        cg_node(ProgramName,Program,_Final,ID), !.
cg_get_node_id(ProgramName,Program,ID) :-
        retract(cg_number_of_nodes(ProgramName,ID)),
        NextID is ID+1,
        assert(cg_number_of_nodes(ProgramName,NextID)),
        final(Program,Final),
        simplify_fml(Final,FinalS),
        assert(cg_node(ProgramName,Program,FinalS,ID)).

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
        cg_edge(ProgramName,ID,Action,NewID,_,_,_),
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
% simplify_fml(F,R) :- simplify(F,R).

% use bdd simplification
simplify_fml(F,R) :- 
        simplify(F,S), % first b/c of UNA
        simplify_formula_bdd(S,R).
