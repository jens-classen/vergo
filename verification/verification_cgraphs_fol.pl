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

:- discontiguous(check_label/5).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Verification Algorithms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * check(+Program,+Property,-Result)
  **/
check(P,ex(Phi),Result) :-
        cg_label(P,ex(Phi),1,0,Result).

/**
  * check_label(+Program,+Property,+Iteration,+Node,-Formula)
  **/
check_label(P,ex(Phi),0,N,F) :-
        path_label(P,N,Path),
        simplify(Phi*Path,F).

check_label(P,ex(Phi),1,N,F) :-
        preimage(P,ex(Phi),0,N,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEG
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_label(_P,eg(_Phi),-1,_N,false).

check_label(_P,eg(Phi),0,_N,F) :-
        simplify(Phi,F).

check_label(P,eg(Phi),I,N,F) :-
        I > 0, !,
        I1 is I-1,
        cg_label(P,eg(Phi),I1,N,F1),
        preimage(P,eg(Phi),I1,F,F2),        
        simplify(F1*F2,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEU
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_label(_P,eu(_Phi1,_Phi2),-1,_N,true).

check_label(P,eu(_Phi1,Phi2),0,N,F) :-
        path_label(P,N,Path),
        simplify(Phi2*Path,F).

check_label(P,eu(Phi1,Phi2),I,N,F) :-
        I > 0, !,
        I1 is I-1,
        cg_label(P,eu(Phi1,Phi2),I1,N,Old),
        preimage(P,eu(Phi1,Phi2),I1,F,Pre),        
        simplify(Old+(Phi1*Pre),F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkPost
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Preimage
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

preimage(P,Phi,I,N,F) :-
        findall(Pre,
                (cg_edge(P,N,A,M,C1,V,C2),
                 cg_label(P,Phi,I,M,Psi),
                 regress(C1*some(V,C2*after(A,Psi)),R),
                 simplify(R,Pre)),
                PreList),
        disjoin(PreList,PreDis),
        simplify(PreDis,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Path
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% todo: implement this!
path_label(_,_,true).

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
        cg_draw_graph(ProgramName),
        
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
        simplify(Condition1,SimplifiedCondition1),
        SimplifiedCondition1\=false,
        simplify(Condition2,SimplifiedCondition2),
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
        simplify(Final,FinalS),
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
