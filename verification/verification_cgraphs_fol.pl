/**
 
verify_abstraction

This file implements a verification algorithm for Golog programs based
on the construction described in

Jens Claßen: Planning and Verification in the Agent Language Golog.
PhD Thesis, Department of Computer Science, RWTH Aachen University,
2013.

@author  Jens Claßen
@license GPL

 **/

:- use_module('../lib/utils').
:- use_module('../lib/env').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEG
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEU
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkPost
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Characteristic Graphs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
        simplify_max(Condition1,SimplifiedCondition1),
        SimplifiedCondition1\=false,
        simplify_max(Condition2,SimplifiedCondition2),
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
        simplify_max(Final,FinalS),
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
