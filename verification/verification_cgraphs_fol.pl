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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEU
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Characteristic Graphs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

construct_characteristic_graph(ProgramName) :-
        
        % eliminate previous instances
        retractall(cg_node(_,_)),
        retractall(cg_edge(_,_,_,_,_,_)),
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
        trans(Program,Action,NewProgram,Condition1,Vars,Condition2),
        simplify_max(Condition1,SimplifiedCondition1),
        simplify_max(Condition2,SimplifiedCondition2),
        simplify_program(NewProgram,NewSimplifiedProgram),
        cg_get_node_id(NewSimplifiedProgram,NewID),
        
        % that is not yet in the graph
        not(cg_edge(ID,Action,NewID,SimplifiedCondition1,Vars,
                    SimplifiedCondition2)),        
        
        % then
        !,
                
        % create a new edge.
        assert(cg_edge(ID,Action,NewID,SimplifiedCondition1,Vars,
                       SimplifiedCondition2)).

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
        cg_edge(ID,Action,NewID,_,_,_),
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
