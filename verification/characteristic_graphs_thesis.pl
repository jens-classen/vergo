/**
 
characteristic_graphs_guards

This file provides predicates for using characteristic graphs 
as described in 

Jens Claßen: Planning and Verification in the Agent Language Golog.
PhD Thesis, Department of Computer Science, RWTH Aachen University,
2013.

@author  Jens Claßen
@license GPLv2

 **/

:- use_module('../transfinal/program_simplify').
:- use_module('../transfinal/transfinal_thesis').

:- multifile use_sink_states/0.

:- dynamic cg_node/4.
:- dynamic cg_edge/7.
:- dynamic cg_number_of_nodes/2.

construct_characteristic_graph(ProgramName) :-
        
        % eliminate previous instances
        retractall(cg_node(ProgramName,_,_,_)),
        retractall(cg_edge(ProgramName,_,_,_,_,_,_)),
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
        transition(Program,Action,NewProgram,Condition1,Vars,Condition2),

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

transition(Program,Action,NewProgram,Condition1,Vars,Condition2) :-
        use_sink_states, !,
        step(Program,Action,NewProgram,Condition1,Vars,Condition2).
transition(Program,Action,NewProgram,Condition1,Vars,Condition2) :-
        not(use_sink_states), !,
        trans(Program,Action,NewProgram,Condition1,Vars,Condition2).
is_final(_Program,false) :-
        use_sink_states, !.
is_final(Program,Final) :-
        not(use_sink_states), !,
        final(Program,Final).

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
        cg_edge(ProgramName,ID,Action,ID2,Cond1,Vars,Cond2),
        cg_print_edge(ID,Action,ID2,Cond1,Vars,Cond2),
        fail.
cg_print_edges2(_ProgramName).
cg_print_edge(ID,Action,ID2,Cond1,Vars,Cond2) :- !,
        write(ID),
        write(' --['),
        write(Action),
        write(']--> '),
        write(ID2),
        write('\n\t'),
        write(Cond1),
        write(' : '),
        write(Vars),
        write(' : '),
        write(Cond2),
        write('\n').

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
