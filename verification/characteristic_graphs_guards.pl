/**
 
<module> characteristic_graphs_guards

This module provides predicates for using characteristic graphs that
use "guards" on edges, i.e. sequences of test conditions and pick
operators.

@author  Jens Claßen
@license GPLv2

 **/
:- module(characteristic_graphs_guards,
          [construct_characteristic_graph/1,
           cg_print_graph/1,
           cg_draw_graph/1,
           cg_node/4,
           cg_edge/5,
           cg_number_of_nodes/2]).

:- reexport('../golog/transfinal_guards',
            [guardcond/2, guardcond/3]).

:- use_module('../lib/utils').
:- use_module('../lib/env').
:- use_module('../logic/l').
:- use_module('../golog/program_simplify').
:- use_module('../golog/transfinal_guards').

:- multifile user:use_sink_states/0.

:- dynamic cg_node/4.
:- dynamic cg_edge/5.
:- dynamic cg_number_of_nodes/2.

/**
  * cg_node(?ProgramName,?Program,?Final,?ID) is nondet.
  *
  * Facts of this dynamic predicate represent a single node each. They
  * will be created when calling construct_characteristic_graph/1.
  *
  * @arg ProgramName the name of a program, defined by the user via a
  *                  fact over the predicate program/2
  * @arg Program     the program expression representing what remains
  *                  to be executed at this node
  * @arg Final       a formula expressing under what condition program
  *                  execution may terminate at this node
  * @arg ID          a numerical ID that is unique for ProgramName;
  *                  nodes are numbered consecutively, starting at 0
  *                  (representing the initial node)
  */

/**
  * cg_edge(?ProgramName,?FromID,?Guard,?Action,?ToID) is nondet.
  *
  * Facts of this dynamic predicate represent a single edge each. They
  * will be created when calling construct_characteristic_graph/1.
  *
  * @arg ProgramName the name of a program, defined by the user via a
  *                  fact over the predicate program/2
  * @arg FromID      the ID of the node from which the edge starts
  * @arg Guard       a guard for the edge, a sequence (list) of pick
  *                  operators and test conditions
  * @arg Action      an action term
  * @arg ToID        the ID of the node to where the edge leads 
 **/

/**
  * cg_number_of_nodes(?ProgramName,?Number) is nondet.
  *
  * A fact of this dynamic predicate represents the number of nodes in
  * a characteristic graph. It will be created when calling
  * construct_characteristic_graph/1. For a graph with N nodes, node
  * IDs will be 0,...,N-1, where 0 represents the initial node.
  *
  * @arg ProgramName the name of a program, defined by the user via a
  *                  fact over the predicate program/2
  * @arg Number      the number of nodes in the graph
 **/

/**
  * construct_characteristic_graph(+ProgramName) is det.
  *
  * Constructs the characteristic graph for the program of the given
  * name. Nodes and edges will be generated in the form of newly
  * created facts for the dynamic predicates cg_node/4 and cg_edge/5,
  * as well as cg_number_of_nodes/2, deleting any previous instances
  * for a program of the same name.
  *
  * @arg ProgramName the name of a program, defined by the user via a
  *                  fact over the predicate program/2
 **/
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
        user:use_sink_states, !,
        step(Program,Guard,Action,NewProgram).
transition(Program,Guard,Action,NewProgram) :-
        not(user:use_sink_states), !,
        trans(Program,Guard,Action,NewProgram,offline).
is_final(_Program,false) :-
        user:use_sink_states, !.
is_final(Program,Final) :-
        not(user:use_sink_states), !,
        final(Program,Final).

simplify_guard([],[]) :- !.
simplify_guard([pick(V),test(F)|G],R) :- %push picks inwards when possible
        free_variables(F,FVs),
        not(member2(V,FVs)), !,
        simplify_guard([test(F),pick(V)|G],R).
simplify_guard([test(F1),test(F2)|G],R) :- !,
        simplify_guard([test(F1*F2)|G],R).
simplify_guard([test(F)|_],[test(false)]) :-
        simplify(F,false), !.
simplify_guard([test(F)|G],[test(FS)|R]) :- !,
        simplify(F,FS),
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
        simplify(Final,FinalS),
        assert(cg_node(ProgramName,Program,FinalS,ID)).

/**
  * cg_print_graph(+ProgramName) is det.
  *
  * Prints a textual representation of the characteristic graph for
  * the program of the given name to standard output.
  *
  * @arg ProgramName the name of a program, defined by the user via a
  *                  fact over the predicate program/2
 */
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

/**
  * cg_draw_graph(+ProgramName) is det.
  *
  * Generates a dot file in the temp directory for drawing the
  * characteristic graph for the program of the given name.
  *
  * @arg ProgramName the name of a program, defined by the user via a
  *                  fact over the predicate program/2
 */
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
