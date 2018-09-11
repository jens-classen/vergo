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
:- dynamic cached_label/5.
:- dynamic cg_max_iteration/3.

% TODO: is there a better way to do this?
% options
use_sink_states(false).
use_path_labels(false).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% To Do List
%% ----------
%% - todo: property(propX,somepath(main,always(F)))
%% - todo: remove defs without call to regress
%% - todo: pretty print formulas/programs (also using defs)
%% - todo: full check method
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
        check(Program,Property,Result),
        entails_initially(Result,TruthValue),
        report_message(['Verified: \n',
                        '\t Property   : ', Property, '\n',
                        '\t Result Fml : ', Result, '\n',
                        '\t Truth Value: ', TruthValue, '\n']).        

/**
  * check(+Program,+Property,-Result)
  **/
check(Program,somepath(next(Phi)),Result) :- !,
        report_message(['Checking \'', somepath(next(Phi)),
                        '\' on program \'', Program, '\'...']),
        check_ex(Program,Phi,Result).
        
check(Program,somepath(always(Phi)),Result) :- !,
        report_message(['Checking \'', somepath(always(Phi)),
                        '\' on program \'', Program, '\'...']),
        check_eg(Program,Phi,Result).

check(Program,somepath(until(Phi1,Phi2)),Result) :- !,
        report_message(['Checking \'', somepath(until(Phi1,Phi2)),
                        '\' on program \'', Program, '\'...']),
        check_eu(Program,Phi1,Phi2,Result).

check(Program,somepath(eventually(Phi)),Result) :- !,
        report_message(['Checking \'', somepath(eventually(Phi)),
                        '\' on program \'', Program, '\'...']),
        check_eu(Program,true,Phi,Result).
        
check(Program,allpaths(next(Phi)),Result) :- !,
        report_message(['Checking \'', allpaths(next(Phi)),
                        '\' on program \'', Program, '\'...']),
        check_ex(Program,-Phi,R),
        simplify_fml(-R,Result).
        
check(Program,allpaths(always(Phi)),Result) :- !,
        report_message(['Checking \'', allpaths(always(Phi)),
                        '\' on program \'', Program, '\'...']),
        check_eu(Program,true,-Phi,R),
        simplify_fml(-R,Result).

check(Program,allpaths(until(Phi1,Phi2)),Result) :- !,
        report_message(['Checking \'', allpaths(until(Phi1,Phi2)),
                        '\' on program \'', Program, '\'...']),
        check_eu(Program,-Phi2,(-Phi1)*(-Phi2),R1),
        check_eg(Program,-Phi2,R2),
        simplify_fml((-R1)*(-R2),Result).

check(Program,allpaths(eventually(Phi)),Result) :- !,
        report_message(['Checking \'', allpaths(eventually(Phi)),
                        '\' on program \'', Program, '\'...']),
        check_eg(Program,-Phi,R),
        simplify_fml(-R,Result).

check(Program,postcond(Phi),Result) :- !,
        report_message(['Checking \'', postcond(Phi),
                        '\' on program \'', Program, '\'...']),
        check_post(Program,Phi,R),
        simplify_fml(R,Result).

check(Program,unipostcond(Phi),Result) :- !,
        report_message(['Checking \'', unipostcond(Phi),
                        '\' on program \'', Program, '\'...']),
        check_post(Program,-Phi,R),
        simplify_fml(-R,Result).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * check_ex(+Program,+Property,-Result)
  **/
check_ex(P,Phi,Result) :-
        report_message(['--------------------------------------']),
        report_message(['CheckEX[',P,',',Phi,']:']),
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

/**
  * check_eg(+Program,+Property,-Result)
  **/
check_eg(P,Phi,Result) :-
        report_message(['--------------------------------------']),
        report_message(['CheckEG[',P,',',Phi,']:']),
        check_iterate(P,eg(Phi),0,K),
        cg_label(P,eg(Phi),K,0,Result).

check_label(_P,eg(_Phi),-1,_N,false).

check_label(_P,eg(Phi),0,_N,F) :-
        regress(Phi,PhiR),   % b/c of defs
        simplify_fml(PhiR,F).

check_label(P,eg(Phi),I,N,F) :-
        I > 0,
        I1 is I-1,
        cg_label(P,eg(Phi),I1,N,F1),
        preimage(P,eg(Phi),I1,N,F2),        
        simplify_fml(F1*F2,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkEU
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * check_eu(+Program,+Property,-Result)
  **/
check_eu(P,Phi1,Phi2,Result) :-
        report_message(['--------------------------------------']),
        report_message(['CheckEU[',P,',',Phi1,',',Phi2,']:']),
        check_iterate(P,eu(Phi1,Phi2),0,K),
        cg_label(P,eu(Phi1,Phi2),K,0,Result).

check_label(_P,eu(_Phi1,_Phi2),-1,_N,true).

check_label(P,eu(_Phi1,Phi2),0,N,F) :-
        path_label(P,N,Path),
        regress(Phi2,Phi2R),   % b/c of defs
        simplify_fml(Phi2R*Path,F).

check_label(P,eu(Phi1,Phi2),I,N,F) :-
        I > 0,
        I1 is I-1,
        cg_label(P,eu(Phi1,Phi2),I1,N,Old),
        preimage(P,eu(Phi1,Phi2),I1,N,Pre),  
        regress(Phi1,Phi1R),   % b/c of defs      
        simplify_fml(Old+(Phi1R*Pre),F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% checkPost
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * check_post(+Program,+Property,-Result)
  **/
check_post(P,Phi,Result) :-
        report_message(['--------------------------------------']),
        report_message(['CheckPost[',P,',',Phi,']:']),
        check_iterate(P,post(Phi),0,K),
        cg_label(P,post(Phi),K,0,Result).

check_label(_P,post(_Phi),-1,_N,true).

check_label(P,post(Phi),0,N,F) :-
        regress(Phi,PhiR),   % b/c if defs
        simplify_fml(PhiR,PhiRS),
        final_label(P,N,PhiRS,F).

check_label(P,post(Phi),I,N,F) :-
        I > 0,
        I1 is I-1,
        cg_label(P,post(Phi),I1,N,Old),
        preimage(P,post(Phi),I1,N,Pre),        
        simplify_fml(Old+Pre,F).

final_label(P,N,A,F) :-
        use_sink_states(false), !,
        cg_node(P,_Program,Final,N),
        simplify_fml(A*Final,F).
final_label(P,N,A,A) :-
        use_sink_states(true),
        cg_node(P,terminated,false,N), !.
final_label(P,N,_A,false) :-
        use_sink_states(true),
        cg_node(P,Program,false,N),
        Program \= terminated, !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Path
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * path_label(+Program,+Node,-Result)
  **/
path_label(P,N,Result) :-
        cg_max_iteration(P,path,I), !, % use cached values
        cg_label(P,path,I,N,Result).

path_label(P,N,Result) :-
        use_path_labels(true), !,
        report_message(['--------------------------------------']),
        report_message(['Computing PATH labels first...']),
        check_iterate(P,path,0,K),
        cg_label(P,path,K,N,Result),
        report_message(['Done computing PATH labels.']),
        report_message(['--------------------------------------']).
path_label(_Program,_Node,true) :-
        use_path_labels(false), !.

check_label(_P,path,-1,_N,false).

check_label(_P,path,0,_N,true).

check_label(P,path,I,N,F) :-
        I > 0,
        I1 is I-1,
        cg_label(P,path,I1,N,F1),
        preimage(P,path,I1,N,F2),        
        simplify_fml(F1*F2,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Iteration
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

check_iterate(P,Phi,I,K) :- 
        check_not_converged(P,Phi,I), !,
        report_labels(P,Phi,I),
        I1 is I+1,
        compute_labels(P,Phi,I1),
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
        equivalent_l(L,L1,false).
        
% compute labels for all nodes
compute_labels(P,Phi,I) :-
        compute_labels2(P,Phi,I,0).
compute_labels2(P,_Phi,_I,N) :-
        cg_number_of_nodes(P,N), !.
compute_labels2(P,Phi,I,N) :-
        cg_label(P,Phi,I,N,_),
        N1 is N+1,
        compute_labels2(P,Phi,I,N1).

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
                preimage_edge(P,Phi,I,N,Pre),
                PreList),
        disjoin(PreList,PreDis),
        simplify_fml(PreDis,F).

preimage_edge(P,Phi,I,N,Pre) :-
        cg_edge(P,N,G,A,M),
        cg_label(P,Phi,I,M,Psi),
        guardcond(G,after(A,Psi),GC),
        regress(GC,R),
        simplify_fml(R,Pre).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Label caching
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cg_label(P,Phi,I,M,Psi) :-
        cached_label(P,Phi,I,M,Psi), !.

cg_label(P,Phi,I,M,Psi) :-
        check_label(P,Phi,I,M,Psi),
        %not(cached_label(P,Phi,I,M,Psi)),
        assert(cached_label(P,Phi,I,M,Psi)).

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
