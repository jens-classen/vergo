/**
 
fixpoint_ctl_thesis

This file implements a verification algorithm for Golog programs based
on the methods described in

Jens Claßen: Planning and Verification in the Agent Language Golog.
PhD Thesis, Department of Computer Science, RWTH Aachen University,
2013.

@author  Jens Claßen
@license GPLv2

 **/

:- use_module('../lib/utils').
:- use_module('../lib/env').
:- use_module('../projection/regression').
:- use_module('../logic/fobdd').
:- use_module('../logic/l').
:- use_module('../logic/l_kb').
:- use_module('../logic/una').

:- ['characteristic_graphs_thesis'].

:- discontiguous(check_label/5).
:- discontiguous(check/3).

:- dynamic cached_label/5.
:- dynamic cg_max_iteration/3.

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
verify(Program,Property) :- !,
        report_message(['Verifying property \'', Property,
                        '\' for program \'', Program, '\'...']),
        check(Program,Property,Result),
        entails_initially(Result,TruthValue),
        report_message(['Verified: \n',
                        '\t Property   : ', Property, '\n',
                        '\t Result Fml : ', Result, '\n',
                        '\t Truth Value: ', TruthValue, '\n']).        

/**
  * check(+Program,+Property,-Result)
  **/
check(Program,Property,Result) :-
        property(Property,Program,somepath(next(Phi))), !,
        report_message(['Checking \'', somepath(next(Phi)),
                        '\' on program \'', Program, '\'...']),
        check_ex(Program,Phi,Result).
        
check(Program,Property,Result) :-
        property(Property,Program,somepath(always(Phi))), !,
        report_message(['Checking \'', somepath(always(Phi)),
                        '\' on program \'', Program, '\'...']),
        check_eg(Program,Phi,Result).

check(Program,Property,Result) :-
        property(Property,Program,somepath(until(Phi1,Phi2))), !,
        report_message(['Checking \'', somepath(until(Phi1,Phi2)),
                        '\' on program \'', Program, '\'...']),
        check_eu(Program,Phi1,Phi2,Result).

check(Program,Property,Result) :-
        property(Property,Program,somepath(eventually(Phi))), !,
        report_message(['Checking \'', somepath(eventually(Phi)),
                        '\' on program \'', Program, '\'...']),
        check_eu(Program,true,Phi,Result).
        
check(Program,Property,Result) :-
        property(Property,Program,allpaths(next(Phi))), !,
        report_message(['Checking \'', allpaths(next(Phi)),
                        '\' on program \'', Program, '\'...']),
        check_ex(Program,-Phi,R),
        simplify_fml(-R,Result).
        
check(Program,Property,Result) :-
        property(Property,Program,allpaths(always(Phi))), !,
        report_message(['Checking \'', allpaths(always(Phi)),
                        '\' on program \'', Program, '\'...']),
        check_eu(Program,true,-Phi,R),
        simplify_fml(-R,Result).

check(Program,Property,Result) :-
        property(Property,Program,allpaths(until(Phi1,Phi2))), !,
        report_message(['Checking \'', allpaths(until(Phi1,Phi2)),
                        '\' on program \'', Program, '\'...']),
        check_eu(Program,-Phi2,(-Phi1)*(-Phi2),R1),
        check_eg(Program,-Phi2,R2),
        simplify_fml((-R1)*(-R2),Result).

check(Program,Property,Result) :-
        property(Property,Program,allpaths(eventually(Phi))), !,
        report_message(['Checking \'', allpaths(eventually(Phi)),
                        '\' on program \'', Program, '\'...']),
        check_eg(Program,-Phi,R),
        simplify_fml(-R,Result).

check(Program,Property,Result) :-
        property(Property,Program,postcond(Phi)), !,
        report_message(['Checking \'', postcond(Phi),
                        '\' on program \'', Program, '\'...']),
        check_post(Program,Phi,R),
        simplify_fml(R,Result).

check(Program,Property,Result) :-
        property(Property,Program,unipostcond(Phi)), !,
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
        cg_edge(P,N,A,M,C1,V,C2),
        cg_label(P,Phi,I,M,Psi),
        regress(C1*some(V,C2*after(A,Psi)),R),
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
%% Formula Representation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% use fol simplification
simplify_fml(F,R) :- !,
        apply_una(F,F2),
        minimize(F2,F3),
        apply_una(F3,R).
