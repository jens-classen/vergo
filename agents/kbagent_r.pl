/**

kbagent_r

This file presents an interface to a knowledge-based agent in a
dynamic environment, where both projection and updates are handled
using regression, and reasoning about knowledge is reduced to
first-order theorem proving according to the representation theorem
from

Hector J. Levesque and Gerhard Lakemeyer: The Logic of Knowledge
Bases. MIT Press, 2001.

We thus follow Levesque's functional view on knowlede-based
systems. Details are described in

Jens Claßen and Gerhard Lakemeyer: Foundations for Knowledge-Based
Programs using ES. In Proceedings of the 10th Conference on Principles
of Knowledge Representation and Reasoning (KR 2006), pages 318-328,
AAAI Press, 2006.

Jens Claßen: Planning and Verification in the Agent Language Golog.
PhD Thesis, Department of Computer Science, RWTH Aachen University,
2013.

The code herein (and the imported files) represents a complete
re-implementation, but builds upon the lessons learnt from

Marius Grysla. Implementation and Evaluation of an ES-based Golog
System. Bachelor's Thesis, Department of Computer Science, RWTH Aachen
University, May 2010.

and an even earlier implementation of a propositional fragment due to
Yuxiao Hu (2006). The most important improvement is the usage of a
first-order extension of binary decision diagrams (BDDs) for keeping
the size of regressed formulas manageable (cf. the 'fobdd' module).

@author  Jens Claßen
@license GPLv2

 **/

:- dynamic(history/1).
:- dynamic(program/1).

:- use_module('../projection/reduction').
:- use_module('../projection/regression').
:- use_module('../logic/cwa').
:- use_module('../logic/l_kb').
:- use_module('../logic/fobdd').
:- use_module('../logic/una').

:- ['../transfinal/transfinal_simple'].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Interaction Operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

init :- !,
        initialize_kb,
        retractall(history(_)),
        retractall(program(_)),
        assert(history([])),
        assert(program('__undef')).

ask(Fml,Truth) :- !,
        history(H),
        regress_s(H,Fml,Fml2),
        reduce_s(Fml2,Result),
        entails_initially(Result,Truth).

tell(Fml) :- !,
        history(H),
        regress_s(H,Fml,Fml2),
        reduce_s(Fml2,Result),
        extend_initial_kb_by(Result).

execute(Action,SenseResult) :- !,
        retract(history(H)),
        senseresult2fml(SenseResult,Action,Fml),
        regress_s(H,Fml,Fml2),
        reduce_s(Fml2,Result),
        update_program(Action),
        assert(history([Action|H])),
        extend_initial_kb_by(Result).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Program Operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

init(Program) :- !,
        initialize_kb,
        assert(history([])),
        assert(program(Program)).

next_action(Action) :- !,
        program(Program),
        trans_s(Program,Action,Condition),
        ask(Condition,true).        

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Derived Operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ask4(Fml,Result) :- !,
        ask(Fml,TruthP),
        ask(-Fml,TruthN),
        ask4result(TruthP,TruthN,Result).

ask4result(true,true,inconsistent).
ask4result(true,false,true).
ask4result(false,true,false).
ask4result(false,false,unknown).

wh_ask(Fml,Result) :- !,
        history(H),
        regress_s(H,Fml,Fml2),
        reduce_s(know(Fml2),Result).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Helper Predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

senseresult2fml(Result,Action,Fml) :-
        sensing_style(truth),
        Result=true, !,
        Fml=sf(Action).
senseresult2fml(Result,Action,Fml) :-
        sensing_style(truth),
        Result=false, !,
        Fml=(-sf(Action)).
senseresult2fml(Result,Action,Fml) :-
        sensing_style(object), !,
        Fml=(sf(Action)=Result).

regress_s(H,Fml1,Fml2) :- !,
        regress(H,Fml1,Fml3),
        apply_una(Fml3,Fml2).
        % No apply_cwa here since may contain 'know'!
        % No minimize here since may contain 'know'!
        
reduce_s(Fml1,Fml2) :- !,
        reduce(Fml1,Fml3),
        apply_cwa(Fml3,Fml4),
        minimize(Fml4,Fml2).

trans_s(Program,Action,Condition) :-
        trans(Program,Action,_,Cond1),
        minimize(Cond1,Condition).

new_program('__undef',_,'__undef') :- !.
new_program(P,A,Q) :-
        trans(P,A,R,_), !,
        simplify_program(R,Q).
        
new_program(_,_,_,failed).

update_program(Action) :-
        retract(program(P)),
        new_program(P,Action,Q),
        assert(program(Q)).
