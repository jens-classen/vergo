/**

<module> kbagent

This module presents an interface to a knowledge-based agent in a
dynamic environment, where projection is handled using regression,
updates are done either by progression or regression (i.e., memorizing
the action history and regressing queries accordingly), and reasoning
about knowledge is reduced to first-order theorem proving according to
the representation theorem from

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
:- module(kbagent, [init/1, init/2, ask/2, tell/1, execute/2,
                    next_action/1, ask4/2, wh_ask/2, print_kb/0]).

:- dynamic(history_p/1).
:- dynamic(history_r/1).
:- dynamic(program/1).
:- dynamic(update/1).

:- use_module('../projection/progression').
:- use_module('../projection/reduction').
:- use_module('../projection/regression').
:- use_module('../kbs/l_kb').
:- use_module('../logic/cwa').
:- use_module('../logic/fobdd').
:- use_module('../logic/una').
:- use_module('../golog/transfinal_guards').

:- reexport('../logic/fol', [op(1130, xfy, <=>),
                             op(1110, xfy, <=),
                             op(1110, xfy, =>)]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Interaction Operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

init(Update) :- !,
        init(Update,'__undef').
init(Update,Program) :- !,
        initialize_kb(kb),
        retractall(history_p(_)),
        retractall(history_r(_)),
        retractall(program(_)),
        retractall(update(_)),
        assert(history_p([])),
        assert(history_r([])),
        assert(program(Program)),
        assert(update(Update)).

ask(Fml,Truth) :- !,
        history_r(H),
        regress_s(H,Fml,Fml2),
        reduce_s(Fml2,Result),
        entails_kb(kb,Result,Truth).

tell(Fml) :- !,
        history_r(H),
        regress_s(H,Fml,Fml2),
        reduce_s(Fml2,Result),
        extend_kb_by(kb,Result).

execute(Action,SenseResult) :-
        senseresult2fml(SenseResult,Action,Fml),
        history_r(H),
        regress_s(H,Fml,Fml2),
        reduce_s(Fml2,Result),
        extend_kb_by(kb,Result),
        (update(progression) ->
            progress(kb,Action,kb);true),
        update_program(Action),
        update_history(Action).

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
        history_r(H),
        regress_s(H,Fml,Fml2),
        reduce_s(know(Fml2),Result).

next_action(Action) :- !,
        program(Program),
        trans_s(Program,Action,Condition),
        ask(Condition,true).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Helper Predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

print_kb :-
        l_kb:print_kb(kb).

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
        reduce(kb,Fml1,Fml3),
        apply_cwa(kb,Fml3,Fml4),
        minimize(Fml4,Fml2).

trans_s(Program,Action,Condition) :-
        trans(Program,Guard,Action,_),
        guardcond(Guard,Cond1),
        minimize(Cond1,Condition).

new_program('__undef',_,'__undef') :- !.
new_program(P,A,Q) :-
        trans(P,_,A,R), !,
        simplify_program(R,Q).

new_program(_,_,_,failed).

update_program(Action) :-
        retract(program(P)),
        new_program(P,Action,Q),
        assert(program(Q)).

update_history(Action) :-
        update(regression), !,
        retract(history_r(H)),
        assert(history_r([Action|H])).

update_history(Action) :-
        update(progression), !,
        retract(history_p(H)),
        assert(history_p([Action|H])).
