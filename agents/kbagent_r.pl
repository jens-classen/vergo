:- multifile initially/1.

:- dynamic(history/1).
:- dynamic(program/1).
:- dynamic(initially/1).

:- ['../projection/regression'].
:- ['../projection/reduction'].

:- use_module('../reasoning/fol').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Interaction Operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

init :- !,
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
        assert(initially(Result)).

execute(Action,SenseResult) :- !,
        retract(history(H)),
        senseresult2fml(SenseResult,Action,Fml),
        regress_s(H,Fml,Fml2),
        reduce_s(Fml2,Result),
        update_program(Action),
        assert(history([Action|H])),
        assert(initially(Result)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Program Operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

init(Program) :- !,
        assert(history([])),
        assert(program(Program)).

next_action(Action) :- !,
        program(Program),
        trans(Program,Action,_,Condition),
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
        reduce_s(know(Fml),Result).

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
        
reduce_s(Fml1,Fml2) :- !,
        reduce(Fml1,Fml3),
        simplify(Fml3,Fml2).

new_program('__undef',_,'__undef') :- !.
new_program(P,A,Q) :-
        trans(P,A,Q,_), !.
new_program(_,_,_,failed).

update_program(Action) :-
        retract(program(P)),
        new_program(P,Action,Q),
        assert(program(Q)).
