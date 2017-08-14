:- multifile initially/1.

:- dynamic(history/1).
:- dynamic(program/1).
:- dynamic(initially/1).

:- ['../projection/regression'].
:- ['../projection/reduction'].

:- use_module('../reasoning/l').
:- use_module('../reasoning/fol').
:- use_module('../reasoning/fobdd').
:- use_module('../reasoning/una').
:- use_module('../reasoning/cwa').

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

print_kb :-
        initially(F),
        write_readable(F),
        write('\n'),
        fail.
print_kb.

% todo: make this optional, may be costly
extend_initial_kb_by(Fml) :-
        entails_initially(Fml,true), !.
extend_initial_kb_by(Fml) :- !,
        assert(initially(Fml)).

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
        simplify(Fml4,Fml5),
        minimize(Fml5,Fml2).

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
