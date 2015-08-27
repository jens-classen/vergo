:- multifile initially/1.

:- dynamic(history/1).
:- dynamic(initially/1).

:- ['../projection/regression'].
:- ['../projection/reduction'].

:- use_module('../reasoning/fol').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Interaction Operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

init :-
        assert(history([])).


ask(Fml,Truth) :- !,
        history(History),
        regress(History,Fml,RegFml),
        reduce(RegFml,Result),
        entails_initially(Result,Truth).

tell(Fml) :- !,
        history(History),
        regress(History,Fml,RegFml),
        reduce(RegFml,Result),
        assert(initially(Result)).

execute(Action,SenseResult) :- !,
        retract(history(History)),
        senseresult2fml(SenseResult,Action,SRFml),
        regress(History,SRFml,RegFml),
        reduce(RegFml,Result),
        assert(history([Action|History])),
        assert(initially(Result)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Helper Predicates
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
        reduce(know(Fml),Result).

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