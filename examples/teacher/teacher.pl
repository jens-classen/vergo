:- ['../../agents/kbagent_r'].

:- use_module('../../lib/utils').

rel_rigid(teach(_,_)).

initially(teach('#tom', '#sam')).
initially(teach('#tina', '#sue') * (teach('#tom', '#sue') + teach('#ted', '#sue'))).
initially(some(X,teach(X, '#sara'))).
initially(all(X,(teach(X, '#sandy') <=> (X = '#ted')))).
initially(all([X,Y],(teach(X, Y) => ((Y = '#sam') + (Y = '#sue') + (Y = '#sara') + (Y = '#sandy'))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing
% -------
% Reconstruction of full Example from Section 5.7.1 of
% 
% Hector J. Levesque and Gerhard Lakemeyer: The Logic of Knowledge
% Bases. MIT Press, 2001.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% TODO: TELL examples

/**
  * query(+Number,+Formula,+ExpectResultForAsk4)
  **/
query( 1,teach('#tom','#sam'),true).
query( 2,teach('#tom','#sandy'),false).
query( 3,teach('#tom','#sue'),unknown).
query( 4,know(teach('#tom','#sue')),false).
query( 5,some(X,teach(X,'#sara')),true).
query( 6,some(X,know(teach(X,'#sara'))),false).
query( 7,some(X,know(teach(X,'#sue'))),true).
query( 8,some(X,teach(X,'#sue') * -know(teach(X,'#sue'))),true).
query( 9,some(X,teach(X,'#sandy') * -know(teach(X,'#sandy'))),false).
query(10,some(X,teach(X,'#sam') * -know(teach(X,'#sam'))),unknown).
query(11,some(Y,know(all(X,teach(X,Y) => know(teach(X,Y))))),true).
query(12,some(Y,-(Y ='#sam') * -kwhether(all(X,teach(X,Y)=>know(teach(X,Y))))),false).
query(13,some(Y,know(some(X,teach(X,Y) * some(Z,-(Y=Z)*know(teach(X,Z)))))),true).
query(14,know(some(Y,all(X,teach(X,Y) => know(teach(X,Y))))),true). % from Exercise 8

def(kwhether(F),know(F)+know(-F)).

:- begin_tests(lkb, [setup(test_setup)]).

test(lkb_teacher_ask_eprover) :-
        report_message(['Testing with E theorem prover...\n']),
        set_reasoner(eprover),
        forall(query(N,_,_),
               test_query(N)).

test(lkb_teacher_ask_vampire) :-
        report_message(['Testing with Vampire theorem prover...\n']),
        set_reasoner(vampire),
        forall(query(N,_,_),
               test_query(N)).

test(lkb_teacher_ask_fo2solver) :-
        report_message(['Testing with FO2Solver...\n']),
        set_reasoner(fo2solver),
        forall(query(N,_,_),
               test_query(N)).

test_setup :-
        init,
        report_message(['KB:']),
        print_kb,
        report_message(['\n']).

test_query(Number) :-
        query(Number,Formula,ExpectedResult),
        ask4(Formula,Result),
        report_result(Number,Formula,Result,ExpectedResult),
        assertion(Result = ExpectedResult).

report_result(Number,Formula,Result,ExResult) :-
        report_message(['Query          : ', Number, '\n',
                        'Formula        : ', Formula, '\n',
                        'Result         : ', Result, '\n',
                        'Expected Result: ', ExResult, '\n']).

:- end_tests(lkb).
