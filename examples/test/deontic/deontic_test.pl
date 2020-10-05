/**
 
Test Examples for Deontic Constraints

This file uses an approach for expressing deontic constraints by
means of conditionals over program expressions that induce a ranking
over the set of available actions, as described in

Jens Claßen and James Delgrande: "Dyadic Obligations over Complex
Actions as Deontic Constraints in the Situation Calculus", in
Proceedings of KR 2020, AAAI Press.

@author  Jens Claßen
@license GPLv2

 **/

:- use_module('../../../golog/deontic_constraints').
:- use_module('../../../lib/utils').
:- use_module('../../../logic/l').

:- discontiguous program/2.
:- discontiguous drule/2.
:- discontiguous expected_rank/4.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Forrester's Paradox
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

poss(murder(_,_),true).

program(any,pick(A,A)).
program(m,pick(X,murder('#jones',X))).
program(g,murder('#jones','#gently')).

drule(ex1,any ~> not(m)).
drule(ex1,m ~> g).

expected_rank(ex1,A,0,-some(X,(A=murder('#jones',X)))).
expected_rank(ex1,A,1,A=murder('#jones','#gently')).
expected_rank(ex1,A,2,some(X,(A=murder('#jones',X))*(-(X='#gently')))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Horty's Pizza/Asparagus Examples
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

poss(eat(_,_),true).

program(e,pick(X,pick(Y,eat(X,Y)))).
program(p,pick(Y,eat('#pizza',Y))).
program(h,pick(X,eat(X,'#hands'))).
program(ph,eat('#pizza','#hands')).

drule(ex2,e~>not(h)).
drule(ex2,p~>ph).

expected_rank(ex2,A,0, 
              all([X,Y],-(A=eat(X,Y))) + 
              some([X,Y],(A=eat(X,Y))*(-(X='#pizza'))*(-(Y='#hands')))).
% expected_rank(ex2,A,1,
%               A=eat('#pizza','#hands')). % (*)
expected_rank(ex2,A,1,
              some(X,A=eat(X,'#hands'))).
expected_rank(ex2,A,2,
              some(Y,(A=eat('#pizza',Y))*(-(Y='#hands'))) +
              some(Y,(A=eat(X,'#hands'))*(-(X='#pizza')))).

% (*): This condition reported in the paper is actually too strong.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Chisholm's Paradox
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

poss(help,true).
poss(tell,true).

drule(ex3,any '~a>' help).
drule(ex3,help '~b>' tell).
drule(ex3,not(help) '~b>' not(tell)).

%expected_rank(ex3, A,0,(A=help)*did('#tell')). % (**)
expected_rank(ex3, A,0,did('#any')*(A=help)*did('#tell')).
expected_rank(ex3,_A,1,-did('#tell')).
%expected_rank(ex3, A,2,(-(A=help))*did('#tell')). % (**)
expected_rank(ex3, A,2,(-did('#any')+(-(A=help)))*did('#tell')).

% (**): The ranking presented in the paper only refers to situations
%       after doing an action. To correctly capture ranks for
%       arbitrary situations, we have to include did('#any') here
%       (which will be false in the initial situation).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(deontic_conditionals).

test(ex1) :-
        check(ex1).
test(ex2) :-
        check(ex2).
test(ex3) :-
        check(ex3).

:- end_tests(deontic_conditionals).

check(Ex) :-
        findall(R,drule(Ex,R),Rules),
        construct_ranking(Rules,userdb),
        check_ranks(Ex).

check_ranks(Ex) :-
        expected_rank(Ex,A,R,Cond1),
        action_rank(A,R,Cond2),
        report_equivalence(A,R,Cond1,Cond2),
        fail.
check_ranks(_).

report_equivalence(A,R,Psi1,Psi2) :-
        valid_l(all(A,(Psi1<=>Psi2)),Truth), !,
        report_equivalence2(R,Psi1,Truth),
        assertion(valid_l(all(A,(Psi1<=>Psi2)),true)).
report_equivalence2(R,_Psi,true) :- !,
        report_message(['Condition for rank ', R, ' is as expected.']).
report_equivalence2(R,Psi,_) :- !,
        report_message(['Unexpected condition for rank ', R,': ', Psi]).
