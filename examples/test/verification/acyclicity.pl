/**

Simple action theory for unit-testing verification of acyclic action theories.

@author  Jens Claßen
@license GPLv2

**/
:- use_module('../../../verification/abstraction_acyclic').

rel_fluent(f1(_)).
rel_fluent(f2(_)).

poss(act1,true).
poss(act2,true).

causes_true(act1,f1(X),f2(X)).
causes_true(act1,f2(X),f1(X)).

causes_true(act2,f1(X),f2(X)).
causes_true(act2,f2(_),true).

program(main1,loop(act1)).
program(main2,loop(act2)).

:- begin_tests('abstraction_acyclic').

test(non_acyclic) :- !,
        retractall(abstraction_acyclic:effect_description(_,_,_,_,_)),
        abstraction_acyclic:construct_characteristic_graph(main1),
        abstraction_acyclic:determine_eff_con(main1),
        assertion(not(abstraction_acyclic:check_acyclicity)).

test(acyclic) :- !,
        retractall(abstraction_acyclic:effect_description(_,_,_,_,_)),
        abstraction_acyclic:construct_characteristic_graph(main2),
        abstraction_acyclic:determine_eff_con(main2),
        assertion(abstraction_acyclic:check_acyclicity).

:- end_tests('abstraction_acyclic').
