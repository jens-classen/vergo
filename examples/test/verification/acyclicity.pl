/**

Simple action theory for unit-testing verification of acyclic action theories.

@author  Jens Claßen
@license GPLv2

**/
:- use_module('../../../verification/acyclic').

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

:- begin_tests('acyclic').

test(non_acyclic) :- !,
        retractall(acyclic:effect_description(_,_,_,_,_)),
        retractall(acyclic:bat_type(_)),
        acyclic:construct_characteristic_graph(main1),
        not(acyclic:preprocess_actions(main1)).

test(acyclic) :- !,
        retractall(acyclic:effect_description(_,_,_,_,_)),
        retractall(acyclic:bat_type(_)),
        acyclic:construct_characteristic_graph(main2),
        acyclic:preprocess_actions(main2),
        assertion(acyclic:bat_type(acyclic)).

:- end_tests('acyclic').
