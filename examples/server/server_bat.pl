/**

Simplified Server Domain Example

This domain is adapted from the example given in the paper

Benjamin Zarrieß and Jens Claßen:
Decidable Verification of Golog Programs over Non-Local Effect Actions.
In Proceedings of the 13th AAAI Conference on Artificial Intelligence (AAAI 2016),
pages 1109-1115, AAAI Press, 2016. 

for illustrating decidable verification using action theories with
acyclic, non-local effects.

The exact example, provided in server_orig_bat.pl, is not suited for
testing and experimentation because (a) NuSMV does not support the
verification of CTL* properties, (b) the theorem provers used in this
software do not support counting quantifiers, and (c) the induced
abstract transition system is very large and hence takes a long time
to construct.

The example in this file makes some simplification in terms of (a) the
predicates being used, (b) the formulas included in the initial
theory, (c) the possible exogenous actions, and (d) what properties
are to be verified, yet still includes acyclic (non-local-effect)
actions and a non-complete (open world) initial theory.

@author  Jens Claßen
@license GPLv2

**/
:- use_module('../../verification/abstraction_acyclic',
              [compute_abstraction/1,
               verify/3 as verify_abstraction]).
:- use_module('../../verification/characteristic_graphs_guards').
:- use_module('../../lib/utils').
:- use_module('../../logic/l').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

initially(hosts('#s1','#vm')).
initially(hosts('#s1','#p')).
initially(-some(X,hosts('#s2',X))).
initially(all(X,(runs('#vm',X)<=>(X='#p')))).
initially(avail('#s1')).
initially(avail('#s2')).
initially(avail('#vm')).
initially(avail('#p')).
initially(-ovl('#s1')).
initially(-ovl('#s2')).

rel_fluent(hosts(_,_)).
rel_fluent(avail(_)).
rel_fluent(ovl(_)).

rel_rigid(runs(_,_)).
rel_rigid(malware(_)).

poss(migr(_V,_S1,_S2),true).
poss(att(_S),true).
poss(repair(_S),true).

causes_true(migr(V,_S1,S2),avail(X),runs(V,X)*(-ovl(S2))).
causes_true(repair(S),avail(X),hosts(S,X)).
causes_false(att(S),avail(X),hosts(S,X)*some(Y,hosts(S,Y)*malware(Y))).

causes_true(att(S),ovl(X),(X=S)*some(Y,hosts(S,Y)*malware(Y))).
causes_false(repair(S),ovl(X),(X=S)).

causes_true(migr(V,_S1,S2),hosts(X,Y),(X=S2)*(runs(V,Y)+(Y=V))*(-ovl(S2))).
causes_false(migr(V,S1,S2),hosts(X,Y),(X=S1)*(runs(V,Y)+(Y=V))*(-ovl(S2))).

program(control,
        loop([test(some(X,hosts(X,'#vm')*ovl(X))),
              nondet([test(hosts('#s1','#vm')),migr('#vm','#s1','#s2')],
                     [test(hosts('#s2','#vm')),migr('#vm','#s2','#s1')])])).

program(exog,
        loop(nondet(att('#s1'),repair('#s1')))).

program(main,
        conc(control,exog)).

property(prop1,
         main,
         somepath(eventually(ovl('#s1')))).
property(prop2,
         main,
         allpaths(eventually(ovl('#s1')))).
property(prop3,
         main,
         somepath(always(ovl('#s1')))).
property(prop4,
         main,
         allpaths(always(ovl('#s1')))).
property(prop5,
         main,
         somepath(eventually(all(X,runs('#vm',X)=>avail(X))))).
property(prop6,
         main,
         somepath(always(all(X,runs('#vm',X)=>avail(X))))).
property(prop7,
         main,
         allpaths(eventually(all(X,runs('#vm',X)=>avail(X))))).
property(prop8,
         main,
         allpaths(always(all(X,runs('#vm',X)=>avail(X))))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

expected_outcome(prop1,false).
expected_outcome(prop2,false).
expected_outcome(prop3,false).
expected_outcome(prop4,false).
expected_outcome(prop5,true).
expected_outcome(prop6,true).
expected_outcome(prop7,true).
expected_outcome(prop8,false).

:- begin_tests('abstraction_acyclic').

test(abstraction) :- !,
        compute_abstraction(main),
        check_prop(prop1),
        check_prop(prop2),
        check_prop(prop3),
        check_prop(prop4),
        check_prop(prop5),
        check_prop(prop6),
        check_prop(prop7),
        check_prop(prop8).

check_prop(P) :-
        verify_abstraction(main,P,T),
        check_result(P,T), !.

check_result(P,T) :-
        assertion(expected_outcome(P,T)),
        check_result2(P,T).
check_result2(P,T) :-
        expected_outcome(P,T), !,
        report_message(info,['Outcome for ',P,' is as expected!\n']).
check_result2(P,_T) :- !,
        report_message(info,['Outcome for ',P,
                             ' is different from what expected!\n']).

:- end_tests('abstraction_acyclic').

:- begin_tests('acyclic_effects').

test(effects) :- !,
        construct_characteristic_graph(main),
        abstraction_acyclic:preprocess_actions(main),
        F = [runs('#vm','#p')],
        E = [(-,ovl('#s2'),true)],
        A = migr('#vm','#s1','#s2'),
        abstraction_acyclic:determine_effects(F,E,A,NE),
        abstraction_acyclic:apply_effects(E,NE,E2),
        assertion(member((+,avail(X),runs('#vm',X)),E2)),
        assertion(member((+,hosts(X,Y),(X='#s2')*(runs('#vm',Y)+(Y='#vm'))),E2)),
        assertion(member((-,hosts(X,Y),(runs('#vm',Y)+(Y='#vm'))*(X='#s1')),E2)).

:- end_tests('acyclic_effects').
