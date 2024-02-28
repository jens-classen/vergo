/**

Repair Robot

This domain is a simple, non-epistemic variant of the repair robot
example from

Benjamin Zarrieß and Jens Claßen: Verification of Knowledge-Based
Programs over Description Logic Actions. In Proceedings of the
Twenty-Fourth International Joint Conference on Artificial
Intelligence (IJCAI 2015), AAAI Press, 2015.

Its purpose is to demonstrate and test verification by abstraction
based on description logics.

@author  Jens Claßen
@license GPLv2

**/

:- use_module('../../verification/abstraction_acyclic').

base_logic(dl).
use_sink_states.

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

% TBox
initially(subsumedBy(fault,or([crit_fault,uncrit_fault]))).
initially(subsumedBy(exists(has_fault,thing),system)).
initially(subsumedBy(system,only(has_fault,fault))).

% ABox
initially(concept_assertion(system,'#gear')).
initially(concept_assertion(not(on),'#gear')).
initially(concept_assertion(fault,'#blocked')).
initially(role_assertion(has_fault,'#gear','#fault1')).
initially(-concept_assertion(system,'#gear')).

rel_fluent(has_fault(_,_)).
rel_fluent(on(_)).
rel_rigid(fault(_)).
rel_rigid(crit_fault(_)).
rel_rigid(uncrit_fault(_)).
rel_rigid(system(_)).

poss(sense_fault(_,_),true).
poss(sense_on(_),true).
poss(repair(_,_),true).
poss(turn_on(_),true).
poss(raise_alarm(_),true).

causes_true(turn_on(X),
            on(X),
            concept_assertion(not(exists(has_fault,crit_fault)),X)).

causes_false(repair(X,Y),
             has_fault(X,Y),
             true).

program(main,
        [if(role_assertion(has_fault,'#gear','#fault1'),
            repair('#gear','#fault1')),
         turn_on('#gear')]
       ).

property(prop1,
         main,
         somepath(eventually(concept_assertion(on,'#gear')))).
