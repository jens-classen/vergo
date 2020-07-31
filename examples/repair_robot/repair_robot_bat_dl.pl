% verification algorithm
:- ['../../verification/abstraction_local-effect'].

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rigid_r/1.


% TBox
initially(subsumedBy(fault,or([crit_fault,uncrit_fault]))).
initially(subsumedBy(some(has_fault,thing),system)).
initially(subsumedBy(system,all(has_fault,fault))).

% ABox
initially(concept_assertion(system,gear)).
initially(concept_assertion(not(on),gear)).
initially(concept_assertion(fault,blocked)).
initially(role_assertion(has_fault,gear,fault1)).

initially(-concept_assertion(system,gear)).

fluent_r(has_fault).
fluent_c(on).
rigid_c(fault).
rigid_c(crit_fault).
rigid_c(uncrit_fault).
rigid_c(system).

poss(sense_fault(_,_),true).
poss(sense_on(_),true).
poss(repair(_,_),true).
poss(turn_on(_),true).
poss(raise_alarm(_),true).

causes_true(turn_on(X),
            on(X),
            concept_assertion(not(some(has_fault,crit_fault)),X)).

causes_false(repair(X,Y),
             has_fault(X,Y),
             true).

stdname(system).
stdname(gear).
stdname(blocked).
stdname(fault1).

program(main,
        [if(role_assertion(has_fault,gear,fault1),
            repair(gear,fault1)),
         turn_on(gear)]
       ).

property(prop1,
         main,
         eventually(concept_assertion(on,gear))).

test :- 
        findall(Axiom,
                initially(Axiom),
                Axioms),
        dl_consistent(Axioms).
