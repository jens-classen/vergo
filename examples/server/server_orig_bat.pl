/**

Server Domain Example

This domain is the example given in the paper

Benjamin Zarrieß and Jens Claßen:
Decidable Verification of Golog Programs over Non-Local Effect Actions.
In Proceedings of the 13th AAAI Conference on Artificial Intelligence (AAAI 2016),
pages 1109-1115, AAAI Press, 2016. 

for illustrating decidable verification using action theories with
acyclic, non-local effects.

Currently, the exact example cannot be verified because (a) NuSMV does
not support the verification of CTL* properties, and (b) the theorem
provers used in this software do not support counting quantifiers.
Furthermore, it is not suited for testing purposes because the induced
abstract transition system is very large and hence takes a long time
to construct.

For testing and experimentation, use the alternative simpler version
included in this directory.

@author  Jens Claßen
@license GPLv2

**/

:- use_module('../../verification/abstraction_acyclic',
              [compute_abstraction/1,
               verify/3 as verify_abstraction]).
:- use_module('../../lib/utils').
:- use_module('../../logic/l').

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.

initially(hosts('#s1','#vm')).
initially(hosts('#s1','#p')).
initially(runs('#vm','#p')).
initially(-avail('#p')).
initially(server('#s2')).
initially(-ovl('#s2')).
initially(all(Y,some(X,hosts(X,Y)))). % paper: exists <= 1 (C^2)
initially(all([X,Y],hosts(X,Y)=>(server(X)*(proc(Y)+vm(Y))))).

rel_fluent(hosts(_,_)).
rel_fluent(avail(_)).
rel_fluent(ovl(_)).

rel_rigid(runs(_,_)).
rel_rigid(server(_)).
rel_rigid(proc(_)).
rel_rigid(vm(_)).
rel_rigid(malware(_)).

poss(migr(_V,_S1,_S2),true).
poss(att(_S),true).
poss(repair(_S),true).

causes_true(migr(V,_S1,S2),avail(X),runs(V,X)*(-ovl(S2))).
causes_true(repair(S),avail(X),hosts(S,X)*proc(X)).
causes_false(att(S),avail(X),hosts(S,X)*proc(X)*some(Y,hosts(S,Y)*malware(Y))).

causes_true(att(S),ovl(X),(X=S)*some(Y,hosts(S,Y)*malware(Y))).
causes_false(repair(S),ovl(X),(X=S)).

causes_true(migr(V,_S1,S2),hosts(X,Y),(X=S2)*(runs(V,Y)+(Y=V))*(-ovl(S2))).
causes_false(migr(V,S1,S2),hosts(X,Y),(X=S1)*(runs(V,Y)+(Y=V))*(-ovl(S2))).

program(control,
        loop([test(some(X,hosts(X,'#vm')*ovl(X))),
              nondet([test(hosts('#s1','#vm')),migr('#vm','#s1','#s2')],
                     [test(hosts('#s2','#vm')),migr('#vm','#s2','#s1')])])).

program(exog,
        loop(nondet(att('#s1'),nondet(att('#s2'),nondet(repair('#s1'),repair('#s2')))))).

program(main,
        conc(control,exog)).

% NuSMV does not support CTL*!
property(prop,
         main,
         somepath(always(eventually(ovl('#s1')*ovl('#s2')))) =>
         somepath(always(eventually(all(X,runs('#vm',X)=>avail(X))))*
                  always(eventually(ovl('#s1')*ovl('#s2'))))).
