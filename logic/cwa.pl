%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Closed-World Assumption
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
:- module(cwa, [apply_cwa/2]).

:- use_module('../lib/utils').
:- use_module('../logic/l').
:- use_module('../projection/regression', [isfluent/1,isrigid/1]).

:- multifile user:cwa/1.

% replace atoms for which CWA holds by their truth value
% note: not in regression operator because may not be in
% initial situation (e.g. fixpoint loop in verification)
apply_cwa(true,true) :- !.
apply_cwa(false,false) :- !.
apply_cwa(poss(A),poss(A)) :- !.
apply_cwa(exo(A),exo(A)) :- !.
apply_cwa(sf(A),sf(A)) :- !.
apply_cwa(F,true) :- 
        ground(F),
        (isfluent(F);isrigid(F)),
        user:cwa(F),
        initially(F), !.
apply_cwa(F,false) :- 
        ground(F),
        (isfluent(F);isrigid(F)),
        user:cwa(F),
        not(initially(F)), !.
% maybe too expensive...
apply_cwa(F,R) :- 
        not(ground(F)),
        (isfluent(F);isrigid(F)),
        user:cwa(F), !,
        term_variables(F,Vars),
        findall((Vars,Unifier),
                (initially(FI),
                 unifiable((F,Vars),(FI,Vars),Unifier)),
                Instances),
        describe_instances(Vars,Instances,R).
apply_cwa(F1,F2) :-
        def(F1,F3), !,
        apply_cwa(F3,F2).
apply_cwa(-F1,-F2) :- !,
        apply_cwa(F1,F2).
apply_cwa((F1+F2),(F3+F4)) :- !,
        apply_cwa(F1,F3),
        apply_cwa(F2,F4).
apply_cwa((F1*F2),(F3*F4)) :- !,
        apply_cwa(F1,F3),
        apply_cwa(F2,F4).
apply_cwa((F1<=>F2),(F3<=>F4)) :- !,
        apply_cwa(F1,F3),
        apply_cwa(F2,F4).
apply_cwa((F1=>F2),(F3=>F4)) :- !,
        apply_cwa(F1,F3),
        apply_cwa(F2,F4).
apply_cwa((F1<=F2),(F3<=F4)) :- !,
        apply_cwa(F1,F3),
        apply_cwa(F2,F4).
apply_cwa(some(Vars,F1),some(Vars,F2)) :- !,
        apply_cwa(F1,F2).
apply_cwa(all(Vars,F1),all(Vars,F2)) :- !,
        apply_cwa(F1,F2).
apply_cwa(F,F) :- !.

describe_instances(_Vars,[],false) :- !.
describe_instances(Vars,[(Vars,Unifier)],R) :- !,
        describe_instance(Vars,Unifier,R).
describe_instances(Vars,[(Vars,Unifier)|Instances],R1+R2) :- !,
        describe_instance(Vars,Unifier,R1),
        describe_instances(Vars,Instances,R2).
describe_instance(_Vars,[],true) :- !.
describe_instance(_Vars,[E],E) :- !.
describe_instance(Vars,[E|Es],E*R) :-
        describe_instance(Vars,Es,R).
