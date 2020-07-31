%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Simple Example that generates an infinite fixpoint, i.e.
% the fixpoint verification method will not terminate (the
% solution here would have to be a second-order formula that
% expresses the property that initially, there are infinitely
% many instances of the f fluent).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- ['../../../verification/fixpoint_ctl'].

:- discontiguous causes_true/3.
:- discontiguous causes_false/3.
:- discontiguous rel_fluent/1.

%initially(...).

rel_fluent(f(_)).

poss(a(_),true).
poss(b(_),true).

causes_true(b(X),f(X),true).
causes_false(a(X),f(X),true).

%include_preconditions. % no precondition extension

program(main,
        [while(some(X,f(X)),
               pick(X,[test(f(X)),
                       a(X)])),
         b('#c')]).

property(prop1,
         main,
         somepath(always(-f('#c')))).

run_infinite :-
        construct_characteristic_graph(main),
        verify(main,prop1).
