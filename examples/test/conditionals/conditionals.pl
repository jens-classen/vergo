:- use_module('../../../kbs/conditional_kb').

initially(p~>b).
initially(b~>f).
initially(p~>(-f)).
initially(p~>a).
initially(b~>w).
initially(f~>m).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- begin_tests(system_z).
test(pearl1990) :-
        set_reasoner(system_z),
        initialize_kb(kb),
        check_entailments(pearl1990).
:- end_tests(system_z).

:- begin_tests(rational_closure).
test(pearl1990) :-
        set_reasoner(rational_closure),
        initialize_kb(kb),
        check_entailments(pearl1990).
:- end_tests(rational_closure).

check_entailments(pearl1990) :- !,
        % 0-entailments
        assertion(    entails_kb(kb,    p*b ~> (-f))),
        assertion(    entails_kb(kb,     f  ~> (-p))),
        assertion(    entails_kb(kb,     b  ~> (-p))),
        assertion(    entails_kb(kb,    p*a ~>   b )),
        % 1-entailments
        assertion(    entails_kb(kb,   (-b) ~> (-p))),
        assertion(    entails_kb(kb,   (-f) ~> (-b))),
        assertion(    entails_kb(kb,     b  ~>   m )),
        assertion(    entails_kb(kb,   (-m) ~> (-b))),
        assertion(    entails_kb(kb, p*(-w) ~>   b )),
        assertion(not(entails_kb(kb,     p  ~>   w))),
        assertion(not(entails_kb(kb, p*(-a) ~> (-f)))),
        assertion(not(entails_kb(kb, p*(-a) ~>   w ))).