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
        assertion(entails_kb(kb,    p*b ~> (-f), true)),
        assertion(entails_kb(kb,     f  ~> (-p), true)),
        assertion(entails_kb(kb,     b  ~> (-p), true)),
        assertion(entails_kb(kb,    p*a ~>   b , true)),
        % 1-entailments
        assertion(entails_kb(kb,   (-b) ~> (-p), true)),
        assertion(entails_kb(kb,   (-f) ~> (-b), true)),
        assertion(entails_kb(kb,     b  ~>   m , true)),
        assertion(entails_kb(kb,   (-m) ~> (-b), true)),
        assertion(entails_kb(kb, p*(-w) ~>   b , true)),
        assertion(entails_kb(kb,     p  ~>   w , false)),
        assertion(entails_kb(kb, p*(-a) ~> (-f), false)),
        assertion(entails_kb(kb, p*(-a) ~>   w , false)).