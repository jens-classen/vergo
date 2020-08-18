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
        initialize_kb,
        % 0-entailments
        assertion(entails_kb(   p*b ~> (-f),true)),
        assertion(entails_kb(    f  ~> (-p),true)),
        assertion(entails_kb(    b  ~> (-p),true)),
        assertion(entails_kb(   p*a ~>   b ,true)),
        % 1-entailments
        assertion(entails_kb(  (-b) ~> (-p),true)),
        assertion(entails_kb(  (-f) ~> (-b),true)),
        assertion(entails_kb(    b  ~>   m ,true)),
        assertion(entails_kb(  (-m) ~> (-b),true)),
        assertion(entails_kb(p*(-w) ~>   b ,true)),
        assertion(entails_kb(    p  ~>   w ,false)),
        assertion(entails_kb(p*(-a) ~> (-f),false)),
        assertion(entails_kb(p*(-a) ~>   w ,false)).
:- end_tests(system_z).
