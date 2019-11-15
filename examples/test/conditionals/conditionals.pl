:- use_module('../../../logic/system_z_kb').

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
        assertion(entails_initially(   p*b ~> (-f),true)),
        assertion(entails_initially(    f  ~> (-p),true)),
        assertion(entails_initially(    b  ~> (-p),true)),
        assertion(entails_initially(   p*a ~>   b ,true)),
        % 1-entailments
        assertion(entails_initially(  (-b) ~> (-p),true)),
        assertion(entails_initially(  (-f) ~> (-b),true)),
        assertion(entails_initially(    b  ~>   m ,true)),
        assertion(entails_initially(  (-m) ~> (-b),true)),
        assertion(entails_initially(p*(-w) ~>   b ,true)),
        assertion(entails_initially(    p  ~>   w ,false)),
        assertion(entails_initially(p*(-a) ~> (-f),false)),
        assertion(entails_initially(p*(-a) ~>   w ,false)).
:- end_tests(system_z).
