% Note: standard names are Prolog atoms starting with '#', e.g. '#bob'

:- module(l, [entails_l/3,
              inconsistent_l/2,
              consistent_l/2,
              valid_l/2,
              equivalent_l/3,
              is_stdname/1,
              get_fml_std_names/2,
              get_ini_std_names/1,
              get_new_std_name/2]).

:- use_module('../reasoning/fol').

% standard name: any constant (Prolog atom) starting with '#'
% e.g. '#1', '#2', '#bob'
is_stdname(X) :-
        atomic(X),
        atom_concat('#',_,X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check formula against set of formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
entails_l(Formulas,Fml,Truth) :-
        get_fml_std_names([Fml|Formulas],Names),
        findall(StdNameAxiom,
                (member(X,Names),
                 member(Y,Names),
                 X @< Y,
                 StdNameAxiom = -(X=Y)),
                StdNameAxioms),
        union(Formulas,StdNameAxioms,FormulasWithAxioms),
        entails(FormulasWithAxioms,Fml), !,
        Truth = true.
entails_l(_Formulas,_Fml,Truth) :- !,
        Truth = false.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check inconsistency of set of formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
inconsistent_l(Formulas,Truth) :-
        get_fml_std_names(Formulas,Names),
        findall(StdNameAxiom,
                (member(X,Names),
                 member(Y,Names),
                 X @< Y,
                 StdNameAxiom = -(X=Y)),
                StdNameAxioms),
        union(Formulas,StdNameAxioms,FormulasWithAxioms),
        inconsistent(FormulasWithAxioms), !,
        Truth = true.
inconsistent_l(_Formulas,Truth) :- !,
        Truth = false.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check consistency of set of formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
consistent_l(Formulas,true) :-
        inconsistent_l(Formulas,false), !.
consistent_l(Formulas,false) :-
        inconsistent_l(Formulas,true), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check validity of formula
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
valid_l(Formula,Truth) :-
        entails_l([true],Formula,Truth), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check equivalence of two formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
                            
equivalent_l(Formula1,Formula2,Truth) :-
        entails_l([Formula1],Formula2,true),
        entails_l([Formula2],Formula1,true), !,
        Truth = true.
equivalent_l(_Formula1,_Formula2,Truth) :- !,
        Truth = false.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Helper predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

get_fml_std_names(Fml,Names) :- !,
        collect_names(Fml,Names2),
        sort(Names2,Names).
get_ini_std_names(Names) :- !,
        findall(Names2,
                (initially(Fml),
                 collect_names(Fml,Names2)),
                Names3),
        flatten(Names3,Names4),
        sort(Names4,Names).
get_new_std_name(Names,New) :- !,
        create_new_names(Names,1,[New]).

collect_names([Fml|Fmls],Names) :- !,
        collect_names(Fml,Names1),
        collect_names(Fmls,Names2),
        union(Names1,Names2,Names).
collect_names([],[]) :- !.
collect_names(Fml1<=>Fml2,Names) :- !,
        collect_names(Fml1,Names1),
        collect_names(Fml2,Names2),
        union(Names1,Names2,Names).
collect_names(Fml1=>Fml2,Names) :- !,
        collect_names(Fml1,Names1),
        collect_names(Fml2,Names2),
        union(Names1,Names2,Names).
collect_names(Fml1<=Fml2,Names) :- !,
        collect_names(Fml1,Names1),
        collect_names(Fml2,Names2),
        union(Names1,Names2,Names).
collect_names(Fml1*Fml2,Names) :- !,
        collect_names(Fml1,Names1),
        collect_names(Fml2,Names2),
        union(Names1,Names2,Names).
collect_names(Fml1+Fml2,Names) :- !,
        collect_names(Fml1,Names1),
        collect_names(Fml2,Names2),
        union(Names1,Names2,Names).
collect_names(-Fml,Names) :- !,
        collect_names(Fml,Names).
collect_names(some(_Vars,Fml),Names) :- !,
        collect_names(Fml,Names).
collect_names(all(_Vars,Fml),Names) :- !,
        collect_names(Fml,Names).
collect_names(know(Fml),Names) :- !,
        collect_names(Fml,Names).
collect_names((X=Y),Names) :- !,
        collect_names_term(X,Names1),
        collect_names_term(Y,Names2),
        union(Names1,Names2,Names).
collect_names(Atom,Names) :- !,
        Atom =.. [_P|Args],
        collect_names_term_list(Args,Names).

collect_names_term(T,[]) :-
        var(T), !.
collect_names_term(T,[T]) :-
        is_stdname(T), !.
collect_names_term(T,[]) :-
        not(is_stdname(T)), !.
collect_names_term(T,Names) :- !,
        T =.. [_|L],
        collect_names_term_list(L,Names).

collect_names_term_list([],[]) :- !.
collect_names_term_list([E|L],Names) :- !,
        collect_names_term(E,Names1),
        collect_names_term_list(L,Names2),
        union(Names1,Names2,Names).

create_new_names(_Names,0,[]) :- !.
create_new_names(Names,K,[C|Names2]) :- K > 0, !,
        K1 is K - 1,
        create_new_names(Names,K1,Names2),
        smallest_name_not_contained(Names,Names2,C).

smallest_name_not_contained(S1,S2,C) :- !,
        smallest_name_not_contained2(S1,S2,C,[97]).

smallest_name_not_contained2(S1,S2,C,[Char|Chars]) :-
        string_to_list(String,[Char|Chars]),
        atom_string(Atom,String),
        not(member(Atom,S1)),
        not(member(Atom,S2)), !,
        atom_concat('#',Atom,C).

smallest_name_not_contained2(S1,S2,C,[Char|Chars]) :-
        string_to_list(String,[Char|Chars]),
        atom_string(Atom,String),
        (member(Atom,S1);member(Atom,S2)),
        Char < 122, !,
        Char1 is Char + 1,
        smallest_name_not_contained2(S1,S2,C,[Char1|Chars]).

smallest_name_not_contained2(S1,S2,C,[Char|Chars]) :-
        string_to_list(String,[Char|Chars]),
        atom_string(Atom,String),
        (member(Atom,S1);member(Atom,S2)),
        Char = 122, !,
        smallest_name_not_contained2(S1,S2,C,[97,122|Chars]).
