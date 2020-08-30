:- module(una, [apply_una/2,
                is_stdname/1,
                get_std_names_axioms/2,
                get_fml_std_names/2,
                get_new_std_name/2]).

:- use_module('../lib/utils').
:- use_module('../logic/cwa').
:- use_module('../logic/fol').
:- use_module('../projection/regression', [isfluent/1,isrigid/1]).

:- multifile user:poss/2.
:- multifile user:poss/3.

:- discontiguous collect_names/2.

apply_una(true,true) :- !.
apply_una(false,false) :- !.
apply_una(poss(A),poss(A)) :- !.
apply_una(exo(A),exo(A)) :- !.
apply_una(sf(A),sf(A)) :- !.
apply_una(F,F) :- isfluent(F), !.
apply_una(F,F) :- isrigid(F), !.
apply_una(F,F) :- def(F,_), !.

apply_una((X=Y),true) :- X==Y, !.
apply_una(-(X=Y),false) :- X==Y, !.

apply_una(-(X=Y),InEqualities) :-
        nonvar(X), nonvar(Y),
        unique_name(X),
        unique_name(Y),
        X =.. [A|XArgs], Y =..[A|YArgs], !,
        make_inequalities(XArgs,YArgs,InEqualities2),
        apply_una(InEqualities2,InEqualities).
apply_una(-(X=Y),true) :-
        nonvar(X), nonvar(Y),
        unique_name(X),
        unique_name(Y),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.
apply_una((X=Y),Equalities) :-
        nonvar(X), nonvar(Y),
        unique_name(X),
        unique_name(Y),
        X =.. [A|XArgs], Y =..[A|YArgs], !,
        make_equalities(XArgs,YArgs,Equalities2),
        apply_una(Equalities2,Equalities).
apply_una((X=Y),false) :-
        nonvar(X), nonvar(Y),
        unique_name(X),
        unique_name(Y),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.

apply_una(-F1,-F2) :- !,
        apply_una(F1,F2).
apply_una((F1+F2),(F3+F4)) :- !,
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1*F2),(F3*F4)) :- !,
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1<=>F2),(F3<=>F4)) :- !,
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1=>F2),(F3=>F4)) :- !,
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una((F1<=F2),(F3<=F4)) :- !,
        apply_una(F1,F3),
        apply_una(F2,F4).
apply_una(some(A,F),R) :-
        var(A), !,
        apply_una(some([A],F),R).
apply_una(all(A,F),R) :-
        var(A), !,
        apply_una(all([A],F),R).
% ?[A]:(?[X]:(A=f(X))&F) --> ?[X]:F with A replaced by f(X)
apply_una(some([A],F1),some(Vars,F4)) :- % (*)
        action_equality_conjunct(A,Act,F1,F2,Vars), !,
        subv(A,Act,F2,F3),
        apply_una(F3,F4).
% ![A]:(![X]:(-(A=f(X)))|F) --> ![X]:F with A replaced by f(X)
apply_una(all([A],F1),all(Vars,F4)) :- % (**)
        action_inequality_disjunct(A,Act,F1,F2,Vars), !,
        subv(A,Act,F2,F3),
        apply_una(F3,F4).
% simplification using standard names
apply_una(some([X],-(Y=Z)),true) :-
        X==Y,
        unique_name(Z), !.
apply_una(some([X],-(Z=Y)),true) :-
        X==Y,
        unique_name(Z), !.
apply_una(all([X],(Y=Z)),false) :-
        X==Y,
        unique_name(Z), !.
apply_una(all([X],(Z=Y)),false) :-
        X==Y,
        unique_name(Z), !.
apply_una(some(Vars,F1),some(Vars,F2)) :- !,
        apply_una(F1,F2).
apply_una(all(Vars,F1),all(Vars,F2)) :- !,
        apply_una(F1,F2).
apply_una(some_t(Vars,F1),some_t(Vars,F2)) :- !,
        apply_una(F1,F2).
apply_una(all_t(Vars,F1),all_t(Vars,F2)) :- !,
        apply_una(F1,F2).
apply_una(after(A,F1),after(A,F2)) :- !,
        apply_una(F1,F2).
apply_una(know(F1),know(F2)) :- !,
        apply_una(F1,F2).

apply_una(F,F) :- !.

make_equalities([],[],true) :- !.
make_equalities([X],[Y],(X=Y)) :- !.
make_equalities([X|Xs],[Y|Ys],(X=Y)*Equ) :-  !,
        make_equalities(Xs,Ys,Equ).
make_inequalities([],[],false) :- !.
make_inequalities([X],[Y],-(X=Y)) :- !.
make_inequalities([X|Xs],[Y|Ys],(-(X=Y))+Equ) :- !,
        make_inequalities(Xs,Ys,Equ).

% standard name: any constant (Prolog atom) starting with '#'
is_stdname(X) :-
        atomic(X),
        atom_concat('#',_,X).

unique_name(X) :-
        poss(X,_);
        poss(X,_,_);
        X == fail; X == terminate;
        X =.. [F|_], is_stdname(F).

/**
  * action_equality_conjunct(-A,-Act,+Fml1,-Fml2,-Vars) is nondet
  *
  * If A is an existentially quantified variable representing an
  * action, this predicate looks for a conjunct in formula Fml1 
  * of the form some(Vars,(A=Act)*F) (modulo ordering) that will be
  * replaced by F in the process. Act and Vars will be returned such
  * that A can be substituted by Act and some([A],...) by 
  * some(Vars,...) in the process in rule (*) of apply_una above.
  *
  * @arg A    a (logical) variable, representing an action
  * @arg Act  a (non-variable) action term
  * @arg Fml1 a formula
  * @arg Fml2 resulting formula
  * @arg Vars quantified variables
  */
action_equality_conjunct(A,Act,(X=Y),(X=Y),[]) :-
        A==X,
        nonvar(Y),
        unique_name(Y),
        Act=Y, !.
action_equality_conjunct(A,Act,(X=Y),(X=Y),[]) :-
        A==Y,
        nonvar(X),
        unique_name(X),
        Act=X, !.
action_equality_conjunct(A,Act,some_t(VTs,F),Fml2,Vars) :- !,
        untype(some_t(VTs,F),Fml1),
        action_equality_conjunct(A,Act,Fml1,Fml2,Vars).
action_equality_conjunct(A,Act,some(Vars,F),F,Vars) :- !,
        action_equality_conjunct(A,Act,F,F,[]).
action_equality_conjunct(A,Act,-all_t(VTs,F),Fml2,Vars) :- !,
        untype(all_t(VTs,F),Fml1),
        action_equality_conjunct(A,Act,-Fml1,Fml2,Vars).
action_equality_conjunct(A,Act,-all(Vars,F),-F,Vars) :- !,
        action_inequality_disjunct(A,Act,F,F,[]). % sign change (!)
action_equality_conjunct(X,Y,Fml1*Fml2,Fml1P*Fml2,Vars) :-
        action_equality_conjunct(X,Y,Fml1,Fml1P,Vars), !.
action_equality_conjunct(X,Y,Fml1*Fml2,Fml1*Fml2P,Vars) :-
        action_equality_conjunct(X,Y,Fml2,Fml2P,Vars), !.

/**
  * action_inequality_disjunct(-A,-Act,+Fml1,-Fml2,-Vars) is nondet
  *
  * If A is a universally quantified variable representing an
  * action, this predicate looks for a disjunct in formula Fml1 
  * of the form all(Vars,(-(A=Act))+F) (modulo ordering) that will be
  * replaced by F in the process. Act and Vars will be returned such
  * that A can be substituted by Act and all([A],...) by 
  * all(Vars,...) in the process in rule (**) of apply_una above.
  *
  * @arg A    a (logical) variable, representing an action
  * @arg Act  a (non-variable) action term
  * @arg Fml1 a formula
  * @arg Fml2 resulting formula
  * @arg Vars quantified variables
  */
action_inequality_disjunct(A,Act,-(X=Y),-(X=Y),[]) :-
        A==X,
        nonvar(Y),
        unique_name(Y),
        Act=Y, !.
action_inequality_disjunct(A,Act,-(X=Y),-(X=Y),[]) :-
        A==Y,
        nonvar(X),
        unique_name(X),
        Act=X, !.
action_inequality_disjunct(A,Act,all_t(VTs,F),Fml2,Vars) :- !,
        untype(all_t(VTs,F),Fml1),
        action_inequality_disjunct(A,Act,Fml1,Fml2,Vars).
action_inequality_disjunct(A,Act,all(Vars,F),F,Vars) :- !,
        action_inequality_disjunct(A,Act,F,F,[]).
action_inequality_disjunct(A,Act,-some_t(VTs,F),Fml2,Vars) :- !,
        untype(some_t(VTs,F),Fml1),
        action_inequality_disjunct(A,Act,-Fml1,Fml2,Vars).
action_inequality_disjunct(A,Act,-some(Vars,F),-F,Vars) :- !,
        action_equality_conjunct(A,Act,F,F,[]). % sign change (!)
action_inequality_disjunct(X,Y,Fml1+Fml2,Fml1P+Fml2,Vars) :-
        action_inequality_disjunct(X,Y,Fml1,Fml1P,Vars), !.
action_inequality_disjunct(X,Y,Fml1+Fml2,Fml1+Fml2P,Vars) :-
        action_inequality_disjunct(X,Y,Fml2,Fml2P,Vars), !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Standard names
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

get_std_names_axioms(Formulas,Axioms) :-
        get_fml_std_names(Formulas,Names),
        findall(Axiom,
                (member(X,Names),
                 member(Y,Names),
                 X @< Y,
                 Axiom = -(X=Y)),
                Axioms).

get_fml_std_names(Fml,Names) :- !,
        collect_names(Fml,Names2),
        sort(Names2,Names).
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

% description logics
collect_names(concept_assertion(C,N),Names) :- !,
        collect_names_concept(C,Names1),
        collect_names_term(N,Names2),
        append([Names1,Names2],Names).
collect_names(role_assertion(_R,N1,N2),Names) :- !,
        % no names in roles...
        collect_names_term(N1,Names1),
        collect_names_term(N2,Names2),
        append([Names1,Names2],Names).
collect_names(subsumedBy(C1,C2),Names) :- !,
        collect_names_concept(C1,Names1),
        collect_names_concept(C2,Names2),
        append([Names1,Names2],Names).
collect_names_concept(only(_,C),Names) :- !,
        collect_names_concept(C,Names).
collect_names_concept(exists(_,C),Names) :- !,
        collect_names_concept(C,Names).
collect_names_concept(oneof(Ts),Names) :- !,
        collect_names_term_list(Ts,Names).
collect_names_concept(not(C),Names) :- !,
        collect_names_concept(C,Names).
collect_names_concept(or(Cs),Names) :- !,
        collect_names_concept_list(Cs,Names).
collect_names_concept(and(Cs),Names) :- !,
        collect_names_concept_list(Cs,Names).
collect_names_concept(nothing,[]) :- !.
collect_names_concept(thing,[]) :- !.
collect_names_concept(_,[]) :- !.

collect_names_concept_list([],[]) :- !.
collect_names_concept_list([C|Cs],Names) :- !,
        collect_names_concept(C,Names1),
        collect_names_concept_list(Cs,Names2),
        append(Names1,Names2,Names).

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
