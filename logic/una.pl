/**

<module> Unique Names Assumption

This module provides functionality implementing the unique names
assumption (UNA). It provides predicates for applying UNA to formulas,
(i.e. simplifying them accordingly) as well as collect the names
contained in a set of formulas and generate the corresponding UNA
axioms.

Elements subject to the UNA are (a) standard names, which are atomic
terms starting with `#`, as well as (b) a broader class of terms that
includes (i) standard names, (ii) action terms whose operators have
been declared via `poss/2` or `poss/3`, and (iii) terms whose functors
start with `#` (which will be treated similar to actions, e.g.
`'#f'('#a')` and `'#f'('#b')` are assumed to be distinct).

@author  Jens Claßen
@license GPLv2

 **/
:- module(una, [is_std_name/1,
                is_uni_name/1,
                apply_una/2,
                get_names_axioms_from_fmls/3,
                get_names_axioms_from_names/2,
                get_fml_names/3,
                get_fml_std_names/2,
                get_fml_uni_names/2,
                get_new_std_name/2]).

:- use_module('../lib/utils').
:- use_module('../logic/cwa').
:- use_module('../logic/fol', [op(1130, xfy, <=>),
                               op(1110, xfy, <=),
                               op(1110, xfy, =>)]).
:- use_module('../projection/regression', [isfluent/1,isrigid/1]).

:- multifile user:poss/2.
:- multifile user:poss/3.

:- discontiguous collect_names/3.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * is_std_name(+Term) is det.
  *
  * Succeeds if the specified term is a standard name, i.e. a constant
  * (Prolog atom) that starts with `#`, e.g. `'#alice'`, `'#bob'` etc.
  *
  * While vergo itself will be able to treat arbitrary such atoms as
  * standard names, for the compilation into other languages (such as
  * PDDL) it is recommended to only use lower case letters (a-z),
  * digits (0-9), and underscores ('_'), and use a lower case letter
  * as the first character (after `#`).
  *
  * @arg Term a term
  */
is_std_name(X) :-
        atomic(X),
        atom_concat('#',_,X).

/**
  * is_uni_name(+Term) is det.
  *
  * Succeeds if the specified term is a unique name, i.e. an action,
  * one of the special action symbols `fail` or `terminate`, a
  * standard name, or a term whose functor starts with `#`.
  *
  * @arg Term a term
  */
is_uni_name(X) :-
        poss(X,_);
        poss(X,_,_);
        X == fail; X == terminate;
        X =.. [F|_], is_std_name(F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Application of UNA to Formulas
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * apply_una(+Formula,-Result) is det.
  *
  * Applies the unique names assumption to the given Formula in order
  * to simplify it, yielding Result. In particular, simplification
  * applies to equalities (substituting e.g. `('#alice'='#bob')` by
  * `false` and `(pickup(X)=drop(Y))` by `(X=Y)`), and to eliminating
  * quantifiers where possible (e.g. `some(X,(X='#cup')*onTable(X))`
  * is replaced by `onTable('#cup')`).
  *
  * @arg Names    a list of unique names, given in the form
  *               `Functor/Arity` (e.g. `pickup/1` for an action with
  *               one argument); if the arity is zero, it can be left
  *               out (e.g. `'#bob'` instead of `'#bob'/0` for a
  *               standard name)
  * @arg Axioms   the unique names axioms corresponding to the names
  *               occurring in Formulas
  */
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
        is_uni_name(X),
        is_uni_name(Y),
        X =.. [A|XArgs], Y =..[A|YArgs], !,
        make_inequalities(XArgs,YArgs,InEqualities2),
        apply_una(InEqualities2,InEqualities).
apply_una(-(X=Y),true) :-
        nonvar(X), nonvar(Y),
        is_uni_name(X),
        is_uni_name(Y),
        X =.. [A|_], Y =.. [B|_],
        A \= B, !.
apply_una((X=Y),Equalities) :-
        nonvar(X), nonvar(Y),
        is_uni_name(X),
        is_uni_name(Y),
        X =.. [A|XArgs], Y =..[A|YArgs], !,
        make_equalities(XArgs,YArgs,Equalities2),
        apply_una(Equalities2,Equalities).
apply_una((X=Y),false) :-
        nonvar(X), nonvar(Y),
        is_uni_name(X),
        is_uni_name(Y),
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
        is_uni_name(Z), !.
apply_una(some([X],-(Z=Y)),true) :-
        X==Y,
        is_uni_name(Z), !.
apply_una(all([X],(Y=Z)),false) :-
        X==Y,
        is_uni_name(Z), !.
apply_una(all([X],(Z=Y)),false) :-
        X==Y,
        is_uni_name(Z), !.
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
        is_uni_name(Y),
        Act=Y, !.
action_equality_conjunct(A,Act,(X=Y),(X=Y),[]) :-
        A==Y,
        nonvar(X),
        is_uni_name(X),
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
        is_uni_name(Y),
        Act=Y, !.
action_inequality_disjunct(A,Act,-(X=Y),-(X=Y),[]) :-
        A==Y,
        nonvar(X),
        is_uni_name(X),
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
% Unique Names Axioms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * get_names_axioms_from_names(++Names,-Axioms) is det.
  *
  * Returns the set of unique names axioms for the specified list of
  * names. Axioms will be of two types, namely of the form
  *
  * `all([X,Y], (pickup(X)=pickup(Y)) => (X=Y) )`,
  *
  * saying that two terms with the same (unique name) functor are
  * identical just in case their arguments are identical, and of the
  * form
  *
  * `all([X,Y], -(pickup(X)=drop(Y)) )`,
  *
  * saying that terms with a different (unique name) functor are
  * distinct.
  *
  * @arg Names    a list of unique names, given in the form
  *               `Functor/Arity` (e.g. `pickup/1` for an action with
  *               one argument); if the arity is zero, it can be left
  *               out (e.g. `'#bob'` instead of `'#bob'/0` for a
  *               standard name)
  * @arg Axioms   the unique names axioms corresponding to the names
  *               occurring in Formulas
  */
get_names_axioms_from_names(Names,Axioms) :-
        get_type1_axioms_from_names(Names,Axioms1),
        get_type2_axioms_from_names(Names,Axioms2),
        append(Axioms1,Axioms2,Axioms).

/**
  * get_names_axioms_from_fmls(++Type,+Formulas,-Axioms) is det.
  *
  * Similar as get_names_axioms_from_names/2, but first determines the
  * names of the specified type from the given set (list) of formulas.
  *
  * @arg Type     the type of names to be considered, either `std`
  *               (denoting only standard names), or `uni` (denoting
  *               all unique names, including standard names and
  *               actions)
  * @arg Formulas a list of formulas
  * @arg Axioms   the unique names axioms corresponding to the names
  *               occurring in Formulas
  */
get_names_axioms_from_fmls(Type,Formulas,Axioms) :-
        get_fml_names(Type,Formulas,Names),
        get_names_axioms_from_names(Names,Axioms).

/**
  * get_names_axioms_from_fmls(++Type,+Formulas,-Axioms) is det.
  *
  * Similar as get_names_axioms_from_names/2, but first determines the
  * names of the specified type from the given set (list) of formulas.
  *
  * @arg Type     the type of names to be considered, either `std`
  *               (denoting only standard names), or `uni` (denoting
  *               all unique names, including standard names and
  *               actions)
  * @arg Formulas a list of formulas
  * @arg Axioms   the unique names axioms corresponding to the names
  *               occurring in Formulas
  */
get_names_axioms_from_fmls(Type,Formulas,Axioms) :-
        get_fml_names(Type,Formulas,Names),
        get_names_axioms_from_names(Names,Axioms).

get_type1_axioms_from_names([],[]) :- !.
get_type1_axioms_from_names([Name|Names],[Axiom|Axioms]) :-
        una_axiom_type1(Name,Axiom), !,
        get_type1_axioms_from_names(Names,Axioms).
get_type1_axioms_from_names([_Name|Names],Axioms) :- !,
        get_type1_axioms_from_names(Names,Axioms).

una_axiom_type1(Name/N,Axiom) :-
        N > 0, !,
        fresh_variables(N,AVars),
        fresh_variables(N,BVars),
        NA =.. [Name|AVars],
        NB =.. [Name|BVars],
        vars_equalities(AVars,BVars,AequB),
        append(AVars,BVars,Vars),
        Axiom = all(Vars,(NA=NB)=>(AequB)).

get_type2_axioms_from_names([],[]) :- !.
get_type2_axioms_from_names([Name|Names],Axioms) :- !,
        get_type2_axioms_from_names2(Name,Names,Axioms1),
        get_type2_axioms_from_names(Names,Axioms2),
        append(Axioms1,Axioms2,Axioms).
get_type2_axioms_from_names2(_Name,[],[]) :- !.
get_type2_axioms_from_names2(Name,[N|Ns],[Axiom|Axioms]) :- !,
        una_axiom_type2(Name,N,Axiom),
        get_type2_axioms_from_names2(Name,Ns,Axioms).

una_axiom_type2(NameA,NameB/NB,Axiom) :-
        atomic(NameA), !,
        una_axiom_type(NameA/0,NameB/NB,Axiom).
una_axiom_type2(NameA/NA,NameB,Axiom) :-
        atomic(NameB), !,
        una_axiom_type(NameA/NA,NameB/0,Axiom).
una_axiom_type2(NameA,NameB,-(NameA=NameB)) :-
        atomic(NameA),
        atomic(NameB), !.
una_axiom_type2(NameA/0,NameB/0,-(NameA=NameB)) :- !.
una_axiom_type2(NameA/NA,NameB/NB,Axiom) :- !,
        fresh_variables(NA,AVars),
        fresh_variables(NB,BVars),
        A =.. [NameA|AVars],
        B =.. [NameB|BVars],
        append(AVars,BVars,Vars),
        Axiom = all(Vars,-(A=B)).

fresh_variables(0,[]) :- !.
fresh_variables(N,[_X|Vars]) :-
        N > 0, !,
        N1 is N-1,
        fresh_variables(N1,Vars).

vars_equalities([],[],true) :- !.
vars_equalities([X],[Y],(X=Y)) :- !.
vars_equalities([X|Xs],[Y|Ys],(X=Y)*Equ) :- !,
        vars_equalities(Xs,Ys,Equ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Collecting Names
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * get_fml_names(++Type,+Fml,-Names) is det.
  *
  * Returns a list Names of all unique names of the specified Type
  * occurring in Fml. The type is either `std` (meaning only standard
  * names such as `'#bob'`) or `uni` (meaning all unique names,
  * including action operators). Unique names with arguments will be
  * denoted as `Functor/Arity`.
  *
  * @arg Type     the type of names to be determined, either `std`
  *               (denoting only standard names), or `uni` (denoting
  *               all unique names, including standard names and
  *               actions)
  * @arg Fml      a formula or a list of formulas (L or DL)
  * @arg Names    the list of occurring unique names, given in the
  *               form `Functor/Arity` (e.g. `pickup/1` for an action with
  *               one argument) if the type is `std`, or a list of
  *               standard names (without the `/0` arity specifier) if
  *               the type is `uni`
  */
get_fml_names(Type,Fml,Names) :- !,
        collect_names(Type,Fml,Names2),
        sort(Names2,Names).

/**
  * get_fml_std_names(+Fml,-Names) is det.
  *
  * Returns a list Names of all standard names occurring in Fml.
  *
  * @arg Fml      a formula or a list of formulas (L or DL)
  * @arg Names    the list of occurring standard names
  */
get_fml_std_names(Fml,Names) :- !,
        collect_names(std,Fml,Names2),
        sort(Names2,Names).

/**
  * get_fml_uni_names(+Fml,-Names) is det.
  *
  * Returns a list Names of all unique names in Fml, denoted as
  * `Functor/Arity`.
  *
  * @arg Fml      a formula or a list of formulas (L or DL)
  * @arg Names    the list of occurring unique names, given in the
  *               form `Functor/Arity` (e.g. `pickup/1` for an action with
  *               one argument)
  */
get_fml_uni_names(Fml,Names) :- !,
        collect_names(uni,Fml,Names2),
        sort(Names2,Names).

/**
  * collect_names(++Type,+FmlList,-Names) is det.
  *
  * Returns a list of all unique names of the specified type occurring
  * in the given list of formulas. The type is either `std` (meaning
  * only standard names such as `'#bob'`) or `uni` (meaning all unique
  * names, including action operators). Unique names with arguments
  * will be denoted as `Functor/Arity`.
  *
  * @arg Type    the type of names, either `std` or `uni`
  * @arg FmlList a list of formulas (L or DL)
  * @arg Names   a list of all occurring names
  */
collect_names(Type,[Fml|Fmls],Names) :- !,
        collect_names(Type,Fml,Names1),
        collect_names(Type,Fmls,Names2),
        append(Names1,Names2,Names).
collect_names(_Type,[],[]) :- !.
collect_names(Type,Fml1<=>Fml2,Names) :- !,
        collect_names(Type,Fml1,Names1),
        collect_names(Type,Fml2,Names2),
        append(Names1,Names2,Names).
collect_names(Type,Fml1=>Fml2,Names) :- !,
        collect_names(Type,Fml1,Names1),
        collect_names(Type,Fml2,Names2),
        append(Names1,Names2,Names).
collect_names(Type,Fml1<=Fml2,Names) :- !,
        collect_names(Type,Fml1,Names1),
        collect_names(Type,Fml2,Names2),
        append(Names1,Names2,Names).
collect_names(Type,Fml1*Fml2,Names) :- !,
        collect_names(Type,Fml1,Names1),
        collect_names(Type,Fml2,Names2),
        append(Names1,Names2,Names).
collect_names(Type,Fml1+Fml2,Names) :- !,
        collect_names(Type,Fml1,Names1),
        collect_names(Type,Fml2,Names2),
        append(Names1,Names2,Names).
collect_names(Type,-Fml,Names) :- !,
        collect_names(Type,Fml,Names).
collect_names(Type,some(_Vars,Fml),Names) :- !,
        collect_names(Type,Fml,Names).
collect_names(Type,all(_Vars,Fml),Names) :- !,
        collect_names(Type,Fml,Names).
collect_names(Type,some_t(_Vars,Fml),Names) :- !,
        collect_names(Type,Fml,Names).
collect_names(Type,all_t(_Vars,Fml),Names) :- !,
        collect_names(Type,Fml,Names).
collect_names(Type,know(Fml),Names) :- !,
        collect_names(Type,Fml,Names).
collect_names(Type,(X=Y),Names) :- !,
        collect_names_term(Type,X,Names1),
        collect_names_term(Type,Y,Names2),
        append(Names1,Names2,Names).

% description logics
collect_names(Type,concept_assertion(C,N),Names) :- !,
        collect_names_concept(Type,C,Names1),
        collect_names_term(Type,N,Names2),
        append([Names1,Names2],Names).
collect_names(Type,role_assertion(_R,N1,N2),Names) :- !,
        % no names in roles...
        collect_names_term(Type,N1,Names1),
        collect_names_term(Type,N2,Names2),
        append([Names1,Names2],Names).
collect_names(Type,subsumedBy(C1,C2),Names) :- !,
        collect_names_concept(Type,C1,Names1),
        collect_names_concept(Type,C2,Names2),
        append([Names1,Names2],Names).
collect_names_concept(Type,only(_,C),Names) :- !,
        collect_names_concept(Type,C,Names).
collect_names_concept(Type,exists(_,C),Names) :- !,
        collect_names_concept(Type,C,Names).
collect_names_concept(Type,oneof(Ts),Names) :- !,
        collect_names_term_list(Type,Ts,Names).
collect_names_concept(Type,not(C),Names) :- !,
        collect_names_concept(Type,C,Names).
collect_names_concept(Type,or(Cs),Names) :- !,
        collect_names_concept_list(Type,Cs,Names).
collect_names_concept(Type,and(Cs),Names) :- !,
        collect_names_concept_list(Type,Cs,Names).
collect_names_concept(_Type,nothing,[]) :- !.
collect_names_concept(_Type,thing,[]) :- !.
collect_names_concept(_Type,_,[]) :- !.

collect_names_concept_list(_Type,[],[]) :- !.
collect_names_concept_list(Type,[C|Cs],Names) :- !,
        collect_names_concept(Type,C,Names1),
        collect_names_concept_list(Type,Cs,Names2),
        append(Names1,Names2,Names).

collect_names(Type,Atom,Names) :- !,
        Atom =.. [_P|Args],
        collect_names_term_list(Type,Args,Names).

collect_names_term(_Type,T,[]) :-
        var(T), !.
collect_names_term(std,T,[T]) :-
        is_std_name(T), !.
collect_names_term(uni,T,[U|Names]) :-
        is_uni_name(T), !,
        T =.. [F|Args],
        length(Args,N),
        U = F/N,
        collect_names_term_list(uni,Args,Names).
collect_names_term(Type,T,Names) :- !,
        T =.. [_|L],
        collect_names_term_list(Type,L,Names).

collect_names_term_list(_Type,[],[]) :- !.
collect_names_term_list(Type,[E|L],Names) :- !,
        collect_names_term(Type,E,Names1),
        collect_names_term_list(Type,L,Names2),
        append(Names1,Names2,Names).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Creating New Names
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * get_new_std_name(++Names,-New) is det.
  *
  * Returns a new standard name that is not contained in the specified
  * list of standard names. The new name is lexicographically the
  * smallest one only consisting of lower case letters (except for the
  * `#` prefix).
  *
  * @arg Names a list of standard names
  * @arg New   a standard name not occurring in Names
  */
get_new_std_name(Names,New) :- !,
        create_new_names(Names,1,[New]).

create_new_names(_Names,0,[]) :- !.
create_new_names(Names,K,[C|Names2]) :- K > 0, !,
        K1 is K - 1,
        create_new_names(Names,K1,Names2),
        smallest_name_not_contained(Names,Names2,C).

smallest_name_not_contained(S1,S2,C) :- !,
        smallest_name_not_contained2(S1,S2,C,[97]).

smallest_name_not_contained2(S1,S2,C,[Char|Chars]) :-
        atom_codes(Atom,[35,Char|Chars]), % 35 = '#'
        not(member(Atom,S1)),
        not(member(Atom,S2)), !,
        C = Atom.

smallest_name_not_contained2(S1,S2,C,[Char|Chars]) :-
        atom_codes(Atom,[35,Char|Chars]), % 35 = '#'
        (member(Atom,S1);member(Atom,S2)),
        Char < 122, !,
        Char1 is Char + 1,
        smallest_name_not_contained2(S1,S2,C,[Char1|Chars]).

smallest_name_not_contained2(S1,S2,C,[Char|Chars]) :-
        atom_codes(Atom,[35,Char|Chars]), % 35 = '#'
        (member(Atom,S1);member(Atom,S2)),
        Char = 122, !,
        smallest_name_not_contained2(S1,S2,C,[97,122|Chars]).
