/**

<module> Closed-World Assumption

This module provides predicates for including the closed-world
assumption (CWA) into an action theory. For this purpose, fluent and
rigid predicates are to be declared as underlying the CWA by means of
the cwa/1 predicate where appropriate.

By means of apply_cwa/3, CWA information can be compiled into a
formula (subformulas are replaced by their CWA truth value where
possible). eval_cwa/2 allows to evaluate a formula wrt the CWA, where
free variables (understood as existentially quantified) will be
instantiated in the process, each substitution corresponding to one
solution instance.

In both cases, truth values of CWA fluents are evaluated against a
knowledge base specified by means of an identifier (a ground term).
The special identifier 'userdb' denotes the database of facts given by
user:initially/1, cf. the l_kb module.

This module also handles types, which can be viewed as unary rigid
predicates, with a finite domain, underlying the CWA. They are hence
treated similarly by the above mentioned procedures.

is_type/1 unifies its argument with anything that is a type.
is_type_element/2 unifies its two arguments with pairs of type and
type element. is_instance/2 instantiates a term for a given list of
typed variables. types_cons/2 turns a list of typed variables into an
equivalent list of type constraint formulas, where types are
represented as unary predicates. untype/2 removes typed quantifiers by
re-writing them using standard first order syntax (treating types as
unary predicates). get_types/3 looks up the types of variables in a
list of typed variables.

@author  Jens Claßen
@license GPLv2

 **/
:- module(cwa, [apply_cwa/3, eval_cwa/2,
                is_type/1, is_type_element/2, is_instance/2,
                untype/2, types_cons/2,
                get_types/3]).

:- use_module('../kbs/l_kb').
:- use_module('../lib/utils').
:- use_module('../logic/l').
:- use_module('../projection/regression', [isfluent/1,isrigid/1]).

:- multifile user:cwa/1.
:- multifile user:type/1.
:- multifile user:subtype/2.
:- multifile user:domain/2.

/**
  * apply_cwa(++KB,+Formula,-Result) is det
  *
  * Result is the result of applying the closed-world assumption to
  * the Formula, i.e. ground atoms over fluents and rigids which have
  * been marked as underlying the CWA via cwa/1 will be replaced by
  * their truth value, atoms with free variables will be replaced by
  * an equality expression describing all and only instances of that
  * fluent, and all other parts of the Formula that are not subject to
  * CWA remain. KB is the identifier of the knowledge base from which
  * truth values will be determined, a special case being 'userdb',
  * denoting that facts of user:initially/1 are to be used.
  *
  * Additionally, lazy evaluation is used to simplify the Result
  * formula as early as possible wrt. true/false. Quantified
  * subformulas are tested through eval_cwa/2, and, if either true or
  * false, replaced by the corresponding outcome.
  *
  * Note: Since truth values of fluents in the initial situation are
  * tested, this should only be used if the Formula refers to the
  * initial situation. In particular, it should not be used during
  * regression or program verification.
  *
  * @arg KBID    the identifier (handle) of the KB containing facts to
  *              be used for CWA evaluation
  * @arg Formula a static objective formula about the initial
  *              situation
  * @arg Result  an equivalent formula where atoms underlying the CWA
  *              have been replaced by their truth value ('true' or
  *              'false'), and that has been simplified
 **/
apply_cwa(_KB,true,true) :- !.
apply_cwa(_KB,false,false) :- !.
apply_cwa(_KB,poss(A),poss(A)) :- !.
apply_cwa(_KB,exo(A),exo(A)) :- !.
apply_cwa(_KB,sf(A),sf(A)) :- !.
apply_cwa(_KB,X=Y,true) :-
        X == Y, !.
apply_cwa(KB,F,true) :-
        ground(F),
        (isfluent(F);isrigid(F)),
        user:cwa(F),
        kb_axiom(KB,F), !.
apply_cwa(KB,F,false) :-
        ground(F),
        (isfluent(F);isrigid(F)),
        user:cwa(F),
        not(kb_axiom(KB,F)), !.
% maybe too expensive...
apply_cwa(KB,F,R) :-
        not(ground(F)),
        (isfluent(F);isrigid(F)),
        user:cwa(F), !,
        term_variables(F,Vars),
        findall((Vars,Unifier),
                (kb_axiom(KB,FI),
                 unifiable((F,Vars),(FI,Vars),Unifier)),
                Instances),
        describe_instances(Vars,Instances,R).
apply_cwa(_KB,F,true) :-
        ground(F),
        F =.. [Type,Ele],
        is_type(Type),
        is_type_element(Type,Ele), !.
apply_cwa(_KB,F,false) :-
        ground(F),
        F =.. [Type,Ele],
        is_type(Type),
        not(is_type_element(Type,Ele)), !.
% maybe too expensive...
apply_cwa(_KB,F,R) :-
        nonvar(F),
        F =.. [Type,Var],
        var(Var),
        is_type(Type), !,
        findall((Var,Unifier),
                (is_type_element(Type,Ele),
                 unifiable(Var,Ele,Unifier)),
                Instances),
        describe_instances(Var,Instances,R).
apply_cwa(KB,F1,R) :-
        def(F1,F2), !,
        apply_cwa(KB,F2,R).
apply_cwa(KB,-F1,R) :- !,
        apply_cwa(KB,F1,F2),
        apply_cwa_neg(KB,F2,R).
apply_cwa(KB,(F1+F2),R) :- !,
        apply_cwa(KB,F1,F3),
        apply_cwa_or(KB,F3,F2,R).
apply_cwa(KB,(F1*F2),R) :- !,
        apply_cwa(KB,F1,F3),
        apply_cwa_and(KB,F3,F2,R).
apply_cwa(KB,(F1<=>F2),R) :- !,
        apply_cwa(KB,F1,F3),
        apply_cwa(KB,F2,F4),
        apply_cwa_equiv(KB,F3,F4,R).
apply_cwa(KB,(F1=>F2),R) :- !,
        apply_cwa(KB,F2,F4),
        apply_cwa_impl(KB,F1,F4,R).
apply_cwa(KB,(F1<=F2),R) :- !,
        apply_cwa(KB,F1,F3),
        apply_cwa_lpmi(KB,F3,F2,R).
apply_cwa(KB,some_t([],F),R) :- !,
        apply_cwa(KB,F,R).
apply_cwa(KB,some_t([V-T|VTs],F),R) :- !,
        findall(E,is_type_element(T,E),Es),
        apply_cwa(KB,some_inst(V,Es,some_t(VTs,F)),R).
apply_cwa(_KB,some_inst(_,[],_F),false) :- !.
apply_cwa(KB,some_inst(V,[E|Es],F),R) :- !,
        subv(V,E,F,FI),
        apply_cwa(KB,FI+some_inst(V,Es,F),R).
apply_cwa(KB,all_t([],F),R) :- !,
        apply_cwa(KB,F,R).
apply_cwa(KB,all_t([V-T|VTs],F),R) :- !,
        findall(E,is_type_element(T,E),Es),
        apply_cwa(KB,all_inst(V,Es,all_t(VTs,F)),R).
apply_cwa(_KB,all_inst(_,[],_F),true) :- !.
apply_cwa(KB,all_inst(V,[E|Es],F),R) :- !,
        subv(V,E,F,FI),
        apply_cwa(KB,FI*all_inst(V,Es,F),R).
apply_cwa(KB,some(Vars,F1),some(Vars,F2)) :- !,
        apply_cwa(KB,F1,F2).
        % todo: apply una here?
apply_cwa(KB,all(Vars,F1),all(Vars,F2)) :- !,
        apply_cwa(KB,F1,F2).
        % todo: apply una here?
apply_cwa(_KB,F,F) :- !.

apply_cwa_neg(_KB,true,false) :- !.
apply_cwa_neg(_KB,false,true) :- !.
apply_cwa_neg(_KB,-F,F) :- !.
apply_cwa_neg(_KB,F,-F).

apply_cwa_or(_KB,true,_,true) :- !.
apply_cwa_or(KB,false,F,R) :- !,
        apply_cwa(KB,F,R).
apply_cwa_or(KB,F1,F2,(F1+R2)) :-
        apply_cwa(KB,F2,R2).

apply_cwa_and(_KB,false,_,false) :- !.
apply_cwa_and(KB,true,F,R) :- !,
        apply_cwa(KB,F,R).
apply_cwa_and(KB,F1,F2,(F1*R2)) :-
        apply_cwa(KB,F2,R2).

apply_cwa_equiv(_KB,false,false,true) :- !.
apply_cwa_equiv(_KB,false,true,false) :- !.
apply_cwa_equiv(_KB,true,false,false) :- !.
apply_cwa_equiv(_KB,true,true,true) :- !.
apply_cwa_equiv(_KB,F1,F2,true) :-
        F1 == F2, !.
apply_cwa_equiv(_KB,F1,F2,F1<=>F2).

apply_cwa_impl(_KB,_,true,true) :- !.
apply_cwa_impl(KB,F,false,R) :- !,
        apply_cwa(KB,-F,R).
apply_cwa_impl(KB,F1,F2,(R1=>F2)) :-
        apply_cwa(KB,F1,R1).

apply_cwa_lpmi(_KB,true,_,true) :- !.
apply_cwa_lpmi(KB,false,F,R) :- !,
        apply_cwa(KB,-F,R).
apply_cwa_lpmi(KB,F1,F2,(F1<=R2)) :-
        apply_cwa(KB,F2,R2).

apply_cwa_some(_KB,true,_,_,true) :- !.
apply_cwa_some(_KB,false,_,_,false) :- !.
apply_cwa_some(KB,unknown,Vars,F,some(Vars,R)) :- !,
        apply_cwa(KB,F,R).

apply_cwa_all(_KB,true,_,_,true) :- !.
apply_cwa_all(_KB,false,_,_,false) :- !.
apply_cwa_all(KB,unknown,Vars,F,all(Vars,R)) :- !,
        apply_cwa(KB,F,R).

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

/**
  * eval_cwa(?Formula) is nondet
  *
  * Succeeds if the formula holds under the closed-world assumption.
  * Free variables are understood as existentially quantified and will
  * be instantiated, where every answer subsitution corresponds to one
  * solution.
  *
  * @arg KBID    the identifier (handle) of the KB containing facts to
  *              be used for evaluation
  * @arg Formula a static objective formula about the initial
  *              situation, possibly with free variables
  **/
eval_cwa(KB,F) :-
        user:def(F,FD), !,
        eval_cwa(KB,FD).
eval_cwa(KB,Atom) :-
        (isfluent(Atom);isrigid(Atom)),
        user:cwa(Atom),
        kb_axiom(KB,Atom).
eval_cwa(KB,Atom) :-
        (isfluent(Atom);isrigid(Atom)),
        not(user:cwa(Atom)),
        report_message(warn,['Warning: Applying closed-world',
                             ' assumption to non-CWA atom <',
                             Atom, '>!']),
        kb_axiom(KB,Atom).
eval_cwa(_KB,TAtom) :-
        TAtom =.. [Type,Arg],
        is_type(Type),
        is_type_element(Type,Arg).
eval_cwa(_KB,X=Y) :-
        X = Y.
eval_cwa(_KB,true).
eval_cwa(_KB,false) :- fail.
eval_cwa(KB,F1*F2) :-
        eval_cwa(KB,F1),
        eval_cwa(KB,F2).
eval_cwa(KB,F1+F2) :-
        eval_cwa(KB,F1);
        eval_cwa(KB,F2).
eval_cwa(KB,-F) :-
        not(eval_cwa(KB,F)).
eval_cwa(KB,F1<=>F2) :- !,
        eval_cwa(KB,(F1=>F2)*(F2=>F1)).
eval_cwa(KB,F1=>F2) :- !,
        eval_cwa(KB,(-F1)+F2).
eval_cwa(KB,F1<=F2) :- !,
        eval_cwa(KB,F1+(-F2)).
eval_cwa(KB,some_t([V-T|VTs],F)) :-
        is_type_element(T,E),
        subv(V,E,F,F1), % substitute, vars may be reused!
        eval_cwa(KB,some_t(VTs,F1)).
eval_cwa(KB,some_t([],F)) :- !,
        eval_cwa(KB,F).
eval_cwa(KB,all_t(VTs,F)) :-
        eval_cwa(KB,-some_t(VTs,-F)).

/**
  * is_type(?Type) is nondet.
  *
  * Unifies Type with a term representing a type, either declared by
  * the user as primitive type by means of user:type/1 or
  * user:subtype/2, or a term of the form either(List), where List is
  * a list of such primitive types.
  *
  * @arg Type a variable or an atom, representing a primitive type, or
  *           a term of the form either(List), where List is a list of
  *           atoms representing the union of primitive types
  **/
is_type(T) :-
        is_primitive_type(T).
is_type(T) :-
        nonvar(T),
        T = either([T2]),
        is_primitive_type(T2).
is_type(T) :-
        nonvar(T),
        T = either([T2|Ts]),
        is_primitive_type(T2),
        is_type(either(Ts)).

is_primitive_type(T) :-
        user:type(T).
is_primitive_type(T) :-
        user:subtype(_,T).

/**
  * is_type_element(?Type, ?Element) is nondet.
  *
  * Unifies Type with a ground term representing a type, and Element
  * with an atom representing a standard name such that Element is an
  * element of type Type. Type terms are the same as for is_type/1,
  * i.e., either an atom representing a primitive term declared by the
  * user by means of user:type/1 or user:subtype/2, or an expression
  * either(List), where List is a list of such primitive types.
  *
  * @arg Type    a ground term representing a type
  * @arg Element a variable or an atom, representing a standard name
  **/
is_type_element(T,E) :-
        is_primitive_type(T),
        user:domain(T,E).
is_type_element(T,E) :-
        user:subtype(T,TS),
        is_type_element(TS,E).
is_type_element(T,E) :-
        nonvar(T),
        T = either([T2]),
        is_primitive_type(T2),
        is_type_element(T2,E).
is_type_element(T,E) :-
        nonvar(T),
        T = either([_|Ts]),
        is_type_element(either(Ts),E).

/**
  * is_instance(+TypedVarList, ?Term) is nondet.
  *
  * Unifies Term with a variant where all typed variables from
  * TypedVarList have been instantiated using is_type_element/2.
  *
  * @arg TypedVarList a list of typed variables
  * @arg Term         a term, all of whose variables that appear in
  *                   TypedVarList will be instantiated
  **/
is_instance([],_).
is_instance([V-T|VTs],X) :-
        is_type_element(T,V),
        is_instance(VTs,X).

/**
  * untype(+Formula,-Result) is det.
  *
  * Turns a typed quantified formula into an equivalent one where the
  * type information is represented through unary predicates. E.g.,
  * some_t([X-type],F) becomes some([X],type(X)*F), and
  * all_t([X-type],F) becomes all([X],type(X)=>F).
  * 
  * @arg Formula a static, objective formula
  * @arg Result  an equivalent formula with type information encoded
  *              through unary predicates and standard quantifiers
  **/
untype(F1*F2,F3*F4) :- !,
        untype(F1,F3),
        untype(F2,F4).
untype(F1+F2,F3+F4) :- !,
        untype(F1,F3),
        untype(F2,F4).
untype(-F1,-F2) :- !,
        untype(F1,F2).
untype(F1<=>F2,F3<=>F4) :- !,
        untype(F1,F3),
        untype(F2,F4).
untype(F1=>F2,F3=>F4) :- !,
        untype(F1,F3),
        untype(F2,F4).
untype(F1<=F2,F3<=F4) :- !,
        untype(F1,F3),
        untype(F2,F4).
untype(some(Vars,F1),F2) :-
        Vars == [], !,
        untype(F1,F2).
untype(all(Vars,F1),F2) :-
        Vars == [], !,
        untype(F1,F2).
untype(some_t(Vars,F1),F2) :-
        Vars == [], !,
        untype(F1,F2).
untype(all_t(Vars,F1),F2) :-
        Vars == [], !,
        untype(F1,F2).
untype(some(Vars,F1),some(Vars,F2)) :- !,
        untype(F1,F2).
untype(all(Vars,F1),all(Vars,F2)) :- !,
        untype(F1,F2).
untype(some_t(VTs,F1),some(Vs,TVFml*F2)) :- !,
        untype_vars(VTs,Vs,TVFml),
        untype(F1,F2).
untype(all_t(VTs,F1),all(Vs,TVFml=>F2)) :- !,
        untype_vars(VTs,Vs,TVFml),
        untype(F1,F2).
untype(F1,F2) :-
        def(F1,F3), !,
        untype(F3,F2).
untype(F,F) :- !.

untype_vars(VTs,Vs,TVFml) :- !,
        types_cons(VTs,Cons),
        free_variables(Cons,Vs),
        conjoin(Cons,TVFml).

/**
  * types_cons(+TypedVarList,-ResultList) is det.
  *
  * Given a list of typed variables, returns a list of formulas
  * corresponding to equivalent type constraints where primitive types
  * are represented as unary predicates. For example, if 'block' is a
  * primitive type, X-block is translated to block(X), and an
  * expression  X-either([car,bike]) to car(X)+bike(X).
  *
  * @arg TypedVarList a list of typed variables
  * @arg ResultList   a list representing these type constraints
  *                   through formulas
  **/
types_cons([],[]).
% X is an atom (std.name) => check if type is correct
types_cons([X-T|XTs],Pres) :-
        atomic(X), !,
        is_type_element(T,X),
        types_cons(XTs,Pres).
% X is anything else, T is primitive => treat T as unary rigid predicate
types_cons([X-T|XTs],[Pre|Pres]) :-
        atomic(T), !,
        Pre =.. [T,X],
        types_cons(XTs,Pres).
% X is anything else, T is either([...]) => disjunction
types_cons([X-T|XTs],[Pre|Pres]) :-
        T = either(Ts), !,
        types_con_either(Ts,X,Pre),
        types_cons(XTs,Pres).

types_con_either([T],X,Pre) :- !,
        Pre =.. [T,X].
types_con_either([T|Ts],X,Pre) :- !,
        Pre1 =.. [T,X],
        types_con_either(Ts,X,Pre2),
        Pre = Pre1+Pre2.

/**
  * get_types(+VarList,+TypedVarList,-Result) is det.
  *
  * Given a list of variables VarList and a list of typed variables
  * TypedVarList, returns the subset of TypedVarList for variables
  * that occur in VarList. A variable that occurs untyped in VarList,
  * but has no typed counterpart in TypedVarList is not included in
  * the result.
  *
  * For example, get_type([X,Y],[Y-typeA,Z-typeB],Result) will yield
  * in Result = [Y-typeA].
  *
  * @arg VarList      a list of variables without associated types
  * @arg TypedVarList a list of variables with associated types
  * @arg Result       a list of those variables with associated types
  *                   from TypedVarList that also occur in VarList
  **/
get_types([],_YTs,[]) :- !.
get_types([X|Xs],YTs,[X-T|XTs]) :-
        get_type(X,YTs,T), !,
        get_types(Xs,YTs,XTs).
get_types([_|Xs],YTs,XTs) :- !,
        get_types(Xs,YTs,XTs).

get_type(Var,[X-T|_XTs],T) :-
        Var == X, !.
get_type(Var,[_-_|XTs],T) :- !,
        get_type(Var,XTs,T).
get_type(_Var,[],_T) :- !, fail.
