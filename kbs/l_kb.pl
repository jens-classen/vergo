/**

<module> Knowledge Base under Base Logic L

This module encapsulates a data structure for managing and accessing a
single or multiple knowledge bases whose formulas are elements of the
logic 'L', i.e., first-order logic with standard names.

Queries will be first evaluated according to the closed-world and
unique names assumption, where applicable, before being processed by
the theorem prover.

Knowledge bases are identified through a unique identifier that be can
be any fully grounded Prolog term, e.g. a name such as 'kb1', or a
list of ground actions, for example to indicate that the KB is the
result of progressing through this action sequence.

A special identifier is 'userdb', indicating that the KB works
directly on facts of the dynamic predicate initially/1 inside user
space. Otherwise, KB formulas will be stored inside this module as
facts of the dynamic predicate kb_axiom/2.

@author  Jens Claßen
@license GPLv2

*/
:- module(l_kb, [initialize_kb/1,
                 kb_axiom/2,
                 entails_kb/3,
                 extend_kb_by/2,
                 print_kb/1,
                 get_kb_std_names/2,
                 update_kb/3,
                 create_kb/2,
                 delete_kb/1,
                 copy_kb/2,
                 kb_as_list/2]).

:- reexport(['../logic/l']).

:- use_module('../logic/cwa').
:- use_module('../logic/def').
:- use_module('../logic/l').
:- use_module('../logic/una').
:- use_module('../lib/utils').

:- dynamic kb_axiom/2.
:- dynamic user:initially/1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Initialize KB
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * initialize_kb(++KBID) is det.
  *
  * Initializes a new knowledge base from facts provided by means of
  * the initially/1 predicate in user space, usually as part of a
  * basic action theory. If a knowledge base with the specified
  * identifier already exists, it will be overwritten.
  *
  * @arg KBID the identifier (handle) to be used for the KB, must be a
  *           ground term; if 'userdb' is used, the KB will work
  *           directly on the facts of the dynamic predicate
  *           initially/1 in user space, otherwise formulas will be
  *           stored internally as facts of kb_axiom/2.
 **/
initialize_kb(userdb) :- !. % nothing to do
initialize_kb(KB) :- !,
        ground(KB), % KB ID has to be ground term
        delete_kb(KB),
        forall(user:initially(F),
               assert(kb_axiom(KB,F))).

/**
  * kb_axiom(++KBID,?Fml) is nondet.
  *
  * Dynamic predicate that is managed by this module and succeeds iff
  * Fml unifies with a formula that is part of the knowledge base with
  * ID KBID.
  *
  * @arg KBID  the identifier (handle) of the KB in question, must be
  *            a ground term
  * @arg Fml   a term representing a formula
 **/
kb_axiom(userdb,F) :- % work on fact in user space directly
        user:initially(F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check formula against KB
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * entails_kb(++KBID,+Fml,-Truth) is det.
  *
  * Returns the truth value of whether the provided formula is
  * entailed in logic L by the given knowledge base. Parts of the
  * formula that are subject to the closed-world and unique names
  * assumption will first be evaluated, before the query is handed
  * over to the theorem prover.
  *
  * @arg KBID  the identifier (handle) of the KB in question, must be
  *            a ground term
  * @arg Fml   a term representing a formula
  * @arg Truth 'true' if the formula is entailed, 'false' if not
 **/
entails_kb(KB,Fml,Truth) :-
        apply_cwa(KB,Fml,FmlP), % includes macro expansion
        entails_kb2(KB,FmlP,Truth).

% don't call theorem prover on 'true'
entails_kb2(_KB,true,true) :- !.
% call theorem prover only on non-trivial formula
entails_kb2(KB,Fml,Truth) :-
        findall(IniFml,
                initial_axiom(KB,IniFml),
                KBAxioms),
        entails_l(KBAxioms,Fml,Truth), !.

initial_axiom(KB,F) :-
        kb_axiom(KB,F2),
        not(cwa(F2)), % CWA is compiled away from queries
        apply_cwa(KB,F2,F3),
        apply_una(F3,F4),
        simplify(F4,F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Pretty-print KB
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * print_kb(++KBID) is det.
  *
  * Pretty-prints the knowledge base with the given identifier to
  * standard output.
  *
  * @arg KBID  the identifier (handle) of the KB in question, must be
  *            a ground term
 **/
print_kb(KB) :-
        kb_axiom(KB,F),
        write_readable(F),
        write('\n'),
        fail.
print_kb(_KB).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Extend KB by new formula
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * extend_kb_by(++KBID,+Fml) is det.
  *
  * Extends the specified knowledge base by the given formula. This
  * means the formula is added to the knowledge base if it is not
  * already entailed by it.
  *
  * @arg KBID  the identifier (handle) of the KB in question, must be
  *            a ground term
  * @arg Fml   a term representing a formula
 **/
extend_kb_by(KB,Fml) :-
        entails_kb(KB,Fml,true), !.
extend_kb_by(KB,Fml) :- !,
        add_to_kb(KB,Fml).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Standard names in KB
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * get_kb_std_names(++KBID,-Names) is det.
  *
  * Returns a (sorted) list (without duplicates) of all standard names
  * appearing in the formulas of the specified knowledge base.
  *
  * @arg KBID  the identifier (handle) of the KB in question, must be
  *            a ground term
  * @arg Fml   a list of all standard names in the KB
 **/
get_kb_std_names(KB,Names) :- !,
        findall(Names2,
                (kb_axiom(KB,Fml),
                 get_fml_std_names(Fml,Names2)),
                Names3),
        flatten(Names3,Names4),
        findall(DName,
                (is_type_element(_Type,DName)),
                Names5),
        append(Names4,Names5,Names6),
        sort(Names6,Names).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Update KB to new KB
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * update_kb(++KBID1,+Mods,++KBID2) is det.
  *
  * Applies a list of modifications (adds and deletes of formulas) to
  * a specified knowledge base in order to obtain a new knowledge base
  * under a (different or equal) new identifier.
  *
  * If the identifiers of the old and new KB are identical, the update
  * will be performed "in situ", i.e. the modifications will be applied
  * directly to the knowledge base itself. Otherwise, a new knowledge
  * base under the specified second identifier will be created by
  * first copying the old one and then applying the modifications to
  * it. If a knowledge base under the second identifier already exists,
  * it will be overwritten.
  *
  * @arg KBID1 the identifier (handle) of an existing (current) KB,
  *            must be a ground term
  * @arg Mods  a list of modifications as terms of the form 'add(Fml)'
  *            and/or 'del(Fml)', where the 'Fml' are terms
  *            representing formulas to be deleted or added,
  *            respectively
  * @arg KBID2 the identifier (handle) of the target KB, must be a
  *            ground term
 **/
update_kb(KB1,Mods,KB2) :-
        KB1 == KB2, !,
        apply_mods(KB1,Mods).
update_kb(KB1,Mods,KB2) :-
        copy_kb(KB1,KB2),
        apply_mods(KB2,Mods).

apply_mods(_KB,[]) :- !.
apply_mods(KB,[add(Fml)|Mods]) :- !,
        add_to_kb(KB,Fml),
        apply_mods(KB,Mods).
apply_mods(KB,[del(Fml)|Mods]) :- !,
        del_fr_kb(KB,Fml),
        apply_mods(KB,Mods).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Helper predicates
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * create_kb(++KBID,+Fmls) is det.
  *
  * Create a new KB with the specified name from the given list of
  * formulas. If a KB of that name already exists, it will be
  * overwritten.
  *
  * @arg KBID  the identifier (handle) of the KB to be created
  * @arg Fmls  a list of formulas to be inserted into the new KB
 **/
create_kb(KB,Fmls) :- !,
        delete_kb(KB),
        forall(member(Fml,Fmls),add_to_kb(KB,Fml)).

/**
  * delete_kb(++KBID) is det.
  *
  * Deletes the specified KB.
  *
  * @arg KBID  the identifier (handle) of the KB to be deleted
 **/
delete_kb(userdb) :- !,
        retractall(user:initially(_)).
delete_kb(KB) :- !,
        retractall(kb_axiom(KB,_)).

/**
  * copy_kb(++KB1,++KB2) is det.
  *
  * Creates a copy of KBID1 with identifier KBID2. If KBID2 already
  * exists, it will be overwritten.
  *
  * @arg KBID  the identifier (handle) of the KB to be deleted
 **/
copy_kb(KB,KB) :- !. % do nothing if KB1=KB2
copy_kb(KB1,KB2) :- !,
        delete_kb(KB2),
        forall(kb_axiom(KB1,Fml),
               assert(kb_axiom(KB2,Fml))).

add_to_kb(userdb,Fml) :- !,
        assert(user:initially(Fml)).
add_to_kb(KB,Fml) :- !,
        assert(kb_axiom(KB,Fml)).
del_fr_kb(userdb,Fml) :-
        retract(user:initially(Fml)), !.
del_fr_kb(KB,Fml) :-
        retract(kb_axiom(KB,Fml)), !.
del_fr_kb(_,_) :- !. % if fml not exists

/**
  * kb_as_list(++KBID,-List) is det.
  *
  * Returns a list of all formulas contained in the KB with the
  * specified identifier.
  *
  * @arg KBID the identifier (handle) of the KB
  * @arg List a list of all formulas in the KB
 **/
kb_as_list(KB,List) :- !,
        findall(Fml,kb_axiom(KB,Fml),List).
