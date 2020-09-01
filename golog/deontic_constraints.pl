/**
 
<module> Deontic Constraints

This module implements an approach for expressing deontic constraints
by means of conditionals over program expressions that induce a
ranking over the set of available actions, as described in

Jens Claßen and James Delgrande: "Dyadic Obligations over Complex
Actions as Deontic Constraints in the Situation Calculus", in
Proceedings of KR 2020, AAAI Press.

The computation used for determining a ranking is similar to that for
rational closure as in

Daniel J. Lehmann and Menachem Magidor: "What does a conditional
knowledge base entail?", Artificial Intelligence, 55(1):1–60, 1992.

with the difference that program expressions take the place of
propositional formulas, and reachability/executability that of
consistency. Moreover, this module supports three different types of
conditionals:

    p  ~> q,     read as "if about to do p, ought to do q instead"
    p ~a> q,     read as "if about to do p, ought to do q afterwards"
    p ~b> q,     read as "if about to do p, ought to do q before"

@author  Jens Claßen
@license GPLv2

 **/
:- module(deontic_constraints, [action_rank/3,
                                construct_ranking/2,
                                create_action_costs/1,
                                report_ranking/0,
                                op(1150, xfy, ~>),
                                op(1150, xfy, '~a>'),
                                op(1150, xfy, '~b>')]).

:- op(1150, xfy, ~>).
:- op(1150, xfy, '~a>').
:- op(1150, xfy, '~b>').

:- use_module(library(pcre)).

:- use_module('../kbs/l_kb').
:- use_module('../logic/cwa').
:- use_module('../logic/fobdd').
:- use_module('../logic/una').
:- use_module('../lib/utils').

:- multifile user:program/2.

:- dynamic rcpart/6.
:- dynamic rcmax/1.
:- dynamic new_axiom/1.
:- dynamic program_name/2.
:- dynamic program_name_max/1.

/**
  * action_rank(+Action,?R,-Condition) is nondet.
  *
  * Given a (possibly non-ground) action term, returns a numeric rank
  * and a formula encoding a condition under which the action has that
  * rank. Before calling this predicate, the ranking needs to be
  * constructed once using construct_ranking/1.
  *
  * @arg Action    an action term
  * @arg R         a numerical (ordinal) rank
  * @arg Condition a formula representing the condition that the
  *                specified action has that rank
 **/
action_rank(Action,R,Condition) :-
        rcpart(R,Action,_Rules,_Mat,_Neg,Cond),
        simplify_fml(Cond,Condition),
        Condition \= false.

/**
 * construct_ranking(+RuleSet,+Axioms) is det.
 *
 * Given a list of conditionals RuleSet, constructs an internal
 * representation (through dynamic predicates) of a ranking according 
 * to rational closure. Prints a warning to standard output in case the
 * RuleSet does not satisfy Lehmann and Magidors admissibility
 * criterion. If temporal constraints are used, additional axioms for
 * representing the auxiliary `did(X)` fluent in a basic action theory
 * will be created, which can either be asserted directly into user
 * space (by passing `userdb` as second argument) or returned as a
 * list (by passing a term of the form `axioms(A)` as second argument,
 * where the list of axioms will be bound to `A`).
 *
 * @arg RuleSet a list of conditional rules, using `~>` or `~a>`/`~b>`
 * @arg Axioms  the constant `userdb`, or a term of the form
 *              `axioms(A)` with a free variable `A`
 */
construct_ranking(Rules,userdb) :- !,
        construct_ranking(Rules,axioms(Axioms)),
        forall(member(Axiom,Axioms),assert_if_not_exists(user:Axiom)).
construct_ranking(Rules,axioms(Axioms)) :- !,
        retractall(rcpart(_,_,_,_,_,_)),
        retractall(rcmax(_)),
        retractall(program_name(_,_)),
        retractall(program_name_max(_)),
        assert(program_name_max(0)),
        materialize_rules(A,Rules,Mat),
        assert(rcpart(0,A,Rules,Mat,-Mat,Mat)),
        construct_ranking_recursive(0,Axioms).
construct_ranking_recursive(I,Axioms) :-
        rcpart(I,A,Rules,Mat,Neg,_Bad),
        exceptional_rules(A,RulesEx,Rules,Mat),
        length(RulesEx,LengthEx),
        length(Rules,Length),
        LengthEx < Length, !, % proper subset
        I1 is I+1,
        materialize_rules(A,RulesEx,MatEx),
        simplify_fml(MatEx*Neg,BadCond),
        assert(rcpart(I1,A,RulesEx,MatEx,(-MatEx)*Neg,BadCond)),
        construct_ranking_recursive(I1,Axioms).
construct_ranking_recursive(I,Axioms) :- !,
        assert(rcmax(I)),
        check_admissibility(I),
        report_ranking,
        % axioms for additional "did" fluents
        findall(Axiom,new_axiom(Axiom),Axioms).

% the set is inadmissable if there are rules "left over" at the max rank
check_admissibility(I) :-
        rcpart(I,_A,[],_,_,_), !.
check_admissibility(_) :- !,
        report_message(warn,
                       ['Warning: The provided set of conditionals is ',
                        'not admissible!']). 

exceptional_rules(A,RulesEx,Rules,MatRules) :-
        findall(Rule,
                (member(Rule,Rules),
                 exceptional(A,Rule,MatRules)),
                RulesEx).

exceptional(A,L~>_,MatRules) :-
        gprogram_formula(A,L,LFml),
        minimize(some(A,LFml*MatRules),Fml1),
        equivalent_l(Fml1,false,true).
exceptional(A,L'~a>'_,MatRules) :-
        gprogram_formula(A,[L,any],LFml),
        minimize(some(A,LFml*MatRules),Fml1),
        equivalent_l(Fml1,false,true).
exceptional(A,L'~b>'_,MatRules) :-
        gprogram_formula(A,[any,L],LFml),
        minimize(some(A,LFml*MatRules),Fml1),
        equivalent_l(Fml1,false,true).

materialize_rules(A,Rules,R) :- !,
        materialize_rules2(A,Rules,MRules),
        conjoin(MRules,M),
        simplify_fml(M,R).
materialize_rules2(_,[],[]).
materialize_rules2(A,[Rule|Rules],[RuleM|RulesM]) :-
        materialize_rule(A,Rule,RuleM),
        materialize_rules2(A,Rules,RulesM).

materialize_rule(A,L~>R,M) :-
        gprogram_formula(A,nondet(not(L),R),Fml),
        simplify_fml(Fml,M).
materialize_rule(A,L'~a>'R,M) :-
        gprogram_formula(A,nondet([not(L),any],[any,R]),Fml),
        simplify_fml(Fml,M).
materialize_rule(A,L'~b>'R,M) :-
        gprogram_formula(A,nondet([any,not(L)],[R,any]),Fml),
        simplify_fml(Fml,M).

% Convert a program to a formula, with free action variable A.
% Corresponds to C operator from paper.
gprogram_formula(A,B,(A=B)) :-
        var(B), !.
gprogram_formula(A,[P],F) :- !,
        gprogram_formula(A,P,F).
gprogram_formula(A,P,F) :-
        program(P,D), !,
        gprogram_formula(A,D,F).
gprogram_formula(A,B,(A=B)) :-
        (poss(B,_);poss(B,_,_)), !.
gprogram_formula(A,pick(X,P),some(X,F)) :- !,
        gprogram_formula(A,P,F).
gprogram_formula(A,pick(X,T,P),F) :- !,
        findall((A,FE),
                (is_type_element(T,E),
                 subv(X,E,P,PE),
                 gprogram_formula(A,PE,FE)),
              AFEs),
        inst_conds(A,AFEs,Conds),
        disjoin(Conds,F).
gprogram_formula(A,[test(Phi)|P],Phi*F) :- !,
        gprogram_formula(A,P,F).
gprogram_formula(A,not(P),-F) :- !,
        gprogram_formula(A,P,F).
gprogram_formula(A,nondet(P1,P2),F1+F2) :- !,
        gprogram_formula(A,P1,F1),
        gprogram_formula(A,P2,F2).
gprogram_formula(A,and(P1,P2),F1*F2) :- !,
        gprogram_formula(A,P1,F1),
        gprogram_formula(A,P2,F2).
gprogram_formula(A,[P1|P2],F1*F2) :- !,
        gprogram_did(P1,F1),
        gprogram_formula(A,P2,F2).

% instantiate conditions for a given action term
inst_conds(A,[(A,F)|AFs],[F|Fs]) :-
        inst_conds(A,AFs,Fs).
inst_conds(_,[],[]).

% For temporal conditionals, create new fluents memorizing whether a
% certain program expression happened previously.
gprogram_did(P,F) :-
        gprogram_formula(A,P,F2),
        simplify_fml(F2,F3),
        gprogram_did2(P,A,F3,F).
gprogram_did2(_P,_A,false,false,[]) :- !.
gprogram_did2(not(P),A,F,R) :- !,
        gprogram_did2(P,A,-F,R1),
        simplify_fml(-R1,R).
gprogram_did2(P,A,F,did(N)) :- !,
        simplify_fml(F,FS),
        create_ssa(P,A,FS),
        program_to_name(P,N).

create_ssa(P,A,F) :-
        program_to_name(P,N),
        simplify_fml(-F,NF),
        assert_if_not_exists(new_axiom(rel_fluent(did(X),[X-golog_program]))),
        assert_if_not_exists(new_axiom(cwa(did(_)))),
        assert_if_not_exists(new_axiom(domain(golog_program,N))),
        assert_if_not_exists(new_axiom(causes_true(did(N),A,F))),
        assert_if_not_exists(new_axiom(causes_false(did(N),A,NF))).

% Represent a program expression by a unique standard name (module
% variable renaming) by turning the term into an atom, replacing every
% character that is not a letter, a number, or '_' by '_',
% substituting variables by 'x1','x2','x3',..., and putting '#' in
% front.
program_to_name(P,N) :- !,
        copy_term(P,PC),
        term_variables(PC,Vars),
        inst_vars(PC,Vars,1),
        term_to_atom(PC,A1),
        re_replace('\\W'/ga,'_',A1,A2),
        atom_concat('#',A2,N).

inst_vars(_,[],_) :- !.
inst_vars(P,[V|Vs],I) :- !,
        atom_concat('x',I,XI),
        V = XI,
        I1 is I+1,
        inst_vars(P,Vs,I1).

% Only assert a clause if it does not yet exists.
assert_if_not_exists(G) :-
        G, !.
assert_if_not_exists(G) :-
        assert(G), !.

/**
  * create_action_costs(+Axioms) is det.
  *
  * With this predicate, a ranking (that has been previously computed
  * through construct_ranking/1) is converted into axioms that
  * interpret ranks as costs of actions, represented through a numeric
  * functional fluent 'total-cost' in the style of PDDL. The axioms
  * can either be returned as result (by using `axioms(A)` as argument,
  * where A will be bound to a list of axioms), or asserted directly
  * into user space (by using `userdb` as argument).
  *
  * @arg Axioms a term of the form axioms(Axioms), or `userdb`
 **/
create_action_costs(userdb) :- !,
        create_action_costs(axioms(Axioms)),
        forall(member(Axiom,Axioms),assert_if_not_exists(user:Axiom)).
create_action_costs(axioms(Axioms)) :- !,
        % cost axioms for actions
        findall(Axiom,
                (cost_axioms_action(CAxioms),
                 member(Axiom,CAxioms)),
                Axioms1),
        % total cost function
        Axioms2 = [fun_fluent('total-cost',number,[]),
                   cwa('total-cost'=_),
                   initially('total-cost'=0),
                   metric(deontic,minimize('total-cost'))],
        append([Axioms1,Axioms2],Axioms).

% case: non-typed action => use conditional effects
cost_axioms_action([Axiom]) :-
        poss(A,_),
        action_rank(A,I,Cond1),
        simplify_fml(Cond1,Cond),
        Cond \= false,
        Axiom = causes(A,'total-cost',Y,((Y='total-cost'+I)*Cond)).

% case: typed action => use special cost functions for use in PDDL
cost_axioms_action(Axioms) :-
        poss(A,VTs,_),
        relevant_args(A,VTs,Args),
        action_cost_fct(A,Args,Fct),
        get_types(Args,VTs,ArgTs),
        findall(Axiom,
                cost_axioms_action_instance(A,VTs,Args,Axiom),
                Axioms1),
        append([fun_fluent(Fct,number,ArgTs),
                cwa(Fct=_),
                causes(A,'total-cost',Y,(Y='total-cost'+Fct))],
               Axioms1,Axioms).

% relevant arguments = only those mentioned in a rank condition
relevant_args(A,VTs,Args) :- !,
        relevant_args(A,VTs,Args,1).
relevant_args(_A,_VTs,[],I) :-
        rcmax(M), I > M, !.
relevant_args(A,VTs,Args,I) :- !,
        action_rank(A,I,Cond1),
        simplify_fml(Cond1,Cond),
        term_variables(Cond,Args1),
        I1 is I+1,
        relevant_args(A,VTs,Args2,I1),
        union2(Args1,Args2,Args).

cost_axioms_action_instance(A,VTs,Args,Axiom) :-
        is_instance(VTs,A),
        action_rank(A,I,Cond1),
        simplify_fml(Cond1,Cond),
        Cond \= false, % todo: non-static case?
        valid_l(Cond,true),
        action_cost_fct(A,Args,Fct),
        Axiom = initially(Fct=I).

action_cost_fct(A,RArgs,F) :-
        A =.. [Act|_],
        atom_concat(Act,'_cost',ActN),
        F =.. [ActN|RArgs].

/**
 * report_ranking is det.
 *
 * Prints a presentation of the internal representation of the KB to
 * standard output.
 */
report_ranking :-
        rcpart(0,A,_,_,_,_), !,
        write('Ranking (free action variable is '),
        write(A),
        write('):\n'),
        write('------------------------------------------------\n'),
        report_ranking(0,A).
report_ranking(I,_A) :-
        rcmax(Max),
        I > Max, !,
        write('------------------------------------------------\n').
report_ranking(I,A) :-
        rcpart(I,A,Rules,RulesMat,_Neg,BadCond),
        report_rank(I,A,Rules,RulesMat,BadCond),
        I1 is I+1,
        report_ranking(I1,A).
report_rank(I,_A,Rules,RulesMat,BadCond) :-
        write('Rank '),
        write(I),
        write(':\n'),
        write('\tRules          : '),
        write(Rules),
        write('\n'),
        write('\tMaterialization: '),
        write(RulesMat),
        write('\n'),
        write('\tCondition      : '),
        write(BadCond),
        write('\n').

% formula simplification
simplify_fml(F,R) :- !,
        minimize(F,R).
