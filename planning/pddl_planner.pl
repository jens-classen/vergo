/**

PDDL Planner

This module provides functionality for solving planning tasks in Golog
by means of a PDDL planner following the approach described in [Claßen
et al. 2007] and [Claßen 2013, Ch. 4].

All involved fluents and rigids have to underly the closed-world
assumption, and all involved fluents, rigids and actions must be
typed.

So far, this module supports what can be mapped to PDDL's ADL fragment
together with (number and object) functions, metrics, and action
costs.

As PDDL planner, at the moment only Fast Downward (www.fast-
downward.org) is being used, but support for other planners may be
included in the future.

References:

      [Claßen et al. 2007] Claßen, J.; Eyerich, P.; Lakemeyer, G.;
           and Nebel, B. 2007. Towards an integration of Golog
           and planning. In Proceedings of IJCAI-07, AAAI Press.

      [Claßen 2013] Claßen, J. 2013. Planning and Verification in the
           Agent Language Golog. PhD Thesis, Department of Computer
           Science, RWTH Aachen University, 2013.

@author  Jens Claßen
@license GPLv2

**/

:- module(pddl_planner, [get_plan/3,
                         get_plan/4,
                         generate_domain/5,
                         generate_problem/3,
                         write_domain/7,
                         write_problem/7,
                         fastdownward/3,
                         read_plan/2,
                         preprocess_actions/3,
                         postprocess_actions/3]).

:- use_module('../kbs/l_kb').
:- use_module('../lib/env').
:- use_module('../lib/utils').
:- use_module('../logic/cwa').
:- use_module('../logic/fol', [op(1130, xfy, <=>),
                               op(1110, xfy, <=),
                               op(1110, xfy, =>)]).
:- use_module(library(pio)).

:- multifile user:goal/2.
:- multifile user:def/2.
:- multifile user:metric/2.
:- multifile user:type/1.
:- multifile user:subtype/2.
:- multifile user:domain/2.
:- multifile user:cwa/1.
:- multifile user:rel_fluent/2.
:- multifile user:fun_fluent/3.
:- multifile user:rel_rigid/2.
:- multifile user:fun_rigid/3.
:- multifile user:causes_true/3.
:- multifile user:causes_false/3.
:- multifile user:causes/4.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Main Method
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * get_plan(++KB,+Goal,-Plan) is det.
  *
  * This predicate (1) generates a PDDL domain and problem from the
  * current state of the BAT, using all typed fluents (relational and
  * functional, including numeric ones) that are subject to the CWA,
  * all typed rigids (relational and functional, including numeric
  * ones) that are subject to the CWA, and all typed actions. It then
  * (2) calls the Fast Downward PDDL planner on it, and (3) converts
  * the resulting plan back into a sequence of actions. If there is no
  * solution plan, or Fast Downward did not find any, 'fail' is
  * returned.
  *
  * @arg KB   the identifier (handle) of the KB containing facts to
  *           be used for the initial state; use 'userdb' to work on
  *           facts given by user:initially/1
  * @arg Goal a goal, either in the form of a formula, or the name of
  *           a goal formula defined through goal/2 or def/2
  * @arg Plan a sequence (list) of actions representing a solution
  *           plan, or 'fail'
  */
get_plan(KB,Goal,Plan) :-
        get_plan(KB,Goal,none,Plan).

/**
  * get_plan(++KB,+Goal,+Metric,-Plan) is det.
  *
  * Similar as get_plan/2, but additionally uses a plan metric.
  *
  * @arg KB     the identifier (handle) of the KB containing facts to
  *             be used for the initial state; use 'userdb' to work on
  *             facts given by user:initially/1
  * @arg Goal   a goal, either in the form of a formula, or the name
  *             of a goal formula defined through goal/2 or def/2
  * @arg Metric a metric, either in the form of a term minimize(Exp)
  *             or maximize(Exp), or the name of a metric defined
  *             through metric/2, or 'none'
  * @arg Plan   a sequence (list) of actions representing a solution
  *             plan, or 'fail'
  */
get_plan(KB,Goal,Metric,Plan) :-
        goal_fml(Goal,GoalF),
        metric_def(Metric,MetricF),
        temp_domain_file(DomF),
        temp_problem_file(ProF),
        temp_plan_file(PlaF),
        temp_domain_name(Dom),
        temp_problem_name(Pro),
        generate_domain(Typ,Con,Pre,Fun,Act),
        generate_problem(KB,Obj,Ini),
        preprocess_actions(Act,Map,ActP),
        write_domain(DomF,Dom,Typ,Con,Pre,Fun,ActP),
        write_problem(ProF,Pro,Dom,Obj,Ini,GoalF,MetricF),
        fastdownward(DomF,ProF,PlaF),
        read_plan(PlaF,PlanFD),
        postprocess_actions(PlanFD,Map,Plan).

goal_fml(Goal,GoalF) :-
        user:goal(Goal,GoalF), !.
goal_fml(Goal,GoalF) :-
        user:def(Goal,GoalF), !.
goal_fml(Goal,Goal) :- !.

metric_def(Name,MetricF) :-
        user:metric(Name,MetricF), !.
metric_def(MetricF,MetricF) :- !.

temp_domain_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/domain.pddl', File).
temp_problem_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/problem.pddl', File).
temp_plan_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/sas_plan', File).

temp_domain_name(tmpdom).
temp_problem_name(tmppro).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Domains
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

generate_domain(Types,Constants,Predicates,Functions,Actions) :- !,
        collect_types(Types),
        collect_constants(Constants),
        collect_predicates(Predicates),
        collect_functions(Functions),
        collect_actions(Actions).

collect_types(Types) :- !,
        findall(subtypes(Type,SubTypes),
                (is_type(Type),
                 \+ \+ subtype(Type,_), % only one instance
                 findall(SubType,user:subtype(Type,SubType),SubTypes)),
                Types1),
        findall(type(Type),
                (user:type(Type),
                 not(user:subtype(Type,_)),
                 not(user:subtype(_,Type))),
                Types2),
        append(Types1,Types2,Types).

collect_constants(Constants) :- !,
        findall(C-T,
                (user:domain(T,C),
                 is_type(T),
                 mentioned_by_action(C)),
                Constants1),
        sort(Constants1,Constants). % remove duplicates

mentioned_by_action(X) :-
        causes_true(A,F,C),
        mentions((A,F,C),X).
mentioned_by_action(X) :-
        causes_false(A,F,C),
        mentions((A,F,C),X).
mentioned_by_action(X) :-
        causes(A,F,Y,C),
        mentions((A,F,Y,C),X).

mentions(X,O) :-
        nonvar(X),
        X = O, !.
mentions(X,O) :-
        nonvar(X),
        def(X,D), !,
        mentions(D,O).
mentions(L,O) :-
        is_list(L), !,
        mentions_list(L,O).
mentions(X,O) :-
        nonvar(X), !,
        X =.. [_|R],
        mentions(R,O).
mentions_list([X|L],O) :-
        mentions(X,O);
        mentions_list(L,O).

collect_predicates(Predicates) :- !,
        findall(predicate(Name,Args),
                (rel_fluent(Fluent,Args),
                 user:cwa(Fluent),
                 Fluent =.. [Name|_]),
                Predicates1),
        findall(predicate(Name,Args),
                (rel_rigid(Rigid,Args),
                 user:cwa(Rigid),
                 Rigid =.. [Name|_]),
                Predicates2),
        append(Predicates1,Predicates2,Predicates).

collect_functions(Functions) :- !,
        findall(function(Name,Type,Args),
                (fun_fluent(Fluent,Type,Args),
                 user:cwa(Fluent=_),
                 Fluent =.. [Name|_]),
                Functions1),
        findall(function(Name,Type,Args),
                (fun_rigid(Rigid,Type,Args),
                 user:cwa(Rigid=_),
                 Rigid =.. [Name|_]),
                Functions2),
        append(Functions1,Functions2,Functions).

collect_actions(Actions) :- !,
        findall(action(Name,Args,Precondition,Effects),
                (poss(A,Args,Precondition),
                 A =.. [Name|_],
                 collect_effects(A,Effects),
                 Effects \= [],
                 not(mentions_non_cwa(Effects))),
                Actions).

collect_effects(A,Effects) :- !,
        findall(Effect,
                is_effect(A,Effect),
                Effects2),
        instantiate_effects(A,Effects2,Effects).

is_effect(A,(A,QArgTypes,Cond,AddOrDel,F)) :-
        add_or_del(A,F,Cond,AddOrDel),
        user:rel_fluent(F,FArgTypes),
        user:cwa(F),
        F =.. [_FName|FArgs],
        A =.. [_AName|AArgs],
        setminus2(FArgs,AArgs,NArgs),
        term_variables(NArgs,NArgVars),
        get_types(NArgVars,FArgTypes,QArgTypes).

is_effect(A,(A,QArgTypes,Cond,Op,F)) :-
        assign_op(A,F,Cond,Op),
        user:fun_fluent(F,number,FArgTypes),
        user:cwa(F=_),
        F =.. [_FName|FArgs],
        A =.. [_AName|AArgs],
        setminus2(FArgs,AArgs,NArgs),
        term_variables(NArgs,NArgVars),
        get_types(NArgVars,FArgTypes,QArgTypes).

add_or_del(A,F,Cond,add) :-
        user:causes_true(A,F,Cond).
add_or_del(A,F,Cond,del) :-
        user:causes_false(A,F,Cond).

assign_op(A,F,true,increase(Val)) :-
        user:causes(A,F,Y,(Y=(F+Val))).
assign_op(A,F,Cond,increase(Val)) :-
        user:causes(A,F,Y,(Y=(F+Val))*Cond).
assign_op(A,F,true,decrease(Val)) :-
        user:causes(A,F,Y,(Y=(F-Val))).
assign_op(A,F,Cond,decrease(Val)) :-
        user:causes(A,F,Y,(Y=(F-Val))*Cond).
assign_op(A,F,true,'scale-up'(Val)) :-
        user:causes(A,F,Y,(Y=(F*Val))).
assign_op(A,F,Cond,'scale-up'(Val)) :-
        user:causes(A,F,Y,(Y=(F*Val))*Cond).
assign_op(A,F,true,'scale-down'(Val)) :-
        user:causes(A,F,Y,(Y=(F/Val))).
assign_op(A,F,Cond,'scale-down'(Val)) :-
        user:causes(A,F,Y,(Y=(F/Val))*Cond).
assign_op(A,F,true,assign(Val)) :-
        user:causes(A,F,Y,(Y=Val)),
        \+ (Val =.. [Op,_T1,_T2], % Val is number or function
            member(Op,['+','-','*','/'])).
assign_op(A,F,Cond,assign(Val)) :-
        user:causes(A,F,Y,(Y=Val)*Cond),
        \+ (Val =.. [Op,_T1,_T2], % Val is number or function
            member(Op,['+','-','*','/'])).

mentions_non_cwa(Effects) :-
        (rel_fluent(F,_);rel_fluent(F);
         rel_rigid(F,_);rel_rigid(F);
         fun_fluent(F,_,_),fun_fluent(F),
         fun_rigid(F,_,_);fun_rigid(F)),
        not(cwa(F)),
        member(eff(_,Cond,_,_),Effects),
        mentions(Cond,F).

instantiate_effects(_A,[],[]) :- !.
instantiate_effects(A,[Effect|Effects],[IEffect|IEffects]) :- !,
        Effect = (A,QArgTypes,Cond,AddDelOp,F),
        IEffect = eff(QArgTypes,Cond,AddDelOp,F),
        instantiate_effects(A,Effects,IEffects).

write_domain(File,Name,Types,Constants,Predicates,Functions,Actions) :-
        construct_domain(Desc,Name,Types,Constants,Predicates,
                         Functions,Actions),
        write_description(Desc,File).

% Constructs PDDL domain description as a list consisting of atoms and
% variables. Variables are instantiated as ?v1,?v2,?v3,... all at once
% just before writing to file to avoid problems with Prolog's internal
% variable representation (an internal name such as "_123456" may
% change while writing to a file).
construct_domain(Domain,Name,Types,Constants,Predicates,Functions,
                 Actions) :- !,
        construct_domain_header(D1,Name),
        construct_requirements(D2,Functions),
        construct_types(D3,Types),
        construct_constants(D4,Constants),
        construct_predicates(D5,Predicates),
        construct_functions(D6,Functions),
        construct_actions(D7,Actions),
        construct_domain_footer(D8),
        append([D1,D2,D3,D4,D5,D6,D7,D8],Domain).

construct_types(D,Types) :- !,
        construct_types2(DT,Types),
        append([['(:types'],DT,[')\n']],D).
construct_types2([],[]) :- !.
construct_types2(D,[subtypes(Type,Subtypes)|Types]) :- !,
        construct_subtypes(DS,Subtypes),
        construct_types2(DT,Types),
        append([DS,[' - ',Type],DT],D).
construct_types2(D,[type(Type)|Types]) :- !,
        construct_types2(DT,Types),
        append([[' ',Type],DT],D).

construct_subtypes([],[]) :- !.
construct_subtypes(D,[Type|Types]) :- !,
        construct_subtypes(DS,Types),
        append([[' ',Type],DS],D).

construct_constants(D,Constants) :- !,
        construct_objects2(DC,Constants),
        append([['(:constants\n'],DC,[')\n']],D).

construct_predicates(D,Predicates) :- !,
        construct_predicates2(DP,Predicates),
        append([['(:predicates\n'],DP,[')\n']],D).
        
construct_predicates2([],[]) :- !.
construct_predicates2(D,[predicate(Name,[])|Predicates]) :- !,
        construct_predicates2(DP,Predicates),
        append([['\t(',Name,')\n'],DP],D).
construct_predicates2(D,[predicate(Name,Args)|Predicates]) :- !,
        construct_args(DA,Args),
        construct_predicates2(DP,Predicates),
        append([['\t(',Name,' '],DA,[')\n'],DP],D).

construct_functions(D,Functions) :- !,
        construct_functions2(DF,Functions),
        append([['(:functions\n'],DF,[')\n']],D).

construct_functions2([],[]) :- !.
construct_functions2(D,[function(Name,Type,[])|Functions]) :- !,
        construct_functions2(DF,Functions),
        append([['\t(',Name,') - ',Type,'\n'],DF],D).
construct_functions2(D,[function(Name,Type,Args)|Functions]) :- !,
        construct_args(DA,Args),
        construct_functions2(DF,Functions),
        append([['\t(',Name,' '],DA,[') - ',Type,'\n'],DF],D).

construct_actions([],[]) :- !.
construct_actions(D,[Action|Actions]) :- !,
        construct_action(DA,Action),
        construct_actions(DAs,Actions),
        append(DA,DAs,D).
construct_action(D,action(Name,Args,Pre,Eff)) :- !,
        construct_args(DArgs,Args),
        construct_precondition(DPre,Pre),
        construct_effects(DEff,Eff),
        append([['(:action ',Name,'\n'],
                [' :parameters ('],DArgs,[')\n'],
                [' :precondition\n'],DPre,
                [' :effect\n'],DEff,
                [')\n']],D).

construct_precondition(D,Precondition) :- !,
        construct_formula(DP,'\t',Precondition),
        append([DP,['\n']],D).

construct_effects(D,Effects) :- !,
        construct_effects2(DE,Effects),
        append([['\t(and\n'],DE,['\t)\n']],D).
construct_effects2([],[]) :- !.
construct_effects2(D,[Effect|Effects]) :- !,
        construct_effect(DE,Effect),
        construct_effects2(DEs,Effects),
        append([DE,['\n'],DEs],D).

% QArgs \= [] => '(forall ...)'
construct_effect(D,eff([],Cond,Op,F)) :- !,
        construct_effect2(DE,Cond,Op,F),
        append([['\t\t'],DE],D).
construct_effect(D,eff(QArgs,Cond,Op,F)) :- !,
        construct_args(DArgs, QArgs),
        construct_effect2(DEff,Cond,Op,F),
        append([['\t\t(forall ('],DArgs,[') '],DEff,[')']],D).
% Cond \= true => '(when ...)'
construct_effect2(D,true,Op,F) :- !,
        construct_effect3(D,Op,F).
construct_effect2(D,Cond,Op,F) :- !,
        construct_formula2(DCond, Cond),
        construct_effect3(DEff,Op,F),
        append([['(when '],DCond,[' '],DEff,[')']],D).
% assignment of function value
construct_effect3(D,Assign,F) :-
        Assign =.. [Op,Val],
        member(Op,[increase,decrease,'scale-up','scale-down',assign]), !,
        construct_pterm(DF,F),
        construct_exp(DV,Val),
        append([['(',Op,' '],DF,[' '],DV,[')']],D).
% AorD == del => '(not ...)'
construct_effect3(D,add,F) :- !,
        construct_effect4(D,F).
construct_effect3(D,del,F) :- !,
        construct_effect4(DEff,F),
        append([['(not '],DEff,[')']],D).
% write actual effect
construct_effect4(D,F) :- !,
        construct_formula2(D,F).

construct_domain_header(D,Name) :- !,
        construct_timestamp(DTime),
        append([DTime,['(define (domain ',Name,')\n']],D).
construct_domain_footer(D) :- !,
        D = [')'].

construct_requirements(D,Functions) :-
        construct_requirements2(DReq,Functions),
        append([['(:requirements :adl'],DReq,[')\n']],D).
construct_requirements2(D,Functions) :-
        member(function('total-cost',number,[]),Functions), !,
        construct_requirements3(DReq,Functions),
        append([[' :action-costs'],DReq],D).
construct_requirements2(D,Functions) :- !,
        construct_requirements3(D,Functions).
construct_requirements3(D,Functions) :-
        member(function(F,number,_),Functions),
        F \= 'total-cost',
        causes(_,F,_,_), !, % otherwise, ":action-costs" suffice
        construct_requirements4(DReq,Functions),
        append([[' :numeric-fluents'],DReq],D).
construct_requirements3(D,Functions) :- !,
        construct_requirements4(D,Functions).
construct_requirements4(D,Functions) :-
        member(function(_,T,_),Functions),
        T \= number, !,
        D = [' :object-fluents'].
construct_requirements4(D,_Functions) :- !,
        D = [].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Problems
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

generate_problem(KB,Objects,Init) :- !,
        collect_objects(Objects),
        collect_init(KB,Init).

collect_objects(Objects) :- !,
        collect_constants(Constants),
        findall(O-T,
                (user:domain(T,O),
                 is_type(T)),
                ObjectsConstants),
        setminus2(ObjectsConstants,Constants,Objects).

collect_init(KB,Init) :- !,
        findall(Atom,
                (kb_axiom(KB,Atom),
                 cwa(Atom)),
                Init).

write_problem(File,PName,DName,Objects,Init,Goal,Metric) :- !,
        construct_problem(Desc,PName,DName,Objects,Init,Goal,Metric),
        write_description(Desc,File).
        
construct_problem(Problem,PName,DName,Objects,Init,Goal,Metric) :- !,
        construct_problem_header(D1,PName,DName),
        construct_objects(D2,Objects),
        construct_init(D3,Init),
        construct_goal(D4,Goal),
        construct_metric(D5,Metric),
        construct_problem_footer(D6),
        append([D1,D2,D3,D4,D5,D6],Problem).

construct_objects(D,Objects) :- !,
        construct_objects2(DO,Objects),
        append([['(:objects\n'],DO,[')\n']],D).
construct_objects2([],[]) :- !.
construct_objects2(D,[O-T|OTs]) :- !,
        atom_concat('#',N,O), % remove "#" from std.name
        construct_objects2(DO,OTs),
        append([['\t',N,' - ',T,'\n'],DO],D).

construct_init(D,Init) :- !,
        construct_init2(DI,Init),
        append([['(:init\n'],DI,[')\n']],D).
construct_init2([],[]) :- !.
construct_init2(D,[A|As]) :- !,
        construct_formula(DF,'\t',A),
        construct_init2(DI,As),
        append([DF,['\n'],DI],D).

construct_goal(D,Goal) :- !,
        construct_goal2(DG,Goal),
        append([['(:goal\n'],DG,['\n)\n']],D).
construct_goal2(D,Goal) :- !,
        construct_formula(D,'\t',Goal).

construct_metric(D,none) :- !,
        D = [].
construct_metric(D,Metric) :- !,
        construct_metric2(DM,Metric),
        append([['(:metric\n'],DM,['\n)\n']],D).
construct_metric2(D,Metric) :- !,
        Metric =.. [MinMax,Exp],
        construct_exp(DE,Exp),
        append([['\t',MinMax,' '],DE],D).

construct_problem_header(D,PName,DName) :- !,
        construct_timestamp(DT),
        append([DT,
                ['(define (problem ',PName,')\n'],
                ['(:domain ',DName,')\n']],D).

construct_problem_footer(D) :- !,
        D = [')'].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Common
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

write_description(Desc,FileName) :- !,
        term_variables(Desc,Vars),
        inst_variables(Vars),
        atomic_list_concat(Desc,DescA),
        open(FileName,write,Stream),
        write(Stream,DescA),
        close(Stream).

% instantiate Prolog variables with atoms v1,v2,v3,...
inst_variables(Vars) :- !,
        inst_variables2(Vars,1).
inst_variables2([],_) :- !.
inst_variables2([Var|Vars],N) :- !,
        atom_concat('v',N,VN),
        Var = VN,
        N1 is N+1,
        inst_variables2(Vars,N1).
        
construct_args([], []) :- !.
construct_args(D, [Arg]) :- !,
        construct_arg(D,Arg).
construct_args(D, [Arg|Args]) :- !,
        construct_arg(DArg,Arg),
        construct_args(DArgs,Args),
        append([DArg,[' '],DArgs],D).
construct_arg(D,X-T) :- !,
        D = ['?',X,' - ',T].

construct_formula(D,Pre,Fml) :-
        Fml = (_*_), !,
        conjuncts(Fml,Conjuncts),
        construct_conjunction(D,Pre,Conjuncts).
construct_formula(D,Pre,Fml) :- !,
        construct_formula2(DFml,Fml),
        append([[Pre],DFml],D).

construct_conjunction(D,Pre,Conjuncts) :- !,
        atom_concat(Pre,'\t',Pre2),
        construct_conjuncts(DCon,Pre2,Conjuncts),
        append([[Pre,'(and\n'],DCon,[Pre,')']],D).
construct_conjuncts([],_Pre,[]) :- !.
construct_conjuncts(D,Pre,[Conjunct|Conjuncts]) :- !,
        construct_formula(DCon,Pre,Conjunct),
        construct_conjuncts(DCons,Pre,Conjuncts),
        append([DCon,['\n'],DCons],D).

conjuncts(F1*F2,Conjuncts) :- !,
        conjuncts(F1,Con1),
        conjuncts(F2,Con2),
        append(Con1,Con2,Conjuncts).
conjuncts(F,[F]) :- !.

construct_formula2(D,F) :-
        def(F,Def), !,
        construct_formula2(D,Def).
construct_formula2(D,F1<=>F2) :- !,
        construct_formula2(D,(F1=>F2)*(F2=>F1)).
construct_formula2(D,F1<=F2) :- !,
        construct_formula2(D,F2=>F1).
construct_formula2(D,F1=>F2) :- !,
        construct_binary_formula(D,F1,'imply',F2).
construct_formula2(D,F1*F2) :- !,
        construct_binary_formula(D,F1,'and',F2).
construct_formula2(D,F1+F2) :- !,
        construct_binary_formula(D,F1,'or',F2).
construct_formula2(D,-F) :- !,
        construct_formula2(DF,F),
        append([['(not '],DF,[')']],D).
construct_formula2(D,some_t(V,F)) :- !,
        construct_quantified_formula(D,'exists',V,F).
construct_formula2(D,all_t(V,F)) :- !,
        construct_quantified_formula(D,'forall',V,F).
construct_formula2(D,true) :- !,
        append([['()']],D). % what about false?
construct_formula2(D,Atom) :- !,
        Atom =.. [F|Terms], % predicate atoms and equality
        construct_pterms(DTerms,Terms),
        append([['(',F,' '],DTerms,[')']],D).

construct_binary_formula(D,F1,Op,F2) :- !,
        construct_formula2(DF1,F1),
        construct_formula2(DF2,F2),
        append([['(',Op],DF1,[' '],DF2,[')']],D).

construct_quantified_formula(D,Op,V,F) :- !,
        construct_args(DArgs,V),
        construct_formula2(DF,F),
        append([['(',Op,' ('],DArgs,[') '],DF,[')']],D).

construct_exp(D,Exp) :-
        Exp =.. [Op,T1,T2],
        member(Exp,['+','-','*','/']), !,
        construct_exp(D1,T1),
        construct_exp(D2,T2),
        append([['(',Op,' '],D1,[' '],D2,[')']],D).
construct_exp(D,Num) :-
        number(Num), !,
        D = [Num].
construct_exp(D,T) :- !,
        construct_pterm(D,T).

construct_pterms([],[]) :- !.
construct_pterms(D,[T]) :- !,
        construct_pterm(D,T).
construct_pterms(D,[T|Ts]) :- !,
        construct_pterm(DT,T),
        construct_pterms(DTs,Ts),
        append([DT,[' '],DTs],D).

construct_pterm(D,T) :-
        var(T), !,
        D = ['?',T].
construct_pterm(D,T) :-
        atom(T),
        atom_concat('#',Name,T), !,  % remove "#" from std.name
        D = [Name].
construct_pterm(D,Num) :-
        number(Num), !,
        D = [Num].
construct_pterm(D,T) :-
        T =.. [F], !,
        append([['(',F,')']],D).
construct_pterm(D,T) :-
        T =.. [F|Args], !,
        construct_pterms(DArgs,Args),
        append([['(',F,' '],DArgs,[')']],D).

construct_timestamp(D) :- !,
        local_time_and_date_as_string(TimeS),
        atom_string(TimeA,TimeS),
        D = ['; Automatically generated PDDL file\n',
             '; ',TimeA,'\n\n'].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Plans
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

read_plan(PlanFile,Plan) :-
        exists_file(PlanFile), !,
        phrase_from_file(plan(Plan),PlanFile).
read_plan(_PlanFile,fail).

plan([Action|Actions]) -->
        action(Action), "\n", !,
        plan(Actions).
plan(Actions) -->
        comment, !,
        plan(Actions).
plan([]) --> [].

action(Action) --> "(", aname(Name,''), " ", args(Args), ")", !,
        {Action =.. [Name|Args]}.

aname(Name,Pre) --> 
        aname2(Codes),
        {atom_codes(Name2,Codes),
         % PDDL is not case-sensitive => lower case everywhere
         downcase_atom(Name2,Name3),
         atom_concat(Pre,Name3,Name)}.
aname2([C|Cs]) -->
        [C], {C \= 32, C \= 10, C \= 41}, % up to " ", "\n" or ")"
        aname2(Cs).
aname2([]) --> [].

args([Arg|Args]) -->
        aname(Arg,'#'), " ", args(Args).
args([Arg]) -->
        aname(Arg,'#').
args([]) --> [].

comment --> ";", !, all_to_end_of_line.
all_to_end_of_line -->
        "\n", !.
all_to_end_of_line --> [_], !,
        all_to_end_of_line.

delete_old_plan(File) :-
        exists_file(File), !,
        delete_file(File).
delete_old_plan(_) :- !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Interface to Fast Downward PDDL Planner
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% We use the following search/evaluator configuration because we want
% - optimality (via A* and an admissable heuristic function)
% - support for action costs
% - support for full ADL, including conditional effects
% cf. http://www.fast-downward.org/Doc/Evaluator#Additive_heuristic
fdconf('astar(hmax(transform=no_transform(),cache_estimates=true))').

% Execution:
% $ fast-downward.py domain.pddl problem.pddl --search \
%   "astar(hmax(transform=no_transform(), cache_estimates=true))"
% (Unfortunately, this configuration does not support specifying a
% designated output plan file, but Fast Downward will just put the
% solution into 'sas_plan' in the current working directory, so we
% have to change to the temp directory and back...)

% To get fast, satisficing planning, we could use
% $ fast-downward.py --alias lama-first domain.pddl problem.pddl \
%   --plan-file plan.pddl
% (Perhaps make this an alternative or option?)

/* Calls Fast Downward on planning problem. */
fastdownward(DomainFile,ProblemFile,PlanFile) :-
        delete_old_plan(PlanFile),               % no plan file = no plan
        temp_dir(TempDir),
        working_directory(WorkDir,TempDir),      % change to temp dir
        fdconf(FDConf),
        process_create(path('fast-downward.py'), 
                       [DomainFile,              % domain input file
                        ProblemFile,             % problem input file
                        '--search', FDConf],     % search conf.
                       [stdout(pipe(Output)),    % use output for debugging
                        stderr(pipe(Output)),    % use output for debugging
                        process(PID)]),          % need PID for exit status
        process_wait(PID, Status), !,            % wait for completion
        working_directory(_,WorkDir),            % back to previous wd
        fd_result(Status,Output).                % check for failures
fastdownward(_,_,_) :-
        fd_failed.

% Exit codes according to http://www.fast-downward.org/ExitCodes.
% Block 0-9: successfull termination
fd_result(exit(N),_) :-
        N < 10, !.
% Block 10-19: unsuccessfull, but error-free termination
fd_result(exit(N),_) :-
        N >= 10, N < 20, !.
% Block 20-29: expected failures
% Block 30-39: unrecoverable failures
fd_result(exit(N),Output) :-
        N >= 20, !,
        read_string(Output,"","",_,String),
        close(Output),
        report_message(error,['Fast Downward output:']),
        report_message(error,[String]),
        fail.

fd_failed :-
        report_message(error,['Failed while attempting to use Fast Downward planner']),
        report_message(error,['Aborting...']),
        report_message(error,['Check your settings! (PATH_GOLOG variable set?)']),
        abort.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Pre- and Postprocessing of Actions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Because Fast Downward (so far) does not support state-dependent
% action costs, action descriptions have to be pre- and post-
% processed.

% Every action with a conditional effect affecting the 'total-cost'
% fluent will be split up into a negative and a positive variant,
% where the (negated) condition of the original effect becomes part of
% the precondition of the new actions.

% The newly generated actions' names are obtained by concatenating
% '_n' or '_p' at the end of the original action's name.

% With multiple conditional effects on 'total-cost', this process may
% repeat, resulting in an exponential blow-up in the number of
% actions.

% A 'Map' keeps tracks of the relation between original name and new
% names, and is used for restoring original names when reading the
% plan generated by Fast Downward.

preprocess_actions([],[],[]).
preprocess_actions([Action|Actions],[Map|Maps],ActionsSP) :-
        Action = action(_,_,_,Effects),
        member(eff(_,_,_,'total-cost'),Effects), !,
        split_action_by_costs(Action,Map,ActionsS),
        preprocess_actions(Actions,Maps,ActionsP),
        append(ActionsS,ActionsP,ActionsSP).
preprocess_actions([Action|Actions],Maps,[Action|ActionsP]) :- !,
        preprocess_actions(Actions,Maps,ActionsP).

split_action_by_costs(Action,Map,NewActions) :-
        Action = action(Name,Args,Precondition,Effects),
        findall(CEffect,
                (member(CEffect,Effects),
                 CEffect = eff(_,Cond,_,'total-cost'),
                 Cond \= true),
                CEffects),
        subtract(Effects,CEffects,REffects),
        ActionN = action(Name,Args,Precondition,REffects),
        split_action_by_costs2([ActionN],CEffects,NewActions,Name,Map).
split_action_by_costs2(Actions,[],Actions,_Name,[]) :- !.
split_action_by_costs2(Actions,[CEff|CEffs],NewActions,Name,Map) :- !,
        split_action_by_costs3(Actions,CEff,Actions2,Name,Map1),
        split_action_by_costs2(Actions2,CEffs,NewActions,Name,Map2),
        append(Map1,Map2,Map).
split_action_by_costs3([],_CEff,[],_Name,[]) :- !.
split_action_by_costs3([Act|Actions],CEff,[ActP,ActN|NewActions],
                       Name,[Name-NameP,Name-NameN|Map]) :- !,
        CEff = eff([],Cond,Op,'total-cost'),
        Act = action(Name,Args,Precond,Effects),
        atomic_list_concat([Name,'_',p],NameP),
        atomic_list_concat([Name,'_',n],NameN),
        EffP = eff([],true,Op,'total-cost'),
        ActP = action(NameP,Args,Cond*Precond,[EffP|Effects]),
        ActN = action(NameN,Args,(-Cond)*Precond,Effects),
        split_action_by_costs3(Actions,CEff,NewActions,Name,Map).

postprocess_actions([],_Map,[]) :- !.
postprocess_actions([Action|Actions],Map,[ActionP|ActionsP]) :-
        Action =.. [Name|Args],
        member(NameO-Name,Map), !,
        ActionP =.. [NameO|Args],
        postprocess_actions(Actions,Map,ActionsP).
postprocess_actions([Action|Actions],Map,[Action|ActionsP]) :- !,
        postprocess_actions(Actions,Map,ActionsP).
