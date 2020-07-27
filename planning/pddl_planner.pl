/**

PDDL Planner

This module provides functionality for solving planning tasks in Golog
by means of a PDDL planner following the approach described in [Claßen
et al. 2007] and [Claßen 2013, Ch. 4].

All involved fluents have to underly the closed-world assumption, and
all involved fluents and actions must be typed.

Currently, only PDDL's ADL fragment is supported. In particular,
functional fluents will not be considered.

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

:- module(pddl_planner, [get_plan/2,
                         generate_domain/4,
                         generate_problem/2,
                         write_domain/6,
                         write_problem/6,
                         fastdownward/3,
                         read_plan/2]).

:- use_module('../lib/env').
:- use_module('../lib/utils').
:- use_module('../logic/cwa').
:- use_module('../logic/fol', [op(1130, xfy, <=>),
                               op(1110, xfy, <=),
                               op(1110, xfy, =>)]).
:- use_module(library(pio)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Main Method
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/**
  * get_plan(+Goal,-Plan) is det.
  *
  * Generates a PDDL domain and problem from the current state of the
  * BAT, using all typed relational fluents underlying the CWA and all
  * typed actions, calls the Fast Downward PDDL planner on it, and
  * converts the resulting plan back into a sequence of actions. If
  * there is no solution plan, or Fast Downward did not find any,
  * 'fail' is returned.
  *
  * @arg Goal a goal, either in the form of a formula, or the name of
  *           a goal formula defined through goal/2 or def/2
  * @arg Plan a sequence (list) of actions representing a solution
  *           plan, or 'fail'
  */
get_plan(Goal,Plan) :-
        goal_fml(Goal,GoalF),
        temp_domain_file(DomF),
        temp_problem_file(ProF),
        temp_plan_file(PlaF),
        temp_domain_name(Dom),
        temp_problem_name(Pro),
        generate_domain(Typ,Pre,Fun,Act),
        generate_problem(Obj,Ini),
        write_domain(DomF,Dom,Typ,Pre,Fun,Act),
        write_problem(ProF,Pro,Dom,Obj,Ini,GoalF),
        fastdownward(DomF,ProF,PlaF),
        read_plan(PlaF,Plan).

goal_fml(Goal,GoalF) :-
        goal(Goal,GoalF), !.
goal_fml(Goal,GoalF) :-
        def(Goal,GoalF), !.
goal_fml(Goal,Goal) :- !.

temp_domain_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/domain.pddl', File).
temp_problem_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/problem.pddl', File).
temp_plan_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/plan.pddl', File).

temp_domain_name(tmpdom).
temp_problem_name(tmppro).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Domains
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

generate_domain(Types,Predicates,_Functions,Actions) :- !,
        collect_types(Types),
        collect_predicates(Predicates),
        % collect_functions(Functions),
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

collect_actions(Actions) :- !,
        findall(action(Name,Args,Precondition,Effects),
                (poss(A,Args,Precondition),
                 A =.. [Name|_],
                 collect_effects(A,Effects)),
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
        get_types(NArgs,FArgTypes,QArgTypes).

add_or_del(A,F,Cond,add) :-
        user:causes_true(A,F,Cond).
add_or_del(A,F,Cond,del) :-
        user:causes_false(A,F,Cond).

instantiate_effects(_A,[],[]) :- !.
instantiate_effects(A,[Effect|Effects],[IEffect|IEffects]) :- !,
        Effect = (A,QArgTypes,Cond,ADl,F),
        IEffect = eff(QArgTypes,Cond,ADl,F),
        instantiate_effects(A,Effects,IEffects).

write_domain(File,Name,Types,Predicates,Functions,Actions) :-
        construct_domain(Desc,Name,Types,Predicates,Functions,Actions),
        write_description(Desc,File).

% Constructs PDDL domain description as a list consisting of atoms and
% variables. Variables are instantiated as ?v1,?v2,?v3,... all at once
% just before writing to file to avoid problems with Prolog's internal
% variable representation (an internal name such as "_123456" may
% change while writing to a file).
construct_domain(Domain,Name,Types,Predicates,_Functions,Actions) :- !,
        construct_domain_header(D1,Name),
        construct_types(D2,Types),
        construct_predicates(D3,Predicates),
        % construct_functions(D4,Functions),
        construct_actions(D5,Actions),
        construct_domain_footer(D6),
        append([D1,D2,D3,D5,D6],Domain).

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

construct_predicates(D,Predicates) :- !,
        construct_predicates2(DP,Predicates),
        append([['(:predicates\n'],DP,[')\n']],D).
        
construct_predicates2([],[]) :- !.
construct_predicates2(D,[predicate(Name,Args)|Predicates]) :- !,
        construct_args(DA,Args),
        construct_predicates2(DP,Predicates),
        append([['\t(',Name,' '],DA,[')\n'],DP],D).

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
construct_effect(D,eff([],Cond,AorD,F)) :- !,
        construct_effect2(DE,Cond,AorD,F),
        append([['\t\t'],DE],D).
construct_effect(D,eff(QArgs,Cond,AorD,F)) :- !,
        construct_args(DArgs, QArgs),
        construct_effect2(DEff,Cond,AorD,F),
        append([['\t\t(forall ('],DArgs,[') '],DEff,[')']],D).
% Cond \= true => '(when ...)'
construct_effect2(D,true,AorD,F) :- !,
        construct_effect3(D,AorD,F).
construct_effect2(D,Cond,AorD,F) :- !,
        construct_formula2(DCond, Cond),
        construct_effect3(DEff,AorD,F),
        append([['(when '],DCond,[' '],DEff,[')']],D).
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
        append([DTime,
                ['(define (domain ',Name,')\n'],
                ['(:requirements :adl :equality :typing)\n']],D).
construct_domain_footer(D) :- !,
        D = [')'].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Problems
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

generate_problem(Objects,Init) :- !,
        collect_objects(Objects),
        collect_init(Init).

collect_objects(Objects) :- !,
        findall(O-T,
                (user:domain(T,O),
                 is_type(T)),
                Objects).

collect_init(Init) :- !,
        findall(Atom,
                (initially(Atom),
                 cwa(Atom)),
                Init).

write_problem(File,PName,DName,Objects,Init,Goal) :- !,
        construct_problem(Desc,PName,DName,Objects,Init,Goal),
        write_description(Desc,File).
        
construct_problem(Problem,PName,DName,Objects,Init,Goal) :- !,
        construct_problem_header(D1,PName,DName),
        construct_objects(D2,Objects),
        construct_init(D3,Init),
        construct_goal(D4,Goal),
        construct_problem_footer(D5),
        append([D1,D2,D3,D4,D5],Problem).

construct_objects(D,Objects) :- !,
        construct_objects2(DO,Objects),
        append([['(:objects\n'],DO,[')\n']],D).
construct_objects2([],[]) :- !.
construct_objects2(D,[O-T|OTs]) :- !,
        atom_concat('#',N,O), % remove "#" from std.name
        construct_objects2(DO,OTs),
        append([['\t',N,' - ',T],DO],D).

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
construct_formula2(D,Atom) :- !,
        Atom =.. [F|Terms], % predicate atoms and equality
        construct_pterms(DTerms,Terms),
        append([['(',F,' '],DTerms,[')']],D).
% true and false?

construct_binary_formula(D,F1,Op,F2) :- !,
        construct_formula2(DF1,F1),
        construct_formula2(DF2,F2),
        append([['(',Op],DF1,[' '],DF2,[')']],D).

construct_quantified_formula(D,Op,V,F) :- !,
        construct_args(DArgs,V),
        construct_formula2(DF,F),
        append([['(',Op,' ('],DArgs,[') '],DF,[')']],D).

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
construct_pterm(D,T) :- !,
        atom_concat('#',Name,T), !,  % remove "#" from std.name
        D = [Name].
% other kinds of terms (functions)?

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

/* Calls Fast Downward on planning problem. */
fastdownward(DomainFile,ProblemFile,PlanFile) :-
        delete_old_plan(PlanFile),               % no plan file = no plan
        process_create(path('fast-downward.py'), 
                       ['--alias', 'lama-first', % default alias (config)
                        '--plan-file', PlanFile, % plan result file
                        DomainFile,              % domain input file
                        ProblemFile],            % problem input file
                       [stdout(null),            % completely silent
                        stderr(null),            % completely silent
                        process(PID)]),          % need PID for exit status
        process_wait(PID, Status), !,            % wait for completion
        fd_succeeded(Status).                    % check for failures
fastdownward(_,_,_) :-
        fd_failed.

% Exit codes according to http://www.fast-downward.org/ExitCodes.
% Block 0-9: successfull termination
fd_succeeded(exit(N)) :-
        N < 10, !.
% Block 10-19: unsuccessfull, but error-free termination
fd_succeeded(exit(N)) :-
        N >= 10, N < 20, !.
% Block 20-29: expected failures
% Block 30-39: unrecoverable failures
get_fd_result(exit(N)) :-
        N >= 20, !,
        fail.

fd_failed :-
        report_message(error,['Failed while attempting to use Fast Downward planner']),
        report_message(error,['Aborting...']),
        report_message(error,['Check your settings! (PATH_GOLOG variable set?)']),
        abort.
