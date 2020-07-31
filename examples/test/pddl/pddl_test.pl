%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing PDDL parsing and planning
%
% 1. Parse PDDL domain and problem into Golog using pddl_parser
% 2. Compile domain and problem back to PDDL using pddl_planner
% 3. Translate the resulting plan (if any) into a sequence of Golog
%    actions.
% 4. Validate the plan/sequence in Golog
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- ['../../../agents/kbagent_r'].
:- use_module('../../../lib/utils').
:- use_module('../../../planning/pddl_parser').
:- use_module('../../../planning/pddl_planner').

:- dynamic type/1.
:- dynamic subtype/2.
:- dynamic rel_fluent/2.
:- dynamic fun_fluent/3.
:- dynamic cwa/1.
:- dynamic poss/3.
:- dynamic causes_true/3.
:- dynamic causes_false/3.
:- dynamic causes/4.
:- dynamic domain/2.
:- dynamic initially/1.
:- dynamic goal/2.
:- dynamic metric/2.

:- discontiguous pddl_domain/2.
:- discontiguous pddl_problem/3.

:- begin_tests(pddl).

test(airport) :-
        check(airport,p1),
        check(airport,p2),
        check(airport,p3).

test(miconic) :-
        check(miconic,p1),
        check(miconic,p2),
        check(miconic,p3).

test(trucks) :-
        check(trucks,p1),
        check(trucks,p2),
        check(trucks,p3).

test(citycar) :-
        check(citycar,p1),
        check(citycar,p2),
        check(citycar,p3).

:- end_tests(pddl).

pddl_domain(airport,'airport-adl_domain.pddl').
pddl_problem(airport,p1,'airport-adl_problem_1.pddl').
pddl_problem(airport,p2,'airport-adl_problem_2.pddl').
pddl_problem(airport,p3,'airport-adl_problem_3.pddl').

pddl_domain(miconic,'miconic-adl_domain.pddl').
pddl_problem(miconic,p1,'miconic-adl_problem_1.pddl').
pddl_problem(miconic,p2,'miconic-adl_problem_2.pddl').
pddl_problem(miconic,p3,'miconic-adl_problem_3.pddl').

pddl_domain(trucks,'trucks_domain.pddl').
pddl_problem(trucks,p1,'trucks_problem_1.pddl').
pddl_problem(trucks,p2,'trucks_problem_2.pddl').
pddl_problem(trucks,p3,'trucks_problem_3.pddl').

pddl_domain(citycar,'citycar-opt14-adl_domain.pddl').
pddl_problem(citycar,p1,'citycar-opt14-adl_problem_1.pddl').
pddl_problem(citycar,p2,'citycar-opt14-adl_problem_2.pddl').
pddl_problem(citycar,p3,'citycar-opt14-adl_problem_3.pddl').

check(Dom,Pro) :-
        clear,
        
        load_pddl_domain_file(Dom,Symbols),
        report_message(['Done loading domain ',Dom,'.']),
        
        load_pddl_problem_file(Dom,Pro,Symbols),
        report_message(['Done loading problem ',Pro,'.']),
        
        goal(_,Goal),
        (metric(_,MetricD) -> Metric=MetricD; Metric=none),

        get_plan(Goal,Metric,Plan),
        length(Plan,N),
        report_message(['Found plan of length ',N,'.']),
        
        init,
        validate(Plan,Goal),
        report_message(['Successfully validated plan.']).

clear :-
        retractall(type(_)),
        retractall(subtype(_,_)),
        retractall(rel_fluent(_,_)),
        retractall(fun_fluent(_,_,_)),
        retractall(cwa(_)),
        retractall(poss(_,_,_)),
        retractall(causes_true(_,_,_)),
        retractall(causes_false(_,_,_)),
        retractall(causes(_,_,_,_)),
        retractall(domain(_,_)),
        retractall(initially(_)),
        retractall(goal(_,_)),
        retractall(metric(_,_)).

load_pddl_domain_file(Domain,Symbols) :-
        pddl_domain(Domain,File), !,
        parse_pddl_domain(file(File),axioms(Axioms),Symbols),
        forall(member(Axiom,Axioms),assert(Axiom)).

load_pddl_problem_file(Domain,Problem,Symbols) :-
        pddl_problem(Domain,Problem,File), !,
        parse_pddl_problem(file(File),axioms(Axioms),Symbols),
        forall(member(Axiom,Axioms),assert(Axiom)).

validate(fail,Goal) :- !,
        ask(Goal,false).               % no plan => Goal shouldn't hold
validate(Plan,Goal) :- 
        append(Prefix,[_LastAction],Plan), !,
        ask(executable(Plan),true),    % plan should be executable
        ask(after(Plan,Goal),true),    % plan should achieve Goal
        ask(after(Prefix,Goal),false). % plan w/o last action shouldn't
