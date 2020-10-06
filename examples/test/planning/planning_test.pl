%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Testing planning
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module('../../../agents/kbagent').
:- use_module('../../../lib/utils').
:- use_module('../../../planning/pddl_parser').
:- use_module('../../../planning/planner').

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

:- begin_tests(planner).

test(office) :-
        check(office,p1).

test(miconic) :-
        check(miconic,p1),
        check(miconic,p2),
        check(miconic,p3).

% too expensive...
% test(trucks) :-
%         check(trucks,p1),
%         check(trucks,p2),
%         check(trucks,p3).

% too expensive...
% test(citycar) :-
%         check(citycar,p1),
%         check(citycar,p2),
%         check(citycar,p3).

:- end_tests(planner).

pddl_domain(office,'office_robot_domain.pddl').
pddl_problem(office,p1,'office_robot_problem_1.pddl').

pddl_domain(miconic,'../pddl/miconic-adl_domain.pddl').
pddl_problem(miconic,p1,'../pddl/miconic-adl_problem_1.pddl').
pddl_problem(miconic,p2,'../pddl/miconic-adl_problem_2.pddl').
pddl_problem(miconic,p3,'../pddl/miconic-adl_problem_3.pddl').

pddl_domain(trucks,'../pddl/trucks_domain.pddl').
pddl_problem(trucks,p1,'../pddl/trucks_problem_1.pddl').
pddl_problem(trucks,p2,'../pddl/trucks_problem_2.pddl').
pddl_problem(trucks,p3,'../pddl/trucks_problem_3.pddl').

pddl_domain(airport,'../pddl/airport-adl_domain.pddl').
pddl_problem(airport,p1,'../pddl/airport-adl_problem_1.pddl').

pddl_domain(citycar,'../pddl/citycar-opt14-adl_domain.pddl').
pddl_problem(citycar,p1,'../pddl/citycar-opt14-adl_problem_1.pddl').
pddl_problem(citycar,p2,'../pddl/citycar-opt14-adl_problem_2.pddl').
pddl_problem(citycar,p3,'../pddl/citycar-opt14-adl_problem_3.pddl').

check(Dom,Pro) :-
        clear,

        pddl_domain(Dom,DFile), !,
        parse_pddl_domain(file(DFile),userdb,Symbols),
        report_message(['Done loading domain ',Dom,'.']),

        pddl_problem(Dom,Pro,PFile), !,
        parse_pddl_problem(file(PFile),userdb,Symbols),
        report_message(['Done loading problem ',Pro,'.']),

        goal(_,Goal),
        (metric(_,MetricD) -> Metric=MetricD; Metric=none),

        get_plan(userdb,Goal,Metric,Plan), !,
        length(Plan,N),
        report_message(['Found plan of length ',N,'.']),

        init(regression),
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

validate(fail,Goal) :- !,
        ask(Goal,false).               % no plan => Goal shouldn't hold
validate(Plan,Goal) :- 
        append(Prefix,[_LastAction],Plan), !,
        ask(executable(Plan),true),    % plan should be executable
        ask(after(Plan,Goal),true),    % plan should achieve Goal
        ask(after(Prefix,Goal),false). % plan w/o last action shouldn't
