:- use_module('../../planning/pddl_parser').

% Parse RCLL PDDL domain description.
% So far, duration constraints are ignored.
test :-
        parse_pddl_domain(file('rcll_domain_production_durations.pddl'),
                          file('rcll.pl'),_S).
