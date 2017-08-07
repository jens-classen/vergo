progress(Action) :-
        progression_style(Style),
        progress(Action,Style).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Closed-World STRIPS progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

progress(Action,strips(closed)) :-
        ground(Action), !,
        findall(Fluent,causes_false(Action,Fluent,true),Dels),
        findall(Fluent,causes_true(Action,Fluent,true),Adds),
        del_facts_closed(Dels),
        add_facts_closed(Adds).

del_facts_closed([Fact|Facts]) :- 
        retract(initially(Fact)),
        del_facts_closed(Facts).
del_facts_closed([]).

add_facts_closed([Fact|Facts]) :- 
        assert(initially(Fact)),
        add_facts_closed(Facts).
add_facts_closed([]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Open-World STRIPS progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

progress(Action,strips(open)) :-
        ground(Action), !,
        findall(Fluent,causes_false(Action,Fluent,true),Dels),
        findall(Fluent,causes_true(Action,Fluent,true),Adds),
        del_facts_open(Dels),
        add_facts_open(Adds).

del_facts_open([Fact|Facts]) :- 
        retract(initially(Fact)),
        assert(initially(-Fact)),
        del_facts_open(Facts).
del_facts_open([]).

add_facts_open([Fact|Facts]) :-
        retract(initially(-Fact)),
        assert(initially(Fact)),
        add_facts_open(Facts).
add_facts_open([]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Progression for local-effect theories
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

progress(Action,local_effect) :-
        ground(Action), !,
        findall(Fluent,
                (causes_false(Action,Fluent,_Cond);
                 causes_true(Action,Fluent,_Cond)),
                CharacteristicSet).
        % generate all combinations / truth assignment
        % generate all instantiated SSAs
        % unify each with initial theory
        % apply regression from verification_abstraction to each
        % disjoin them all = result
