%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% STRIPS-style progression
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

progress(Action) :-
        ground(Action), !,
        findall(Fluent,causes_false(Action,Fluent,true),Dels),
        findall(Fluent,causes_true(Action,Fluent,true),Adds),
        del_facts(Dels),
        add_facts(Adds).

del_facts([Fact|Facts]) :- 
        retract(initially(Fact)),
        del_facts(Facts).
del_facts([]).

add_facts([Fact|Facts]) :- 
        assert(initially(Fact)),
        del_facts(Facts).
add_facts([]).
