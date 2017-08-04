%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Progression for local-effect theories
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

progress(Action) :-
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
