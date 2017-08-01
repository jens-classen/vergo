:- use_module('../lib/utils').
:- use_module('../reasoning/fol').
:- use_module('../reasoning/l').

:- multifile def/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Reduction
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

reduce(-Fml,-Result) :- !,
        reduce(Fml,Result).
reduce(Fml1+Fml2,Result1+Result2) :- !,
        reduce(Fml1,Result1),
        reduce(Fml2,Result2).
reduce(Fml1*Fml2,Result1*Result2) :- !,
        reduce(Fml1,Result1),
        reduce(Fml2,Result2).
reduce(Fml1<=>Fml2,Result1<=>Result2) :- !,
        reduce(Fml1,Result1),
        reduce(Fml2,Result2).
reduce(Fml1=>Fml2,Result1=>Result2) :- !,
        reduce(Fml1,Result1),
        reduce(Fml2,Result2).
reduce(Fml1<=Fml2,Result1<=Result2) :- !,
        reduce(Fml1,Result1),
        reduce(Fml2,Result2).
reduce(all(Vars,Fml),all(Vars,Result)) :- !,
        reduce(Fml,Result).
reduce(some(Vars,Fml),some(Vars,Result)) :- !,
        reduce(Fml,Result).
reduce(Fml,Result) :-
        def(Fml,Def), !,
        reduce(Def,Result).
reduce(know(Fml),Result) :- !,
        reduce(Fml,FmlR),
        free_variables(FmlR,Vars),
        resolve(FmlR,Vars,Result).
reduce(Fml,Fml) :- !.                             
                             
resolve(Fml,[],Result) :- !,
        entails_initially(Fml,Result).
resolve(Fml,[Var|Vars],Result) :- !,
        get_ini_std_names(KNames),
        get_fml_std_names(Fml,FNames),
        union(KNames,FNames,Names),
        get_new_std_name(Names,New),
        resolve_pos_disjunct(Fml,Var,Vars,Names,Pos),
        resolve_neg_disjunct(Fml,Var,Vars,Names,New,Neg),
        Result2 = Pos + Neg,
        simplify(Result2,Result).
        
resolve_pos_disjunct(Fml,Var,Vars,[Name],Result) :- !,
        subv(Var,Name,Fml,FmlS),
        resolve(FmlS,Vars,ResC),
        simplify((Var=Name)*ResC,Result).
resolve_pos_disjunct(Fml,Var,Vars,[Name|Names],Result) :- !,
        subv(Var,Name,Fml,FmlS),
        resolve(FmlS,Vars,ResC),
        resolve_pos_disjunct(Fml,Var,Vars,Names,ResR),
        simplify((Var=Name)*ResC + ResR,Result).
resolve_neg_disjunct(Fml,Var,Vars,Names,New,Result) :- !,
        subv(Var,New,Fml,FmlS),
        resolve(FmlS,Vars,ResC),
        subv(New,Var,ResC,ResR),
        neg_disjunct_inequalities(Var,Names,Inequalities),
        simplify(Inequalities * ResR,Result).

neg_disjunct_inequalities(_Var,[],true) :- !.
neg_disjunct_inequalities(Var,[Name],(-(Var=Name))) :- !.
neg_disjunct_inequalities(Var,[Name|Names],(-(Var=Name))*Inequalities) :- !,
        neg_disjunct_inequalities(Var,Names,Inequalities).
