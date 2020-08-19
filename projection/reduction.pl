%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Reduction
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(reduction, [reduce/3,
                      resolve/4]).

:- use_module('../kbs/l_kb').
:- use_module('../lib/utils').

:- multifile user:def/2.

reduce(KB,-Fml,-Result) :- !,
        reduce(KB,Fml,Result).
reduce(KB,Fml1+Fml2,Result1+Result2) :- !,
        reduce(KB,Fml1,Result1),
        reduce(KB,Fml2,Result2).
reduce(KB,Fml1*Fml2,Result1*Result2) :- !,
        reduce(KB,Fml1,Result1),
        reduce(KB,Fml2,Result2).
reduce(KB,Fml1<=>Fml2,Result1<=>Result2) :- !,
        reduce(KB,Fml1,Result1),
        reduce(KB,Fml2,Result2).
reduce(KB,Fml1=>Fml2,Result1=>Result2) :- !,
        reduce(KB,Fml1,Result1),
        reduce(KB,Fml2,Result2).
reduce(KB,Fml1<=Fml2,Result1<=Result2) :- !,
        reduce(KB,Fml1,Result1),
        reduce(KB,Fml2,Result2).
reduce(KB,all(Vars,Fml),all(Vars,Result)) :- !,
        reduce(KB,Fml,Result).
reduce(KB,some(Vars,Fml),some(Vars,Result)) :- !,
        reduce(KB,Fml,Result).
reduce(KB,all_t(Vars,Fml),all_t(Vars,Result)) :- !,
        reduce(KB,Fml,Result).
reduce(KB,some_t(Vars,Fml),some_t(Vars,Result)) :- !,
        reduce(KB,Fml,Result).
reduce(KB,Fml,Result) :-
        user:def(Fml,Def), !,
        reduce(KB,Def,Result).
reduce(KB,know(Fml),Result) :- !,
        reduce(KB,Fml,FmlR),
        free_variables(FmlR,Vars),
        resolve(KB,FmlR,Vars,Result).
reduce(_KB,Fml,Fml) :- !.
                             
resolve(KB,Fml,[],Result) :- !,
        entails_kb(KB,Fml,Result).
resolve(KB,Fml,[Var|Vars],Result) :- !,
        get_kb_std_names(KB,KNames),
        get_fml_std_names(Fml,FNames),
        union(KNames,FNames,Names),
        get_new_std_name(Names,New),
        resolve_pos_disjunct(KB,Fml,Var,Vars,Names,Pos),
        resolve_neg_disjunct(KB,Fml,Var,Vars,Names,New,Neg),
        Result2 = Pos + Neg,
        simplify(Result2,Result).
        
resolve_pos_disjunct(KB,Fml,Var,Vars,[Name],Result) :- !,
        subv(Var,Name,Fml,FmlS),
        resolve(KB,FmlS,Vars,ResC),
        simplify((Var=Name)*ResC,Result).
resolve_pos_disjunct(KB,Fml,Var,Vars,[Name|Names],Result) :- !,
        subv(Var,Name,Fml,FmlS),
        resolve(KB,FmlS,Vars,ResC),
        resolve_pos_disjunct(KB,Fml,Var,Vars,Names,ResR),
        simplify((Var=Name)*ResC + ResR,Result).
resolve_neg_disjunct(KB,Fml,Var,Vars,Names,New,Result) :- !,
        subv(Var,New,Fml,FmlS),
        resolve(KB,FmlS,Vars,ResC),
        subv(New,Var,ResC,ResR),
        neg_disjunct_inequalities(Var,Names,Inequalities),
        simplify(Inequalities * ResR,Result).

neg_disjunct_inequalities(_Var,[],true) :- !.
neg_disjunct_inequalities(Var,[Name],(-(Var=Name))) :- !.
neg_disjunct_inequalities(Var,[Name|Names],(-(Var=Name))*Inequalities) :- !,
        neg_disjunct_inequalities(Var,Names,Inequalities).
