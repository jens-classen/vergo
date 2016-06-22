:- use_module('../lib/utils').
:- use_module('../reasoning/fol').

:- multifile stdname/1.
:- multifile def/2.

:- dynamic(stdname/1).

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
        Result = (Var=Name)*ResC.
resolve_pos_disjunct(Fml,Var,Vars,[Name|Names],Result) :- !,
        subv(Var,Name,Fml,FmlS),
        resolve(FmlS,Vars,ResC),
        resolve_pos_disjunct(Fml,Var,Vars,Names,ResR),
        Result = (Var=Name)*ResC + ResR.
resolve_neg_disjunct(Fml,Var,Vars,Names,New,Result) :- !,
        subv(Var,New,Fml,FmlS),
        resolve(FmlS,Vars,ResC),
        subv(New,Var,ResC,ResR),
        neg_disjunct_inequalities(Var,Names,Inequalities),
        Result = Inequalities * ResR.

get_fml_std_names(Fml,Names) :- !,
        collect_names(Fml,Names2),
        sort(Names2,Names).
get_ini_std_names(Names) :- !,
        findall(Names2,
                (initially(Fml),
                 collect_names(Fml,Names2)),
                Names3),
        flatten(Names3,Names4),
        sort(Names4,Names).
get_new_std_name(Names,New) :- !,
        create_new_names(Names,1,[New]),
        assert(stdname(New)).

collect_names(Fml1<=>Fml2,Names) :- !,
        collect_names(Fml1,Names1),
        collect_names(Fml2,Names2),
        union(Names1,Names2,Names).
collect_names(Fml1=>Fml2,Names) :- !,
        collect_names(Fml1,Names1),
        collect_names(Fml2,Names2),
        union(Names1,Names2,Names).
collect_names(Fml1<=Fml2,Names) :- !,
        collect_names(Fml1,Names1),
        collect_names(Fml2,Names2),
        union(Names1,Names2,Names).
collect_names(Fml1*Fml2,Names) :- !,
        collect_names(Fml1,Names1),
        collect_names(Fml2,Names2),
        union(Names1,Names2,Names).
collect_names(Fml1+Fml2,Names) :- !,
        collect_names(Fml1,Names1),
        collect_names(Fml2,Names2),
        union(Names1,Names2,Names).
collect_names(-Fml,Names) :- !,
        collect_names(Fml,Names).
collect_names(some(_Vars,Fml),Names) :- !,
        collect_names(Fml,Names).
collect_names(all(_Vars,Fml),Names) :- !,
        collect_names(Fml,Names).
collect_names(know(Fml),Names) :- !,
        collect_names(Fml,Names).
collect_names((X=Y),Names) :- !,
        collect_names_term(X,Names1),
        collect_names_term(Y,Names2),
        union(Names1,Names2,Names).
collect_names(Atom,Names) :- !,
        Atom =.. [_P|Args],
        collect_names_term_list(Args,Names).

collect_names_term(T,[]) :-
        var(T), !.
collect_names_term(T,[T]) :-
        atom(T),
        stdname(T), !.
collect_names_term(T,[]) :-
        atom(T),
        not(stdname(T)), !.
collect_names_term(T,Names) :- !,
        T =.. [_|L],
        collect_names_term_list(L,Names).

collect_names_term_list([],[]) :- !.
collect_names_term_list([E|L],Names) :- !,
        collect_names_term(E,Names1),
        collect_names_term_list(L,Names2),
        union(Names1,Names2,Names).

create_new_names(_Names,0,[]) :- !.
create_new_names(Names,K,[C|Names2]) :- K > 0, !,
        K1 is K - 1,
        create_new_names(Names,K1,Names2),
        smallest_name_not_contained(Names,Names2,C).

smallest_name_not_contained(S1,S2,C) :- !,
        smallest_name_not_contained2(S1,S2,C,[97]).

smallest_name_not_contained2(S1,S2,C,[Char|Chars]) :-
        string_to_list(String,[Char|Chars]),
        atom_string(Atom,String),
        not(member(Atom,S1)),
        not(member(Atom,S2)), !,
        C=Atom.

smallest_name_not_contained2(S1,S2,C,[Char|Chars]) :-
        string_to_list(String,[Char|Chars]),
        atom_string(Atom,String),
        (member(Atom,S1);member(Atom,S2)),
        Char < 122, !,
        Char1 is Char + 1,
        smallest_name_not_contained2(S1,S2,C,[Char1|Chars]).

smallest_name_not_contained2(S1,S2,C,[Char|Chars]) :-
        string_to_list(String,[Char|Chars]),
        atom_string(Atom,String),
        (member(Atom,S1);member(Atom,S2)),
        Char = 122, !,
        smallest_name_not_contained2(S1,S2,C,[97,122|Chars]).

neg_disjunct_inequalities(_Var,[],true) :- !.
neg_disjunct_inequalities(Var,[Name],(-(Var=Name))) :- !.
neg_disjunct_inequalities(Var,[Name|Names],(-(Var=Name))*Inequalities) :- !,
        neg_disjunct_inequalities(Var,Names,Inequalities).

                             
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check result against initial theory
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TODO: integrate this into reasoner!!!

initially(-(X=Y)) :-
        stdname(X),
        stdname(Y),
        X \= Y.

% TODO: duplicate code!!! (verification_cgraphs)                             
                             
entails_initially(Fml,Truth) :-
        findall(IniFml,
                initially(IniFml),
                KB),
        entails(KB,Fml), !,
        Truth = true.
entails_initially(_Fml,Truth) :- !,
        Truth = false.

% TODO: what about defs???
