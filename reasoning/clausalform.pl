:- module(clausalform).

:- use_module(tptp).
:- use_module(utils).

:- lib(lists).

:- export(clausalform_cnf/6).
:- export(clauses2fml_cnf/5).

:- export(clausalform_dnf/6).
:- export(clauses2fml_dnf/5).

:- export(simplify_formula_cnf/2).
:- export(simplify_formula_dnf/2).

%:- get_flag(output_options,Old),
%   set_flag(output_options,[variables(full)|Old]).

% todo: deal with unused variables!

% todo: unique variables!!!

clausalform_cnf(Fml,Cla,Unis,Exis,Vars,Skol) :-
        cf_nnf(Fml,Fml1,[],Unis,Exis,Vars,'skol1',_SkolS2,Skol),
        cf_cnf(Fml1,Fml2),
        cf_cnf_clauses(Fml2,Cla).

% cf_nnf(+Fml1,-Fml2,-Fml3,+FreeV,-Unis,+SkolS1,-SkolS2,-Skol):
% ** Fml2 is the negational normal form of Fml1 **
%    -> FreeV are the free variables of Fml1
%    -> Unis  are the universally quantified variables of Fml2
%    -> Exis  are the existentially quantified variables of Fml2
%    -> AllVars are all variables appearing in Fml2
%       in the correct order (for the prenex form)
%    -> SkolS1 is the next usable skolem function symbol *before*
%       conversion (starting with 'skol1','skol2',...)
%    -> SkolS2 is the next usable skolem function symbol *after*
%       conversion
%    -> Skol is the set of skolem terms introduced during conversion

cf_nnf((F1<=>F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf((~F1|F2)&(F1|~F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
cf_nnf((F1=>F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf((~F1|F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
cf_nnf((F1<=F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf((F1|~F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
cf_nnf((F1&F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf(F1,Fml1,FreeV,Unis1,Exis1,AllVars1,SkolS1,SkolS3,Skol1),
        cf_nnf(F2,Fml2,FreeV,Unis2,Exis2,AllVars2,SkolS3,SkolS2,Skol2),
        append(Unis1,Unis2,Unis),
        append(Exis1,Exis2,Exis),
        append(AllVars1,AllVars2,AllVars),
        append(Skol1,Skol2,Skol),
        Fml=(Fml1&Fml2).
cf_nnf((F1|F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf(F1,Fml1,FreeV,Unis1,Exis1,AllVars1,SkolS1,SkolS3,Skol1),
        cf_nnf(F2,Fml2,FreeV,Unis2,Exis2,AllVars2,SkolS3,SkolS2,Skol2),
        append(Unis1,Unis2,Unis),
        append(Exis1,Exis2,Exis),
        append(AllVars1,AllVars2,AllVars),
        append(Skol1,Skol2,Skol),
        Fml=(Fml1|Fml2).
cf_nnf(!Vars:F,Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        append(Vars,FreeV,FreeV1),
        cf_nnf(F,Fml,FreeV1,Unis1,Exis,AllVars1,SkolS1,SkolS2,Skol),
        append(Vars,Unis1,Unis),
        append(Vars,AllVars1,AllVars).
cf_nnf(?[Var|Vars]:F,Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,[NewSymbol|Skol1]) :- !,
        NewSymbol =.. [SkolS1|FreeV],
        %Var = NewSymbol,
        skol_next(SkolS1,SkolS3),
        cf_nnf(?Vars:F,Fml,FreeV,Unis,Exis1,AllVars1,SkolS3,SkolS2,Skol1),
        Exis=[Var|Exis1],
        AllVars=[Var|AllVars1].
cf_nnf(?[]:F,Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf(F,Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
        
cf_nnf(~(~F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf(F,Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
cf_nnf(~(F1<=>F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf((F1|F2)&(~F1|~F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
cf_nnf(~(F1=>F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf((F1&(~F2)),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
cf_nnf(~(F1<=F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf((~F1&F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
cf_nnf(~(F1&F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf((~F1|~F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
cf_nnf(~(F1|F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf(((~F1)&(~F2)),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
cf_nnf(~(!Vars:F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf(?Vars:(~F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
cf_nnf(~(?Vars:F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        cf_nnf(!Vars:(~F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).

cf_nnf(Lit,Lit,_FreeV,[],[],[],SkolS,SkolS,[]).

% skolem symbols are 'skol1','skol2','skol3',...
skol_next(A1,A2) :-
        atom_string(A1,S1),
        append_strings("skol",N1,S1),
        number_string(I1,N1),
        I2 is I1+1,
        number_string(I2,N2),
        append_strings("skol",N2,S2),
        atom_string(A2,S2).

% convert NNF into CNF by distributing disjunctions over conjunctions
cf_cnf((F1&F2)|F3,(Fml1&Fml2)) :- !,
        cf_cnf((F1|F3),Fml1),
        cf_cnf((F2|F3),Fml2).
cf_cnf(F1|(F2&F3),(Fml1&Fml2)) :- !,
        cf_cnf((F1|F2),Fml1),
        cf_cnf((F1|F3),Fml2).
cf_cnf((F1|F2),Fml) :- !,
        cf_cnf(F1,Fml1),
        cf_cnf(F2,Fml2),
        ( (Fml1=(_A1&_B1);Fml2=(_A2&_B2)) -> cf_cnf((Fml1|Fml2),Fml); Fml=(Fml1|Fml2)).
cf_cnf((F1&F2),(Fml1&Fml2)) :- !,
        cf_cnf(F1,Fml1),
        cf_cnf(F2,Fml2).
cf_cnf(Lit,Lit).

% convert CNF formula in clause set
cf_cnf_clauses(F1&F2,Clauses) :- !,
        cf_cnf_clauses(F1,Clauses1),
        cf_cnf_clauses(F2,Clauses2),
        append(Clauses1,Clauses2,Clauses).
cf_cnf_clauses(F1|F2,[Clause]) :- !,
        cf_cnf_clauses(F1,[Clause1]),
        cf_cnf_clauses(F2,[Clause2]),
        append(Clause1,Clause2,Clause).
cf_cnf_clauses($true,[]).
cf_cnf_clauses($false,[[]]).
cf_cnf_clauses(Lit,[[Lit]]).


cf_cnf_clauses_simplify(Cla1,_U,_E,_V,Cla1).% :-
        %remove true
        %remove false
        %remove subsumed variants (incl. duplicates, variants)
        %unit propagation?
        %exists x.x=t


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clauses2fml_cnf(Fml,Cla,Unis,Exis,Vars) :-
        %make_fresh_variables(Unis,Skol,NewVars),
        clauses2cnf(Cla,CNF),
        attach_quantifiers(Fml1,CNF,Unis,Exis,Vars),
        flatten_quantifiers(Fml1,Fml).

clauses2cnf([Clause],Fml) :- !,
        clause2disjunction(Clause,Fml).
clauses2cnf([Clause|Clauses],(Fml1&Fml2)) :- !,
        clause2disjunction(Clause,Fml1),
        clauses2cnf(Clauses,Fml2).
clauses2cnf([],$true).

clause2disjunction([Lit],Lit) :- !.
clause2disjunction([Lit|Lits],(Lit|Fml)) :- !,
        clause2disjunction(Lits,Fml).
clause2disjunction([],$false).

% if X does not appear in CNF => ignore
attach_quantifiers(Fml,CNF,Unis,Exis,[X|Vars]) :-
        term_variables(CNF,TVars),
        not(member2(X,TVars)),!,
        attach_quantifiers(Fml,CNF,Unis,Exis,Vars).

attach_quantifiers(Fml,CNF,Unis,Exis,[X|Vars]) :-
        member2(X,Unis),!,
        attach_quantifiers(Fml1,CNF,Unis,Exis,Vars),
        Fml=(![X]:Fml1).
attach_quantifiers(Fml,CNF,Unis,Exis,[X|Vars]) :-
        member2(X,Exis),!,
        attach_quantifiers(Fml1,CNF,Unis,Exis,Vars),
        Fml=(?[X]:Fml1).
attach_quantifiers(CNF,CNF,_Unis,_Exis,[]).

flatten_quantifiers(!Vars1:(!Vars2:Fml),Result) :- !,
        append(Vars1,Vars2,Vars),
        flatten_quantifiers(!Vars:Fml,Result).
flatten_quantifiers(?Vars1:(?Vars2:Fml),Result) :- !,
        append(Vars1,Vars2,Vars),
        flatten_quantifiers(?Vars:Fml,Result).
flatten_quantifiers(?Vars1:(!Vars2:Fml),?Vars1:Result) :- !,
        flatten_quantifiers(!Vars2:Fml,Result).
flatten_quantifiers(!Vars1:(?Vars2:Fml),!Vars1:Result) :- !,
        flatten_quantifiers(?Vars2:Fml,Result).
flatten_quantifiers(Fml,Fml).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simplify_formula_cnf(Fml,Fml2) :-
        clausalform_cnf(Fml,Cla,U,E,V,_S),!,
        clauses2fml_cnf(Fml2,Cla,U,E,V).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clausalform_dnf(Fml,Cla,Unis,Exis,Vars,Skol) :-
        cf_nnf(Fml,Fml1,[],Unis,Exis,Vars,'skol1',_SkolS2,Skol),
        cf_dnf(Fml1,Fml2),
        cf_dnf_clauses(Fml2,Cla).

% convert NNF into DNF by distributing conjunctions over disjunctions
cf_dnf((F1|F2)&F3,(Fml1|Fml2)) :- !,
        cf_dnf((F1&F3),Fml1),
        cf_dnf((F2&F3),Fml2).
cf_dnf(F1&(F2|F3),(Fml1|Fml2)) :- !,
        cf_dnf((F1&F2),Fml1),
        cf_dnf((F1&F3),Fml2).
cf_dnf((F1&F2),Fml) :- !,
        cf_dnf(F1,Fml1),
        cf_dnf(F2,Fml2),
        ( (Fml1=(_A1|_B1);Fml2=(_A2|_B2)) -> cf_dnf((Fml1&Fml2),Fml); Fml=(Fml1&Fml2)).
cf_dnf((F1|F2),(Fml1|Fml2)) :- !,
        cf_dnf(F1,Fml1),
        cf_dnf(F2,Fml2).
cf_dnf(Lit,Lit).

% convert DNF formula in clause set
cf_dnf_clauses(F1|F2,Clauses) :- !,
        cf_dnf_clauses(F1,Clauses1),
        cf_dnf_clauses(F2,Clauses2),
        append(Clauses1,Clauses2,Clauses).
cf_dnf_clauses(F1&F2,[Clause]) :- !,
        cf_dnf_clauses(F1,[Clause1]),
        cf_dnf_clauses(F2,[Clause2]),
        append(Clause1,Clause2,Clause).
cf_dnf_clauses($false,[]).
cf_dnf_clauses($true,[[]]).
cf_dnf_clauses(Lit,[[Lit]]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simplify_formula_dnf(Fml,Fml2) :- !,
        clausalform_dnf(Fml,Cla,U,E,V,_S), !,
        clauses2fml_dnf(Fml2,Cla,U,E,V).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clauses2fml_dnf(Fml,Cla,Unis,Exis,Vars) :-
        %make_fresh_variables(Unis,Skol,NewVars),
        clauses2dnf(Cla,DNF),
        attach_quantifiers(Fml1,DNF,Unis,Exis,Vars),
        flatten_quantifiers(Fml1,Fml).

clauses2dnf([Clause],Fml) :- !,
        clause2conjunction(Clause,Fml).
clauses2dnf([Clause|Clauses],(Fml1|Fml2)) :- !,
        clause2conjunction(Clause,Fml1),
        clauses2dnf(Clauses,Fml2).
clauses2dnf([],$false).

clause2conjunction([Lit],Lit) :- !.
clause2conjunction([Lit|Lits],(Lit&Fml)) :- !,
        clause2conjunction(Lits,Fml).
clause2conjunction([],$true).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 