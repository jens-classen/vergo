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

:- export(elim/3).

:- export equivalent/2.
:- export equivalent/3.
:- export entails/3.

%:- get_flag(output_options,Old),
%   set_flag(output_options,[variables(full)|Old]).

:- dynamic(clause_dnf/4).

:- dynamic equivalent_cached/3.
:- dynamic nonequiv_cached/3.

uno(e).
uno(p).
functional_fluent(q1).
functional_fluent(q2).

% todo: deal with unused variables!

% todo: unique variables!!!

clausalform_cnf(Fml,Cla,Unis,Exis,Vars,Skol) :-
        cf_nnf(Fml,Fml1,[],Unis,Exis,Vars,'skol1',_SkolS2,Skol),
        cf_cnf(Fml1,Fml2),
        cf_cnf_clauses(Fml2,Cla1),
        cf_cnf_clauses_simplify(Cla1,Unis,Exis,Vars,Cla).

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
        cf_dnf_clauses(Fml2,Cla1),
        cf_dnf_clauses_simplify(Cla1,Unis,Exis,Vars,Cla).

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

cf_dnf_clauses_simplify(Cla,Unis,Exis,Vars,Cla2) :-
        %unit propagation?
        cf_dnf_simplify_exi(Cla,Unis,Exis,Vars,Cla3),!,
        cf_dnf_remove_true_false(Cla3,Cla4),!,
        %cf_dnf_remove_tautologies(Cla5,Unis,Exis,Vars,Cla2).
        cf_dnf_remove_unsat(Cla4,Cla5),!,
        cf_dnf_remove_duplicate_lits(Cla5,Cla6),!,
        cf_dnf_remove_duplicate_clauses(Cla6,Cla7),!,
        cf_dnf_remove_subsumed(Cla7,Cla8),!,
        cf_dnf_simplify_resolution(Cla8,Cla2,Unis,Exis,Vars).
        %cf_dnf_remove_subsumed_variants(Cla4,Unis,Exis,Vars,Cla2).
        % test if empty => false

cf_dnf_simplify_exi([Clause|Clauses],Unis,Exis,Vars,[Clause2|Clauses2]) :-
        cf_dnf_simplify_exi_clause(Clause,Unis,Exis,Vars,Clause2),
        cf_dnf_simplify_exi(Clauses,Unis,Exis,Vars,Clauses2).
cf_dnf_simplify_exi([],_,_,_,[]).

cf_dnf_simplify_exi_clause(Clause,U,E,V,Clause2) :-
        cf_dnf_simplify_exi_clause2(Clause,[],U,E,V,Clause3),
        cf_dnf_simplify_exi_clause3(Clause3,U,E,V,Clause2).
cf_dnf_simplify_exi_clause2([(X=Y)|Lits],Lits2,Unis,Exis,Vars,Clause2) :-
        member2(X,Exis),
        ground(Y), !,
        subv(X,Y,Lits,LitsX),
        subv(X,Y,Lits2,Lits2X),
        cf_dnf_simplify_exi_clause2(LitsX,Lits2X,Unis,Exis,Vars,Clause2).
cf_dnf_simplify_exi_clause2([(X=Y)|Lits],Lits2,Unis,Exis,Vars,Clause2) :-
        member2(Y,Exis),
        ground(X), !,
        subv(Y,X,Lits,LitsX),
        subv(Y,X,Lits2,Lits2X),
        cf_dnf_simplify_exi_clause2(LitsX,Lits2X,Unis,Exis,Vars,Clause2).
cf_dnf_simplify_exi_clause2([Lit|Lits],Lits2,Unis,Exis,Vars,Clause2) :-
        cf_dnf_simplify_exi_clause2(Lits,[Lit|Lits2],Unis,Exis,Vars,Clause2).
cf_dnf_simplify_exi_clause2([],Lits,_Unis,_Exis,_Vars,Clause2) :-
        reverse(Lits,Clause2).

cf_dnf_simplify_exi_clause3(Clause,U,E,V,Clause2) :-
        % do existentials only appear in equalities with ground terms?
        %% cf_dnf_exis_inequalities_only(Clause,U,E,V),!,
        % then remove these inequalities from clause
        cf_dnf_remove_exis_inequalities(Clause,[],U,E,V,Clause2).
cf_dnf_simplify_exi_clause3(Clause,_,_,_,Clause).

%% cf_dnf_exis_inequalities_only([~(X=Y)|Lits],U,E,V) :-
%%         member2(X,E),
%%         ground(Y),
%%         cf_dnf_exis_inequalities_only(Lits,U,E,V).
%% cf_dnf_exis_inequalities_only([~(Y=X)|Lits],U,E,V) :-
%%         member2(X,E),
%%         ground(Y),
%%         cf_dnf_exis_inequalities_only(Lits,U,E,V).
%% cf_dnf_exis_inequalities_only([Lit|Lits],U,E,V) :-
%%         term_variables(Lit,LVars),
%%         disjoint2(LVars,E),
%%         cf_dnf_exis_inequalities_only(Lits,U,E,V).
%% cf_dnf_exis_inequalities_only([],_,_,_).

cf_dnf_remove_exis_inequalities([~(X=Y)|Lits],Lits2,U,E,V,Clause2) :-
        member2(X,E),
        ground(Y),
        cf_dnf_remove_exis_inequalities(Lits,Lits2,U,E,V,Clause2).
cf_dnf_remove_exis_inequalities([~(Y=X)|Lits],Lits2,U,E,V,Clause2) :-
        member2(X,E),
        ground(Y),
        cf_dnf_remove_exis_inequalities(Lits,Lits2,U,E,V,Clause2).
cf_dnf_remove_exis_inequalities([Lit|Lits],Lits2,U,E,V,Clause2) :-
        term_variables(Lit,LVars),
        disjoint2(LVars,E),        
        cf_dnf_remove_exis_inequalities(Lits,[Lit|Lits2],U,E,V,Clause2).
cf_dnf_remove_exis_inequalities([],Lits2,_,_,_,Clause2) :-
        reverse(Lits2,Clause2).
                                   
                                   
%% cf_dnf_simplify_exi_clause2([~(X=Y)|Lits],Lits2,Unis,Exis,Vars,Clause2) :-
%%         member2(X,Exis),
%%         ground(Y),
%%         term_variables((Lits,Lits2),CVars),
%%         not(member2(X,CVars)),!,
%%         cf_dnf_simplify_exi_clause2(Lits,Lits2,Unis,Exis,Vars,Clause2).
%% cf_dnf_simplify_exi_clause2([~(X=Y)|Lits],Lits2,Unis,Exis,Vars,Clause2) :-
%%         member2(Y,Exis),
%%         ground(X),
%%         term_variables((Lits,Lits2),CVars),
%%         not(member2(Y,CVars)),!,
%%         cf_dnf_simplify_exi_clause2(Lits,Lits2,Unis,Exis,Vars,Clause2).

cf_dnf_remove_true_false([Clause|Clauses],Clauses2) :-
        member2($false,Clause),!,
        cf_dnf_remove_true_false(Clauses,Clauses2).
cf_dnf_remove_true_false([Clause|Clauses],Clauses2) :-
        member2(~($true),Clause),!,
        cf_dnf_remove_true_false(Clauses,Clauses2).
cf_dnf_remove_true_false([Clause|Clauses],Clauses2) :-
        cf_dnf_unsat_inequality(Clause), !,
        cf_dnf_remove_true_false(Clauses,Clauses2).
cf_dnf_remove_true_false([Clause|Clauses],Clauses2) :-
        cf_dnf_unsat_equality(Clause), !,
        cf_dnf_remove_true_false(Clauses,Clauses2).
cf_dnf_remove_true_false([Clause|Clauses],[Clause2|Clauses2]) :-
        cf_dnf_remove_true(Clause,Clause2),
        cf_dnf_remove_true_false(Clauses,Clauses2).
cf_dnf_remove_true_false([],[]).

cf_dnf_unsat_inequality([~(X=Y)|_Lits]) :-
        X==Y.
cf_dnf_unsat_inequality([_|Lits]) :-
        cf_dnf_unsat_inequality(Lits).

cf_dnf_unsat_equality([(X=Y)|_Lits]) :-
        ground(X), ground(Y), uno(X), uno(Y), X \== Y.
cf_dnf_unsat_equality([_|Lits]) :-
        cf_dnf_unsat_equality(Lits).

cf_dnf_remove_true([$true|Lits],Lits2) :- !,
        cf_dnf_remove_true(Lits,Lits2).
cf_dnf_remove_true([~($false)|Lits],Lits2) :- !,
        cf_dnf_remove_true(Lits,Lits2).
cf_dnf_remove_true([~(X=Y)|Lits],Lits2) :-
        ground(X), ground(Y), uno(X), uno(Y), X \== Y, !,
        cf_dnf_remove_true(Lits,Lits2).
cf_dnf_remove_true([(X=Y)|Lits],Lits2) :- 
        X==Y,!,
        cf_dnf_remove_true(Lits,Lits2).
cf_dnf_remove_true([Lit|Lits],[Lit|Lits2]) :-
        cf_dnf_remove_true(Lits,Lits2).
cf_dnf_remove_true([],[]).

cf_dnf_remove_unsat([Clause|Clauses],Clauses2) :-
        cf_dnf_unsat_clause(Clause),!,
        cf_dnf_remove_unsat(Clauses,Clauses2).
cf_dnf_remove_unsat([Clause|Clauses],[Clause|Clauses2]) :-
        cf_dnf_remove_unsat(Clauses,Clauses2).
cf_dnf_remove_unsat([],[]).

cf_dnf_unsat_clause([Lit|Lits]) :-
        member2(~Lit,Lits).
cf_dnf_unsat_clause([~Atom|Lits]) :-
        member2(Atom,Lits).
cf_dnf_unsat_clause([_Lit|Lits]) :-
        cf_dnf_unsat_clause(Lits).

cf_dnf_remove_subsumed(Clauses,Clauses2) :-
        cf_dnf_remove_subsumed(Clauses,Clauses,Clauses2).
cf_dnf_remove_subsumed([Clause|Clauses1],Clauses,Clauses2) :-
        cf_dnf_subsumed(Clause,Clauses),!,
        cf_dnf_remove_subsumed(Clauses1,Clauses,Clauses2).
cf_dnf_remove_subsumed([Clause|Clauses1],Clauses,[Clause|Clauses2]) :-
        cf_dnf_remove_subsumed(Clauses1,Clauses,Clauses2).
cf_dnf_remove_subsumed([],_,[]).

cf_dnf_subsumed(Clause,[Clause2|_Clauses]) :-
        Clause \== Clause2,
        subsumes(Clause2,Clause),!.
cf_dnf_subsumed(Clause,[_|Clauses]) :-
        cf_dnf_subsumed(Clause,Clauses).

subsumes(Clause1,Clause2) :-
        subset2(Clause1,Clause2).
        
cf_dnf_remove_duplicate_clauses([Clause|Clauses],Clauses2) :-
        cf_dnf_duplicate_clause_list(Clause,Clauses), !,
        cf_dnf_remove_duplicate_clauses(Clauses,Clauses2).
cf_dnf_remove_duplicate_clauses([Clause|Clauses],[Clause|Clauses2]) :-
        cf_dnf_remove_duplicate_clauses(Clauses,Clauses2).
cf_dnf_remove_duplicate_clauses([],[]).

cf_dnf_duplicate_clause_list(Clause,[Clause2|_Clauses]) :-
        cf_dnf_duplicate(Clause,Clause2).
cf_dnf_duplicate_clause_list(Clause,[_|Clauses]) :-
        cf_dnf_duplicate_clause_list(Clause,Clauses).

cf_dnf_duplicate(Clause1,Clause2) :-
        subset2(Clause1,Clause2),
        subset2(Clause2,Clause1).

cf_dnf_remove_duplicate_lits([Clause|Clauses],[Clause2|Clauses2]) :-
        cf_dnf_remove_duplicate_lits_clause(Clause,Clause2),
        cf_dnf_remove_duplicate_lits(Clauses,Clauses2).
cf_dnf_remove_duplicate_lits([],[]).

cf_dnf_remove_duplicate_lits_clause([Lit|Lits],Lits2) :-
        member2(Lit,Lits),!,
        cf_dnf_remove_duplicate_lits_clause(Lits,Lits2).
cf_dnf_remove_duplicate_lits_clause([Lit|Lits],[Lit|Lits2]) :-
        cf_dnf_remove_duplicate_lits_clause(Lits,Lits2).
cf_dnf_remove_duplicate_lits_clause([],[]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cf_dnf_simplify_resolution(Clauses1,Clauses2,U,E,V) :-
        assert_clauses_dnf(Clauses1,U,E,V),
        resolve_clauses_dnf(U,E,V),
        retract_clauses_dnf(Clauses2,U,E,V).

assert_clauses_dnf([Clause|Clauses],U,E,V) :-
        assert(clause_dnf(Clause,U,E,V)),
        assert_clauses_dnf(Clauses,U,E,V).
assert_clauses_dnf([],_,_,_).

retract_clauses_dnf([Clause|Clauses],U,E,V) :-
        retract(clause_dnf(Clause,U,E,V)),
        retract_clauses_dnf(Clauses,U,E,V).
retract_clauses_dnf([],_,_,_).

resolve_clauses_dnf(U,E,V) :-
        clause_dnf(Clause1,U,E,V),
        clause_dnf(Clause2,U,E,V),
        resolve_dnf(Clause1,Clause2,Clause3),!,
        retract(clause_dnf(Clause1,U,E,V)),
        retract(clause_dnf(Clause2,U,E,V)),
        assert(clause_dnf(Clause3,U,E,V)),
        resolve_clauses_dnf(U,E,V).
resolve_clauses_dnf(_,_,_).

resolve_dnf(Clause1,Clause2,Clause3) :-
        length(Clause1,L),
        length(Clause2,L),
        member(Lit1, Clause1),
        member(~ Lit2, Clause2),
        Lit1 == Lit2,
        intersection2(Clause1,Clause2,Clause3),
        L1 is L-1,
        length(Clause3,L1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simplify_formula_dnf(Fml,Fml2) :- !,
        clausalform_dnf(Fml,Cla,U,E,V,_S), !,
        clauses2fml_dnf(Fml2,Cla,U,E,V).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

elim(Preds,Phi1,Phi2) :- !,
        clausalform_dnf(Phi1,Cla,Unis,Exis,Vars,_Skol),
        elim_clauses(Preds,Cla,Cla2,Unis,Exis,Vars),
        clauses2fml_dnf(Phi2,Cla2,Unis,Exis,Vars).

elim_clauses([Pred|Preds],Cla1,Cla2,Unis,Exis,Vars) :-
        atom(Pred),!,
        elim_clauses(Preds,Cla1,Cla3,Unis,Exis,Vars),
        subv(Pred,$true,Cla3,Cla3p),
        subv(Pred,$false,Cla3,Cla3n),
        append(Cla3p,Cla3n,Cla4),
        cf_dnf_clauses_simplify(Cla4,Unis,Exis,Vars,Cla2).
elim_clauses([],Cla,Cla,_U,_E,_V).



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

        



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

equivalent(Fml1,Fml2) :- equivalent(Fml1,Fml2,[]).

equivalent(Fml1,Fml2,Axioms) :- equivalent_cached(Fml1,Fml2,Axioms), !.
equivalent(Fml1,Fml2,Axioms) :- nonequiv_cached(Fml1,Fml2,Axioms), !, fail.
equivalent(Fml1,Fml2,Axioms) :- determine_equivalence(Fml1,Fml2,Axioms,Truth),
        (Truth = ($true) -> asserta(equivalent_cached(Fml1,Fml2,Axioms));
                            (asserta(nonequiv_cached(Fml1,Fml2,Axioms)),fail)).

determine_equivalence(Fml1,Fml2,_Axioms,Truth) :- variant(Fml1,Fml2), !, Truth=($true).

determine_equivalence(Fml1,Fml2,Axioms,($true)) :-
        entails(Fml1,Fml2,Axioms),
        entails(Fml2,Fml1,Axioms), !.

%% determine_equivalence(Fml1,Fml2,Axioms,($true)) :-
%%         write_problem_file(Fml1,Fml2,Axioms,'conjecture.tptp'),
%%         exec(["./prove", "conjecture.tptp", "output.txt"],[]),
%%         sh("rm conjecture.tptp"),
%%         open('output.txt',read,result),
%%         read_string(result,end_of_line,_L2,SecondLine),
%%         close(result),
%%         sh("rm output.txt"),
%%         SecondLine =="% SZS status Theorem", !.

%% entails(Fml1,Fml2,Axioms) :-
%%         term_variables((Fml1,Fml2),[]),
%%         clausalform_dnf(Fml1,Cla1,[],[],[],[]),
%%         clausalform_dnf(Fml2,Cla2,[],[],[],[]),!,
%%         clausal_subsumption_dnf(Cla1,Cla2).
        
        
        
entails(Fml1,Fml2,Axioms) :-
        write_problem_file(Fml2,[Fml1|Axioms],'conjecture.tptp'),
        exec(["./E/bin/eprover", "--tptp3-in", "-m", "2048", "-s",
              "conjecture.tptp", "-o", "output.tptp"],[]),
        %sh("rm conjecture.tptp"),
        sh("mv conjecture.tptp conjecture_old.tptp"),
        open('output.tptp',read,result),
        read_string(result,end_of_line,_L1,_FirstLine),
        read_string(result,end_of_line,_L2,SecondLine),
        close(result),
        sh("rm output.tptp"),
        SecondLine == "# Proof found!".

clausal_subsumption_dnf(Clauses,[Clause2|Clauses2]) :-
        member(Clause,Clauses),
        subset2(Clause2,Clause),
        clausal_subsumption_dnf(Clauses,Clauses2).
clausal_subsumption_dnf(Clauses,[Clause2]) :-
        member(Clause,Clauses),
        subset2(Clause2,Clause).


write_problem_file(Fml,Axioms,FileName) :-
        open(FileName,write,conjecture),
        formula_string(Fml,FormulaS),
        axioms_string(Axioms,AxiomsS),
        concat_string(["fof(conj,conjecture,",FormulaS,")."],EquiSD),
        write(conjecture,AxiomsS),
        writeln(conjecture,EquiSD),
        close(conjecture).
        

determine_equivalence(_Fml1,_Fml2,($false)).

axioms_string(Axioms,String) :-
        axioms_string(Axioms,String,1).

axioms_string([],"",_).
axioms_string([A|Axioms],S,I) :-
        I1 is I + 1,
        axioms_string(Axioms,AxiomsS,I1),
        formula_string(A,AS),
        integer_atom(I,IA),
        atom_string(IA,IS),
        concat_string(["fof(axiom", IS, ",axiom,",AS,").\n", AxiomsS],S).

formula_string(~Fml,S) :- !,
        formula_string(Fml,FS),
        concat_string(["~(",FS,")"],S).
formula_string(F1|F2,S) :- !,
        formula_string(F1,FS1),
        formula_string(F2,FS2),
        concat_string(["(",FS1,")|(",FS2,")"],S).
formula_string(F1&F2,S) :- !,
        formula_string(F1,FS1),
        formula_string(F2,FS2),
        concat_string(["(",FS1,")&(",FS2,")"],S).
formula_string(F1=>F2,S) :- !,
        formula_string(F1,FS1),
        formula_string(F2,FS2),
        concat_string(["(",FS1,")=>(",FS2,")"],S).
formula_string(F1<=>F2,S) :- !,
        formula_string(F1,FS1),
        formula_string(F2,FS2),
        concat_string(["(",FS1,")<=>(",FS2,")"],S).
formula_string(F1<=F2,S) :- !,
        formula_string(F1,FS1),
        formula_string(F2,FS2),
        concat_string(["(",FS1,")<=(",FS2,")"],S).
formula_string(!Vars:Fml,S) :- !,
        term_string(Vars,VarsS),
        formula_string(Fml,FS),
        concat_string(["!",VarsS,":(",FS,")"],S).
formula_string(?Vars:Fml,S) :- !,
        term_string(Vars,VarsS),
        formula_string(Fml,FS),
        concat_string(["?",VarsS,":(",FS,")"],S).
formula_string(X=Y,S) :- !,
        term_string(X,XS),
        term_string(Y,YS),
        concat_string(["(",XS," = ",YS,")"],S).
formula_string($true,"$true") :- !.
formula_string($false,"$false") :- !.
formula_string(Atom,S) :-
        term_string(Atom,S).
