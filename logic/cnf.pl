%- module(clausalform).

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

%:- get_flag(output_options,Old),
%   set_flag(output_options,[variables(full)|Old]).

:- dynamic(clause_dnf/4).

% todo: deal with unused variables!

% todo: unique variables!!!

clausalform_cnf(Fml,Cla,Unis,Exis,Vars,Skol) :-
        cf_nnf(Fml,Fml1,[],Unis,Exis,Vars,'skol1',_SkolS2,Skol),
        cf_cnf(Fml1,Fml2),
        cf_cnf_clauses(Fml2,Cla1),
        cf_cnf_clauses_simplify(Cla1,Unis,Exis,Vars,Cla).

cf_cnf_clauses_simplify(Cla1,_U,_E,_V,Cla1).% :-
        %remove true
        %remove false
        %remove subsumed variants (incl. duplicates, variants)
        %unit propagation?
        %exists x.x=t

%% % generate new variables for deskolemization
%% make_fresh_variables(Unis,[Skol|Skols],[X|NewVars]) :-
%%         make_fresh_variables(Unis,Skols,NewVars),
%%         copy_term((Unis,NewVars,X2),(_Unis2,_NewVars2,X)).
%% make_fresh_variables(_Unis,[],[]).

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
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Variant simplification procedure
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cf_clauses_simplify(Cla1,U,E,V,Cla2) :-
        sort_clauses(Cla1,Cla3),
        cf_find_inconsistencies(Cla3,Cla4),
        cf_remove_tautologies(Cla4,Cla5),
        cf_remove_duplicate_cl(Cla5,Cla6),
        cf_simplify_exi(Cla6,U,E,V,Cla7),
        cf_remove_subsumed(Cla7,Cla8),
        %%cf_simplify_variant_clauses(Cla6,U,Cla7),
        cf_remove_subsumed_variants(Cla8,U,E,V,Cla2).
        %sort_clauses(Cla7,Cla2).

% sort clauses plus their literals (eliminates duplicates)
sort_clauses(Clauses1,Clauses2) :-
        sort_clauses2(Clauses1,Clauses3),
        sort(Clauses3,Clauses2).

% sort the literals in each clause (eliminates duplicates)
sort_clauses2([Clause|Clauses],[Clause2|Clauses2]) :-
        sort(Clause,Clause2),
        sort_clauses(Clauses,Clauses2).
sort_clauses2([],[]).

% remove tautologuous clauses
cf_remove_tautologies([Cl|Cls],Cls2) :-
        member((X=Y),Cl), X==Y, !,
        cf_remove_tautologies(Cls,Cls2).
% remove tautologuous clauses
cf_remove_tautologies([Cl|Cls],Cls2) :-
        (member($true,Cl);member(~($false),Cl)),!,
        cf_remove_tautologies(Cls,Cls2).
% remove tautologuous clauses
cf_remove_tautologies([Cl|Cls],Cls2) :-
        member(~(Atom1),Cl),
        member(Atom2,Cl), 
        Atom1 == Atom2, !,
        cf_remove_tautologies(Cls,Cls2).
cf_remove_tautologies([Cl|Cls],[Cl2|Cls2]) :-
        cf_remove_false(Cl,Cl2),
        cf_remove_tautologies(Cls,Cls2).
cf_remove_tautologies([],[]).

cf_remove_false([~(X=Y)|Lits],Lits2) :-
        X==Y, !,
        cf_remove_false(Lits,Lits2).
cf_remove_false([($false)|Lits],Lits2) :- !,
        cf_remove_false(Lits,Lits2).
cf_remove_false([~($true)|Lits],Lits2) :- !,
        cf_remove_false(Lits,Lits2).
cf_remove_false([Lit|Lits],[Lit|Lits2]) :-
        cf_remove_false(Lits,Lits2).
cf_remove_false([],[]).

% eliminate double clauses
% warning: this is expensive !!!

cf_remove_duplicate_cl([Cl|Cls],Cls2) :-
        %shuffle(Cl,Cl2),
        member2(Cl,Cls), !,
        cf_remove_duplicate_cl(Cls,Cls2).
cf_remove_duplicate_cl([Cl|Cls],[Cl|Cls2]) :-
        cf_remove_duplicate_cl(Cls,Cls2).
cf_remove_duplicate_cl([],[]).

cf_find_inconsistencies(Clauses,[[]]) :-
        member([Lit],Clauses),
        member([~Lit],Clauses), !.
cf_find_inconsistencies(Clauses,[[]]) :-
        member2([~(X=Y)],Clauses),
        X==Y, !.
cf_find_inconsistencies(Clauses,Clauses).

cf_simplify_exi(Cla,Unis,Exis,[X|Vars],Cla2) :-
        member2(X,Unis), !,
        cf_simplify_exi(Cla,Unis,Exis,Vars,Cla2).
cf_simplify_exi(Cla,Unis,Exis,[X|Vars],Cla2) :-
        member2(X,Exis),
        (member2([(Y=Z)],Cla);member2([(Z=Y)],Cla)),
        X==Y,!,
        subv(X,Z,Cla,Cla3),
        cf_simplify_exi(Cla3,Unis,Exis,Vars,Cla2).
cf_simplify_exi(Cla,Unis,Exis,[_X|Vars],Cla2) :-
        cf_simplify_exi(Cla,Unis,Exis,Vars,Cla2).
cf_simplify_exi(Cla,_Unis,_Exis,[],Cla).

cf_remove_subsumed(Clauses1,Clauses2) :-
        findall(Clause2,(member(Clause1,Clauses1),
                         member(Clause2,Clauses1),
                         Clause1 \= Clause2,
                         subset2(Clause1,Clause2)),
                SubsumedClauses),
        subtract(Clauses1,SubsumedClauses,Clauses2).

cf_simplify_variant_clauses([Cla|Clauses],Unis,Clauses2) :-
        member2(Cla2,Clauses),
        variant_clause(Cla,Cla2,Unis),!,
        cf_simplify_variant_clauses(Clauses,Unis,Clauses2).
cf_simplify_variant_clauses([Cla|Clauses],Unis,[Cla|Clauses2]) :-
        cf_simplify_variant_clauses(Clauses,Unis,Clauses2).
cf_simplify_variant_clauses([],_Unis,[]).

variant_clause(Clause1,Clause2,Unis) :-
        term_variables(Clause1,Var1),
        term_variables(Clause2,Var2),
        subset2(Var1,Unis), % only universally qu.
        subset2(Var2,Unis), % vars
        variant(Clause1,Clause2).

cf_remove_subsumed_variants(Clauses1,Unis,Exis,Vars,Clauses2) :-
        cf_remove_subsumed_variants2(Clauses1,Unis,Exis,Vars,Clauses2,[]).

cf_remove_subsumed_variants2([Clause|Clauses],Unis,Exis,Vars,Clauses2,SoFar) :-
        find_smallest_subsumer(Clause,Clauses,Unis,Exis,Vars,Smallest,Nonsubsumed),
        cf_remove_subsumed_variants2(Nonsubsumed,Unis,Exis,Vars,Clauses2,[Smallest|SoFar]).
cf_remove_subsumed_variants2([],_Unis,_Exis,_Vars,Clauses2,Clauses2).

find_smallest_subsumer(Clause,Clauses,Unis,Exis,Vars,Smallest,Nonsubsumed) :-
        find_smallest_subsumer2(Clause,Clauses,Unis,Exis,Vars,Smallest,Nonsubsumed,[]).

find_smallest_subsumer2(Clause,[Clause2|Clauses],Unis,Exis,Vars,Smallest,Nonsubsumed,SoFar) :-
        variant_subsumed(Clause,Clause2,Clause3,Unis,Exis,Vars),!,
        find_smallest_subsumer2(Clause3,Clauses,Unis,Exis,Vars,Smallest,Nonsubsumed,SoFar).
find_smallest_subsumer2(Clause,[Clause2|Clauses],Unis,Exis,Vars,Smallest,Nonsubsumed,SoFar) :-
        find_smallest_subsumer2(Clause,Clauses,Unis,Exis,Vars,Smallest,Nonsubsumed,[Clause2|SoFar]).
find_smallest_subsumer2(Clause,[],_Unis,_Exis,_Vars,Clause,Nonsubsumed,Nonsubsumed).


variant_subsumed(Clause1,Clause2,Clause1,Unis,Exis,Vars) :-
        variant_subsumed2(Clause1,Clause2,Unis,Exis,Vars).
variant_subsumed(Clause1,Clause2,Clause2,Unis,Exis,Vars) :-
        variant_subsumed2(Clause2,Clause1,Unis,Exis,Vars).
        
% Clause1 is a subset of a variant of Clause 2
variant_subsumed2(Clause1,Clause2,Unis,Exis,Vars) :-
        % they must not share variables
        term_variables(Clause1,V1),
        term_variables(Clause2,V2),
        disjoint2(V1,V2),
        % determine a subset of clause2
        variant_subsumed3(Clause1,Clause2,Clause2Sub),
        term_variables(Clause2Sub,V2S),
        % determine which vars are universal and which existential
        intersection2(V1,Unis,Unis1),
        intersection2(V2S,Unis,Unis2),
        intersection2(V1,Exis,Exis1),
        intersection2(V2S,Exis,Exis2),
        % determine their quantification order as in Vars
        intersection2(V1,Vars,Vars1),
        intersection2(V2S,Vars,Vars2),
        variant((Clause1,Unis1,Exis1,Vars1),(Clause2Sub,Unis2,Exis2,Vars2)).
        

% nondeterministically choose a subset of Clause 2
% as a candidate for subsumption
% non-variant literals can be excluded a priori
variant_subsumed3([Lit|Lits],[Lit2|Lits2],[Lit2|Lits3]) :-
        variant(Lit,Lit2),
        variant_subsumed3(Lits,Lits2,Lits3).
variant_subsumed3([Lit|Lits],[_Lit2|Lits2],Lits3) :-
        variant_subsumed3([Lit|Lits],Lits2,Lits3).
variant_subsumed3([],Lits2,Lits2).

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
%% 
%% elim([Pred|Preds],Phi1,Phi2) :-
%%         atom(Pred),!,
%%         elim(Preds,Phi1,Phi3),        
%%         cf_nnf(Phi3,Phi4,[],Unis,Exis,Vars,'1',_SkolS2,Skol),
%%         cf_cnf(Phi4,Phi5),
%%         subv(Pred,$true,Phi5,Phi5p),
%%         subv(Pred,$false,Phi5,Phi5n),
%%         cf_cnf((Phi5p|Phi5n),Phi6),
%%         cf_cnf_clauses(Phi6,Cla),
%%         cf_clauses_simplify(Cla,Unis,Exis,Vars,Cla2),
%%         clauses2fml(Phi2,Cla2,Unis,Exis,Vars).
%% elim([],Phi,Phi).

%% entails(Fml1,Fml2,Axioms) :-
%%         term_variables((Fml1,Fml2),[]),
%%         clausalform_dnf(Fml1,Cla1,[],[],[],[]),
%%         clausalform_dnf(Fml2,Cla2,[],[],[],[]),!,
%%         clausal_subsumption_dnf(Cla1,Cla2).

clausal_subsumption_dnf(Clauses,[Clause2|Clauses2]) :-
        member(Clause,Clauses),
        subset2(Clause2,Clause),
        clausal_subsumption_dnf(Clauses,Clauses2).
clausal_subsumption_dnf(Clauses,[Clause2]) :-
        member(Clause,Clauses),
        subset2(Clause2,Clause).

