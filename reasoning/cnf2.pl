:- module(transform).

:- use_module(tptp).

:- lib(lists).

:- export clausal_form/6.
:- export clauses2fml/5.
:- export simplify_formula2/2.
:- export equivalent/2.
:- export equivalent/3.
:- export entails/3.
:- export elim/3.

:- export intersection2/3.
:- export subset2/2.



:- dynamic equivalent_cached/3.
:- dynamic nonequiv_cached/3.

:- get_flag(output_options,Old),
   set_flag(output_options,[variables(full)|Old]).

% todo: deal with unused variables!

% todo: unique variables!!!
clausal_form(Fml,Cla,Unis,Exis,Vars,Skol) :-
        cf_nnf(Fml,Fml1,[],Unis,Exis,Vars,'skol1',_SkolS2,Skol),
        cf_cnf(Fml1,Fml2),
        cf_cnf_clauses(Fml2,Cla1),
        cf_clauses_simplify(Cla1,Unis,Exis,Vars,Cla).

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

clauses2fml(Fml,Cla,Unis,Exis,Vars) :-
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

% subset2(+,+)
subset2([X|Xs],Ys) :-
        member2(X,Ys),
        subset2(Xs,Ys).
subset2([],_Ys).

intersection2([X|Xs],Ys,[X|Zs]) :-
        member2(X,Ys), !,
        intersection2(Xs,Ys,Zs).
intersection2([_|Xs],Ys,Zs) :-
        intersection2(Xs,Ys,Zs).
intersection2([],_,[]).

disjoint2([X|Xs],Ys) :-
        not(member2(X,Ys)),
        disjoint2(Xs,Ys).
disjoint2([],_Ys).

member2(X,[Y|_L]) :- X == Y.
member2(X,[_|L]) :- member2(X,L).
member2(_,[]) :- fail.



%% % generate new variables for deskolemization
%% make_fresh_variables(Unis,[Skol|Skols],[X|NewVars]) :-
%%         make_fresh_variables(Unis,Skols,NewVars),
%%         copy_term((Unis,NewVars,X2),(_Unis2,_NewVars2,X)).
%% make_fresh_variables(_Unis,[],[]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simplify_formula2(Fml,Fml2) :-
        clausal_form(Fml,Cla,U,E,V,_S),
        clauses2fml(Fml2,Cla,U,E,V).


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

entails(Fml1,Fml2,Axioms) :-
        write_problem_file(Fml2,[Fml1|Axioms],'conjecture.tptp'),
        exec(["./E/bin/eprover", "--tptp3-in", "-s",
              "conjecture.tptp", "-o", "output.tptp"],[]),
        %sh("rm conjecture.tptp"),
        sh("mv conjecture.tptp conjecture_old.tptp"),
        open('output.tptp',read,result),
        read_string(result,end_of_line,_L1,_FirstLine),
        read_string(result,end_of_line,_L2,SecondLine),
        close(result),
        sh("rm output.tptp"),
        SecondLine == "# Proof found!".
        

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



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% do Action for each Goal
forall(Goal,Action):-
        Goal,
	(Action
	->	fail
	;	!,fail).
forall(_,_).

               /*  T2 is T1 with X1 replaced by X2  */
subv(X1,X2,T1,T2) :- var(T1), T1 == X1, !, T2 = X2.
subv(_,_,T1,T2)   :- var(T1), !, T2 = T1.
subv(X1,X2,T1,T2) :- T1 == X1, !, T2 = X2.
subv(X1,X2,T1,T2) :- T1 =..[F|L1], subvl(X1,X2,L1,L2), T2 =..[F|L2].

subvl(_,_,[],[]).
subvl(X1,X2,[T1|L1],[T2|L2]) :- subv(X1,X2,T1,T2), subvl(X1,X2,L1,L2).

