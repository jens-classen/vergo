:- module(clausalform, [clauses2cnf/2,
                        clauses2dnf/2,
                        fml2pinf/2,
                        fml2prime_implicates/2
                        ]).

:- use_module('../reasoning/fol').
:- use_module('../lib/utils').

:- dynamic(clause_n/2).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Clausal form conversions, CNF, DNF
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% fml2nnf(+Fml1,-Fml2,+FreeV,-Unis,-Exis,-AllVars,+SkolS1,-SkolS2,-Skol):
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
%    -> Skol is the set of skolem term substitions (Var,SkolemTerm)
%       introduced during conversion 

fml2nnf((F1<=>F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf((-F1+F2)*(F1+(F2)),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
fml2nnf((F1=>F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf((-F1+F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
fml2nnf((F1<=F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf((F1+(-F2)),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
fml2nnf((F1*F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf(F1,Fml1,FreeV,Unis1,Exis1,AllVars1,SkolS1,SkolS3,Skol1),
        fml2nnf(F2,Fml2,FreeV,Unis2,Exis2,AllVars2,SkolS3,SkolS2,Skol2),
        append(Unis1,Unis2,Unis),
        append(Exis1,Exis2,Exis),
        append(AllVars1,AllVars2,AllVars),
        append(Skol1,Skol2,Skol),
        Fml=(Fml1*Fml2).
fml2nnf((F1+F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf(F1,Fml1,FreeV,Unis1,Exis1,AllVars1,SkolS1,SkolS3,Skol1),
        fml2nnf(F2,Fml2,FreeV,Unis2,Exis2,AllVars2,SkolS3,SkolS2,Skol2),
        append(Unis1,Unis2,Unis),
        append(Exis1,Exis2,Exis),
        append(AllVars1,AllVars2,AllVars),
        append(Skol1,Skol2,Skol),
        Fml=(Fml1+Fml2).
fml2nnf(all(Vars,F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        append(Vars,FreeV,FreeV1),
        fml2nnf(F,Fml,FreeV1,Unis1,Exis,AllVars1,SkolS1,SkolS2,Skol),
        append(Vars,Unis1,Unis),
        append(Vars,AllVars1,AllVars).
fml2nnf(some([Var|Vars],F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,[(Var,NewSymbol)|Skol1]) :- !,
        NewSymbol =.. [SkolS1|FreeV],
        skol_next(SkolS1,SkolS3),
        fml2nnf(some(Vars,F),Fml2,FreeV,Unis,Exis1,AllVars1,SkolS3,SkolS2,Skol1),
        subv(Var,NewSymbol,Fml2,Fml),
        Exis=[Var|Exis1],
        AllVars=[Var|AllVars1].
fml2nnf(some([],F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf(F,Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
        
fml2nnf(-(-F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf(F,Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
fml2nnf(-(F1<=>F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf((F1+F2)*(-F1+(-F2)),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
fml2nnf(-(F1=>F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf((F1*(-F2)),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
fml2nnf(-(F1<=F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf((-F1*F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
fml2nnf(-(F1*F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf((-F1+(-F2)),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
fml2nnf(-(F1+F2),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf(((-F1)*(-F2)),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
fml2nnf(-all(Vars,F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf(some(Vars,-F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).
fml2nnf(-some(Vars,F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol) :- !,
        fml2nnf(all(Vars,-F),Fml,FreeV,Unis,Exis,AllVars,SkolS1,SkolS2,Skol).

fml2nnf(Lit,Lit,_FreeV,[],[],[],SkolS,SkolS,[]).

% propositional case
fml2nnf(Fml1,Fml2) :- !,
        fml2nnf(Fml1,Fml2,[],[],[],[],skol1,_,_).

% skolem symbols are 'skol1','skol2','skol3',...
skol_atom(skol).
skol_first(SkolOne) :-
        skol_atom(Skol),
        atom_number(One,1),
        atom_concat(Skol,One,SkolOne).
skol_next(A1,A2) :-
        skol_atom(Skol),
        atom_concat(Skol,S1,A1),
        atom_number(S1,N1),
        N2 is N1+1,
        atom_number(S2,N2),
        atom_concat(Skol,S2,A2).

% convert NNF into CNF by distributing disjunctions over conjunctions
nnf2cnf((F1*F2)+F3,(Fml1*Fml2)) :- !,
        nnf2cnf((F1|F3),Fml1),
        nnf2cnf((F2|F3),Fml2).
nnf2cnf(F1+(F2*F3),(Fml1*Fml2)) :- !,
        nnf2cnf((F1|F2),Fml1),
        nnf2cnf((F1|F3),Fml2).
nnf2cnf((F1+F2),Fml) :- !,
        nnf2cnf(F1,Fml1),
        nnf2cnf(F2,Fml2),
        ( (Fml1=(_A1*_B1);Fml2=(_A2*_B2)) -> nnf2cnf((Fml1+Fml2),Fml); Fml=(Fml1+Fml2)).
nnf2cnf((F1*F2),(Fml1*Fml2)) :- !,
        nnf2cnf(F1,Fml1),
        nnf2cnf(F2,Fml2).
nnf2cnf(Lit,Lit).

% convert NNF into DNF by distributing conjunctions over disjunctions
nnf2dnf((F1+F2)*F3,(Fml1+Fml2)) :- !,
        nnf2dnf((F1*F3),Fml1),
        nnf2dnf((F2*F3),Fml2).
nnf2dnf(F1*(F2+F3),(Fml1+Fml2)) :- !,
        nnf2dnf((F1*F2),Fml1),
        nnf2dnf((F1*F3),Fml2).
nnf2dnf((F1*F2),Fml) :- !,
        nnf2dnf(F1,Fml1),
        nnf2dnf(F2,Fml2),
        ( (Fml1=(_A1+_B1);Fml2=(_A2+_B2)) -> nnf2dnf((Fml1*Fml2),Fml); Fml=(Fml1*Fml2)).
nnf2dnf((F1+F2),(Fml1+Fml2)) :- !,
        nnf2dnf(F1,Fml1),
        nnf2dnf(F2,Fml2).
nnf2dnf(Lit,Lit).

% convert CNF formula in clause set
cnf2clauses(F1*F2,Clauses) :- !,
        cnf2clauses(F1,Clauses1),
        cnf2clauses(F2,Clauses2),
        append(Clauses1,Clauses2,Clauses).
cnf2clauses(F1+F2,[Clause]) :- !,
        cnf2clauses(F1,[Clause1]),
        cnf2clauses(F2,[Clause2]),
        append(Clause1,Clause2,Clause).
cnf2clauses(true,[]).
cnf2clauses(false,[[]]).
cnf2clauses(Lit,[[Lit]]).

% convert DNF formula in clause set
dnf2clauses(F1+F2,Clauses) :- !,
        dnf2clauses(F1,Clauses1),
        dnf2clauses(F2,Clauses2),
        append(Clauses1,Clauses2,Clauses).
dnf2clauses(F1*F2,[Clause]) :- !,
        dnf2clauses(F1,[Clause1]),
        dnf2clauses(F2,[Clause2]),
        append(Clause1,Clause2,Clause).
dnf2clauses(false,[]).
dnf2clauses(true,[[]]).
dnf2clauses(Lit,[[Lit]]).

% convert clause set to CNF formula
clauses2cnf(Cla,Unis,Exis,Vars,Skols,Fml) :-
        clauses2cnf(Cla,CNF),
        attach_quantifiers(CNF,Unis,Exis,Vars,Skols,Fml2),
        flatten_quantifiers(Fml2,Fml).

clauses2cnf([Clause],Fml) :- !,
        clause2disjunction(Clause,Fml).
clauses2cnf([Clause|Clauses],(Fml1*Fml2)) :- !,
        clause2disjunction(Clause,Fml1),
        clauses2cnf(Clauses,Fml2).
clauses2cnf([],true).

clause2disjunction([Lit],Lit) :- !.
clause2disjunction([Lit|Lits],(Lit+Fml)) :- !,
        clause2disjunction(Lits,Fml).
clause2disjunction([],false).

% convert clause set to DNF formula
clauses2dnf(Cla,Unis,Exis,Vars,Skols,Fml) :-
        clauses2dnf(Cla,DNF),
        attach_quantifiers(DNF,Unis,Exis,Vars,Skols,Fml2),
        flatten_quantifiers(Fml2,Fml).

clauses2dnf([Clause],Fml) :- !,
        clause2conjunction(Clause,Fml).
clauses2dnf([Clause|Clauses],(Fml1+Fml2)) :- !,
        clause2conjunction(Clause,Fml1),
        clauses2dnf(Clauses,Fml2).
clauses2dnf([],false).

clause2conjunction([Lit],Lit) :- !.
clause2conjunction([Lit|Lits],(Lit*Fml)) :- !,
        clause2conjunction(Lits,Fml).
clause2conjunction([],true).

% reattach quantifiers in prenex form
attach_quantifiers(CNF,Unis,Exis,[X|Vars],Skols,Fml) :-
        member2(X,Unis),!,
        attach_quantifiers(CNF,Unis,Exis,Vars,Skols,Fml1),
        Fml=all([X],Fml1).
attach_quantifiers(CNF,Unis,Exis,[X|Vars],Skols,Fml) :-
        member2(X,Exis),!,
        get_skolem_term(X,Skols,Skol),
        attach_quantifiers(CNF,Unis,Exis,Vars,Skols,Fml1),
        subv(Skol,X,Fml1,Fml2),
        Fml=some([X],Fml2).
attach_quantifiers(CNF,_Unis,_Exis,[],_Skols,CNF).

% flatten nested quantifiers using list notation
flatten_quantifiers(all(Vars1,all(Vars2,Fml)),Result) :- !,
        append(Vars1,Vars2,Vars),
        flatten_quantifiers(all(Vars,Fml),Result).
flatten_quantifiers(some(Vars1,some(Vars2,Fml)),Result) :- !,
        append(Vars1,Vars2,Vars),
        flatten_quantifiers(some(Vars,Fml),Result).
flatten_quantifiers(some(Vars1, all(Vars2,Fml)),some(Vars1,Result)) :- !,
        flatten_quantifiers(all(Vars2,Fml),Result).
flatten_quantifiers(all(Vars1,some(Vars2,Fml)),all(Vars1,Result)) :- !,
        flatten_quantifiers(some(Vars2,Fml),Result).
flatten_quantifiers(Fml,Fml).

get_skolem_term(X,[(Y,Skol)|_],Skol) :-
        X == Y, !.
get_skolem_term(X,[(_,_)|Skols],Skol) :-
        get_skolem_term(X,Skols,Skol).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Prime implicate compiler
% ------------------------
% Adapted from Reiter's prime implicate compiler for open-world 
% Golog, see chapter 10 of
%     Raymond Reiter, Knowledge in Action: 
%     Logical Foundations for Specifying and Implementing Dynamical
%     Systems. MIT Press, 2001.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fml2pinf(Fml1,Fml2) :- !,
        fml2prime_implicates(Fml1,PrimeImplicates),
        clauses2cnf(PrimeImplicates,Fml2).

fml2prime_implicates(Fml1,PrimeImplicates) :- !,
        fml2nnf(Fml1,Fml3),
        nnf2cnf(Fml3,Fml4),
        cnf2clauses(Fml4,Clauses),
        clauses2prime_implicates(Clauses,PrimeImplicates).
        
clauses2prime_implicates(Clauses,PrimeImplicates) :-
        assertClauses(Clauses,0),
        resolveAllClauses(0),
        retractClauses(PrimeImplicates).

assertClauses([],_N).
assertClauses([Clause|Clauses],N) :-
        assertClause(Clause,N),
        assertClauses(Clauses,N).
assertClause(Clause,_N) :- 
        clause_tautology(Clause), !.
assertClause(Clause,_N) :-
        clause_subsumed(Clause), !.
assertClause(Clause,N) :-
        retractSubsumedClauses(Clause),
        assert(clause_n(Clause,N)).

retractSubsumedClauses(Clause) :-
        clause_n(Clause2,N),
        clause_subsumes(Clause,Clause2),
        retract(clause_n(Clause2,N)),
        fail.
retractSubsumedClauses(_Clause).

clause_subsumes(Clause1,Clause2) :-
        subset2(Clause1,Clause2).

clause_subsumed([Lit]) :- 
        clause_n([Lit],_N).
clause_subsumed([Lit1,Lit2|Lits]) :-
        clause_n(Clause2,_N),
        clause_subsumes(Clause2,[Lit1,Lit2|Lits]).

clause_tautology([true]).
clause_tautology([Lit1,Lit2|Lits]) :-
        member(L,[Lit1,Lit2|Lits]),
        L \= -_,
        member(-L,[Lit1,Lit2|Lits]).

resolveAllClauses(N) :-
        resolveAllClausesUnit(N),
        resolveAllClausesNonUnit(N).
resolveAllClauses(N) :-
        N1 is N+1,
        clause_n(_Clause,N1), !,
        resolveAllClauses(N1).
resolveAllClauses(_N).

resolveAllClausesUnit(N) :- 
        N1 is N+1, 
        (clause_n([Lit],N), 
         clause_n(Clause,_J);
         clause_n([Lit],J),
         J < N, 
         clause_n(Clause,N)),
        unitResolvent([Lit],Clause,Result),
        retractSubsumedClauses(Result),
        assert(clause_n(Result,N1)), 
        fail.
resolveAllClausesUnit(_N).

unitResolvent([Lit],Clause,Result) :- 
        complement(Lit,CLit), 
        member(CLit,Clause),
        setminus2(Clause,[CLit],Result).

resolveAllClausesNonUnit(N) :- 
        N1 is N+1,
        clause_n([Lit1,Lit2|Lits1],N),
        clause_n([Lit3,Lit4|Lits2],_J),
        resolvent([Lit1,Lit2|Lits1],[Lit3,Lit4|Lits2],Clause),
        assertClause(Clause,N1),
        fail.

resolvent(Clause1,Clause2,Clause) :-
        member(Lit1,Clause1),
        complement(Lit1,Lit2),
        member(Lit2,Clause2),
        setminus2(Clause1,[Lit1],Clause3),
        setminus2(Clause2,[Lit2],Clause4), 
        union2(Clause3,Clause4,Clause).

complement(A,-A) :- 
        A \= (-_).
complement(-A,A).

retractClauses([Clause|Clauses]) :-
        retract(clause_n(Clause,_N)), !,
        retractClauses(Clauses).
retractClauses([]).

