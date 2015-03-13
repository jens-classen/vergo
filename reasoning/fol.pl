:- module(fol, [entails/2,
                inconsistent/1,
                consistent/1,
                consistent/2,
                equivalent/2,
                simplify/2,
                disjoin/2,
                conjoin/2,
                op(1130, xfy, <=>),
                op(1110, xfy, <=),
                op(1110, xfy, =>)]).

/* We use the following symbols for writing formulas:

   true
   false

    *  conjunction
    +  disjunction
    -  negation
   <=> equivalence
    => implication
   <=  implication
    
    =  equality

   some(Variable,Formula) existential quantification
   all(Variable,Formula)  universal quantification

   Variables have to be (uppercase) Prolog variables. */


% % TPTP FOF operator definitions from Jens Otten's LeanCoP
% /* Operator definitions for TPTP syntax. */
:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op(1110, xfy, <=).  % implication
% :- op( 500, fy, ~).    % negation
% :- op( 500,xfy, :).

% :- op(1100, xfy, '|').  % disjunction
% :- op(1000, xfy, &).    % conjunction
% :- op( 500, fy, !).     % universal quantifier
% :- op( 500, fy, ?).     % existential quantifier
% :- op( 400, xfx, =).    % equality
% :- op( 299, fx, $).     % for $true/$false

:- use_module('../lib/env').

:- discontiguous(simplify/2).

/* Succeeds if ListOfAxioms entails Conjecture. */
entails(ListOfAxioms,Conjecture) :-
        entails_eprover(ListOfAxioms,Conjecture).

/* Succeeds if ListOfFormulas is inconsistent. */
inconsistent(ListOfFormulas) :-
        entails(ListOfFormulas, false).

/* Succeeds if ListOfFormulas is consistent. */
consistent(ListOfFormulas) :-
        not(inconsistent(ListOfFormulas)).

/* Succeeds if union of ListOfFormulas1 and ListOfFormulas2 is consistent. */
consistent(ListOfFormulas1, ListOfFormulas2) :-
        append(ListOfFormulas1, ListOfFormulas2, ListOfFormulas),
        consistent(ListOfFormulas).

/* Succeeds if Formula1 and Formula2 are equivlanet. */
equivalent(Formula1,Formula2) :-
        entails([Formula1],Formula2),
        entails([Formula2],Formula1).

/* Succeeds if ListOfAxioms entails Conjecture. Uses the E prover. */
entails_eprover(ListOfAxioms,Conjecture) :-
        temp_file(File),
        writeToFile(ListOfAxioms, Conjecture, File),
        process_create(path('eprover'), 
                       ['--auto',         % use prover as black box
                        '--tptp3-format', % use latest TPTP format
                        '--silent',       % almost no output
                        File],            % input file
                       [stdout(null),     % completely silent
                        process(PID)]),   % need PID for exit status
        process_wait(PID, Status), !,     % wait for completion
        Status=exit(0).                   % return value
        % eprover's return status determines the truth value:
        % 0 =    proof found = Conjecture derivable
        % 1 = no proof found = Conjecture not derivable

        % shell('rm temp.p'). % leave this for debugging
        % TODO: catch other exit statutes (3 = parse error)

temp_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/tptp.p', File).

writeToFile(ListOfAxioms, Conjecture, FileName) :-
        open(FileName, write, Stream),
        writeAxioms(Stream, ListOfAxioms, 0),
        writeConjecture(Stream, Conjecture, conjecture),
	close(Stream).

/* writeAxioms(+Stream, +ListOfAxioms, +N)
   Writes ListOfAxioms to Stream in TPTP syntax, naming
   axioms axiomN, axiom(N+1), axiom(N+2), ... */
writeAxioms(Stream, [], _) :-
        write(Stream, '\n').
writeAxioms(Stream, [Formula|Formulas], N) :-
        write(Stream, 'fof(axiom'),
        write(Stream, N),
        write(Stream, ', axiom, '),
        write_formula(Stream, Formula),
        write(Stream, ').\n'),
        N1 is N+1,
        writeAxioms(Stream, Formulas, N1).

writeConjecture(Stream, Conjecture, Name) :-
        write(Stream, 'fof('),
        write(Stream, Name),
        write(Stream, ', conjecture, '),
        write_formula(Stream, Conjecture),
        write(Stream, ').\n').
        
write_formula(Stream, F1<=>F2) :-
        write_binary_formula(Stream, F1, '<=>', F2).
write_formula(Stream, F1=>F2) :-
        write_binary_formula(Stream, F1, '=>', F2).
write_formula(Stream, F1<=F2) :-
        write_binary_formula(Stream, F1, '<=', F2).
write_formula(Stream, F1*F2) :-
        write_binary_formula(Stream, F1, '&', F2).
write_formula(Stream, F1+F2) :-
        write_binary_formula(Stream, F1, '|', F2).
write_formula(Stream, -F) :-
        write(Stream, '~( '),
        write_formula(Stream, F),
        write(Stream, ' )').
write_formula(Stream, some(V,F)) :-
        is_list(V), !,
        write(Stream, '?'),
        write(Stream, V),
        write(Stream, ':'),
        write_formula(Stream, F).
write_formula(Stream, some(V,F)) :-
        write_formula(Stream, some([V],F)).
write_formula(Stream, all(V,F)) :-
        is_list(V), !,
        write(Stream, '!'),
        write(Stream, V),
        write(Stream, ':'),
        write_formula(Stream, F).
write_formula(Stream, all(V,F)) :-
        write_formula(Stream, all([V],F)).
write_formula(Stream, true) :-
        write(Stream, '$true').
write_formula(Stream, false) :-
        write(Stream, '$false').
write_formula(Stream, F) :-
        write(Stream, F).

write_binary_formula(Stream, F1, Symbol, F2) :-
        write(Stream, '( '),
        write_formula(Stream, F1),
        write(Stream, ' '),
        write(Stream, Symbol),
        write(Stream, ' '),
        write_formula(Stream, F2),
        write(Stream, ' )').

/* simplify(+F,-R)
   simplify formula F to obtain R
   makes 'obvious' simplifications like F&$true => F */

% true, false
simplify(true,true) :- !.
simplify(false,false) :- !.

% equivalence
simplify(F1<=>F2,R) :- 
        simplify(F1,FS1),
        simplify(F2,FS2), !,
        simplify_equiv(FS1,FS2,R).

simplify_equiv(true,false,false) :- !.
simplify_equiv(false,true,false) :- !.
simplify_equiv(F1,F2,true) :-
        F1 == F2, !.
simplify_equiv(F1,F2,F1<=>F2).
             
% implication
simplify(F1=>F2,R) :-
        simplify(F1,FS1),
        simplify(F2,FS2), !,
        simplify_impl(FS1,FS2,R).

simplify_impl(_,true,true) :- !.
simplify_impl(false,_,true) :- !.
simplify_impl(F1,F2,true) :-
        F1 == F2, !.
simplify_impl(F1,F2,F1=>F2).

simplify(F1<=F2,R) :- !,
        simplify(F2=>F1,R).

% disjunction
simplify(F1+F2,R) :-
        simplify(F1,FS1),
        simplify(F2,FS2), !,
        simplify_disj(FS1,FS2,R).

simplify_disj(true,_,true) :- !.
simplify_disj(_,true,true) :- !.
simplify_disj(false,F2,F2) :- !.
simplify_disj(F1,false,F1) :- !.
simplify_disj(-F1,F2,true) :-
        F1 == F2, !.
simplify_disj(F1,-F2,true) :-
        F1 == F2, !.
simplify_disj(F1,F2,R) :-
        F1 == F2, !, R=F1.
simplify_disj(F1,F2,F1+F2).

%conjunction
simplify(F1*F2,R) :-
        simplify(F1,FS1),
        simplify(F2,FS2), !,
        simplify_conj(FS1,FS2,R).

simplify_conj(false,_,false) :- !.
simplify_conj(_,false,false) :- !.
simplify_conj(true,F2,F2) :- !.
simplify_conj(F1,true,F1) :- !.
simplify_conj(-F1,F2,false) :-
        F1 == F2, !.
simplify_conj(F1,-F2,false) :-
        F1 == F2, !.
simplify_conj(F1,F2,R) :-
        F1 == F2, !, R=F1.
simplify_conj(F1,F2,F1*F2).

%negation
simplify(-F,R) :-
        simplify(F,FS), !,
        simplify_neg(FS,R).

simplify_neg(true,false) :- !.
simplify_neg(false,true) :- !.
simplify_neg(-F,F) :- !.
simplify_neg(F,-F).

% quantification
simplify(some(Xs,F1),R) :- !,
        simplify(F1,R1),
        simplify_some(Xs,R1,R).
simplify(all(Xs,F1),R) :- !,
        simplify(F1,R1),
        simplify_all(Xs,R1,R).

simplify_some(_Xs,false,false) :- !.
simplify_some(_Xs,true,true) :- !.
simplify_some(Xs,F,some(Xs,F)).

simplify_all(_Xs,false,false) :- !.
simplify_all(_Xs,true,true) :- !.
simplify_all(Xs,F,all(Xs,F)).

% equality
simplify(X=Y,true) :- 
        X==Y, !.

% base case.
simplify(F,FS) :-
        var(FS), !, FS=F.
simplify(F,FS) :-
        F == FS.

/* conjoin(+L,-F)
   F is the conjunction of the list of formulas L */
conjoin([F],F).
conjoin([F1,F2|Fs],F1*FR) :-
        conjoin([F2|Fs],FR).
conjoin([],true).

/* disjoin(+L,-F)
   F is the disjunction of the list of formulas L */
disjoin([F],F).
disjoin([F1,F2|Fs],F1+FR) :-
        disjoin([F2|Fs],FR).
disjoin([],false).
