:- module(fol, [entails/2,
                inconsistent/1,
                consistent/1,
                consistent/2,
                equivalent/2,
                simplify/2,
                simplify_max/2,
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

/* simplify_max(+F,-R)
   apply simplify(F,R) until nothing changes anymore */
simplify_max(F,R) :-
        simplify(F,R1),
        R1 \= F, !,
        simplify_max(R1,R).
simplify_max(F,F) :-
        simplify(F,F).

/* simplify(+F,-R)
   simplify formula F to obtain R
   makes 'obvious' simplifications like F&$true => F */
simplify(true,true) :- !.
simplify(false,false) :- !.
simplify(F1<=>F2,true) :- 
        simplify(F1, F),
        simplify(F2, F), !.
simplify(F1<=>F2,false) :-
        simplify(F1,true),
        simplify(F2,false), !.
simplify(F1<=>F2,false) :-
        simplify(F1,false),
        simplify(F2,true), !.
simplify(F1<=>F2,R1<=>R2) :- !,
        simplify(F1,R1),
        simplify(F2,R2).
simplify(_F1=>F2,true) :- 
        simplify(F2,true), !.
simplify(F1=>_F2,true) :- 
        simplify(F1,false), !.
simplify(F1=>F2,R1=>R2) :- !,
        simplify(F1,R1),
        simplify(F2,R2).
simplify(F2<=_F1,true) :- 
        simplify(F2,true), !.
simplify(_F2<=F1,true) :- 
        simplify(F1,false), !.
simplify(F2<=F1,R2<=R1) :- !,
        simplify(F1,R1),
        simplify(F2,R2).
simplify(F1+F2,R) :-
        simplify(F1,R),
        simplify(F2,R), !.
simplify(-F1+F2,true) :-
        simplify(F1,R1),
        simplify(F2,R2),
        R1=R2, !.
simplify(F1+(-F2),$true) :-
        simplify(F1,R1),
        simplify(F2,R2),
        R1=R2, !.
simplify(F1+F2,R) :-
        simplify(F1,false),
        simplify(F2,R), !.
simplify(F1+F2,R) :-
        simplify(F2,false),
        simplify(F1,R), !.
simplify(F1+_F2,true) :-
        simplify(F1,true), !.
simplify(_F1+F2,true) :-
        simplify(F2,true), !.
simplify(F1+F2,R1+R2) :-
        simplify(F1,R1),
        simplify(F2,R2), !.
simplify(F1*F2,R) :-
        simplify(F1,R),
        simplify(F2,R), !.
simplify(-F1*F2,false) :-
        simplify(F1,R1),
        simplify(F2,R2),
        R1=R2, !.
simplify(F1*(-F2),false) :-
        simplify(F1,R1),
        simplify(F2,R2),
        R1=R2, !.
simplify(F1*F2,R) :-
        simplify(F1,true),
        simplify(F2,R), !.
simplify(F1*F2,R) :-
        simplify(F2,true),
        simplify(F1,R), !.
simplify(F1*_F2,false) :-
        simplify(F1,false), !.
simplify(_F1*F2,false) :-
        simplify(F2,false), !.
simplify(F1*F2,R1*R2) :-
        simplify(F1,R1),
        simplify(F2,R2), !.
simplify(-F, false) :- 
        simplify(F,true), !.
simplify(-F, true) :- 
        simplify(F,false), !.
simplify(-(-F),R) :- !,
        simplify(F,R).
simplify(-F,-R) :-
        simplify(F,R), !.
simplify(some(Xs,F1),some(Xs,R1)) :- !,
        simplify(F1,R1).
simplify(all(Xs,F1),all(Xs,R1)) :- !,
        simplify(F1,R1).
simplify(X=Y,true) :- 
        X==Y, !.
simplify(F,F).

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
