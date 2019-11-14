:- module(eprover, [entails/2,
                    inconsistent/1,
                    consistent/1,
                    valid/1,
                    equivalent/2,
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
:- use_module('../lib/utils').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Interface to E Theorem Prover
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* Succeeds if ListOfAxioms entails Conjecture. */
entails(ListOfAxioms,Conjecture) :-
        entails_eprover(ListOfAxioms,Conjecture).

/* Succeeds if ListOfFormulas is inconsistent. */
inconsistent(ListOfFormulas) :-
        entails(ListOfFormulas, false).

/* Succeeds if ListOfFormulas is consistent. */
consistent(ListOfFormulas) :-
        not(inconsistent(ListOfFormulas)).

/* Succeeds if Formula is valid. */
valid(Formula) :-
        entails([true],Formula).

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
                        stderr(null),
                        process(PID)]),   % need PID for exit status
        process_wait(PID, Status), !,     % wait for completion
        check_eprover_status(Status).     % return value

entails_eprover(_ListOfAxioms,_Conjecture) :-
        report_message(['Failed while attempting to use E theorem prover!']),
        report_message(['Aborting...']),
        report_message(['Check your settings! (PATH_GOLOG variable set?)']),
        abort.
        
% eprover's return status determines the truth value:
% 0 =    proof found = Conjecture derivable     => succeed
% 1 = no proof found = Conjecture not derivable => fail
% other exit statutes (e.g. 3 = parse error)    => abort execution
check_eprover_status(exit(0)) :- !.
check_eprover_status(exit(1)) :- !,
        fail.
check_eprover_status(exit(S)) :- !,
        temp_file(File),
        report_message(['Unexpected eprover return status (', S,
                        ')!']),
        report_message(['Aborting...']),
        report_message(['Check ', File, '.']),
        abort.        

temp_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/tptp.p', File).

writeToFile(ListOfAxioms, Conjecture, FileName) :-
        open(FileName, write, Stream),
        writeTimeStamp(Stream),
        writeAxioms(Stream, ListOfAxioms, 0),
        writeConjecture(Stream, Conjecture, conjecture),
	close(Stream).

writeTimeStamp(Stream) :-
        local_time_and_date_as_string(TimeS),
        atom_string(TimeA,TimeS),
        write(Stream, '% Automatically generated TPTP problem file\n'),
        write(Stream, '% '),
        write(Stream, TimeA),
        write(Stream, '\n\n').

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
        is_list(V), V \= [], !,
        write(Stream, '?'),
        write(Stream, V),
        write(Stream, ':'),
        write_formula(Stream, F).
write_formula(Stream, some(V,F)) :-
        var(V), !,
        write_formula(Stream, some([V],F)).
write_formula(Stream, some([],F)) :- !,
        write_formula(Stream, F).
write_formula(Stream, all(V,F)) :-
        is_list(V), V \= [], !,
        write(Stream, '!'),
        write(Stream, V),
        write(Stream, ':'),
        write_formula(Stream, F).
write_formula(Stream, all(V,F)) :-
        var(V), !,
        write_formula(Stream, all([V],F)).
write_formula(Stream, all([],F)) :- !,
        write_formula(Stream, F).
write_formula(Stream, true) :-
        write(Stream, '$true').
write_formula(Stream, false) :-
        write(Stream, '$false').
write_formula(Stream, F) :-
        writeq(Stream, F). % use (single) quotes where necessary

write_binary_formula(Stream, F1, Symbol, F2) :-
        write(Stream, '( '),
        write_formula(Stream, F1),
        write(Stream, ' '),
        write(Stream, Symbol),
        write(Stream, ' '),
        write_formula(Stream, F2),
        write(Stream, ' )').
