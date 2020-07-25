:- module(eprover, [entails/2,
                    inconsistent/1,
                    consistent/1,
                    valid/1,
                    equivalent/2]).

:- use_module('tptp').
:- use_module('../logic/fol', [op(1130, xfy, <=>),
                               op(1110, xfy, <=),
                               op(1110, xfy, =>)]).
:- use_module('../lib/env').
:- use_module('../lib/utils').

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Interface to E Theorem Prover
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* Succeeds if ListOfAxioms entails Conjecture. */
entails(ListOfAxioms,Conjecture) :-
        eprover(ListOfAxioms,Conjecture).

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

/* Calls E prover on ListOfAxioms and Conjecture. */
eprover(ListOfAxioms,Conjecture) :-
        temp_file(File),
        writeTPTPFile(ListOfAxioms, Conjecture, File),
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

eprover(_ListOfAxioms,_Conjecture) :-
        report_message(error,['Failed while attempting to use E theorem prover!']),
        report_message(error,['Aborting...']),
        report_message(error,['Check your settings! (PATH_GOLOG variable set?)']),
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
        report_message(error,['Unexpected eprover return status (',S,')!']),
        report_message(error,['Aborting...']),
        report_message(error,['Check ', File, '.']),
        abort.        

temp_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/tptp.p', File).
