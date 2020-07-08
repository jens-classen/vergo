:- module(vampire, [entails/2,
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
% Interface to Vampire Theorem Prover
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/* Succeeds if ListOfAxioms entails Conjecture. */
entails(ListOfAxioms,Conjecture) :-
        vampire(ListOfAxioms,Conjecture,Result), !,
        Result = refutation.

/* Succeeds if ListOfFormulas is inconsistent. */
inconsistent(ListOfFormulas) :-
        entails(ListOfFormulas, false).

/* Succeeds if ListOfFormulas is consistent. */
consistent(ListOfFormulas) :-
        not(inconsistent(ListOfFormulas)). % TODO: use SAT
                                           % functionality here?

/* Succeeds if Formula is valid. */
valid(Formula) :-
        entails([true],Formula).

/* Succeeds if Formula1 and Formula2 are equivalent. */
equivalent(Formula1,Formula2) :-
        entails([Formula1],Formula2),
        entails([Formula2],Formula1).

/* Calls Vampire on ListOfAxioms and Conjecture. */
vampire(ListOfAxioms,Conjecture,Result) :-
        temp_file(File),
        writeTPTPFile(ListOfAxioms,Conjecture,File),
        process_create(path('vampire'), 
                       [File],                % input file
                       [stdout(pipe(Output)), % pipe to parse result
                        stderr(pipe(Output)),
                        process(PID)]),       % need PID for exit status
        process_wait(PID, _Status), !,        % wait for completion
        read_string(Output,"","",_,String),
        close(Output),
        get_vampire_result(String,Result).    % return value

vampire(_ListOfAxioms,_Conjecture,_Result) :-
        report_message(['Failed while attempting to use Vampire theorem prover!']),
        report_message(['Aborting...']),
        report_message(['Check your settings! (PATH_GOLOG variable set?)']),
        abort.

get_vampire_result(String, refutation) :-
        sub_string(String,_,_,_N,"Refutation found."), !.
get_vampire_result(String, satisfiable) :-
        sub_string(String,_,_,_N,"Satisfiable!"), !.
get_fo2_solver_result(String,_) :- !,
        temp_file(File),
        report_message(['Unexpected Vampire output:']),
        report_message(['Aborting...']),
        report_message([String]),
        report_message(['Check ', File, '.']),
        abort.

temp_file(File) :-
        temp_dir(TempDir),
        string_concat(TempDir, '/tptp.p', File).
