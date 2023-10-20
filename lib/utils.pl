:- module(utils, 
          [subv/4,
           subvl/4,
           report_message/1,
           report_message/2,
           report_message_r/1,
           report_message_r/2,
           get_log_level/1,
           set_log_level/1,
           count/2,
           atom_string/2,
           string_codes/2,
           subset2/2,
           union2/3,
           intersection2/3,
           setminus2/3,
           disjoint2/2,
           member2/2,
           nth02/3,
           write_readable/2,
           write_readable/1,
           measure_time_with_limit/4,
           append_to_csv/2,
           local_time_and_date_as_string/1]).

:- use_module(library(csv)).

:- dynamic current_log_level/1.

/*  T2 is T1 with X1 replaced by X2  */
subv(X1,X2,T1,T2) :- var(T1), T1 == X1, !, T2 = X2.
subv(_,_,T1,T2)   :- var(T1), !, T2 = T1.
subv(X1,X2,T1,T2) :- T1 == X1, !, T2 = X2.
subv(X1,X2,T1,T2) :- T1 =..[F|L1], subvl(X1,X2,L1,L2), T2 =..[F|L2].

subvl(_,_,[],[]) :- !.
subvl(X1,X2,[T1|L1],[T2|L2]) :- !, subv(X1,X2,T1,T2), subvl(X1,X2,L1,L2).

/* Print a message using standard notation for variables */
report_message(ML,M) :- !,
        report_message3(ML,M,false).
report_message(M) :- !, % default log level is info
        report_message3(info,M,false).

/* Print a message using readable notation for variables
   (use write_readable/1 instead of write/1) */
report_message_r(ML,M) :- !,
        report_message3(ML,M,true).
report_message_r(M) :- !, % default log level is info
        report_message3(info,M,true).

% only print if current log level less or equal than message's level
report_message3(ML,M,R) :-
        current_log_level(CL),
        log_level(CL,NC),
        log_level(ML,NM),
        NC =< NM, !,
        report_message2(M,R).
report_message3(_,_) :- !.

% actually print message
report_message2([L|Ls],true) :- !, write_readable2(L,false), report_message2(Ls,true).
report_message2([L|Ls],false) :- !, write(L), report_message2(Ls,false).
report_message2([],_) :- !, write('\n'), flush_output(user_output).
report_message2(M,R) :- report_message2([M],R).

current_log_level(info). % default

log_level(all,0).
log_level(debug,1).
log_level(info,2).
log_level(warn,3).
log_level(error,4).
log_level(off,5).

set_log_level(L) :-
        log_level(L,N),
        N > 0, N < 5, !,
        retractall(current_log_level(_)),
        assert(current_log_level(L)).
get_log_level(L) :-
        current_log_level(L).

/* Count solutions */
count(G, Count) :-
        aggregate_all(count, G, Count).

/* Set operations based on _term_ equality, not unification */
subset2([X|Xs],Ys) :-
        member2(X,Ys),
        subset2(Xs,Ys).
subset2([],_Ys).

union2([X|Xs],Ys,[X|Zs]) :-
        not(member2(X,Ys)), !,
        union2(Xs,Ys,Zs).
union2([_|Xs],Ys,Zs) :-
        union2(Xs,Ys,Zs).
union2([],Ys,Ys).

intersection2([X|Xs],Ys,[X|Zs]) :-
        member2(X,Ys), !,
        intersection2(Xs,Ys,Zs).
intersection2([_|Xs],Ys,Zs) :-
        intersection2(Xs,Ys,Zs).
intersection2([],_,[]).

setminus2([X|Xs],Ys,[X|Zs]) :-
        not(member2(X,Ys)), !,
        setminus2(Xs,Ys,Zs).
setminus2([_X|Xs],Ys,Zs) :-
        setminus2(Xs,Ys,Zs).
setminus2([],_,[]).

disjoint2([X|Xs],Ys) :-
        not(member2(X,Ys)),
        disjoint2(Xs,Ys).
disjoint2([],_Ys).

member2(X,[Y|_L]) :- X == Y.
member2(X,[_|L]) :- member2(X,L).
member2(_,[]) :- fail.

nth02(N,[Y|_L],X) :-
        X == Y,
        N = 0.
nth02(N,[_|L],X) :-
        nth02(N1,L,X),
        N is N1+1.
nth02(_,[],_) :-
        fail.

% write Term to Stream using readable variables 
% (A,B,C,... instead of _G201,_G202,...)
write_readable(Stream, Term) :-
        write_readable2(Stream, Term, true).
write_readable2(Stream, Term, Quoted) :-
        \+ \+ ( numbervars(Term, 0, _),
                write_term(Stream, Term,
                           [ numbervars(true),
                             quoted(Quoted)
                           ])
              ).

% write Term using readable variables 
% (A,B,C,... instead of _G201,_G202,...)
write_readable(Term) :-
        write_readable2(Term, true).
write_readable2(Term, Quoted) :-
        \+ \+ ( numbervars(Term, 0, _),
                write_term(Term,
                           [ numbervars(true),
                             quoted(Quoted)
                           ])
              ).

/**
 * measure_time_with_limit(+Goal,+TimeOut,-ExecutionTime,-CPUTime) is det
 * 
 * Executes Goal with time limit TimeOut and returns the ExecutionTime (wall time) 
 * and CPUTime needed. Should the limit be execeeded, ExecutionTime and CPUTime
 * are unified with 'timeout'. Times are also reported to stdout via 
 * report_message/1.
 **/
measure_time_with_limit(Goal,TimeOut,ExecutionTime,CPUTime) :-
        statistics(walltime, [_TimeSinceStart, _TimeSinceLastCall]),
        statistics(runtime, [_CPUTime1, _CPUTimeSinceLastCall]),
        catch(call_with_time_limit(TimeOut,Goal),
              time_limit_exceeded,
              ReachedTimeOut=true),
        (ReachedTimeOut==true ->
            (CPUTime       = timeout,
             ExecutionTime = timeout,
             report_message(['Goal \'', Goal, '\' reached timeout of ',
                             TimeOut, ' seconds!']));
            (statistics(runtime, [_CPUTime2, CPUTime]),
             statistics(walltime, [_NewTimeSinceStart, ExecutionTime]),
             report_message(['Goal \'', Goal, '\' took ', ExecutionTime,
                             ' ms walltime and ', CPUTime,
                             ' ms CPU time.']))).

/**
 * append_to_csv(+FileName,+Data) is det
 * 
 * Appends the data given in the list Data to a CSV file specified by
 * FileName. Uses standard separator (',').
 **/
append_to_csv(FileName,Data) :-
        Row =.. [row|Data],
        setup_call_cleanup(open(FileName, append, Out),
                           csv_write_stream(Out, [Row], []),
                           close(Out)).

/**
 * local_time_and_date_as_string(+Time) is det
 *
 * Returns the local time and date as a string Time.
 **/
local_time_and_date_as_string(Time) :-
        get_time(X),
        stamp_date_time(X,Y,local),
        format_time(string(Time),'%x %X',Y).
