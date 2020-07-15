:- module(utils, 
          [subv/4,
           subvl/4,
           report_message/1,
           count/2,
           atom_string/2,
           string_codes/2,
           subset2/2,
           union2/3,
           intersection2/3,
           setminus2/3,
           disjoint2/2,
           member2/2,
           nth2/3,
           write_readable/2,
           write_readable/1,
           measure_time_with_limit/4,
           append_to_csv/2,
           local_time_and_date_as_string/1]).

:- use_module(library(csv)).

/*  T2 is T1 with X1 replaced by X2  */
subv(X1,X2,T1,T2) :- var(T1), T1 == X1, !, T2 = X2.
subv(_,_,T1,T2)   :- var(T1), !, T2 = T1.
subv(X1,X2,T1,T2) :- T1 == X1, !, T2 = X2.
subv(X1,X2,T1,T2) :- T1 =..[F|L1], subvl(X1,X2,L1,L2), T2 =..[F|L2].

subvl(_,_,[],[]) :- !.
subvl(X1,X2,[T1|L1],[T2|L2]) :- !, subv(X1,X2,T1,T2), subvl(X1,X2,L1,L2).

/* Print a mesage */
report_message([L|Ls]) :- !, write(L), report_message(Ls).
report_message([]) :- !, write('\n').
report_message(M) :- report_message([M]).

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

nth2(X,[Y|_L],N) :-
        X == Y,
        N = 0.
nth2(X,[_|L],N) :-
        nth2(X,L,N1),
        N is N1+1.
nth2(_,[]) :-
        fail.

% write Term to Stream using readable variables 
% (A,B,C,... instead of _G201,_G202,...)
write_readable(Stream, Term) :-
        \+ \+ ( numbervars(Term, 0, _),
                write_term(Stream, Term,
                           [ numbervars(true),
                             quoted(true)
                           ])
              ).

% write Term using readable variables 
% (A,B,C,... instead of _G201,_G202,...)
write_readable(Term) :-
        \+ \+ ( numbervars(Term, 0, _),
                write_term(Term,
                           [ numbervars(true),
                             quoted(true)
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
