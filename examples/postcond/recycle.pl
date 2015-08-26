%:- style_check(-singleton).
%:- ensure_loaded(progress).
%:- ensure_loaded(modelGen).
%:- ensure_loaded(gove).
%:- ensure_loaded(sc).

typeList([obj, bin]).

constList([]).

tdomain(obj, [paper1, paper2, paper3, glass1, glass2, nothing]).
tdomain(bin, [bin1, bin2]).

predList([in_bin, in_paper_bin, in_glass_bin, holding, at_bin,
          paper, glass]).
type_info(in_bin, [obj, bin]).
type_info(in_paper_bin, [obj]).
type_info(in_glass_bin, [obj]).
type_info(holding, [obj]).
type_info(at_bin, [bin]).
type_info(paper, [obj]).
type_info(glass, [obj]).

pred(in_bin(X, Y)) :- 
        tdomain(obj, O), member(X, O),
        tdomain(bin, B), member(Y, B).
pred(in_paper_bin(X)) :- 
        tdomain(obj, O), member(X, O).
pred(in_glass_bin(X)) :- 
        tdomain(obj, O), member(X, O).
pred(holding(X)) :-
        tdomain(obj, O), member(X, [nothing|O]).
pred(at_bin(X)) :-
        tdomain(bin, B), member(X, B).
pred(paper(X)) :-
        member(X, [paper1, paper2, paper3]).
pred(glass(X)) :-
        member(X, [glass1, glass2]).


:- assert(init_states([[
     holding(nothing), in_bin(paper1, bin1),
     in_bin(paper2, bin1), in_bin(paper3, bin2),
     in_bin(glass1, bin2), in_bin(glass2, bin2),
     paper(paper1), paper(paper2), paper(paper3),
     glass(glass1), glass(glass2), 
     
     obj(paper1), obj(paper2), obj(paper3),
     obj(glass1), obj(glass2), bin(bin1), bin(bin2)
   ]])).

:- assert(sc([%holding(nothing) => 
    %   all([x], holding(x) => -paper(x) & -glass(x))
%    all([x], -paper(x) v -glass(x))
     all([x,y], in_bin(x,y) => obj(x) & bin(y)),
     all([x], in_paper_bin(x) => obj(x)),
     all([x], in_glass_bin(x) => glass(x)),
     all([x], holding(x) => obj(x)),
     all([x], at_bin(x) => bin(x)),
     all([x], paper(x) => obj(x)),
     all([x], glass(x) => obj(x)),
     all([x], -obj(x) v -bin(x))
   ])).

:- initall.

poss(pick_from_bin(O, B)) <=> 
     at_bin(B) & holding(nothing) & in_bin(O, B).
poss(drop_paper_bin(B)) <=> holding(B).
poss(drop_glass_bin(B)) <=> holding(B).
poss(move_to(B)) <=> true.

sc_proc(
           while(true,
                 pi([[x,obj],[y,bin]], pick_from_bin(x,y)) #
                 pi([[x,obj]], drop_paper_bin(x)) #
                 pi([[y,obj]], drop_glass_bin(x)) #
                 pi([[x,bin]], move_to(x))
                )
       ).

addList(S, pick_from_bin(O, B)) <=> [holding(O)].
delList(S, pick_from_bin(O, B)) <=>
        [holding(nothing), in_bin(O, B)].

addList(S, drop_paper_bin(O)) <=>
        [holding(nothing), in_paper_bin(O)].
delList(S, drop_paper_bin(O)) <=>
        [holding(X)] :- member(holding(X), S).

addList(S, drop_glass_bin(O)) <=>
        [holding(nothing), in_glass_bin(O)].
delList(S, drop_glass_bin(O)) <=>
        [holding(X)] :- member(holding(X), S).

addList(S, move_to(B)) <=> [at_bin(B)].
delList(S, move_to(B)) <=> [at_bin(X)] :- member(at_bin(X), S).
delList(S, move_to(B)) <=> [].

perform(in_bin(O1, B1), pick_from_bin(O2, B2)) <=>
        in_bin(O1, B1) & -(O1~O2 & B1~B2).

perform(in_paper_bin(O1), drop_paper_bin(O2)) <=>
        in_paper_bin(O1) v (O1~O2).

perform(in_glass_bin(O1), drop_glass_bin(O2)) <=>
        in_glass_bin(O1) v (O1~O2).

perform(holding(O1), pick_from_bin(O2, B)) <=> (O1~O2).
perform(holding(nothing), drop_paper_bin(O2)) <=> true.
perform(holding(nothing), drop_glass_bin(O2)) <=> true.

perform(holding(X), drop_paper_bin(O)) <=> X~nothing.
perform(holding(X), drop_glass_bin(O)) <=> X~nothing.

perform(at_bin(B1), move_to(B2)) <=> B1~B2.

test1 :-
        gove(holding(nothing) & 
             all([[x, obj]], 
                 -paper(x) v some([[b,bin]], in_bin(x, b))),
                              
             while(some([[x, obj], [b, bin]], in_bin(x, b)),
                   pi([[xx, obj], [bb, bin]],
                      move_to(bb) :
                      pick_from_bin(xx, bb) :
                      (?(paper(xx)) : drop_paper_bin(xx) #
                       ?(glass(xx)) : drop_glass_bin(xx)
                      )
                     )
                  ),
             holding(nothing)
            ).

test2 :-
        gove(holding(nothing) & 
             all([[x, obj]], 
                 -paper(x) v some([[b,bin]], in_bin(x, b))),
             while(some([[x, obj], [b, bin]], in_bin(x, b)),
                   pi([[xx, obj], [bb, bin]],
                      move_to(bb) :
                      pick_from_bin(xx, bb) :
                      (?(paper(xx)) : drop_paper_bin(xx) #
                       ?(glass(xx)) : drop_glass_bin(xx)
                      )
                     )
                  ),
             all([[o, obj]], -paper(o) v in_paper_bin(o))
            ).