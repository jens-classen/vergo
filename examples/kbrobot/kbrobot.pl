
stdname(X) :- member(X,[book,room6213,robot,cup]).

prim_action(lookFor(_)).

fun_fluent(location(_)).

%initially(location(book)=room6213).
%initially(location(cup)=kitchen).

poss(lookFor(_),true).

sensing_style(object).
include_preconditions.

senses(lookFor(X),Y,(location(X)=Y)).

causes(lookFor(XP),location(X),Y,(X=robot)*(location(XP)=Y)).

program(control,
        while(-some(X,know(X=location(book))),
              lookFor(book)
             )
       ).
