
rel_rigid(teach(_,_)).

initially(teach(tom, sam)).
initially(teach(tina, sue) * (teach(tom, sue) + teach(ted, sue))).
initially(some(X,teach(X, sara))).
initially(all(X,(teach(X, sandy) <=> (X=ted)))).
initially(all([X,Y],(teach(X, Y) => ((Y=sam) + (Y=sue) + (Y=sara) + (Y= sandy))))).

stdname(X) :- member(X, [tom,tina,ted,sam,sue,sara,sandy]).
