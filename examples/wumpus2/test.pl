% a simple example sequence for the regression agent on 3x3 grid
test :-
        init,
        execute(move('#e'),false),
        execute(senseBreeze,true),
        execute(move('#w'),false),
        execute(move('#n'),false),
        execute(senseBreeze,false),
        ask(pit('#room-3-1'),true),
        ask(pit('#room-2-2'),false),
        ask(pit('#room-1-3'),false).