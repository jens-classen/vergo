:- module(env, 
          [main_dir/1,
           temp_dir/1]).

main_dir(Path) :- 
        getenv('PATH_GOLOG', Path).

temp_dir(Path) :- 
        main_dir(Main),
        string_concat(Main, '/temp', Path).
