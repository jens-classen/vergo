(define (domain DeonticRobot)

    (:requirements :adl)

    (:types room door physob aspect)

    (:constants robot)

    (:predicates (is_open ?d - door)
                 (in ?r - room ?o - object)
                 (connects ?d - door ?r1 ?r2 - room)
    )

    (:action push_through
        :parameters (?o - physob ?d - door ?from ?to - room)
        :precondition (and (in ?from ?o)
                           (in ?from robot)
                           (connects ?d ?from ?to)
                           (is_open ?d)
                      )
        :effect (and
            (in ?to ?o)
            (in ?to robot)
            (not (in ?from ?o))
            (not (in ?from robot))
            )
    )

    (:action go_through
        :parameters (?d - door ?from ?to - room)
        :precondition (and (in ?from robot)
                           (connects ?d ?from ?to)
                           (is_open ?d)
                      )
        :effect (and
            (in ?to robot)
            (not (in ?from robot))
            )
    )

    (:action open
        :parameters (?d - door ?a - aspect)
        :precondition (and (not (is_open ?d))
                           (exists (?r1 ?r2 - room)
                                   (and (in ?r1 robot)
				        (connects ?d ?r1 ?r2)
				   )
                           )
		      )
        :effect (is_open ?d)
    )

    (:action close
        :parameters (?d - door ?a - aspect)
        :precondition (and (is_open ?d)
                           (exists (?r1 ?r2 - room)
                                   (and (in ?r1 robot)
				        (connects ?d ?r1 ?r2)
				   )
                           )
		      )
        :effect (not (is_open ?d))
    )

)
