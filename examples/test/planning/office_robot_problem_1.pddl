; Automatically generated PDDL file
; 2020-08-12 02:56:04 PM

(define (problem p1)
(:domain DeonticRobot)
(:objects
	office - room
	supplies - room
	closet - room
	door_a - door
	door_b - door
	box_1 - physob
	box_2 - physob
)
(:init
	(in office robot)
	(in supplies box_1)
	(in closet box_2)
	(connects door_a office supplies)
	(connects door_a supplies office)
	(connects door_b supplies closet)
	(connects door_b closet supplies)
;	(= (total-cost) 0)
)
(:goal
	(in office box_2)
)
;(:metric
;	minimize (total-cost)
;)
)
