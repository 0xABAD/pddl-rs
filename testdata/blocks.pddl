;; Simple pddl file for testing and benchmarking.

(define (domain blocksworld)
(:requirements :strips :equality) ;; simple requirements;
(:predicates (clear ?x)
             (on-table ?x)
             (arm-empty)
             (holding ?x)
             (on ?x ?y))

(:action pickup ;; a block from the table
  :parameters (?ob)
  :precondition (and (clear ?ob) (on-table ?ob) (arm-empty))
  :effect (and (holding ?ob) (not (clear ?ob)) (not (on-table ?ob)) 
               (not (arm-empty))))

(:action putdown ;; a block onto the table
  :parameters  (?ob)
  :precondition (and (holding ?ob))
  :effect (and (clear ?ob) (arm-empty) (on-table ?ob) 
               (not (holding ?ob))))

(:action stack ;; a block onto another block
  :parameters  (?ob ?underob)
  ;; :precondition (and  (clear ?underob) (holding ?ob) (not (= ?ob ?underob)) )
  :precondition (and  (clear ?underob) (holding ?ob))
  :effect (and (arm-empty) (clear ?ob) (on ?ob ?underob)
               (not (clear ?underob)) (not (holding ?ob))))

(:action unstack ;; a block from another block
  :parameters  (?ob ?underob)
  :precondition (and (on ?ob ?underob) (clear ?ob) (arm-empty))
  :effect (and (holding ?ob) (clear ?underob)
               (not (on ?ob ?underob)) (not (clear ?ob)) (not (arm-empty)))))
