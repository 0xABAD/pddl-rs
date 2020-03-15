(define (domain rover)
  (:requirements
   :strips
   :typing
   :fluents
   :negative-preconditions
   :universal-preconditions)
  (:types data location)

  (:constants
   hev-lab sirelli-crater - location
   isotope - data)

  (:predicates
   (comm ?d - data)
   (have ?d - data)
   (analyzed ?d - data)
   (sampled ?d - data)
   (at ?x - location)
   (avail ?d - data ?x - location)
   ) ;; end :predicates

  (:functions
   (power)
   (temp)
   (effort ?x ?y - location)
   (effort ?d - data)
   ) ;; end :functions

  (:action commun
    :parameters (?d - data)
    :precondition
      (and
        (have ?d)
        (analyzed ?d)
        (not (comm ?d))
        (>= (power) 5))
    :effect
      (and
        (comm ?d)
        (decrease (power) 5)))

  (:action drive
    :parameters (?d - data ?x ?y - location)
    :precondition
      (and
        (at ?x)
        (not (sampled ?d))
        (avail ?d ?y)
        (>= (power) (effort ?x ?y)))
    :effect
      (and
       (not (at ?x))
       (at ?y)
       (decrease (power) (effort ?x ?y))))

  (:action sample
    :parameters (?d - data ?x - location)
    :precondition
      (and
       (at ?x)
       (avail ?d ?x)
       (>= (power) (effort ?d)))
    :effect
      (and
       (decrease (power) (effort ?d))
       (sampled ?d)))

  (:action analyze
    :parameters (?d - data)
    :precondition
      (and
       (have ?d)
       (sampled ?d)
       (>= (power) 2))
    :effect
      (and
       (analyzed ?d)
       (decrease (power) 2)))

  (:action recharge
    :parameters ()
    :precondition (and (<= (power) 10))
    :effect (increase (power) (- 100 (power))))

  (:action return-to-hev-lab
    :parameters (?x - location)
    :precondition
      (and
       (at ?x)
       (forall (?d - data) (comm ?d))
       (>= (power) (effort ?x hev-lab)))
    :effect
      (and
       (not (at ?x))
       (at hev-lab)
       (decrease (power) (effort ?x hev-lab))))

  (:action visit-isotope
    :parameters (?x - location)
    :precondition
      (and
       (avail isotope sirelli-crater)
       (<= (temp) 20)
       (not (at sirelli-crater))
       (>= (power) (effort ?x sirelli-crater)))
    :effect
      (and
       (at sirelli-crater)
       (assign (temp) 100)
       (decrease (power) (effort ?x sirelli-crater))))


) ;; end (domain rover)
