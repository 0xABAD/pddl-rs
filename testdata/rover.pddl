(define (domain rover)
  (:requirements :strips :typing :fluents :negative-preconditions)
  (:types data location)

  (:constants
   a_crater b_crater c_crater - location
   isotope hev-lab - data)

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
   (effort ?x ?y - location)
   (effort ?d - data)
   ) ;; end :functions

  (:action commun
    :parameters (?d - data)
    :precondition (and
                   (have ?d)
                   (analyzed ?d)
                   (>= (power) 5)))

  (:action drive
    :parameters (?d - data ?x ?y - location)
    :precondition (and
                   (at ?x)
                   (not (sampled ?d))
                   (avail ?d ?y)
                   (>= (power) (effort ?x ?y))))

  (:action sample
    :parameters (?d - data ?x - location)
    :precondition (and
                   (at ?x)
                   (avail ?d ?x)
                   (>= (power) (effort ?d))))

  (:action analyze
    :parameters (?d - data)
    :precondition (and (have ?d)
                       (sampled ?d)))

  (:action recharge
    :parameters ()
    :precondition (and (<= (power) 10)))

) ;; end (domain rover)
