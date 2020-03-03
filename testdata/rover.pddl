(define (domain rover)
  (:requirements :strips :typing :fluents)
  (:types data location)

  (:constants
   a_crater b_crater c_crater - location
   isotope hev-lab - data)

  (:predicates
   (comm ?d - data)
   (have ?d - data)
   (at ?x - location)
   (avail ?d - data ?x - location)
   ) ;; end :predicates

  (:functions
   (power)
   (effort ?x ?y - location)
   (effort ?d - data)
   ) ;; end :functions

) ;; end (domain rover)
