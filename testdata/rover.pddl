(define (domain rover)
  (:requirements :strips :typing :fluents)
  (:types data location)

  (:predicates
   (comm ?d - data)
   (have ?d - data)
   (at ?x - location)
   (avail ?d - data ?x - location)
   ) ;; end :predicates

  (:functions
   (power)
   (effort ?x ?y - location)
   (effort-data ?d - data)
   ) ;; end :functions

  ) ;; end (domain rover)
