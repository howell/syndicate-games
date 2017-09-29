#lang racket

(provide
 ;; a Card is a (card Nat Nat) where the first Nat is the value/rank of the card
 ;; and the second Nat is the amount of "bulls"
 (struct-out card)

 ;; type Deck     = (Listof Card)
 ;; Deck 
 the-deck

 ;; Nat Deck -> (Values (Listof Card) Deck)
 ;; Remove cards from a deck
 draw
   
 ;; Deck -> (Values Card Deck)
 ;; Remove the first card from the deck
 draw-one)

;; -----------------------------------------------------------------------------
(require (only-in racket/random random-ref random-sample))

;; -----------------------------------------------------------------------------
(struct card (rank bulls) #:transparent)
  
(define (draw-one deck)
  (match deck
    ['() (error "tried to draw from empty deck")]
    [(cons c cs) (values c cs)]))
  
(define (draw n deck)
  (cond
    [(zero? n) (values '() deck)]
    [else
     (define-values (c new-deck) (draw-one deck))
     (define-values (cs new-new-deck) (draw (sub1 n) new-deck))
     (values (cons c cs) new-new-deck)]))

(define the-deck
  (for/list ([i (in-range 1 105)])
    (define bulls
      (cond
        [(= i 55) 7]
        [(= (modulo i 10) 0) 3]
        [(= (modulo i 5) 0) 2]
        [(member i '(11 22 33 44 66 77 88 99)) 5]
        [else 1]))
    (card i bulls)))

;; (Listof A) -> (Listof A)
(define (shuffle deck)
  (define-values (shuffled _)
    (for/fold ([shuffled-cards '()]
               [deck deck])
              ([_ (in-list deck)])
      (define pick-one (random-ref deck))
      (values (cons pick-one shuffled-cards)
              (remove pick-one deck))))
  shuffled)