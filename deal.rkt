#lang syndicate/actor

(provide
 ;; (Setof PlayerId) (Listof Card) -> (Values (Hashof PlayerId (Listof Card)) (Listof Card))
 ;; Deal each player 10 cards, recording the association in a hash and giving
 ;; back the deck with the dealt cards removed
 deal)

;; ---------------------------------------------------------------------------------------------------
(require racket/set)
(require "deck.rkt")
(module+ test (require rackunit))

;; ---------------------------------------------------------------------------------------------------
(define (deal all-player-ids deck)
  (for/fold ([hands (hash)]
             [deck deck])
            ([pid (in-set all-player-ids)])
    (define-values (hand decky) (draw 10 deck))
    (values (hash-set hands pid hand) decky)))

(module+ test
  (let ()
    (define-values (hands rest-of-deck)
      (deal (set 'p1 'p2 'p3) the-deck))
    ;; each player has a hand, nothing else in the hash
    (check-equal? (hash-count hands) 3)
    (check-true (hash-has-key? hands 'p1))
    (check-true (hash-has-key? hands 'p2))
    (check-true (hash-has-key? hands 'p3))
    ;; each player has 10 cards
    (check-equal? (length (hash-ref hands 'p1)) 10)
    (check-equal? (length (hash-ref hands 'p2)) 10)
    (check-equal? (length (hash-ref hands 'p3)) 10)
    ;; 30 cards removed from the deck
    (check-equal? (length rest-of-deck) (- (length the-deck) 30))))
