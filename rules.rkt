#lang racket

(provide
 (struct-out row)
 ;; Row = (row (Listof Card)) where the length of the list of cards is in [1,5]
 ;; SAM: kinda think rows should be stored in reverse
 ;; Rows = (Listof Row) of length four. ;; MF: why not use a vector here? 

 (struct-out played-in-round)
 ;; Move = (played-in-round PlayerId Nat Card)

 ;; Rows (Listof Move) Scores -> (Values Rows Score)
 play-round

 ;; Scores -> (NonemptyListof PlayerId)
 ;; determine the winner(s) of a game, which is the player, or players in case of
 ;; a tie.

 lowest-score/s)

;; ---------------------------------------------------------------------------------------------------
(require "deck.rkt")
(module+ test (require rackunit))

;; ---------------------------------------------------------------------------------------------------
(struct row (cards) #:transparent)
  
(struct played-in-round (player round card) #:transparent)

(define (play-round rows moves scores)
  (define ordered-moves
    (sort moves
          <
          #:key (compose card-rank played-in-round-card)))
  (for/fold ([rows rows]
             [scores scores])
            ([m (in-list ordered-moves)])
    (match-define (played-in-round pid _ c ) m)
    ;; this is not very helpful for logging.
    (define-values (new-rows bulls row?) (play-card c rows))
    ;; MF: this looks a bit like a cyclic dependency 
    #;
    (when row? (log-row-pickup pid row?))
    (values new-rows (add-bulls-to-score scores pid bulls))))

;; Card (Listof Row) -> (Values (Listof Row) Score (Optionof Row))
;; Add the card to the end of a row, or start a new row with the card, following
;; the rules of the game. Returns the updated rows of the game, the number of
;; bulls on the cards that the player picked up (or 0 if they didn't pick any up),
;; as well as the row of cards that the player picked up (or #f if they didn't).
(define (play-card c rows)
  (define the-row (row-for-card c rows))
  (define other-rows (remove the-row rows))
  (define last-card (last-card-in-row the-row))
  (cond
    [(< (card-rank last-card) (card-rank c))
     ;; card belongs at the end of the row
     (cond
       [(= (row-length the-row) 5)
        ;; player picks up row. The player's card is the beginning of a new row
        (values (cons (row (list c)) other-rows)
                (row-bulls the-row)
                the-row)]
       [else
        ;; add card to the end of the row
        (define next-row (add-card-to-row c the-row))
        (values (cons next-row other-rows) 0 #f)])]
    [else
     ;; player picks up row. The player's card is the beginning of a new row
     (values (cons (row (list c)) other-rows)
             (row-bulls the-row)
             the-row)]))

;; Row Row Rows -> Rows
(define (replace-row old-row new-row rows)
  (cons new-row (remove old-row rows)))

(module+ test
  (let ()
    (define rows
      ;; the "bulls" are just made up and are certainly not in accordance with
      ;; the actual cards
      (list (row (list (card 12 3) (card 28 2)))
            (row (list (card 33 3)))
            (row (list (card 4 3) (card 19 5) (card 52 1) (card 80 1) (card 95 2)))
            (row (list (card 73 3) (card 82 1) (card 100 2)))))
    ;; 18 doesn't go at the end of the row, so give back the row with the lowest
    ;; number of bulls
    (let-values ([(new-rows bulls row?) (play-card (card 18 1) rows)])
      (check-equal? bulls (row-bulls (second rows)))
      (check-equal? (list->set new-rows)
                    (list->set (replace-row (second rows)
                                            (row (list (card 18 1)))
                                            rows)))
      (check-equal? row? (second rows)))
    ;; 98 should go at the end of a row with 5 cards, resulting in the player
    ;; picking up the row and 98 being the start of a new row
    (let-values ([(new-rows bulls row?) (play-card (card 98 1) rows)])
      (check-equal? bulls (row-bulls (third rows)))
      (check-equal? (list->set new-rows)
                    (list->set (replace-row (third rows)
                                            (row (list (card 98 1)))
                                            rows)))
      (check-equal? row? (third rows)))
    ;; the rest of these should pick out a row for the card to go at the end
    (let-values ([(new-rows bulls row?) (play-card (card 32 1) rows)])
      (check-equal? bulls 0)
      (check-equal? (list->set new-rows)
                    (list->set (replace-row (first rows)
                                            (add-card-to-row (card 32 1) (first rows))
                                            rows)))
      (check-false row?))
    (let-values ([(new-rows bulls row?) (play-card (card 34 1) rows)])
      (check-equal? bulls 0)
      (check-equal? (list->set new-rows)
                    (list->set (replace-row (second rows)
                                            (add-card-to-row (card 34 1) (second rows))
                                            rows)))
      (check-false row?))
    (let-values ([(new-rows bulls row?) (play-card (card 75 1) rows)])
      (check-equal? bulls 0)
      (check-equal? (list->set new-rows)
                    (list->set (replace-row (second rows)
                                            (add-card-to-row (card 75 1) (second rows))
                                            rows)))
      (check-false row?))
    (let-values ([(new-rows bulls row?) (play-card (card 104 1) rows)])
      (check-equal? bulls 0)
      (check-equal? (list->set new-rows)
                    (list->set (replace-row (fourth rows)
                                            (add-card-to-row (card 104 1) (fourth rows))
                                            rows)))
      (check-false row?))))

;; Card (NonemptyListof Row) -> Row
;; determine which row a card belongs to
;; Quoting from the rulebook (http://www.world-of-board-games.com.sg/docs/6-Nimmt.pdf)
;; Rule No. 1: “Ascending order”
;; The number of the card that is added to a row must be
;; higher than the number of the current last card in that row.
;; Rule No. 2: “Small difference”
;; A card must always be added to the row with the smallest
;; possible difference between the current last card and the
;; new one.
;;
;; if neither rule 1 nor rule 2 applies, return the row with the smallest number
;; of bulls
(define (row-for-card c rows)
  (define candidate?
    (for/fold ([candidate #f])
              ([r (in-list rows)])
      (define last-card (last-card-in-row r))
      (cond
        [(and (> (card-rank c) (card-rank last-card))
              (or (not candidate)
                  (> (card-rank last-card) (card-rank (last-card-in-row candidate)))))
         r]
        [else candidate])))
  (or candidate?
      (argmin row-bulls rows)))

;; Row -> Nat
;; Sum the bulls of each card in a row
(define (row-bulls r)
  (for/sum ([c (in-list (row-cards r))])
    (card-bulls c)))

;; Row -> Nat
;; the number of cards in a row
(define (row-length r)
  (length (row-cards r)))

(module+ test
  (let ()
    (define rows
      ;; the "bulls" are just made up and are certainly not in accordance with
      ;; the actual cards
      (list (row (list (card 12 3) (card 28 2)))
            (row (list (card 33 3)))
            (row (list (card 4 3) (card 19 5) (card 52 1) (card 80 1)))
            (row (list (card 73 3) (card 82 1) (card 100 2)))))
    ;; 18 doesn't go at the end of the row, so give back the row with the lowest
    ;; number of bulls
    (check-equal? (row-for-card (card 18 1) rows)
                  (row (list (card 33 3))))
    ;; the rest of these should pick out a row for the card to go at the end
    (check-equal? (row-for-card (card 32 1) rows)
                  (row (list (card 12 3) (card 28 2))))
    (check-equal? (row-for-card (card 34 1) rows)
                  (row (list (card 33 3))))
    (check-equal? (row-for-card (card 75 1) rows)
                  (row (list (card 33 3))))
    (check-equal? (row-for-card (card 90 1) rows)
                  (row (list (card 4 3) (card 19 5) (card 52 1) (card 80 1))))
    (check-equal? (row-for-card (card 104 1) rows)
                  (row (list (card 73 3) (card 82 1) (card 100 2))))))

;; Row -> Card
;; determine the last card in a row
(define (last-card-in-row r)
  (last (row-cards r)))

;; Card Row -> Row
(define (add-card-to-row c r)
  (row (append (row-cards r) (list c))))

;; Scores PlayerId Score -> Scores
(define (add-bulls-to-score scores pid bulls)
  (hash-update scores pid (lambda (old-bulls) (+ old-bulls bulls))))

(define (lowest-score/s scores)
  (define min-score
    (apply min (hash-values scores)))
  (for/list ([(pid score) (in-hash scores)]
             #:when (= min-score score))
    pid))