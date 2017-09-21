#lang syndicate/actor

(require racket/list)
(require (only-in racket/set list->set set->list))
(require (only-in racket/random random-ref random-sample))
(require (only-in racket/sequence sequence-length))

(module+ test (require rackunit))

;; let's assume that there are two players.

;; a Card is a (card Nat Nat) where the first Nat is the value/rank of the card
;; and the second Nat is the amount of "bulls"
(struct card (rank bulls) #:transparent)

;; a PlayerId is a Symbol
;; for now, either 'player-1 or 'player-2
(define player-1 'player-1)
(define player-2 'player-2)

;; a Hand is a (Listof Card)

;; a Deck is a (Listof Card)

;; a Score is a Nat

;; a Scores is a (Hashof PlayerId Score)
;; a Scores must contain an entry for each existing PlayerId (i.e. it is safe
;; to use hash-update with a Scores)

;; a Row is a (row (Listof Card)) where the length of the list of cards is in [1,5]
;; kinda think rows should be stored in reverse
(struct row (cards) #:transparent)

;; a Rows is a (Listof Row) of length four.

;; a InHand is (in-hand PlayerId Card)
(struct in-hand (player card) #:transparent)

;; a Round is a (round Nat) the Nat is between 1 and 10
(struct round (number) #:transparent)

;; a Move is (plays PlayerId Nat Card)
(struct plays (player round card) #:transparent)

;; a GamePlayer is a function (Setof Card) Rows -> Card
;; that picks out a card to play based on a current state of the rows.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The Deck

;; Deck -> (Values Card Deck)
;; Remove the first card from the deck
(define (draw-one deck)
  (match deck
    ['() (error "tried to draw from empty deck")]
    [(cons c cs) (values c cs)]))

;; Nat Deck -> (Values (Listof Card) Deck)
;; Remove cards from a deck
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Protocol

;; the dealer asserts (in-hand PlayerId (Listof Card)) for each player
;; the dealer asserts Rows representing the current state of the game
;; the dealer asserts (round Nat) to start each round
;; to play a card during round n, each player asserts a Move with the current
;; round number

;; Invariants
;;
;; 1) No Takesies-Backsies: Once a player makes a move in a round, by asserting
;; (plays PlayerId Round Nat Card), that player never asserts a different card
;; for that round.
;; (plays pid r c1) && (plays pid r c2) ==> c1 == c2
;; or maybe
;; (plays pid r c1) ==> (always (plays pid r c2) ==> c1 == c2)
;; ^ this doesn't say that the player has to maintain the move assertion. Or in
;; other words, is it ok for a player to retract a move once they've made it,
;; say when the next round begins? This protocol doesn't say.
;;
;; 2) No Spying On Other Players Hands
;; Each player can only listen to (in-hand pid card) for their own pid
;;
;; 3) No Watching Other Players' Moves
;; Players do not subscribe to (plays _ _ _)
;;
;; 4) Players Only Play Cards Actually In Their Hand
;; (plays pid r c) ==> (in-hand pid c)
;; Note this is only true momentarily. Once the dealer processes the round,
;; the in-hand assertion goes away (maybe it should stay around. then the player
;; keeps track of what card they play, and we add a new invariant that a player
;; doesn't play a card multiple times).
;;
;; 5) No Impersonation
;; Player actors only make assertions with their own PlayerId

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The Dealer

;; for N players could do:
#|
(field [moves '()])
(for ([pid player-ids])
  (react (on (asserted (plays pid (current-round) $c))
             (moves (cons (plays pid (current-round) c) (moves)))
             (stop (current-facet-id)
                   (when (= (sequence-length player-ids) (length moves))
                     ;; have all the moves, play some cards!
                     #f)))))
|#

;; Deck -> Dealer
(define (spawn-dealer deck)
  (let*-values ([(p1-start-hand deck) (draw 10 deck)]
                [(p2-start-hand deck) (draw 10 deck)]
                [(r1-start deck) (draw-one deck)]
                [(r2-start deck) (draw-one deck)]
                [(r3-start deck) (draw-one deck)]
                ;; not a typo
                [(r4-start decky) (draw-one deck)])
    (spawn
     #:name 'dealer
     (field (deck decky)
            (scores (hash
                     player-1 0
                     player-2 0))
            (p1-hand p1-start-hand)
            (p2-hand p2-start-hand)
            (rows (list (row (list r1-start))
                        (row (list r2-start))
                        (row (list r3-start))
                        (row (list r4-start)))))
     (log-rows (rows))
     ;; -> Card
     (define (draw-card!)
       (define-values (c d) (draw-one (deck)))
       (deck d)
       c)
     (assert (in-hand player-1 (p1-hand)))
     (assert (in-hand player-2 (p2-hand)))
     (for ([r (in-list (rows))])
       (assert r))
     (field (current-round 1))
     (assert (round (current-round)))
     (on (asserted (plays player-1 (current-round) $p1-c))
         (unless (member p1-c (p1-hand))
           (error (format "~v tried to play card ~v not in their hand: ~v" player-1 p1-c (p1-hand))))
         (react
          (on (asserted (plays player-2 (current-round) $p2-c))
              (unless (member p2-c (p2-hand))
                (error (format "~v tried to play card ~v not in their hand: ~v" player-2 p2-c (p2-hand))))
              (define moves (list (plays player-1 (current-round) p1-c)
                                  (plays player-2 (current-round) p2-c)))
              ;; TODO: log in a separate actor
              (log-move (first moves))
              (log-move (second moves))
              (define-values (new-rows new-scores)
                (play-round (rows) moves (scores)))
              (log-rows new-rows)
              (rows new-rows)
              (scores new-scores)
              (p1-hand (remove p1-c (p1-hand)))
              (p2-hand (remove p2-c (p2-hand)))
              (unless (= (current-round) 10)
                (current-round (add1 (current-round))))
              (stop-current-facet)
              #;(when (= (current-round) 11)
                ;; hmmmmmmm not right
                (stop-current-facet))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The Rules of the Game

;; Rows (Listof Move) Scores -> (Values Rows Scores)
(define (play-round rows moves scores)
  (define ordered-moves
    (sort moves
          <
          #:key (compose card-rank plays-card)))
  (for/fold ([rows rows]
             [scores scores])
            ([m (in-list ordered-moves)])
    (match-define (plays pid _ c ) m)
    ;; this is not very helpful for logging.
    (define-values (new-rows bulls) (play-card c rows))
    (values new-rows (add-bulls-to-score scores pid bulls))))

;; Card (Listof Row) -> (Values (Listof Row) Score)
;; Add the card to the end of a row, or start a new row with the card, following
;; the rules of the game. Returns the updated rows of the game as well as the
;; number of bulls on the cards that the player picked up, if any.
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
                (row-bulls the-row))]
       [else
        ;; add card to the end of the row
        (define next-row (add-card-to-row c the-row))
        (values (cons next-row other-rows) 0)])]
    [else
     ;; player picks up row. The player's card is the beginning of a new row
     (values (cons (row (list c)) other-rows)
             (row-bulls the-row))]))

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
    (let-values ([(new-rows bulls) (play-card (card 18 1) rows)])
      (check-equal? bulls (row-bulls (second rows)))
      (check-equal? (list->set new-rows)
                    (list->set (replace-row (second rows)
                                            (row (list (card 18 1)))
                                            rows))))
    ;; 98 should go at the end of a row with 5 cards, resulting in the player
    ;; picking up the row and 98 being the start of a new row
    (let-values ([(new-rows bulls) (play-card (card 98 1) rows)])
      (check-equal? bulls (row-bulls (third rows)))
      (check-equal? (list->set new-rows)
                    (list->set (replace-row (third rows)
                                            (row (list (card 98 1)))
                                            rows))))
    ;; the rest of these should pick out a row for the card to go at the end
    (let-values ([(new-rows bulls) (play-card (card 32 1) rows)])
      (check-equal? bulls 0)
      (check-equal? (list->set new-rows)
                    (list->set (replace-row (first rows)
                                            (add-card-to-row (card 32 1) (first rows))
                                            rows))))
    (let-values ([(new-rows bulls) (play-card (card 34 1) rows)])
      (check-equal? bulls 0)
      (check-equal? (list->set new-rows)
                    (list->set (replace-row (second rows)
                                            (add-card-to-row (card 34 1) (second rows))
                                            rows))))
    (let-values ([(new-rows bulls) (play-card (card 75 1) rows)])
      (check-equal? bulls 0)
      (check-equal? (list->set new-rows)
                    (list->set (replace-row (second rows)
                                            (add-card-to-row (card 75 1) (second rows))
                                            rows))))
    (let-values ([(new-rows bulls) (play-card (card 104 1) rows)])
      (check-equal? bulls 0)
      (check-equal? (list->set new-rows)
                    (list->set (replace-row (fourth rows)
                                            (add-card-to-row (card 104 1) (fourth rows))
                                            rows))))))

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
  (hash-update scores pid + bulls))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Player Agents, AI

;; it seems like there's a race s.t. the player sees the start of a round
;; before their hand updates.

;; PlayerId GamePlayer -> PlayerAgent
(define (spawn-player pid make-decision)
  (spawn
   #:name pid
   (define/query-value my-hand '() (in-hand pid $c) c)
   (define/query-set the-rows (row $r) (row r))
   (on (asserted (round $n))
       (let ([c (make-decision (my-hand) (set->list (the-rows)))])
         (log-player-decision pid c (my-hand))
         (assert! (plays pid n c))))))

;; PlayerAgent
;; randomly pick a card in the hand
(define (random-player hand rows)
  (random-ref hand))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Logging

(define the-topic 'take-5)

(define-logger take-5)

;; Move -> Void
(define (log-move m)
  (match-define (plays pid r c) m)
  (log-take-5-debug "player ~a plays card ~v in round ~v" pid c r))

;; Rows -> Void
(define (log-rows rows)
  (log-take-5-debug "The current rows are:\n\t~v\n\t~v\n\t~v\n\t~v"
                    (first rows) (second rows) (third rows) (fourth rows)))

(define (log-player-decision pid c hand)
  (log-take-5-debug "~a chooses card ~v from hand ~v" pid c hand))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Testing

(spawn-dealer (shuffle the-deck))
(spawn-player player-1 random-player)
(spawn-player player-2 random-player)