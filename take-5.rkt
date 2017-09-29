#lang syndicate/actor

(require racket/list)
(require racket/set)
(require (only-in racket/string string-join))
(require (only-in racket/random random-ref random-sample))
(require (only-in racket/sequence sequence-length))

(require "deck.rkt")
(require "rules.rkt")
(require "logging.rkt")
(require "deal.rkt")

(module+ test (require rackunit))

;; ---------------------------------------------------------------------------------------------------
;; PlayerId = Symbol
;; Hand     = (Listof Card)
;; Score    =  Nat
;; Scores   = (Hashof PlayerId Score)
;; Scores must contain an entry for each existing PlayerId (i.e. it is safe to use hash-update)

(struct in-hand (player card) #:transparent)
;; InHand = (in-hand PlayerId Card)

(struct round-has-begun (number) #:transparent)
;; Round = (round-has-begun Nat) the Nat is between 1 and 10

;; a GamePlayer is a function (Setof Card) Rows -> Card
;; that picks out a card to play based on a current state of the rows.

;; ===================================================================================================
;; Protocol

;; the dealer asserts (in-hand PlayerId (Listof Card)) for each player
;; the dealer asserts Rows representing the current state of the game
;; the dealer asserts (round-has-begun Nat) to start each round
;; to play a card during round n, each player asserts a Move with the current
;; round number

;; Invariants
;;
;; 1) No Takesies-Backsies: Once a player makes a move in a round, by asserting
;; (plays PlayerId Round Nat Card), that player never asserts a different card
;; for that round.
;; (plays-in-round pid r c1) && (plays-in-round pid r c2) ==> c1 == c2
;; or maybe
;; (plays-in-round pid r c1) ==> (always (plays-in-round pid r c2) ==> c1 == c2)
;; ^ this doesn't say that the player has to maintain the move assertion. Or in
;; other words, is it ok for a player to retract a move once they've made it,
;; say when the next round begins? This protocol doesn't say.
;;
;; 2) No Spying On Other Players Hands
;; Each player can only listen to (in-hand pid card) for their own pid
;;
;; 3) No Watching Other Players' Moves
;; Players do not subscribe to (plays-in-round _ _ _)
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
;;
;; 6) Timeliness
;; Players play a card in each round
;; (round-has-begun n) ==> (eventually (plays-in-round pid n c))
;; for all players
;;
;; 7) Patience
;; The dealer waits for each player before starting the next round
;; (round-has-begun n) ==>
;;     (round-has-begun (n+1)) ==>
;;         (forall pid. exists c. (plays-in-round pid n c)))
;;
;; 8) Orderly Succession
;; The dealer starts round in the right order (0, 1, 2, 3, 4, ...)
;; Does the number of the round matter? It's not being used for anything. Maybe
;; it should just be "the dealer starts 10 different rounds"

;; ---------------------------------------------------------------------------------------------------
;; The Dealer

;; Deck (Setof PlayerId) -> Dealer
(define (spawn-dealer deck all-player-ids)
  (define num-players (set-count all-player-ids))
  (unless (and (>= num-players 2) (<= num-players 10))
    (error "Take-5 is played with 2-10 players"))
  (define initial-scores (for/hash ([pid (in-set all-player-ids)]) (values pid 0)))
  
  (let*-values ([(initial-hands deck) (deal all-player-ids deck)]
                ;; you really seem to need a draw-four 
                [(r1-start deck) (draw-one deck)]
                [(r2-start deck) (draw-one deck)]
                [(r3-start deck) (draw-one deck)]
                [(r4-start _) (draw-one deck)])
    (spawn #:name 'dealer
           (field (scores initial-scores)
                  (hands initial-hands)
                  (rows (list (row (list r1-start))
                              (row (list r2-start))
                              (row (list r3-start))
                              (row (list r4-start)))))
           (log-rows (rows))
           
           (for ([r (in-list (rows))])
             (assert r))
           ;; possibly need begin/dataflow?
           (for ([(pid hand) (in-hash (hands))])
             (assert (in-hand pid hand)))
           (field (current-round 1))
           (assert (round-has-begun (current-round)))

           (field [moves '()])
           (for ([pid all-player-ids])
             (on (asserted (played-in-round pid (current-round) $c))
                 (define m (played-in-round pid (current-round) c))
                 
                 (log-move m)
                 
                 (moves (cons m (moves)))
                 (hands (hash-update (hands) pid (lambda (hand) (remove c hand))))
                 (when (= num-players (length (moves)))
                   ;; have all the moves, play some cards!
                   (define-values (new-rows new-scores) (play-round (rows) (moves) (scores)))
                   
                   (log-rows new-rows)
                   (log-scores new-scores)
                   
                   (rows new-rows)
                   (scores new-scores)
                   (cond
                     [(< (current-round) 10) ;; start the next round
                      (moves '())
                      (current-round (add1 (current-round)))]
                     [else ;; the game is over!
                      (define winner/s (lowest-score/s (scores)))
                      (log-winner/s winner/s)
                      (stop-current-facet)])))))))

;; ---------------------------------------------------------------------------------------------------
;; Player Agents, AI

;; it seems like there could be a race s.t. the player sees the start of a round
;; before their hand updates.

;; [Set PID] -> Void
;; spawn player agents 
(define (spawn-player* players)
  ;; Hand Rows -> PlayerAgent
  ;; randomly pick a card in the hand
  (define (random-player hand rows)
    (random-ref hand))
  ;; -- IN -- 
  (for ([player (in-set players)])
    (spawn-player player random-player)))

;; PlayerId GamePlayer -> PlayerAgent
(define (spawn-player pid make-decision)
  (spawn #:name pid
         (define/query-value my-hand '() (in-hand pid $c) c)
         (define/query-set the-rows (row $r) (row r))
         (on (asserted (round-has-begun $n))
             (let ([c (make-decision (my-hand) (set->list (the-rows)))])
               (log-player-decision pid c (my-hand))
               (assert! (played-in-round pid n c))))))

;; ===================================================================================================
;; Test Game

(module+ main 

  (define players
    (set 'tony-the-tiger
         'tucan-sam
         'tophat-jones
         'eyehole-man))

  (spawn-dealer (shuffle the-deck) players)
  (spawn-player* players))