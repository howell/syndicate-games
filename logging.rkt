#lang racket

(provide
 ;; Rows -> Void
 log-rows

 ;; Move -> Void
 log-move

 ;; Scores -> Void
 log-scores

 ;; (Listof PlayerId) -> Void
 log-winner/s

 ;; PlayerId Card (Listof Card) -> Void
 log-player-decision)

;; ---------------------------------------------------------------------------------------------------
(require "rules.rkt")

;; ---------------------------------------------------------------------------------------------------
(define the-topic 'take-5)

(define-logger take-5)

(define (log-move m)
  (match-define (played-in-round pid r c) m)
  (log-take-5-debug "player ~a plays card ~v in round ~v" pid c r))

(define (log-rows rows)
  (log-take-5-debug "The current rows are:\n\t~v\n\t~v\n\t~v\n\t~v"
                    (first rows) (second rows) (third rows) (fourth rows)))

(define (log-player-decision pid c hand)
  (log-take-5-debug "~a chooses card ~v from hand ~v" pid c hand))

(define (log-scores scores)
  (log-take-5-debug "The current scores are:")
  (for ([(pid score) (in-hash scores)])
    (log-take-5-debug "~a has ~v bulls" pid score)))

(define (log-winner/s pids)
  (cond
    [(= 1 (length pids))
     (log-take-5-debug "~a wins!" (first pids))]
    [else
     (define names (map symbol->string pids))
     (log-take-5-debug (string-join names ", "
                                    #:before-last " and "
                                    #:after-last " tie!"))]))


;; PlayerId Row -> Void
(define (log-row-pickup pid r)
  (log-take-5-debug "~a picks up row ~v" pid r))
