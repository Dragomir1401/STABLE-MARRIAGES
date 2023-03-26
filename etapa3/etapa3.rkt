#lang racket

(require "etapa2.rkt")

(provide (all-defined-out))

; TODO 1
; După modelul funcției stable-match?, implementați funcția
; get-unstable-couples care primește o listă de logodne
; engagements, o listă de preferințe masculine mpref și o 
; listă de preferințe feminine wpref, și întoarce lista
; tuturor cuplurilor instabile din engagements.
; Precizări (aspecte care se garantează, nu trebuie verificate):
; - fiecare cuplu din lista engagements are pe prima poziție
;   o femeie
; Nu este permisă recursivitatea pe stivă.
; Nu sunt permise alte funcții ajutătoare decât
; better-match-exists? și funcțiile de manipulare a listelor de
; preferințe definite în etapele anterioare.
; Nu este permisă apelarea multiplă a aceleiași funcții pe
; aceleași argumente.
; Folosiți una sau mai multe dintre expresiile let, let*, letrec,
; named let pentru a vă putea conforma acestor restricții.

;(define (get-unstable-couplesss engagements mpref wpref)
; (for engagements (- (length engagements) 1) mpref wpref))


(define (get-unstable-couples engagements mpref wpref)
  (let iter ([cnt (- (length engagements) 1)] [result '()])            
    (if (equal? cnt -1)                           
        result
        (let* ([couple (list-ref engagements cnt)] [first (car couple)] [second (cdr couple)]
                                                   [reversed-list (map (λ (pair) (cons (cdr pair) (car pair))) engagements)])
          (if (or (better-match-exists? first second
                                        (get-pref-list wpref first) mpref reversed-list)
                  (better-match-exists? second first
                                        (get-pref-list mpref second) wpref engagements) )                                       
              (iter (- cnt 1) (cons couple result))
              (iter (- cnt 1) result))
          ))))


           




; TODO 2
; Implementați funcția engage care primește o listă free-men
; de bărbați încă nelogodiți, o listă de logodne parțiale 
; engagements (unde fiecare cuplu are pe prima poziție o femeie),
; o listă de preferințe masculine mpref și o listă de preferințe 
; feminine wpref, și întoarce o listă completă de logodne stabile,
; obținută conform algoritmului Gale-Shapley:
; - cât timp există un bărbat m încă nelogodit
;   - w = prima femeie din preferințele lui m pe care m nu a cerut-o încă
;   - dacă w este nelogodită, adaugă perechea (w, m) la engagements
;   - dacă w este logodită cu m'
;     - dacă w îl preferă pe m lui m'
;       - m' devine liber
;       - actualizează partenerul lui w la m în engagements
;     - altfel, repetă procesul cu următoarea femeie din lista lui m
; Folosiți named let pentru orice proces recursiv ajutător (deci nu
; veți defini funcții ajutătoare recursive).
; Folosiți let și/sau let* pentru a evita calcule duplicate.


(define mpref
  '([adi  ana  bia cora]
    [bobo cora ana bia ]
    [cos  cora bia ana ]))
(define wpref
  '([ana  bobo adi cos ]
    [bia  adi  cos bobo]
    [cora bobo cos adi ]))

(define (engage1 free-men engagements mpref wpref)
  (let iter ( [cnt (- (length free-men) 1)]  [result '()] )
    (if (equal? cnt -1)
        result
        (let* ( [man  (list-ref free-men cnt) ] [w  (car (get-pref-list mpref man)) ] [w-pref-list (get-pref-list wpref w)] )
      
          (if (not (find-first (λ(L) (or (equal? (car L) w) (equal? (cdr L) w))) engagements))  
              (cons result (cons w man))
          
              (let* ([m1  (cdr (find-first (λ(L) (or (equal? (car L) w) (equal? (cdr L) w))) engagements))])
            
                (if (preferable? w-pref-list man m1)
                    (and (cons free-men m1) (cons result (cons w man)) (filter (λ (pair) (not (equal? (car pair) w))) engagements))
                
                    (iter (- cnt 1))           
                    )))))))

(define (engage2 free-men engagements mpref wpref)
  (let iter ( [cnt (- (length free-men) 1)]  [result '()]  [free-men free-men] )
    (if (equal? cnt -1)
        result
        
        (let* ([man (list-ref free-men cnt)]
               [w (car (get-pref-list mpref man))]
               [w-pref-list (get-pref-list wpref w)])
          
          (if (not (find-first (λ(L) (or (equal? (car L) w) (equal? (cdr L) w))) engagements))
              (cons (cons w man) result)
              
              (let* ([m1 (cdr (find-first (λ(L) (equal? (car L) w)) engagements))])
                
                (if (preferable? w-pref-list man m1)
                    (iter (- cnt 1) (cons (cons w man) (filter (λ (pair) (not (equal? (car pair) w))) engagements))  free-men )
                    
                    (iter (- cnt 1) result free-men))))))))


(define (engage3 free-men engagements mpref wpref)
  (let iter ([cnt (- (length free-men) 1)] [result '()])
    (if (equal? cnt -1)
        result
        (let* ([man (list-ref free-men cnt)]
               [w (car (get-pref-list mpref man))]
               [w-pref-list (get-pref-list wpref w)]
               [current-engagement (find-first (λ (L) (equal? (cdr L) w)) engagements)])
          (cond
            [(not current-engagement)
             (iter (- cnt 1) (cons (cons man w) result))]
            [(preferable? w-pref-list man (car current-engagement))
             (iter (- cnt 1)
                   (append result
                           (list (cons man w))
                           (filter (λ (pair) (and (not (equal? (car pair) w)) (not (equal? (cdr pair) man)))) engagements)))]
            [else
             (iter (- cnt 1) result)]
            )))))


(define (engage4 free-men engagements mpref wpref)
  (let iter ( [cnt (- (length free-men) 1)]  [result '()]  [free-men free-men] )
    (if (equal? cnt -1)
        result
        
        (let* ([man (list-ref free-men cnt)]
               [w (car (get-pref-list mpref man))]
               [w-pref-list (get-pref-list wpref w)])
          
          (if (not (find-first (λ(L) (or (equal? (car L) w) (equal? (cdr L) w))) engagements))
              (iter (- cnt 1) (cons (cons w man) engagements) free-men)
              
              (let* ([m1 (cdr (find-first (λ(L) (equal? (car L) w)) engagements))])
                
                (if (preferable? w-pref-list man m1)
                    (iter (- cnt 1) (cons (cons w man) (filter (λ (pair) (not (equal? (car pair) w))) engagements)) (cons m1 free-men) )
                    
                    (if (equal? cnt 0)
                        (cons m1 (iter (- cnt 1) result (cons man (filter (λ (man) (not (equal? man m1))) free-men))))
                        (iter (- cnt 1) result free-men)))))))))




; TODO 3
; Implementați funcția gale-shapley care este un wrapper pentru
; algoritmul implementat de funcția engage. Funcția gale-shapley
; primește doar o listă de preferințe masculine mpref și o listă
; de preferințe feminine wpref și calculează o listă completă de
; logodne stabile conform acestor preferințe.
(define (gale-shapley mpref wpref)
  'your-code-here)


; TODO 4
; Implementați funcția get-couple-members care primește o listă
; de perechi cu punct și întoarce o listă simplă cu toate elementele 
; care apar în perechi.
; Folosiți funcționale, fără recursivitate explicită.
(define (get-couple-members pair-list)
  (foldr (λ (L acc) (cons (cdr L) (cons (car L) acc))) '() pair-list))


