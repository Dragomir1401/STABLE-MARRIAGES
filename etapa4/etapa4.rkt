#lang racket

(require "etapa2.rkt")
(require "etapa3.rkt")

(provide (all-defined-out))

;; Preferințele bărbaților și femeilor din problemă se pot schimba
;; în timp, dar de obicei ele nu se schimbă radical de la un moment
;; la altul. De aceea, în loc să rulăm de la zero algoritmul
;; Gale-Shapley de fiecare dată când se schimbă ceva, preferăm să
;; pornim de la lista de logodne stabile obținută în pasul anterior
;; și să o actualizăm, conform algoritmului următor:
;; - eliminăm din engagements cuplurile care au devenit instabile
;;   în urma modificărilor de preferințe
;;   - cuplurile rămase sunt stabile între ele și considerăm că
;;     se găsesc împreună într-o cameră, în timp ce membrii cuplurilor
;;     destrămate stau la coadă la intrarea în cameră
;; - cât timp coada nu este goală
;;   - prima persoană p din coadă intră în cameră și încearcă să se
;;     cupleze cu cineva care este deja acolo, astfel:
;;     - p-list = lista de preferințe a lui p
;;     - determină prima persoană p' din p-list care este în cameră
;;     - dacă p' nu e logodită, logodește p' cu p
;;     - dacă p' e logodită
;;       - dacă p' îl preferă pe p partenerului actual p''
;;         - logodește p' cu p
;;         - încearcă să îl cuplezi pe p'' cu altcineva din cameră
;;           (folosind același algoritm)
;;       - altfel, treci la următoarea persoană din p-list (dacă
;;         aceasta există, altfel p rămâne temporar fără partener)


; TODO 1
; Implementați funcția match care primește o persoană person care
; intră în cameră, lista engagements a cuplurilor din cameră
; (cuplurile având pe prima poziție persoanele de gen opus lui 
; person), o listă pref1 care conține preferințele celor de același 
; gen cu person, o listă pref2 cu preferințele celor de gen diferit, 
; respectiv o coadă queue a persoanelor din afara camerei,
; și întoarce lista de cupluri actualizată astfel încât noile
; cupluri să fie stabile între ele.
; Această listă se obține ca rezultat al încercării de a cupla pe
; person cu cineva din cameră (person va încerca în ordine persoanele 
; din lista sa de preferințe), care poate duce la destrămarea
; unui cuplu și necesitatea de a cupla noua persoană rămasă singură
; cu altcineva din cameră, etc. Procesul continuă până când:
; - ori avem numai cupluri stabile între ele în cameră, nimeni
;   nefiind singur
; - ori toate persoanele rămase singure nu ar fi preferate de nimeni
;   altcineva din cameră, și în acest caz convenim să "logodim"
;   aceste persoane cu valoarea #f, astfel încât funcția să
;   întoarcă în aceeași listă atât informația despre cine din
;   cameră este logodit, cât și despre cine este singur

(define (match person engagements pref1 pref2 queue)
  (let iter-pref-list ( [person1 person] [engagements engagements] [person-pref-list (get-pref-list pref1 person)] [found 0] )
    (cond
      ((equal? found 1) engagements)
      ((null? person-pref-list) (cons (cons #f person1) (filter
                                                         (λ (pair)                                    
                                                           (not (and (equal? (car pair) #f) (equal? (cdr pair) person1))))
                                                         engagements)))
        
      (else (let* ( [prefered-pers (car person-pref-list)] )
              (let iter-eng ( [eng engagements] )
                (if (null? eng)
                    (iter-pref-list person1 engagements [cdr person-pref-list] 0 )
                    
                    (let* ( [current-pair (car (filter (λ (pair) (not (equal? #f (car pair)))) eng))]
                            [prefered-person-pref-list (get-pref-list pref2 (car current-pair))]
                            [new-healthy-pair (cons (car current-pair) person1)] [new-temporary-pair (cons #f (cdr current-pair))] )
                      
                      (if (equal? prefered-pers (car current-pair))
                          (if (not (cdr current-pair))
                              (iter-pref-list person1
                                              [cons new-healthy-pair
                                                    (filter
                                                     (λ (pair)                                    
                                                       (and (not (equal? (car pair) (car current-pair)))
                                                            (not (and (equal? (car pair) #f) (equal? (cdr pair) person1)))))
                                                     engagements)]
                                              person-pref-list 1 )
                              
                              (if (preferable? prefered-person-pref-list person1 (cdr current-pair))
                                  (iter-pref-list [cdr current-pair]
                                                  [cons new-healthy-pair
                                                        (cons new-temporary-pair
                                                              (filter
                                                               (λ (pair)                                    
                                                                 (and (not (equal? (car pair) (car current-pair)))
                                                                      (not (equal? (cdr pair) (cdr current-pair)))
                                                                      (not (and (equal? (car pair) #f) (equal? (cdr pair) person1)))))
                                                               engagements))]
                                                  [get-pref-list pref1 (cdr current-pair)] 0 )

                         
                                  (iter-pref-list person1 engagements [cdr person-pref-list] 0 )))
                 
                          (iter-eng [cdr eng]) )))))))))
          
 


; TODO 2
; Implementați funcția path-to-stability care primește lista
; engagements a cuplurilor din cameră, o listă de preferințe 
; masculine mpref, o listă de preferințe feminine wpref, respectiv
; coada queue a persoanelor din afara camerei, și întoarce lista
; completă de logodne stabile, obținută după ce fiecare persoană
; din queue este introdusă pe rând în cameră și supusă procesului
; descris de funcția match.
; Precizări (aspecte care se garantează, nu trebuie verificate):
; - fiecare cuplu din lista engagements are pe prima poziție
;   o femeie
; - persoanele nelogodite din cameră apar în engagements sub forma
;   (#f . nume-bărbat) sau (nume-femeie . #f)
(define (path-to-stability engagements mpref wpref queue)
  (let iter-queue ( [q queue] [eng engagements] [previous 0] )
    (let* ( [men (get-men mpref)] [women (get-women wpref)] [rev-eng (map (λ (pair) (cons (cdr pair) (car pair))) eng)] )
      (if (null? q)
          (if (equal? previous -1)              
              rev-eng         
              eng)
          
          (cond
            ((and (not (null? (filter (λ (man) (equal? man (car q))) men))) (or (equal? previous 1) (equal? previous 0)))
             (iter-queue [cdr q] [match (car q) eng mpref wpref q] 1 ))

            ((and (not (null? (filter (λ (man) (equal? man (car q))) men))) (or (equal? previous -1) (equal? previous 0)))
             (iter-queue [cdr q] [match (car q) rev-eng mpref wpref q] 1 ))
          
            ((and (not (null? (filter (λ (woman) (equal? woman (car q))) women))) (or (equal? previous 1) (equal? previous 0)))
             (iter-queue [cdr q] [match (car q) rev-eng wpref mpref q] -1 ))

            ((and (not (null? (filter (λ (woman) (equal? woman (car q))) women))) (or (equal? previous -1) (equal? previous 0)))
             (iter-queue [cdr q] [match (car q) eng wpref mpref q] -1 ))
          
            (else (iter-queue [cdr q] eng 0))
            )))))
     

          


; TODO 3
; Implementați funcția update-stable-match care primește o listă 
; completă de logodne engagements (soluția anterioară), o listă de 
; preferințe masculine mpref și o listă de preferințe feminine wpref 
; (adică preferințele modificate față de cele pe baza cărora s-a 
; obținut soluția engagements), și calculează o nouă listă de logodne 
; stabile - conform cu noile preferințe, astfel:
; - unstable = cuplurile instabile din engagements
; - room-engagements = engagements - unstable
; - queue = persoanele din unstable
; - aplică algoritmul path-to-stability
; Precizări (aspecte care se garantează, nu trebuie verificate):
; - fiecare cuplu din lista engagements are pe prima poziție
;   o femeie
(define (form-queue engagements mpref wpref)
  (let iter-unstables ( [unstable-couples (get-unstable-couples engagements mpref wpref)] [queue '()] )
    (if (null? unstable-couples)
        queue 
        (let ( [curr-couple (car unstable-couples)] )        
          (iter-unstables [cdr unstable-couples] [cons (cdr curr-couple) (cons (car curr-couple) queue)] )))))

(define (filter-eng engagements mpref wpref queue)
  (let iter-unstable-queue ( [q queue] [engagements engagements] )
    (if (null? q)
        engagements
        (iter-unstable-queue [cdr q] [filter (λ (pair) (not (or (equal? (car pair) (car q)) (equal? (cdr pair) (car q))))) engagements] ))))

(define (update-stable-match engagements mpref wpref)
  (let ( [queue (form-queue engagements mpref wpref)] )
    (path-to-stability [filter-eng engagements mpref wpref queue] mpref wpref queue)))

; TODO 4
; Implementați funcția build-stable-matches-stream care primește
; un flux pref-stream de instanțe SMP și întoarce fluxul de 
; soluții SMP corespunzător acestor instanțe.
; O instanță SMP este o pereche cu punct între o listă de preferințe
; masculine și o listă de preferințe feminine.
; Fluxul rezultat se va obține în felul următor:
; - primul element se calculează prin aplicarea algoritmului
;   Gale-Shapley asupra primei instanțe
; - următoarele elemente se obțin prin actualizarea soluției
;   anterioare conform algoritmului implementat în etapa 4 a temei
; Trebuie să lucrați cu interfața pentru fluxuri. Dacă rezolvați
; problema folosind liste și doar convertiți în/din fluxuri,
; punctajul pe acest exercițiu se anulează în totalitate.

(define (build-stable-matches-stream pref-stream)
  (let iter-stream ( [str pref-stream] [prev-eng empty-stream] )
    (if (stream-empty? str)
        empty-stream    
        (let* ([preferences (stream-first str)]
               [current-eng (gale-shapley (stream-first preferences) (stream-rest preferences))]
               [updated-eng (update-stable-match current-eng (car preferences) (cdr preferences))])         
          (stream-cons current-eng (iter-stream (stream-rest str) updated-eng)))))) 





