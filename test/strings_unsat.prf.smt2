unsat
(declare-fun x () String)
(define @t1 () (str.in_re x (re.* (str.to_re "a"))))
(define @t2 () (skolem (str.substr x 0 (str.indexof x "b" 0))))
(define @t3 () (str.len @t2))
(define @t4 () (= x (str.++ @t2 "b" (skolem (str.substr x (+ 1 @t3) (+ -1 (str.len x) (* -1 @t3)))))))
(define @t5 () (not @t1))
(assume @p1 @t1)
(assume @p2 (str.contains x "b"))
; WARNING: add trust step for MACRO_STRING_INFERENCE
; trust MACRO_STRING_INFERENCE
(step @p3 :rule trust :premises (@p2) :args (@t4))
(assume-push @p4 @t4)
; trust MACRO_STRING_INFERENCE
(step @p5 :rule trust :premises (@p3) :args (@t5))
(step-pop @p10 :rule scope :premises (@p5))
(step @p6 :rule process_scope :premises (@p10) :args (@t5))
(step @p8 :rule implies_elim :premises (@p6))
(step @p9 :rule reordering :premises (@p8) :args ((or @t5 (not @t4))))
; WARNING: add trust step for MACRO_RESOLUTION_TRUST
; trust MACRO_RESOLUTION_TRUST
(step @p10 false :rule trust :premises (@p9 @p3 @p1) :args (false))

