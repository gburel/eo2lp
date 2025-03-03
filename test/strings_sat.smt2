(set-logic QF_SLIA)
(set-option :produce-models true)

(define-const ab String "ab")
(define-const abc String "abc")

(declare-const x String)
(declare-const y String)
(declare-const z String)

; x.ab.y = abc.z
(assert (= (str.++ x ab y) (str.++ abc z)))
; |y| >= 0
(assert (>= (str.len y) 1))

; Regular expression: (ab[c-e]*f)|g|h
(define-const r RegLan
  (re.union
    (re.++ (str.to_re "ab") (re.* (re.range "c" "e")) (str.to_re "f"))
    (str.to_re "f")
    (str.to_re "h")
  )
)

(check-sat)
(get-model)