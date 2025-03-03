(set-logic QF_SLIA)
(set-option :produce-proofs true)

(declare-const x String)

; Constraint 1: x belongs to the regular language "a*"
(assert (str.in_re x (re.* (str.to_re "a"))))

; Constraint 2: x contains "b"
(assert (str.contains x "b"))

(check-sat)
