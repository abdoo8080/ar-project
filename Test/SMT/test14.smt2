(set-logic AX)

(declare-sort I 0)
(declare-sort E 0)

(define-sort A () (Array I E))

(declare-const a1 A)
(declare-const a2 A)
(declare-const a3 A)

(declare-const i1 I)
(declare-const i2 I)
(declare-const i3 I)

(declare-const v1 E)
(declare-const v2 E)
(declare-const v3 E)

(assert (distinct v2 (select (store (store a1 i2 v2) i3 v2) i2)))

(check-sat)
