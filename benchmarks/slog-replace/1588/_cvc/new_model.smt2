(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun x_8 () String)
(declare-fun epsilon () String)
(declare-fun literal_2 () String)
(declare-fun literal_1 () String)
(declare-fun literal_3 () String)
(declare-fun x_9 () String)
(assert (= epsilon ""))
(assert (= literal_2 ""))
(assert (= literal_1 ""))
(assert (or (= x_8 epsilon) (= x_8 literal_2) (= x_8 literal_1) (= x_8 sigmaStar_0)))
(assert (= literal_3 "\x20\x20\x20\x20"))
(assert (= x_9 (str.++ x_8 literal_3)))
(assert (str.in.re x_9 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_9 "\x61" 0)) (str.len x_9)))
(check-sat)
(get-model)
