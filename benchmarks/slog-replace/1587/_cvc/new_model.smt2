(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun x_9 () String)
(declare-fun epsilon () String)
(declare-fun literal_2 () String)
(declare-fun literal_3 () String)
(declare-fun literal_10 () String)
(declare-fun x_11 () String)
(assert (= epsilon ""))
(assert (= literal_2 ""))
(assert (= literal_3 ""))
(assert (or (= x_9 epsilon) (= x_9 literal_2) (= x_9 literal_3) (= x_9 sigmaStar_0)))
(assert (= literal_10 "\x5c\x74"))
(assert (= x_11 (str.++ x_9 literal_10)))
(assert (str.in.re x_11 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_11 "\x61" 0)) (str.len x_11)))
(check-sat)
(get-model)
