(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun literal_0 () String)
(declare-fun x_8 () String)
(declare-fun epsilon () String)
(declare-fun x_9 () String)
(declare-fun literal_10 () String)
(declare-fun x_11 () String)
(declare-fun x_12 () String)
(declare-fun x_13 () String)
(declare-fun literal_14 () String)
(declare-fun x_15 () String)
(assert (= literal_0 "\x2f\x62\x6c\x6f\x63\x6b\x73\x2f"))
(assert (= epsilon ""))
(assert (or (= x_8 epsilon)))
(assert (= x_9 (str.++ literal_0 x_8)))
(assert (= literal_10 "\x2f\x62\x6c\x6f\x63\x6b\x5f"))
(assert (= x_11 (str.++ x_9 literal_10)))
(assert (or (= x_12 epsilon)))
(assert (= x_13 (str.++ x_11 x_12)))
(assert (= literal_14 "\x2e\x70\x68\x70"))
(assert (= x_15 (str.++ x_13 literal_14)))
(assert (str.in.re x_15 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_15 "\x61" 0)) (str.len x_15)))
(check-sat)
(get-model)
