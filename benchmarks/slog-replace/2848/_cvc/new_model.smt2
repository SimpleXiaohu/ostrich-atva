(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_3 () String)
(declare-fun literal_4 () String)
(declare-fun x_2 () String)
(declare-fun literal_0 () String)
(declare-fun literal_1 () String)
(declare-fun x_6 () String)
(declare-fun literal_7 () String)
(declare-fun x_8 () String)
(declare-fun x_9 () String)
(declare-fun epsilon () String)
(declare-fun x_10 () String)
(declare-fun sigmaStar_11 () String)
(declare-fun literal_12 () String)
(declare-fun x_13 () String)
(declare-fun literal_5 () String)
(declare-fun x_14 () String)
(declare-fun literal_15 () String)
(declare-fun x_16 () String)
(assert (= literal_4 "\x2f\x6c\x61\x6e\x67\x2f"))
(assert (= literal_0 ""))
(assert (= literal_1 ""))
(assert (or (= x_2 literal_0) (= x_2 literal_1)))
(assert (= x_6 (str.++ literal_4 x_2)))
(assert (= literal_7 "\x2f\x68\x65\x6c\x70"))
(assert (= x_8 (str.++ x_6 literal_7)))
(assert (= epsilon ""))
(assert (or (= x_9 epsilon)))
(assert (= x_10 (str.++ x_9 x_8)))
(assert (= literal_12 "\x2f\x72\x65\x73\x6f\x75\x72\x63\x65\x2f\x74\x79\x70\x65\x2f"))
(assert (= x_13 (str.++ x_10 literal_12)))
(assert (= literal_5 ""))
(assert (= x_14 (str.++ x_13 literal_5)))
(assert (= literal_15 "\x2e\x68\x74\x6d\x6c"))
(assert (= x_16 (str.++ x_14 literal_15)))
(assert (str.in.re x_16 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_16 "\x61" 0)) (str.len x_16)))
(check-sat)
(get-model)
