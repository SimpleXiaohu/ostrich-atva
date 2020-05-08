(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun x_8 () String)
(declare-fun literal_6 () String)
(declare-fun x_4 () String)
(declare-fun x_7 () String)
(declare-fun literal_5 () String)
(declare-fun x_11 () String)
(declare-fun x_10 () String)
(declare-fun literal_9 () String)
(declare-fun x_15 () String)
(declare-fun x_14 () String)
(declare-fun literal_13 () String)
(declare-fun x_17 () String)
(declare-fun x_16 () String)
(declare-fun epsilon () String)
(declare-fun x_19 () String)
(declare-fun sigmaStar_20 () String)
(declare-fun literal_21 () String)
(declare-fun x_22 () String)
(declare-fun literal_23 () String)
(declare-fun x_24 () String)
(declare-fun literal_25 () String)
(declare-fun x_26 () String)
(declare-fun sigmaStar_29 () String)
(assert (= x_4 (str.replaceall sigmaStar_0 "\x2f\x5b\x5e\x30\x2d\x39\x61\x2d\x7a\x5c\x2d\x5f\x2c\x5d\x2b\x2f\x69" "")))
(assert (= literal_6 ""))
(assert (or (= x_8 literal_6) (= x_8 x_4)))
(assert (= literal_5 ""))
(assert (or (= x_7 x_4) (= x_7 literal_5)))
(assert (= x_11 (str.++ x_8 x_7)))
(assert (= literal_9 ""))
(assert (or (= x_10 literal_9) (= x_10 x_4)))
(assert (= x_15 (str.++ x_11 x_10)))
(assert (= literal_13 "\x65\x6e"))
(assert (or (= x_14 x_4) (= x_14 literal_13)))
(assert (= x_17 (str.++ x_15 x_14)))
(assert (= epsilon ""))
(assert (or (= x_16 epsilon) (= x_16 x_4)))
(assert (= x_19 (str.++ x_17 x_16)))
(assert (= literal_21 "\x2f"))
(assert (= x_22 (str.++ sigmaStar_20 literal_21)))
(assert (= literal_23 "\x74\x69\x6e\x79\x6d\x63\x65\x5f"))
(assert (= x_24 (str.++ x_22 literal_23)))
(assert (= literal_25 "\x2e\x67\x7a"))
(assert (= x_26 (str.++ x_24 literal_25)))
(assert (str.in.re sigmaStar_29 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (> (* 2 (str.indexof x_4 "\x61" 0)) (str.len x_4)))
(check-sat)
(get-model)
