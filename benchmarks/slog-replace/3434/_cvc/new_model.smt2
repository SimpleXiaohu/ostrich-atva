(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun literal_4 () String)
(declare-fun x_8 () String)
(declare-fun literal_6 () String)
(declare-fun x_9 () String)
(declare-fun literal_5 () String)
(declare-fun x_10 () String)
(declare-fun literal_7 () String)
(declare-fun x_11 () String)
(declare-fun x_12 () String)
(declare-fun x_13 () String)
(declare-fun x_15 () String)
(declare-fun x_17 () String)
(declare-fun literal_16 () String)
(declare-fun x_18 () String)
(declare-fun x_21 () String)
(declare-fun x_22 () String)
(declare-fun literal_23 () String)
(declare-fun x_24 () String)
(assert (= literal_4 "\x3c\x62\x72\x3e"))
(assert (= x_8 (str.++ sigmaStar_0 literal_4)))
(assert (= literal_6 ""))
(assert (= x_9 (str.++ literal_6 x_8)))
(assert (= literal_5 "\x3c\x62\x72\x3e"))
(assert (= x_10 (str.++ sigmaStar_3 literal_5)))
(assert (= literal_7 "\x3c\x62\x72\x3e"))
(assert (= x_11 (str.++ sigmaStar_1 literal_7)))
(assert (or (= x_12 x_9) (= x_12 literal_6)))
(assert (= x_13 (str.++ x_12 x_11)))
(assert (or (= x_15 x_9) (= x_15 literal_6) (= x_15 x_13)))
(assert (= x_17 (str.++ x_15 x_10)))
(assert (= literal_16 "\x3c\x62\x72\x3e\x3c\x62\x72\x3e\x5c\x6e"))
(assert (= x_18 (str.++ sigmaStar_2 literal_16)))
(assert (or (= x_21 x_9) (= x_21 x_17) (= x_21 literal_6) (= x_21 x_13)))
(assert (= x_22 (str.++ x_18 x_21)))
(assert (= literal_23 "\x3c\x62\x72\x3e\x5c\x6e"))
(assert (= x_24 (str.++ x_22 literal_23)))
(assert (str.in.re x_24 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_24 "\x61" 0)) (str.len x_24)))
(check-sat)
(get-model)
