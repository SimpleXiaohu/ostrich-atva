(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun literal_4 () String)
(declare-fun x_7 () String)
(declare-fun literal_5 () String)
(declare-fun x_8 () String)
(declare-fun literal_6 () String)
(declare-fun x_9 () String)
(declare-fun literal_10 () String)
(declare-fun x_13 () String)
(declare-fun literal_11 () String)
(declare-fun x_14 () String)
(declare-fun literal_12 () String)
(declare-fun x_15 () String)
(declare-fun literal_19 () String)
(declare-fun x_18 () String)
(declare-fun x_20 () String)
(declare-fun literal_21 () String)
(declare-fun x_22 () String)
(assert (= literal_4 "\x3c\x62\x3e"))
(assert (= x_7 (str.++ literal_4 sigmaStar_0)))
(assert (= literal_5 "\x3c\x62\x3e"))
(assert (= x_8 (str.++ literal_5 sigmaStar_2)))
(assert (= literal_6 "\x3c\x62\x3e"))
(assert (= x_9 (str.++ literal_6 sigmaStar_1)))
(assert (= literal_10 "\x3c\x2f\x62\x3e"))
(assert (= x_13 (str.++ x_7 literal_10)))
(assert (= literal_11 "\x3c\x2f\x62\x3e"))
(assert (= x_14 (str.++ x_8 literal_11)))
(assert (= literal_12 "\x3c\x2f\x62\x3e"))
(assert (= x_15 (str.++ x_9 literal_12)))
(assert (= literal_19 "\x3c\x64\x69\x76\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x3e"))
(assert (or (= x_18 sigmaStar_3) (= x_18 x_15) (= x_18 x_14) (= x_18 x_13)))
(assert (= x_20 (str.++ literal_19 x_18)))
(assert (= literal_21 "\x3c\x2f\x64\x69\x76\x3e\x5c\x6e"))
(assert (= x_22 (str.++ x_20 literal_21)))
(assert (str.in.re x_22 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_22 "\x61" 0)) (str.len x_22)))
(check-sat)
(get-model)
