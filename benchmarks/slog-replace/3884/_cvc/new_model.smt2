(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun literal_4 () String)
(declare-fun x_5 () String)
(declare-fun literal_6 () String)
(declare-fun x_7 () String)
(declare-fun x_9 () String)
(declare-fun literal_8 () String)
(declare-fun x_10 () String)
(declare-fun literal_11 () String)
(declare-fun x_13 () String)
(declare-fun literal_12 () String)
(declare-fun x_14 () String)
(declare-fun literal_17 () String)
(declare-fun x_16 () String)
(declare-fun x_18 () String)
(declare-fun literal_19 () String)
(declare-fun x_20 () String)
(assert (= literal_4 "\x3c\x62\x3e"))
(assert (= x_5 (str.++ literal_4 sigmaStar_2)))
(assert (= literal_6 "\x20"))
(assert (= x_7 (str.++ x_5 literal_6)))
(assert (= x_9 (str.++ x_7 sigmaStar_0)))
(assert (= literal_8 "\x3c\x62\x3e"))
(assert (= x_10 (str.++ literal_8 sigmaStar_3)))
(assert (= literal_11 "\x3c\x2f\x62\x3e"))
(assert (= x_13 (str.++ x_9 literal_11)))
(assert (= literal_12 "\x3c\x2f\x62\x3e"))
(assert (= x_14 (str.++ x_10 literal_12)))
(assert (= literal_17 "\x3c\x64\x69\x76\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x3e"))
(assert (or (= x_16 sigmaStar_1) (= x_16 x_14) (= x_16 x_13)))
(assert (= x_18 (str.++ literal_17 x_16)))
(assert (= literal_19 "\x3c\x2f\x64\x69\x76\x3e\x5c\x6e"))
(assert (= x_20 (str.++ x_18 literal_19)))
(assert (str.in.re x_20 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_20 "\x61" 0)) (str.len x_20)))
(check-sat)
(get-model)
