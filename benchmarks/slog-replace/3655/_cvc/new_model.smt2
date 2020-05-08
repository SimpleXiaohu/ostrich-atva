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
(declare-fun x_8 () String)
(declare-fun literal_7 () String)
(declare-fun x_9 () String)
(declare-fun literal_10 () String)
(declare-fun x_11 () String)
(declare-fun x_12 () String)
(declare-fun literal_15 () String)
(declare-fun x_14 () String)
(declare-fun x_16 () String)
(declare-fun literal_17 () String)
(declare-fun x_18 () String)
(assert (= literal_4 "\x3c\x62\x3e"))
(assert (= x_5 (str.++ literal_4 sigmaStar_2)))
(assert (= literal_6 "\x3c\x62\x3e"))
(assert (= x_8 (str.++ literal_6 sigmaStar_3)))
(assert (= literal_7 "\x3c\x2f\x62\x3e\x3c\x62\x72\x3e\x5c\x6e"))
(assert (= x_9 (str.++ x_5 literal_7)))
(assert (= literal_10 "\x3c\x2f\x62\x3e"))
(assert (= x_11 (str.++ x_8 literal_10)))
(assert (= x_12 (str.++ x_9 sigmaStar_0)))
(assert (= literal_15 "\x3c\x64\x69\x76\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x3e"))
(assert (or (= x_14 x_11) (= x_14 sigmaStar_1) (= x_14 x_12)))
(assert (= x_16 (str.++ literal_15 x_14)))
(assert (= literal_17 "\x3c\x2f\x64\x69\x76\x3e\x5c\x6e"))
(assert (= x_18 (str.++ x_16 literal_17)))
(assert (str.in.re x_18 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_18 "\x61" 0)) (str.len x_18)))
(check-sat)
(get-model)
