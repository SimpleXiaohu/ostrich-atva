(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun literal_7 () String)
(declare-fun x_6 () String)
(declare-fun literal_4 () String)
(declare-fun literal_5 () String)
(declare-fun x_8 () String)
(declare-fun x_10 () String)
(declare-fun epsilon () String)
(declare-fun x_11 () String)
(declare-fun literal_12 () String)
(declare-fun x_13 () String)
(declare-fun x_14 () String)
(declare-fun x_15 () String)
(declare-fun x_16 () String)
(declare-fun literal_17 () String)
(declare-fun x_18 () String)
(declare-fun x_19 () String)
(declare-fun literal_20 () String)
(declare-fun x_21 () String)
(assert (= literal_7 "\x5b\x3c\x61\x20\x68\x72\x65\x66\x3d\x27"))
(assert (= literal_4 ""))
(assert (= literal_5 "\x68\x74\x74\x70\x3a\x2f\x2f"))
(assert (or (= x_6 literal_4) (= x_6 literal_5)))
(assert (= x_8 (str.++ literal_7 x_6)))
(assert (= epsilon ""))
(assert (or (= x_10 epsilon) (= x_10 sigmaStar_2)))
(assert (= x_11 (str.++ x_8 x_10)))
(assert (= literal_12 "\x27\x20\x74\x69\x74\x6c\x65\x3d\x27"))
(assert (= x_13 (str.++ x_11 literal_12)))
(assert (= x_14 (str.++ x_13 x_6)))
(assert (or (= x_15 epsilon) (= x_15 sigmaStar_0)))
(assert (= x_16 (str.++ x_14 x_15)))
(assert (= literal_17 "\x27\x20\x74\x61\x72\x67\x65\x74\x3d\x27\x5f\x62\x6c\x61\x6e\x6b\x27\x3e"))
(assert (= x_18 (str.++ x_16 literal_17)))
(assert (= x_19 (str.++ x_18 sigmaStar_1)))
(assert (= literal_20 "\x3c\x2f\x61\x3e\x5d\x5c\x6e"))
(assert (= x_21 (str.++ x_19 literal_20)))
(assert (str.in.re x_21 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_21 "\x61" 0)) (str.len x_21)))
(check-sat)
(get-model)
