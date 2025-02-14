(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun sigmaStar_4 () String)
(declare-fun sigmaStar_5 () String)
(declare-fun sigmaStar_6 () String)
(declare-fun literal_12 () String)
(declare-fun x_13 () String)
(declare-fun epsilon () String)
(declare-fun literal_8 () String)
(declare-fun x_14 () String)
(declare-fun literal_15 () String)
(declare-fun x_16 () String)
(assert (= literal_12 "\x3c\x73\x74\x72\x6f\x6e\x67\x3e\x20"))
(assert (= epsilon ""))
(assert (= literal_8 "\x75\x73\x65\x72"))
(assert (or (= x_13 epsilon) (= x_13 literal_8)))
(assert (= x_14 (str.++ literal_12 x_13)))
(assert (= literal_15 "\x3c\x2f\x73\x74\x72\x6f\x6e\x67\x3e"))
(assert (= x_16 (str.++ x_14 literal_15)))
(assert (str.in.re x_16 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_16 "\x61" 0)) (str.len x_16)))
(check-sat)
(get-model)
