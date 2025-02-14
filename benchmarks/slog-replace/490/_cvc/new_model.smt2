(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_7 () String)
(declare-fun literal_9 () String)
(declare-fun x_10 () String)
(declare-fun epsilon () String)
(declare-fun literal_8 () String)
(declare-fun x_11 () String)
(declare-fun literal_12 () String)
(declare-fun x_13 () String)
(assert (= literal_9 "\x3c\x74\x72\x3e\x3c\x74\x64\x3e\x3c\x62\x3e"))
(assert (= epsilon ""))
(assert (= literal_8 "\x3c\x3c\x20\x6e\x6f\x74\x69\x74\x6c\x65\x20\x20\x3e\x3e"))
(assert (or (= x_10 epsilon) (= x_10 literal_8)))
(assert (= x_11 (str.++ literal_9 x_10)))
(assert (= literal_12 "\x3c\x2f\x62\x3e\x3c\x2f\x74\x64\x3e\x3c\x2f\x74\x72\x3e\x5c\x6e"))
(assert (= x_13 (str.++ x_11 literal_12)))
(assert (str.in.re x_13 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_13 "\x61" 0)) (str.len x_13)))
(check-sat)
(get-model)
