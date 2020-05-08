(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_8 () String)
(declare-fun x_9 () String)
(declare-fun epsilon () String)
(declare-fun literal_6 () String)
(declare-fun literal_5 () String)
(declare-fun x_11 () String)
(declare-fun literal_12 () String)
(declare-fun x_13 () String)
(declare-fun literal_10 () String)
(declare-fun x_14 () String)
(declare-fun literal_15 () String)
(declare-fun x_16 () String)
(assert (= literal_8 "\x5c\x6e\x3c\x65\x6d\x62\x65\x64\x20\x73\x72\x63\x3d\x5c\x22"))
(assert (= epsilon ""))
(assert (= literal_6 "\x2f\x66\x69\x6c\x65\x2e\x70\x68\x70\x3f\x66\x69\x6c\x65\x3d\x2f\x2f"))
(assert (= literal_5 "\x2f\x66\x69\x6c\x65\x2e\x70\x68\x70\x2f\x2f"))
(assert (or (= x_9 epsilon) (= x_9 literal_6) (= x_9 literal_5)))
(assert (= x_11 (str.++ literal_8 x_9)))
(assert (= literal_12 "\x5c\x22\x20\x6e\x61\x6d\x65\x3d\x5c\x22\x6d\x73\x70\x6c\x61\x79\x65\x72\x5c\x22\x20\x74\x79\x70\x65\x3d\x5c\x22"))
(assert (= x_13 (str.++ x_11 literal_12)))
(assert (= literal_10 "\x74\x79\x70\x65"))
(assert (= x_14 (str.++ x_13 literal_10)))
(assert (= literal_15 "\x5c\x22\x20"))
(assert (= x_16 (str.++ x_14 literal_15)))
(assert (str.in.re x_16 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_16 "\x61" 0)) (str.len x_16)))
(check-sat)
(get-model)
