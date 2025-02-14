(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun literal_5 () String)
(declare-fun x_6 () String)
(declare-fun epsilon () String)
(declare-fun literal_4 () String)
(declare-fun x_7 () String)
(declare-fun literal_1 () String)
(declare-fun x_8 () String)
(declare-fun literal_9 () String)
(declare-fun x_10 () String)
(assert (= literal_5 "\x73\x65\x6c\x65\x63\x74\x20\x63\x6f\x75\x6e\x74\x28\x2a\x29\x20\x66\x72\x6f\x6d\x20"))
(assert (= epsilon ""))
(assert (= literal_4 ""))
(assert (or (= x_6 epsilon) (= x_6 literal_4)))
(assert (= x_7 (str.++ literal_5 x_6)))
(assert (= literal_1 ""))
(assert (= x_8 (str.++ x_7 literal_1)))
(assert (= literal_9 "\x3c\x62\x72\x3e\x54\x6f\x74\x61\x6c\x20\x6e\x75\x6d\x62\x65\x72\x20\x6f\x66\x20\x72\x65\x63\x6f\x72\x64\x73\x20\x69\x73\x20\x2e\x2e"))
(assert (= x_10 (str.++ literal_9 x_8)))
(assert (str.in.re x_10 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_10 "\x61" 0)) (str.len x_10)))
(check-sat)
(get-model)
