(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun literal_3 () String)
(declare-fun x_4 () String)
(declare-fun literal_5 () String)
(declare-fun x_8 () String)
(declare-fun literal_9 () String)
(declare-fun x_10 () String)
(declare-fun literal_7 () String)
(declare-fun x_11 () String)
(declare-fun literal_17 () String)
(assert (= literal_3 "\x2f\x6c\x61\x6e\x67\x2f"))
(assert (= x_4 (str.++ literal_3 sigmaStar_0)))
(assert (= literal_5 "\x0d\x0a"))
(assert (= x_8 (str.++ literal_5 x_4)))
(assert (= literal_9 "\x2f"))
(assert (= x_10 (str.++ x_8 literal_9)))
(assert (= literal_7 "\x63\x75\x72\x72\x65\x6e\x74\x66\x69\x6c\x65"))
(assert (= x_11 (str.++ x_10 literal_7)))
(assert (= literal_17 "\x3c\x70\x20\x61\x6c\x69\x67\x6e\x3d\x22\x63\x65\x6e\x74\x65\x72\x22\x3e\x3c\x66\x6f\x6e\x74\x20\x63\x6f\x6c\x6f\x72\x3d\x72\x65\x64\x3e\x66\x69\x6c\x65\x6d\x69\x73\x73\x69\x6e\x67\x3c\x2f\x66\x6f\x6e\x74\x3e\x3c\x2f\x70\x3e"))
(assert (str.in.re literal_17 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_11 "\x61" 0)) (str.len x_11)))
(check-sat)
(get-model)
