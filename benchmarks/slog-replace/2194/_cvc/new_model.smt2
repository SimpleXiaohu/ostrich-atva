(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun x_6 () String)
(declare-fun literal_3 () String)
(declare-fun literal_5 () String)
(declare-fun x_7 () String)
(declare-fun literal_4 () String)
(declare-fun x_8 () String)
(assert (= literal_3 "\x75\x6e\x63\x61\x74\x65\x67\x6f\x72\x69\x73\x65\x64"))
(assert (or (= x_6 literal_3) (= x_6 sigmaStar_1)))
(assert (= literal_5 "\x20"))
(assert (= x_7 (str.++ x_6 literal_5)))
(assert (= literal_4 "\x67\x72\x61\x64\x65\x73"))
(assert (= x_8 (str.++ x_7 literal_4)))
(assert (str.in.re x_8 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_8 "\x61" 0)) (str.len x_8)))
(check-sat)
(get-model)
