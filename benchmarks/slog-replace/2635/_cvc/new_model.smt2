(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_2 () String)
(declare-fun x_3 () String)
(declare-fun literal_6 () String)
(declare-fun x_7 () String)
(declare-fun literal_5 () String)
(declare-fun x_8 () String)
(assert (= literal_2 "\x2f\x6c\x61\x6e\x67\x2f"))
(assert (= x_3 (str.++ literal_2 sigmaStar_0)))
(assert (= literal_6 "\x2f"))
(assert (= x_7 (str.++ x_3 literal_6)))
(assert (= literal_5 "\x63\x75\x72\x72\x65\x6e\x74\x66\x69\x6c\x65"))
(assert (= x_8 (str.++ x_7 literal_5)))
(assert (str.in.re x_8 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_8 "\x61" 0)) (str.len x_8)))
(check-sat)
(get-model)
