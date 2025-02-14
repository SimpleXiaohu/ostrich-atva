(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_4 () String)
(declare-fun x_3 () String)
(declare-fun literal_2 () String)
(declare-fun literal_1 () String)
(declare-fun x_5 () String)
(declare-fun literal_6 () String)
(declare-fun x_7 () String)
(assert (= literal_4 "\x41\x63\x74\x69\x6f\x6e\x20\x27"))
(assert (= literal_2 ""))
(assert (= literal_1 "\x61\x63\x74\x69\x6f\x6e"))
(assert (or (= x_3 literal_2) (= x_3 literal_1)))
(assert (= x_5 (str.++ literal_4 x_3)))
(assert (= literal_6 "\x27\x20\x6e\x6f\x74\x20\x72\x65\x63\x6f\x67\x6e\x69\x7a\x65\x64"))
(assert (= x_7 (str.++ x_5 literal_6)))
(assert (str.in.re x_7 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_7 "\x61" 0)) (str.len x_7)))
(check-sat)
(get-model)
