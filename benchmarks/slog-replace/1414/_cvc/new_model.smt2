(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_6 () String)
(declare-fun x_5 () String)
(declare-fun literal_3 () String)
(declare-fun literal_4 () String)
(declare-fun x_7 () String)
(declare-fun literal_8 () String)
(declare-fun x_9 () String)
(assert (= literal_6 "\x72\x65\x70\x6f\x72\x74\x2f"))
(assert (= literal_3 "\x6d\x6f\x64\x65"))
(assert (= literal_4 "\x6f\x76\x65\x72\x76\x69\x65\x77"))
(assert (or (= x_5 literal_3) (= x_5 literal_4)))
(assert (= x_7 (str.++ literal_6 x_5)))
(assert (= literal_8 "\x2f\x72\x65\x70\x6f\x72\x74\x2e\x70\x68\x70"))
(assert (= x_9 (str.++ x_7 literal_8)))
(assert (str.in.re x_9 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_9 "\x61" 0)) (str.len x_9)))
(check-sat)
(get-model)
