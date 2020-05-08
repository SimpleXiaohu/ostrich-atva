(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_1 () String)
(declare-fun x_2 () String)
(assert (= literal_1 "\x3c\x2f\x74\x64\x3e\x3c\x2f\x74\x72\x3e\x5c\x6e\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x5c\x6e"))
(assert (= x_2 (str.++ sigmaStar_0 literal_1)))
(assert (str.in.re x_2 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_2 "\x61" 0)) (str.len x_2)))
(check-sat)
(get-model)
