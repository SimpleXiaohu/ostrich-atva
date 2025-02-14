(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_5 () String)
(declare-fun sigmaStar_6 () String)
(declare-fun sigmaStar_7 () String)
(declare-fun literal_8 () String)
(declare-fun x_11 () String)
(declare-fun literal_9 () String)
(declare-fun x_12 () String)
(declare-fun literal_10 () String)
(declare-fun x_13 () String)
(declare-fun x_16 () String)
(declare-fun literal_1 () String)
(assert (= literal_8 "\x2f\x44\x65\x66\x61\x75\x6c\x74\x2e\x68\x74\x6d"))
(assert (= x_11 (str.++ sigmaStar_5 literal_8)))
(assert (= literal_9 "\x2f\x69\x6e\x64\x65\x78\x2e\x68\x74\x6d\x6c"))
(assert (= x_12 (str.++ sigmaStar_6 literal_9)))
(assert (= literal_10 "\x2f\x69\x6e\x64\x65\x78\x2e\x68\x74\x6d"))
(assert (= x_13 (str.++ sigmaStar_7 literal_10)))
(assert (= literal_1 "\x66\x69\x6c\x65\x2e\x70\x68\x70"))
(assert (or (= x_16 x_11) (= x_16 literal_1) (= x_16 x_13) (= x_16 x_12)))
(assert (str.in.re x_16 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_16 "\x61" 0)) (str.len x_16)))
(check-sat)
(get-model)
