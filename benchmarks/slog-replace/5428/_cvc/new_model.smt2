(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_3 () String)
(declare-fun x_4 () String)
(assert (= literal_3 "\x69\x6e\x63\x6c\x75\x64\x65\x2f"))
(assert (= x_4 (str.++ literal_3 sigmaStar_0)))
(assert (str.in.re x_4 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_4 "\x61" 0)) (str.len x_4)))
(check-sat)
(get-model)
