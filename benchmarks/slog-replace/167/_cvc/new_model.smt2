(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun literal_4 () String)
(declare-fun x_5 () String)
(declare-fun x_6 () String)
(assert (= literal_4 "\x27\x5d\x2e"))
(assert (= x_5 (str.++ sigmaStar_3 literal_4)))
(assert (= x_6 (str.++ x_5 sigmaStar_3)))
(assert (str.in.re x_6 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_6 "\x61" 0)) (str.len x_6)))
(check-sat)
(get-model)
