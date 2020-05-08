(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun literal_3 () String)
(declare-fun x_4 () String)
(declare-fun x_5 () String)
(assert (= literal_3 "\x3f\x61\x64\x64\x72\x65\x73\x73\x3d"))
(assert (or (= x_4 sigmaStar_1) (= x_4 sigmaStar_0)))
(assert (= x_5 (str.++ literal_3 x_4)))
(assert (str.in.re x_5 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_5 "\x61" 0)) (str.len x_5)))
(check-sat)
(get-model)
