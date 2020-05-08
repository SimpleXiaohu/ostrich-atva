(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_1 () String)
(declare-fun x_2 () String)
(declare-fun literal_3 () String)
(declare-fun x_5 () String)
(declare-fun literal_4 () String)
(declare-fun x_6 () String)
(assert (= literal_1 "\x23\x20\x44\x61\x74\x61\x62\x61\x73\x65\x20\x4e\x61\x6d\x65\x3a\x20\x60"))
(assert (= x_2 (str.++ literal_1 sigmaStar_0)))
(assert (= literal_3 "\x60"))
(assert (= x_5 (str.++ x_2 literal_3)))
(assert (= literal_4 "\x5c\x6e"))
(assert (= x_6 (str.++ x_5 literal_4)))
(assert (str.in.re x_6 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_6 "\x61" 0)) (str.len x_6)))
(check-sat)
(get-model)
