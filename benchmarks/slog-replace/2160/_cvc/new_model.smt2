(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_1 () String)
(declare-fun x_2 () String)
(declare-fun literal_3 () String)
(declare-fun x_4 () String)
(assert (= literal_1 "\x3c\x6d\x65\x74\x61\x20\x68\x74\x74\x70\x2d\x65\x71\x75\x69\x76\x3d\x22\x63\x6f\x6e\x74\x65\x6e\x74\x2d\x74\x79\x70\x65\x22\x20\x63\x6f\x6e\x74\x65\x6e\x74\x3d\x22\x74\x65\x78\x74\x2f\x68\x74\x6d\x6c\x3b\x20\x63\x68\x61\x72\x73\x65\x74\x3d"))
(assert (= x_2 (str.++ literal_1 sigmaStar_0)))
(assert (= literal_3 "\x22\x20\x2f\x3e"))
(assert (= x_4 (str.++ x_2 literal_3)))
(assert (str.in.re x_4 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_4 "\x61" 0)) (str.len x_4)))
(check-sat)
(get-model)
