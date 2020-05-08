(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_1 () String)
(declare-fun x_2 () String)
(declare-fun literal_3 () String)
(declare-fun x_4 () String)
(assert (= literal_1 "\x3c\x66\x6f\x72\x6d\x20\x61\x63\x74\x69\x6f\x6e\x3d\x5c\x22\x63\x6f\x75\x72\x73\x65\x66\x69\x6c\x65\x73\x2e\x70\x68\x70\x5c\x22\x20\x6d\x65\x74\x68\x6f\x64\x3d\x5c\x22\x70\x6f\x73\x74\x5c\x22\x20\x6e\x61\x6d\x65\x3d\x5c\x22\x66\x6f\x72\x6d\x5c\x22\x20"))
(assert (= x_2 (str.++ literal_1 sigmaStar_0)))
(assert (= literal_3 "\x3e\x5c\x6e"))
(assert (= x_4 (str.++ x_2 literal_3)))
(assert (str.in.re x_4 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_4 "\x61" 0)) (str.len x_4)))
(check-sat)
(get-model)
