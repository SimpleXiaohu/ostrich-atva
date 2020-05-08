(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_1 () String)
(declare-fun x_2 () String)
(declare-fun literal_3 () String)
(declare-fun x_4 () String)
(assert (= literal_1 "\x3c\x73\x63\x72\x69\x70\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x2f\x6a\x61\x76\x61\x73\x63\x72\x69\x70\x74\x27\x3e\x0d\x0a\x66\x75\x6e\x63\x74\x69\x6f\x6e\x20\x44\x65\x6c\x65\x74\x65\x49\x74\x65\x6d\x28\x29\x20\x7b\x0d\x0a\x09\x72\x65\x74\x75\x72\x6e\x20\x63\x6f\x6e\x66\x69\x72\x6d\x28\x27"))
(assert (= x_2 (str.++ literal_1 sigmaStar_0)))
(assert (= literal_3 "\x27\x29\x3b\x0d\x0a\x7d\x0d\x0a\x3c\x2f\x73\x63\x72\x69\x70\x74\x3e\x5c\x6e"))
(assert (= x_4 (str.++ x_2 literal_3)))
(assert (str.in.re x_4 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_4 "\x61" 0)) (str.len x_4)))
(check-sat)
(get-model)
