(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_1 () String)
(declare-fun x_2 () String)
(declare-fun literal_3 () String)
(declare-fun x_4 () String)
(assert (= literal_1 "\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x5c\x22\x68\x69\x64\x64\x65\x6e\x5c\x22\x20\x6e\x61\x6d\x65\x3d\x5c\x22\x61\x63\x74\x69\x6f\x6e\x5c\x22\x20\x76\x61\x6c\x75\x65\x3d\x5c\x22\x69\x6e\x73\x74\x61\x6c\x6c\x5c\x22\x3e\x5c\x6e\x0d\x0a\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x5c\x22\x68\x69\x64\x64\x65\x6e\x5c\x22\x20\x6e\x61\x6d\x65\x3d\x5c\x22\x70\x6c\x75\x67\x69\x6e\x5f\x66\x69\x6c\x65\x5c\x22\x20\x76\x61\x6c\x75\x65\x3d\x5c\x22"))
(assert (= x_2 (str.++ literal_1 sigmaStar_0)))
(assert (= literal_3 "\x5c\x22\x3e\x5c\x6e\x0d\x0a\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x5c\x22\x73\x75\x62\x6d\x69\x74\x5c\x22\x20\x6e\x61\x6d\x65\x3d\x5c\x22\x70\x6c\x75\x67\x69\x6e\x5f\x76\x61\x72\x69\x61\x62\x6c\x65\x73\x5f\x73\x65\x74\x5c\x22\x20\x76\x61\x6c\x75\x65\x3d\x5c\x22\x53\x75\x62\x6d\x69\x74\x5c\x22\x3e\x5c\x6e\x3c\x2f\x66\x6f\x72\x6d\x3e"))
(assert (= x_4 (str.++ x_2 literal_3)))
(assert (str.in.re x_4 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_4 "\x61" 0)) (str.len x_4)))
(check-sat)
(get-model)
