(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_16 () String)
(assert (= literal_16 "\x3c\x6c\x69\x3e\x3c\x69\x6d\x67\x20\x73\x72\x63\x3d\x5c\x22\x69\x6d\x61\x67\x65\x73\x2f\x69\x6d\x73\x2e\x67\x69\x66\x5c\x22\x20\x61\x6c\x74\x3d\x5c\x22\x49\x4d\x53\x20\x43\x50\x20\x50\x61\x63\x6b\x61\x67\x65\x5c\x22\x20\x2f\x3e\x20\x3c\x65\x6d\x3e\x20\x2d\x20\x6e\x6f\x74\x64\x65\x70\x6c\x6f\x79\x65\x64\x3c\x2f\x65\x6d\x3e\x20\x28\x3c\x61\x20\x68\x72\x65\x66\x3d\x5c\x22\x72\x65\x70\x6f\x73\x69\x74\x6f\x72\x79\x5f\x64\x65\x70\x6c\x6f\x79\x2e\x70\x68\x70\x3f\x66\x69\x6c\x65\x3d\x5c\x22\x3e\x64\x65\x70\x6c\x6f\x79\x3c\x2f\x61\x3e\x29\x3c\x2f\x6c\x69\x3e\x5c\x6e"))
(assert (str.in.re literal_16 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_16  "\x61" 0)) (str.len literal_16 )))
(check-sat)
(get-model)
