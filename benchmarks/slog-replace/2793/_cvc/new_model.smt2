(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_8 () String)
(assert (= literal_8 "\x3c\x64\x69\x76\x20\x63\x6c\x61\x73\x73\x3d\x22\x72\x65\x70\x6f\x72\x74\x6c\x69\x6e\x6b\x22\x3e\x3c\x61\x20\x68\x72\x65\x66\x3d\x22\x65\x6e\x76\x69\x72\x6f\x6e\x6d\x65\x6e\x74\x2e\x70\x68\x70\x3f\x61\x63\x74\x69\x6f\x6e\x3d\x75\x70\x64\x61\x74\x65\x63\x6f\x6d\x70\x6f\x6e\x65\x6e\x74\x26\x61\x6d\x70\x3b\x73\x65\x73\x73\x6b\x65\x79\x3d\x22\x3e\x75\x70\x64\x61\x74\x65\x63\x6f\x6d\x70\x6f\x6e\x65\x6e\x74\x3c\x2f\x61\x3e\x3c\x2f\x64\x69\x76\x3e"))
(assert (str.in.re literal_8 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_8  "\x61" 0)) (str.len literal_8 )))
(check-sat)
(get-model)
