(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_8 () String)
(assert (= literal_8 "\x3c\x66\x6f\x72\x6d\x20\x6e\x61\x6d\x65\x3d\x22\x74\x65\x6d\x70\x66\x6f\x72\x6d\x22\x20\x61\x63\x74\x69\x6f\x6e\x3d\x22\x74\x65\x6d\x70\x6c\x61\x74\x65\x73\x2e\x70\x68\x70\x3f\x64\x3d\x26\x61\x6d\x70\x3b\x6d\x6f\x64\x65\x3d\x6d\x6f\x64\x65\x22\x20\x6d\x65\x74\x68\x6f\x64\x3d\x22\x70\x6f\x73\x74\x22\x3e"))
(assert (str.in.re literal_8 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_8  "\x61" 0)) (str.len literal_8 )))
(check-sat)
(get-model)
