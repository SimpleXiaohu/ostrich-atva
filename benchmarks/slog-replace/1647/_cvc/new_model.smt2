(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_10 () String)
(assert (= literal_10 "\x3c\x64\x69\x76\x20\x63\x6c\x61\x73\x73\x3d\x5c\x22\x72\x65\x70\x6f\x72\x74\x6c\x69\x6e\x6b\x5c\x22\x3e\x3c\x61\x20\x74\x61\x72\x67\x65\x74\x3d\x5c\x22\x5c\x22\x20\x68\x72\x65\x66\x3d\x5c\x22\x72\x65\x70\x6f\x72\x74\x2e\x70\x68\x70\x3f\x69\x64\x3d\x5c\x22\x3e\x76\x69\x65\x77\x61\x6c\x6c\x72\x65\x70\x6f\x72\x74\x73\x3c\x2f\x61\x3e\x3c\x2f\x64\x69\x76\x3e"))
(assert (str.in.re literal_10 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_10  "\x61" 0)) (str.len literal_10 )))
(check-sat)
(get-model)
