(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_11 () String)
(assert (= literal_11 "\x3c\x66\x6f\x72\x6d\x20\x61\x63\x74\x69\x6f\x6e\x3d\x22\x69\x6e\x64\x65\x78\x2e\x70\x68\x70\x22\x20\x6d\x65\x74\x68\x6f\x64\x3d\x22\x70\x6f\x73\x74\x22\x3e\x5c\x6e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x22\x68\x69\x64\x64\x65\x6e\x22\x20\x6e\x61\x6d\x65\x3d\x22\x6d\x6f\x64\x65\x22\x20\x76\x61\x6c\x75\x65\x3d\x22\x6d\x6f\x64\x65\x22\x20\x2f\x3e\x5c\x6e"))
(assert (str.in.re literal_11 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_11  "\x61" 0)) (str.len literal_11 )))
(check-sat)
(get-model)
