(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_5 () String)
(assert (= literal_5 "\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x22\x73\x75\x62\x6d\x69\x74\x22\x20\x6e\x61\x6d\x65\x3d\x22\x73\x75\x62\x6d\x69\x74\x22\x20\x76\x61\x6c\x75\x65\x3d\x22\x73\x61\x76\x65\x63\x68\x61\x6e\x67\x65\x73\x22\x20\x6f\x6e\x63\x6c\x69\x63\x6b\x20\x3d\x20\x22\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x73\x75\x62\x6d\x69\x74\x66\x6f\x72\x6d\x2e\x6d\x65\x6e\x75\x69\x6e\x64\x65\x78\x2e\x76\x61\x6c\x75\x65\x20\x3d\x20\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x73\x75\x62\x6d\x69\x74\x66\x6f\x72\x6d\x2e\x67\x72\x61\x64\x65\x2e\x73\x65\x6c\x65\x63\x74\x65\x64\x49\x6e\x64\x65\x78\x22\x20\x2f\x3e"))
(assert (str.in.re literal_5 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_5  "\x61" 0)) (str.len literal_5 )))
(check-sat)
(get-model)
