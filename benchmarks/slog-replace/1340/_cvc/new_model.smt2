(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_4 () String)
(declare-fun literal_8 () String)
(assert (= literal_8 "\x3c\x74\x64\x20\x63\x6c\x61\x73\x73\x3d\x22\x63\x31\x22\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x22\x74\x65\x78\x74\x22\x20\x73\x69\x7a\x65\x3d\x22\x33\x35\x22\x20\x6e\x61\x6d\x65\x3d\x22\x6e\x6f\x74\x77\x6f\x72\x64\x73\x22\x20\x76\x61\x6c\x75\x65\x3d\x22\x6e\x6f\x74\x77\x6f\x72\x64\x73\x22\x20\x61\x6c\x74\x3d\x22\x22\x3e\x3c\x2f\x74\x64\x3e"))
(assert (str.in.re literal_8 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_8  "\x61" 0)) (str.len literal_8 )))
(check-sat)
(get-model)
