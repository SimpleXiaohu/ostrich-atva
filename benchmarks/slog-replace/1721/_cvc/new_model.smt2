(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun literal_13 () String)
(assert (= literal_13 "\x3c\x61\x20\x68\x72\x65\x66\x3d\x5c\x22\x72\x65\x70\x6f\x72\x74\x2e\x70\x68\x70\x3f\x6d\x6f\x64\x65\x3d\x6f\x76\x65\x72\x76\x69\x65\x77\x26\x61\x6d\x70\x3b\x69\x64\x3d\x5c\x22\x3e\x6e\x75\x6d\x61\x74\x74\x65\x6d\x70\x74\x73\x3c\x2f\x61\x3e\x3c\x62\x72\x20\x2f\x3e\x61\x74\x74\x65\x6d\x70\x74\x73\x65\x78\x69\x73\x74"))
(assert (str.in.re literal_13 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_13  "\x61" 0)) (str.len literal_13 )))
(check-sat)
(get-model)
