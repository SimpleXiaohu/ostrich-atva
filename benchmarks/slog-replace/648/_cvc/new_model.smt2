(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_11 () String)
(assert (= literal_11 "\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x22\x73\x75\x62\x6d\x69\x74\x22\x20\x76\x61\x6c\x75\x65\x3d\x22\x67\x6f\x22\x20\x2f\x3e\x5c\x6e\x3c\x2f\x74\x64\x3e\x3c\x2f\x74\x72\x3e\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x5c\x6e\x3c\x2f\x66\x6f\x72\x6d\x3e\x5c\x6e"))
(assert (str.in.re literal_11 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_11  "\x61" 0)) (str.len literal_11 )))
(check-sat)
(get-model)
