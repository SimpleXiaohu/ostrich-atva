(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_6 () String)
(assert (= literal_6 "\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x22\x73\x75\x62\x6d\x69\x74\x22\x20\x76\x61\x6c\x75\x65\x3d\x22\x72\x65\x70\x6f\x72\x74\x62\x75\x74\x74\x6f\x6e\x22\x3e\x3c\x2f\x74\x64\x3e\x3c\x2f\x74\x72\x3e"))
(assert (str.in.re literal_6 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_6  "\x61" 0)) (str.len literal_6 )))
(check-sat)
(get-model)
