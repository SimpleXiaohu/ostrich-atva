(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_13 () String)
(assert (= literal_13 "\x20\x3c\x61\x20\x68\x72\x65\x66\x3d\x5c\x22\x75\x73\x65\x72\x73\x2e\x70\x68\x70\x3f\x63\x68\x61\x74\x5f\x73\x69\x64\x3d\x63\x68\x61\x74\x5f\x73\x69\x64\x26\x61\x6d\x70\x3b\x62\x65\x65\x70\x3d\x5c\x22\x3e\x62\x65\x65\x70\x3c\x2f\x61\x3e"))
(assert (str.in.re literal_13 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_13  "\x61" 0)) (str.len literal_13 )))
(check-sat)
(get-model)
