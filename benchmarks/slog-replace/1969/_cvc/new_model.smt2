(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_12 () String)
(assert (= literal_12 "\x3c\x61\x20\x68\x72\x65\x66\x3d\x22\x65\x64\x69\x74\x2e\x70\x68\x70\x3f\x63\x6f\x75\x72\x73\x65\x69\x64\x3d\x26\x61\x6d\x70\x3b\x70\x65\x72\x70\x61\x67\x65\x3d\x32\x30\x22\x3e\x73\x68\x6f\x77\x70\x65\x72\x70\x61\x67\x65\x3c\x2f\x61\x3e"))
(assert (str.in.re literal_12 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_12  "\x61" 0)) (str.len literal_12 )))
(check-sat)
(get-model)
