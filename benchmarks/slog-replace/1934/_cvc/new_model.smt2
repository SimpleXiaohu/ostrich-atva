(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_12 () String)
(assert (= literal_12 "\x3c\x61\x20\x68\x72\x65\x66\x3d\x5c\x22\x2f\x71\x75\x65\x73\x74\x69\x6f\x6e\x2f\x65\x78\x70\x6f\x72\x74\x2e\x70\x68\x70\x3f\x63\x61\x74\x65\x67\x6f\x72\x79\x3d\x26\x61\x6d\x70\x3b\x63\x6f\x75\x72\x73\x65\x69\x64\x3d\x5c\x22\x3e\x65\x78\x70\x6f\x72\x74\x71\x75\x65\x73\x74\x69\x6f\x6e\x73\x3c\x2f\x61\x3e"))
(assert (str.in.re literal_12 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_12  "\x61" 0)) (str.len literal_12 )))
(check-sat)
(get-model)
