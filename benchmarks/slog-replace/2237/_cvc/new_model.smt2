(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_6 () String)
(assert (= literal_6 "\x3c\x63\x65\x6e\x74\x65\x72\x3e\x3c\x66\x6f\x6e\x74\x20\x63\x6f\x6c\x6f\x72\x3d\x22\x72\x65\x64\x22\x3e\x65\x72\x72\x6f\x72\x67\x72\x61\x64\x65\x76\x61\x6c\x75\x65\x6e\x6f\x6e\x6e\x75\x6d\x65\x72\x69\x63\x3c\x2f\x66\x6f\x6e\x74\x3e\x3c\x2f\x63\x65\x6e\x74\x65\x72\x3e"))
(assert (str.in.re literal_6 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_6  "\x61" 0)) (str.len literal_6 )))
(check-sat)
(get-model)
