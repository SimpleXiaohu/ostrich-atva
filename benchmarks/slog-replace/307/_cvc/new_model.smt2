(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun literal_15 () String)
(assert (= literal_15 "\x3c\x74\x72\x3e\x5c\x6e\x3c\x74\x68\x20\x61\x6c\x69\x67\x6e\x3d\x5c\x22\x6c\x65\x66\x74\x5c\x22\x3e\x6e\x61\x6d\x65\x3c\x2f\x74\x68\x3e\x3c\x74\x68\x20\x61\x6c\x69\x67\x6e\x3d\x5c\x22\x72\x69\x67\x68\x74\x5c\x22\x3e\x73\x69\x7a\x65\x3c\x2f\x74\x68\x3e\x3c\x74\x68\x20\x61\x6c\x69\x67\x6e\x3d\x5c\x22\x72\x69\x67\x68\x74\x5c\x22\x3e\x6d\x6f\x64\x69\x66\x69\x65\x64\x3c\x2f\x74\x68\x3e\x3c\x2f\x74\x72\x3e"))
(assert (str.in.re literal_15 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_15  "\x61" 0)) (str.len literal_15 )))
(check-sat)
(get-model)
