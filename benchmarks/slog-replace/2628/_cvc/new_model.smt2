(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_9 () String)
(assert (= literal_9 "\x2f\x2f\x6c\x61\x6e\x67\x64\x6f\x63\x2e\x70\x68\x70\x3f\x73\x65\x73\x73\x6b\x65\x79\x3d\x26\x61\x6d\x70\x3b\x63\x75\x72\x72\x65\x6e\x74\x66\x69\x6c\x65\x3d"))
(assert (str.in.re literal_9 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_9  "\x61" 0)) (str.len literal_9 )))
(check-sat)
(get-model)
