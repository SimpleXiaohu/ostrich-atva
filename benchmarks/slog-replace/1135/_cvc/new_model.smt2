(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_9 () String)
(assert (= literal_9 "\x3c\x63\x65\x6e\x74\x65\x72\x3e\x73\x75\x62\x6d\x69\x74\x74\x65\x64\x3a\x20\x3c\x2f\x63\x65\x6e\x74\x65\x72\x3e\x3c\x62\x72\x20\x2f\x3e"))
(assert (str.in.re literal_9 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_9  "\x61" 0)) (str.len literal_9 )))
(check-sat)
(get-model)
