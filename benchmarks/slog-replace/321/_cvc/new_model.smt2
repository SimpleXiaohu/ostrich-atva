(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_5 () String)
(assert (= literal_5 "\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x5c\x22\x73\x75\x62\x6d\x69\x74\x5c\x22\x20\x76\x61\x6c\x75\x65\x3d\x5c\x22\x6d\x6f\x76\x65\x66\x69\x6c\x65\x73\x74\x6f\x68\x65\x72\x65\x5c\x22\x20\x2f\x3e\x5c\x6e"))
(assert (str.in.re literal_5 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_5  "\x61" 0)) (str.len literal_5 )))
(check-sat)
(get-model)
