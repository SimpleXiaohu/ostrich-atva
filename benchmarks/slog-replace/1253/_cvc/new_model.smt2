(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_9 () String)
(assert (= literal_9 "\x3c\x61\x20\x68\x72\x65\x66\x3d\x22\x2f\x75\x73\x65\x72\x2f\x76\x69\x65\x77\x2e\x70\x68\x70\x3f\x69\x64\x3d\x26\x61\x6d\x70\x3b\x63\x6f\x75\x72\x73\x65\x3d\x22\x3e\x3c\x2f\x61\x3e\x3c\x62\x72\x20\x2f\x3e"))
(assert (str.in.re literal_9 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_9  "\x61" 0)) (str.len literal_9 )))
(check-sat)
(get-model)
