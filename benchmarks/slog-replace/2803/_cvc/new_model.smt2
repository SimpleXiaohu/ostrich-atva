(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_1 () String)
(assert (= literal_1 "\x68\x65\x61\x6c\x74\x68\x6e\x6f\x70\x72\x6f\x62\x6c\x65\x6d\x73\x66\x6f\x75\x6e\x64"))
(assert (str.in.re literal_1 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_1  "\x61" 0)) (str.len literal_1 )))
(check-sat)
(get-model)
