(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_8 () String)
(assert (= literal_8 "\x3c\x70\x3e\x79\x6f\x75\x63\x61\x6e\x64\x65\x6c\x65\x74\x65\x61\x6c\x6c\x72\x65\x70\x65\x61\x74\x73\x3c\x2f\x70\x3e"))
(assert (str.in.re literal_8 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_8  "\x61" 0)) (str.len literal_8 )))
(check-sat)
(get-model)
