(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_5 () String)
(assert (= literal_5 "\x3c\x63\x65\x6e\x74\x65\x72\x3e\x61\x64\x6d\x69\x6e\x68\x65\x6c\x70\x65\x6e\x76\x69\x72\x6f\x6e\x6d\x65\x6e\x74\x3c\x2f\x63\x65\x6e\x74\x65\x72\x3e\x3c\x62\x72\x20\x2f\x3e"))
(assert (str.in.re literal_5 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_5  "\x61" 0)) (str.len literal_5 )))
(check-sat)
(get-model)
