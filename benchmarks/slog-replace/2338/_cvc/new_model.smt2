(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_5 () String)
(assert (= literal_5 "\x3c\x74\x72\x3e\x3c\x74\x64\x3e\x3c\x62\x3e\x70\x61\x72\x74\x69\x63\x69\x70\x61\x6e\x74\x73\x3c\x2f\x62\x3e\x3c\x2f\x74\x64\x3e\x3c\x74\x64\x3e"))
(assert (str.in.re literal_5 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_5  "\x61" 0)) (str.len literal_5 )))
(check-sat)
(get-model)
