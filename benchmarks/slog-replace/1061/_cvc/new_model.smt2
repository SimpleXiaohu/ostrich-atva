(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_7 () String)
(assert (= literal_7 "\x20\x6f\x6e\x3c\x2f\x62\x3e\x3c\x2f\x70\x3e\x3c\x2f\x74\x64\x3e\x3c\x2f\x74\x72\x3e\x3c\x74\x72\x3e\x3c\x74\x64\x3e\x5c\x6e"))
(assert (str.in.re literal_7 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_7  "\x61" 0)) (str.len literal_7 )))
(check-sat)
(get-model)
