(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun sigmaStar_4 () String)
(declare-fun sigmaStar_5 () String)
(declare-fun literal_26 () String)
(assert (= literal_26 "\x66\x69\x72\x73\x74\x6e\x61\x6d\x65\x5c\x74\x6c\x61\x73\x74\x6e\x61\x6d\x65\x5c\x74\x69\x64\x6e\x75\x6d\x62\x65\x72\x5c\x74\x69\x6e\x73\x74\x69\x74\x75\x74\x69\x6f\x6e\x5c\x74\x64\x65\x70\x61\x72\x74\x6d\x65\x6e\x74\x5c\x74\x65\x6d\x61\x69\x6c"))
(assert (str.in.re literal_26 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_26  "\x61" 0)) (str.len literal_26 )))
(check-sat)
(get-model)
