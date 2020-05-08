(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_4 () String)
(declare-fun literal_10 () String)
(assert (= literal_10 "\x2f\x6d\x6f\x64\x2f\x67\x6c\x6f\x73\x73\x61\x72\x79\x2f\x66\x6f\x72\x6d\x61\x74\x73\x2f\x6d\x6f\x64\x2f\x67\x6c\x6f\x73\x73\x61\x72\x79\x2f\x66\x6f\x72\x6d\x61\x74\x73\x2f\x6d\x6f\x64\x2f\x67\x6c\x6f\x73\x73\x61\x72\x79\x2f\x66\x6f\x72\x6d\x61\x74\x73\x5f\x66\x6f\x72\x6d\x61\x74\x2e\x70\x68\x70"))
(assert (str.in.re literal_10 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_10  "\x61" 0)) (str.len literal_10 )))
(check-sat)
(get-model)
