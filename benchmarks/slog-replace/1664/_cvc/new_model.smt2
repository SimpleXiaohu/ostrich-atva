(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun literal_0 () String)
(assert (= literal_0 "\x2f\x6d\x6f\x64\x2f\x72\x65\x73\x6f\x75\x72\x63\x65\x2f\x74\x79\x70\x65\x2f\x69\x6d\x73\x2f\x72\x65\x70\x6f\x73\x69\x74\x6f\x72\x79\x5f\x63\x6f\x6e\x66\x69\x67\x2e\x70\x68\x70"))
(assert (str.in.re literal_0 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_0  "\x61" 0)) (str.len literal_0 )))
(check-sat)
(get-model)
