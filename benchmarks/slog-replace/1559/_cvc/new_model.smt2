(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun literal_2 () String)
(assert (= literal_2 "\x2f\x6d\x6f\x64\x2f\x64\x61\x74\x61\x2f\x66\x69\x65\x6c\x64\x2f\x2f\x66\x69\x65\x6c\x64\x2e\x63\x6c\x61\x73\x73\x2e\x70\x68\x70"))
(assert (str.in.re literal_2 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_2  "\x61" 0)) (str.len literal_2 )))
(check-sat)
(get-model)
