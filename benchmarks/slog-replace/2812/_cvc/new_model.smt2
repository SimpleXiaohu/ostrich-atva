(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun literal_4 () String)
(assert (= literal_4 "\x2f\x62\x6c\x6f\x63\x6b\x73\x2f\x2f\x62\x6c\x6f\x63\x6b\x5f\x2e\x70\x68\x70"))
(assert (str.in.re literal_4 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_4  "\x61" 0)) (str.len literal_4 )))
(check-sat)
(get-model)
