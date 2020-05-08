(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_4 () String)
(assert (= literal_4 "\x63\x68\x6f\x6f\x73\x65\x2f\x52\x45\x41\x44\x4d\x45\x2e\x68\x74\x6d\x6c"))
(assert (str.in.re literal_4 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_4  "\x61" 0)) (str.len literal_4 )))
(check-sat)
(get-model)
