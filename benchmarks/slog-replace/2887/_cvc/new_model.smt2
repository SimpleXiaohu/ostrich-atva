(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_5 () String)
(assert (str.in.re sigmaStar_5 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof sigmaStar_5  "\x61" 0)) (str.len sigmaStar_5 )))
(check-sat)
(get-model)
