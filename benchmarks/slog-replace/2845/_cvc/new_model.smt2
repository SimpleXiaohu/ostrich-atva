(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun literal_4 () String)
(assert (= literal_4 "\x68\x65\x6c\x70"))
(assert (str.in.re literal_4 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_4  "\x61" 0)) (str.len literal_4 )))
(check-sat)
(get-model)
