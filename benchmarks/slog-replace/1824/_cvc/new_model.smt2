(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_18 () String)
(declare-fun literal_19 () String)
(declare-fun x_20 () String)
(declare-fun literal_21 () String)
(declare-fun x_22 () String)
(assert (= literal_19 "\x54\x68\x65\x20\x6d\x64\x35\x20\x63\x68\x65\x63\x6b\x73\x75\x6d\x20\x6f\x66\x20\x74\x68\x65\x20\x66\x69\x6c\x65\x20\x69\x73\x20"))
(assert (= x_20 (str.++ literal_19 sigmaStar_18)))
(assert (= literal_21 "\x3c\x62\x72\x20\x2f\x3e"))
(assert (= x_22 (str.++ x_20 literal_21)))
(assert (str.in.re x_22 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_22 "\x61" 0)) (str.len x_22)))
(check-sat)
(get-model)
