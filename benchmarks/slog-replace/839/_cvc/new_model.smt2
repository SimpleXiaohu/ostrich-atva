(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_5 () String)
(declare-fun literal_7 () String)
(declare-fun x_8 () String)
(declare-fun sigmaStar_11 () String)
(declare-fun sigmaStar_14 () String)
(declare-fun literal_12 () String)
(declare-fun x_15 () String)
(declare-fun sigmaStar_16 () String)
(declare-fun sigmaStar_17 () String)
(declare-fun literal_18 () String)
(declare-fun x_19 () String)
(declare-fun x_20 () String)
(assert (= literal_7 "\x2e"))
(assert (= x_8 (str.++ literal_7 sigmaStar_5)))
(assert (= literal_12 "\x2f\x74\x65\x6d\x70\x2f\x6d\x6f\x64\x75\x6c\x65\x73\x2f"))
(assert (= x_15 (str.++ literal_12 sigmaStar_14)))
(assert (= literal_18 "\x2f"))
(assert (= x_19 (str.++ x_15 literal_18)))
(assert (= x_20 (str.++ x_19 sigmaStar_17)))
(assert (str.in.re x_20 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_20 "\x61" 0)) (str.len x_20)))
(check-sat)
(get-model)
