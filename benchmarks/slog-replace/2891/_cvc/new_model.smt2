(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun sigmaStar_8 () String)
(declare-fun sigmaStar_9 () String)
(declare-fun literal_10 () String)
(declare-fun x_4 () String)
(declare-fun x_11 () String)
(declare-fun literal_12 () String)
(declare-fun x_14 () String)
(declare-fun literal_13 () String)
(declare-fun x_15 () String)
(declare-fun literal_16 () String)
(declare-fun x_17 () String)
(declare-fun sigmaStar_18 () String)
(assert (= x_4 (str.replace sigmaStar_0 "\x2f\x5b\x5e\x30\x2d\x39\x61\x2d\x7a\x5c\x2d\x5f\x2c\x5d\x2b\x2f\x69" "")))
(assert (= literal_10 "\x70\x6c\x75\x67\x69\x6e\x73\x2f"))
(assert (= x_11 (str.++ literal_10 sigmaStar_8)))
(assert (= literal_12 "\x2f\x65\x64\x69\x74\x6f\x72\x5f\x70\x6c\x75\x67\x69\x6e"))
(assert (= x_14 (str.++ x_11 literal_12)))
(assert (= literal_13 ""))
(assert (= x_15 (str.++ x_14 literal_13)))
(assert (= literal_16 "\x2e\x6a\x73"))
(assert (= x_17 (str.++ x_15 literal_16)))
(assert (str.in.re sigmaStar_18 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_17 "\x61" 0)) (str.len x_17)))
(check-sat)
(get-model)
