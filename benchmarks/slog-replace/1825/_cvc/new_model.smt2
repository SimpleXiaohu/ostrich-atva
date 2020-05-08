(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun sigmaStar_5 () String)
(declare-fun sigmaStar_7 () String)
(declare-fun literal_9 () String)
(declare-fun x_8 () String)
(declare-fun x_10 () String)
(declare-fun sigmaStar_12 () String)
(declare-fun literal_13 () String)
(declare-fun x_14 () String)
(declare-fun literal_16 () String)
(declare-fun x_17 () String)
(assert (= literal_9 "\x5c\x4c\x61\x72\x67\x65\x20"))
(assert (or (= x_8 sigmaStar_7)))
(assert (= x_10 (str.++ literal_9 x_8)))
(assert (= literal_13 "\x2e\x67\x69\x66"))
(assert (= x_14 (str.++ sigmaStar_12 literal_13)))
(assert (= literal_16 "\x2f\x2f"))
(assert (= x_17 (str.++ literal_16 x_14)))
(assert (str.in.re x_17 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_17 "\x61" 0)) (str.len x_17)))
(check-sat)
(get-model)
