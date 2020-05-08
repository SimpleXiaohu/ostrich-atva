(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_4 () String)
(declare-fun sigmaStar_7 () String)
(declare-fun sigmaStar_11 () String)
(declare-fun x_8 () String)
(declare-fun literal_13 () String)
(declare-fun x_12 () String)
(declare-fun x_14 () String)
(declare-fun literal_15 () String)
(declare-fun x_16 () String)
(declare-fun x_19 () String)
(declare-fun epsilon () String)
(assert (or (= x_8 sigmaStar_1) (= x_8 sigmaStar_7)))
(assert (= x_12 (str.replaceall x_8 "\x2e\x67\x69\x66" "")))
(assert (= literal_13 "\x2f"))
(assert (= x_14 (str.++ literal_13 x_12)))
(assert (= literal_15 "\x2e\x67\x69\x66"))
(assert (= x_16 (str.++ x_14 literal_15)))
(assert (= epsilon ""))
(assert (or (= x_19 epsilon) (= x_19 x_16)))
(assert (str.in.re x_19 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (> (* 2 (str.indexof x_14 "\x61" 0)) (str.len x_14)))
(check-sat)
(get-model)
