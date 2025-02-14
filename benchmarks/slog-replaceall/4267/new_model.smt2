(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun sigmaStar_6 () String)
(declare-fun sigmaStar_8 () String)
(declare-fun literal_9 () String)
(declare-fun x_7 () String)
(declare-fun x_10 () String)
(declare-fun literal_11 () String)
(declare-fun x_12 () String)
(assert (= x_7 (str.replaceall sigmaStar_1 "\x2c" "\x20")))
(assert (= literal_9 "\x3c\x73\x70\x61\x6e\x20\x63\x6c\x61\x73\x73\x3d\x27\x73\x6d\x61\x6c\x6c\x32\x27\x3e"))
(assert (= x_10 (str.++ literal_9 sigmaStar_8)))
(assert (= literal_11 "\x3c\x2f\x73\x70\x61\x6e\x3e"))
(assert (= x_12 (str.++ x_10 literal_11)))
(assert (str.in.re x_12 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (> (* 2 (str.indexof x_7 "\x61" 0)) (str.len x_7)))
(check-sat)
(get-model)
