(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun literal_4 () String)
(declare-fun x_5 () String)
(declare-fun literal_6 () String)
(declare-fun x_7 () String)
(declare-fun x_8 () String)
(declare-fun x_9 () String)
(declare-fun literal_10 () String)
(declare-fun x_11 () String)
(declare-fun x_12 () String)
(declare-fun literal_13 () String)
(declare-fun x_14 () String)
(assert (= literal_4 "\x3c\x62\x72\x3e\x3c\x62\x72\x3e\x0d\x0a\x3c\x61\x20\x68\x72\x65\x66\x3d\x27\x76\x69\x65\x77\x66\x6f\x72\x75\x6d\x2e\x70\x68\x70\x3f\x66\x6f\x72\x75\x6d\x5f\x69\x64\x3d"))
(assert (= x_5 (str.++ literal_4 sigmaStar_2)))
(assert (= literal_6 "\x27\x3e"))
(assert (= x_7 (str.++ x_5 literal_6)))
(assert (= x_8 (str.++ sigmaStar_3 x_7)))
(assert (= x_9 (str.++ x_8 sigmaStar_1)))
(assert (= literal_10 "\x3c\x2f\x61\x3e\x3c\x62\x72\x3e\x3c\x62\x72\x3e\x0d\x0a\x3c\x61\x20\x68\x72\x65\x66\x3d\x27\x69\x6e\x64\x65\x78\x2e\x70\x68\x70\x27\x3e"))
(assert (= x_11 (str.++ x_9 literal_10)))
(assert (= x_12 (str.++ x_11 sigmaStar_0)))
(assert (= literal_13 "\x3c\x2f\x61\x3e\x3c\x62\x72\x3e\x3c\x62\x72\x3e\x5c\x6e"))
(assert (= x_14 (str.++ x_12 literal_13)))
(assert (str.in.re x_14 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_14 "\x61" 0)) (str.len x_14)))
(check-sat)
(get-model)
