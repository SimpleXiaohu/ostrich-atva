(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun sigmaStar_11 () String)
(declare-fun literal_12 () String)
(declare-fun x_14 () String)
(declare-fun literal_13 () String)
(declare-fun x_15 () String)
(declare-fun literal_16 () String)
(declare-fun x_17 () String)
(declare-fun x_18 () String)
(declare-fun x_19 () String)
(declare-fun literal_20 () String)
(declare-fun x_21 () String)
(declare-fun x_22 () String)
(declare-fun literal_23 () String)
(declare-fun x_24 () String)
(assert (= literal_12 "\x3c\x2f\x74\x72\x3e\x5c\x6e\x3c\x74\x72\x3e\x5c\x6e\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x63\x6f\x6c\x73\x70\x61\x6e\x3d\x27"))
(assert (= x_14 (str.++ literal_12 sigmaStar_1)))
(assert (= literal_13 "\x3f\x61\x69\x64\x3d"))
(assert (= x_15 (str.++ literal_13 sigmaStar_11)))
(assert (= literal_16 "\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x32\x27\x3e\x3c\x61\x20\x68\x72\x65\x66\x3d\x27\x70\x68\x6f\x74\x6f\x61\x6c\x62\x75\x6d\x73\x2e\x70\x68\x70"))
(assert (= x_17 (str.++ x_14 literal_16)))
(assert (or (= x_18 sigmaStar_0) (= x_18 x_15)))
(assert (= x_19 (str.++ x_17 x_18)))
(assert (= literal_20 "\x27\x3e"))
(assert (= x_21 (str.++ x_19 literal_20)))
(assert (= x_22 (str.++ x_21 sigmaStar_2)))
(assert (= literal_23 "\x3c\x2f\x61\x3e\x3c\x2f\x74\x64\x3e\x5c\x6e\x3c\x2f\x74\x72\x3e\x5c\x6e\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x5c\x6e"))
(assert (= x_24 (str.++ x_22 literal_23)))
(assert (str.in.re x_24 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_24 "\x61" 0)) (str.len x_24)))
(check-sat)
(get-model)
