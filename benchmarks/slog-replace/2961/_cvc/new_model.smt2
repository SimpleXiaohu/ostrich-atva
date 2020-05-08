(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun literal_7 () String)
(declare-fun x_8 () String)
(declare-fun literal_9 () String)
(declare-fun x_10 () String)
(declare-fun literal_11 () String)
(declare-fun x_12 () String)
(declare-fun literal_13 () String)
(declare-fun x_14 () String)
(declare-fun x_15 () String)
(declare-fun literal_16 () String)
(declare-fun x_17 () String)
(declare-fun literal_18 () String)
(declare-fun x_19 () String)
(declare-fun literal_20 () String)
(declare-fun x_21 () String)
(declare-fun x_22 () String)
(declare-fun literal_23 () String)
(declare-fun x_24 () String)
(assert (= literal_7 "\x3c\x69\x6d\x67\x20\x73\x72\x63\x3d\x27\x69\x6d\x61\x67\x65\x73\x2f\x62\x75\x6c\x6c\x65\x74\x2e\x67\x69\x66\x27\x20\x61\x6c\x74\x3d\x27\x27\x3e\x20\x3c\x61\x20\x68\x72\x65\x66\x3d\x27\x65\x64\x69\x74\x5f\x70\x72\x6f\x66\x69\x6c\x65\x2e\x70\x68\x70\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x73\x69\x64\x65\x27\x3e"))
(assert (= x_8 (str.++ literal_7 sigmaStar_1)))
(assert (= literal_9 "\x3c\x2f\x61\x3e\x3c\x62\x72\x3e\x0d\x0a\x3c\x69\x6d\x67\x20\x73\x72\x63\x3d\x27"))
(assert (= x_10 (str.++ x_8 literal_9)))
(assert (= literal_11 "\x69\x6d\x61\x67\x65\x73\x2f\x62\x75\x6c\x6c\x65\x74\x2e\x67\x69\x66\x27\x20\x61\x6c\x74\x3d\x27\x27\x3e\x20\x3c\x61\x20\x68\x72\x65\x66\x3d\x27"))
(assert (= x_12 (str.++ x_10 literal_11)))
(assert (= literal_13 "\x6d\x65\x73\x73\x61\x67\x65\x73\x2e\x70\x68\x70\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x73\x69\x64\x65\x27\x3e"))
(assert (= x_14 (str.++ x_12 literal_13)))
(assert (= x_15 (str.++ x_14 sigmaStar_0)))
(assert (= literal_16 "\x3c\x2f\x61\x3e\x3c\x62\x72\x3e\x0d\x0a\x3c\x69\x6d\x67\x20\x73\x72\x63\x3d\x27"))
(assert (= x_17 (str.++ x_15 literal_16)))
(assert (= literal_18 "\x69\x6d\x61\x67\x65\x73\x2f\x62\x75\x6c\x6c\x65\x74\x2e\x67\x69\x66\x27\x20\x61\x6c\x74\x3d\x27\x27\x3e\x20\x3c\x61\x20\x68\x72\x65\x66\x3d\x27"))
(assert (= x_19 (str.++ x_17 literal_18)))
(assert (= literal_20 "\x6d\x65\x6d\x62\x65\x72\x73\x2e\x70\x68\x70\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x73\x69\x64\x65\x27\x3e"))
(assert (= x_21 (str.++ x_19 literal_20)))
(assert (= x_22 (str.++ x_21 sigmaStar_2)))
(assert (= literal_23 "\x3c\x2f\x61\x3e\x3c\x62\x72\x3e\x5c\x6e"))
(assert (= x_24 (str.++ x_22 literal_23)))
(assert (str.in.re x_24 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_24 "\x61" 0)) (str.len x_24)))
(check-sat)
(get-model)
