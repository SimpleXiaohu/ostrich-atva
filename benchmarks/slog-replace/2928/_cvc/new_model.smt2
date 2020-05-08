(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun literal_5 () String)
(declare-fun x_6 () String)
(declare-fun literal_7 () String)
(declare-fun x_8 () String)
(declare-fun literal_9 () String)
(declare-fun x_10 () String)
(declare-fun x_11 () String)
(declare-fun literal_12 () String)
(declare-fun x_13 () String)
(declare-fun literal_14 () String)
(declare-fun x_15 () String)
(declare-fun x_16 () String)
(declare-fun literal_17 () String)
(declare-fun x_18 () String)
(assert (= literal_5 "\x3c\x74\x72\x3e\x5c\x6e\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x63\x6f\x6c\x73\x70\x61\x6e\x3d\x27\x35\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x31\x27\x3e\x3c\x73\x70\x61\x6e\x20\x63\x6c\x61\x73\x73\x3d\x27\x73\x6d\x61\x6c\x6c\x27\x3e\x3c\x61\x20\x68\x72\x65\x66\x3d\x27\x66\x6f\x72\x75\x6d\x5f\x74\x68\x72\x65\x61\x64\x73\x5f\x6c\x69\x73\x74\x5f\x70\x61\x6e\x65\x6c\x2f\x6d\x79\x5f\x74\x68\x72\x65\x61\x64\x73\x2e\x70\x68\x70\x27\x3e"))
(assert (= x_6 (str.++ literal_5 sigmaStar_2)))
(assert (= literal_7 "\x3c\x2f\x61\x3e\x20\x7c\x0d\x0a\x3c\x61\x20\x68\x72\x65\x66\x3d\x27"))
(assert (= x_8 (str.++ x_6 literal_7)))
(assert (= literal_9 "\x66\x6f\x72\x75\x6d\x5f\x74\x68\x72\x65\x61\x64\x73\x5f\x6c\x69\x73\x74\x5f\x70\x61\x6e\x65\x6c\x2f\x6d\x79\x5f\x70\x6f\x73\x74\x73\x2e\x70\x68\x70\x27\x3e"))
(assert (= x_10 (str.++ x_8 literal_9)))
(assert (= x_11 (str.++ x_10 sigmaStar_1)))
(assert (= literal_12 "\x3c\x2f\x61\x3e\x20\x7c\x0d\x0a\x3c\x61\x20\x68\x72\x65\x66\x3d\x27"))
(assert (= x_13 (str.++ x_11 literal_12)))
(assert (= literal_14 "\x66\x6f\x72\x75\x6d\x5f\x74\x68\x72\x65\x61\x64\x73\x5f\x6c\x69\x73\x74\x5f\x70\x61\x6e\x65\x6c\x2f\x6e\x65\x77\x5f\x70\x6f\x73\x74\x73\x2e\x70\x68\x70\x27\x3e"))
(assert (= x_15 (str.++ x_13 literal_14)))
(assert (= x_16 (str.++ x_15 sigmaStar_0)))
(assert (= literal_17 "\x3c\x2f\x61\x3e\x3c\x2f\x73\x70\x61\x6e\x3e\x3c\x2f\x74\x64\x3e\x5c\x6e\x3c\x2f\x74\x72\x3e\x5c\x6e"))
(assert (= x_18 (str.++ x_16 literal_17)))
(assert (str.in.re x_18 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_18 "\x61" 0)) (str.len x_18)))
(check-sat)
(get-model)
