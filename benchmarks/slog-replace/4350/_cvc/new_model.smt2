(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_2 () String)
(declare-fun x_3 () String)
(declare-fun literal_4 () String)
(declare-fun x_5 () String)
(declare-fun x_7 () String)
(declare-fun epsilon () String)
(declare-fun x_8 () String)
(declare-fun literal_9 () String)
(declare-fun x_10 () String)
(declare-fun x_11 () String)
(declare-fun literal_12 () String)
(declare-fun x_13 () String)
(declare-fun x_14 () String)
(declare-fun literal_15 () String)
(declare-fun x_16 () String)
(declare-fun x_17 () String)
(declare-fun literal_18 () String)
(declare-fun x_19 () String)
(declare-fun x_20 () String)
(declare-fun literal_24 () String)
(declare-fun x_25 () String)
(declare-fun x_26 () String)
(declare-fun x_27 () String)
(declare-fun literal_28 () String)
(declare-fun x_29 () String)
(assert (= literal_2 "\x3c\x74\x72\x3e\x0d\x0a\x3c\x74\x64\x20\x77\x69\x64\x74\x68\x3d\x27\x31\x34\x35\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x32\x27\x3e"))
(assert (= x_3 (str.++ literal_2 sigmaStar_0)))
(assert (= literal_4 "\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x74\x64\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x32\x27\x3e\x3c\x61\x20\x6e\x61\x6d\x65\x3d\x27\x70\x6f\x73\x74\x5f"))
(assert (= x_5 (str.++ x_3 literal_4)))
(assert (= epsilon ""))
(assert (or (= x_7 epsilon)))
(assert (= x_8 (str.++ x_5 x_7)))
(assert (= literal_9 "\x27\x20\x69\x64\x3d\x27\x70\x6f\x73\x74\x5f"))
(assert (= x_10 (str.++ x_8 literal_9)))
(assert (= x_11 (str.++ x_10 x_7)))
(assert (= literal_12 "\x27\x3e\x3c\x2f\x61\x3e"))
(assert (= x_13 (str.++ x_11 literal_12)))
(assert (= x_14 (str.++ x_13 x_7)))
(assert (= literal_15 "\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x2f\x74\x72\x3e\x0d\x0a\x3c\x74\x72\x3e\x0d\x0a\x3c\x74\x64\x20\x76\x61\x6c\x69\x67\x6e\x3d\x27\x74\x6f\x70\x27\x20\x72\x6f\x77\x73\x70\x61\x6e\x3d\x27\x33\x27\x20\x77\x69\x64\x74\x68\x3d\x27\x31\x34\x35\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x31\x27\x3e\x0d\x0a\x3c\x61\x20\x68\x72\x65\x66\x3d\x27\x2e\x2e\x2f\x70\x72\x6f\x66\x69\x6c\x65\x2e\x70\x68\x70\x3f\x6c\x6f\x6f\x6b\x75\x70\x3d"))
(assert (= x_16 (str.++ x_14 literal_15)))
(assert (= x_17 (str.++ x_16 x_7)))
(assert (= literal_18 "\x27\x3e"))
(assert (= x_19 (str.++ x_17 literal_18)))
(assert (= x_20 (str.++ x_19 x_7)))
(assert (= literal_24 "\x3c\x2f\x61\x3e\x3c\x62\x72\x3e\x0d\x0a\x3c\x73\x70\x61\x6e\x20\x63\x6c\x61\x73\x73\x3d\x27\x61\x6c\x74\x27\x3e"))
(assert (= x_25 (str.++ x_20 literal_24)))
(assert (or (= x_26 epsilon) (= x_26 sigmaStar_1)))
(assert (= x_27 (str.++ x_25 x_26)))
(assert (= literal_28 "\x3c\x2f\x73\x70\x61\x6e\x3e\x3c\x62\x72\x3e\x3c\x62\x72\x3e\x5c\x6e"))
(assert (= x_29 (str.++ x_27 literal_28)))
(assert (str.in.re x_29 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_29 "\x61" 0)) (str.len x_29)))
(check-sat)
(get-model)
