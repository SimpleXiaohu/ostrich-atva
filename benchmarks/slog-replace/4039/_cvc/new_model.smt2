(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_8 () String)
(declare-fun x_12 () String)
(declare-fun literal_2 () String)
(declare-fun literal_3 () String)
(declare-fun literal_6 () String)
(declare-fun literal_7 () String)
(declare-fun literal_4 () String)
(declare-fun x_13 () String)
(declare-fun literal_14 () String)
(declare-fun x_15 () String)
(declare-fun x_16 () String)
(declare-fun literal_17 () String)
(declare-fun x_18 () String)
(assert (= literal_8 "\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x63\x68\x65\x63\x6b\x62\x6f\x78\x27\x20\x6e\x61\x6d\x65\x3d\x27\x6c\x69\x6e\x65\x5f\x62\x72\x65\x61\x6b\x73\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x79\x65\x73\x27"))
(assert (= literal_2 ""))
(assert (= literal_3 "\x20\x63\x68\x65\x63\x6b\x65\x64"))
(assert (= literal_6 ""))
(assert (= literal_7 "\x20\x63\x68\x65\x63\x6b\x65\x64"))
(assert (= literal_4 "\x20\x63\x68\x65\x63\x6b\x65\x64"))
(assert (or (= x_12 literal_2) (= x_12 literal_3) (= x_12 sigmaStar_0) (= x_12 literal_6) (= x_12 literal_7) (= x_12 literal_4)))
(assert (= x_13 (str.++ literal_8 x_12)))
(assert (= literal_14 "\x3e\x20"))
(assert (= x_15 (str.++ x_13 literal_14)))
(assert (= x_16 (str.++ x_15 sigmaStar_1)))
(assert (= literal_17 "\x3c\x62\x72\x3e\x5c\x6e"))
(assert (= x_18 (str.++ x_16 literal_17)))
(assert (str.in.re x_18 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_18 "\x61" 0)) (str.len x_18)))
(check-sat)
(get-model)
