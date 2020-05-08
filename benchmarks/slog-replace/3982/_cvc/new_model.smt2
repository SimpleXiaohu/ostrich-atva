(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_10 () String)
(declare-fun literal_11 () String)
(declare-fun x_12 () String)
(declare-fun literal_14 () String)
(declare-fun x_13 () String)
(declare-fun x_15 () String)
(declare-fun literal_16 () String)
(declare-fun x_17 () String)
(declare-fun x_18 () String)
(declare-fun literal_19 () String)
(declare-fun x_20 () String)
(assert (= literal_11 "\x3f\x61\x69\x64\x3d"))
(assert (= x_12 (str.++ literal_11 sigmaStar_10)))
(assert (= literal_14 "\x3c\x74\x72\x3e\x5c\x6e\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x63\x6f\x6c\x73\x70\x61\x6e\x3d\x27\x37\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x31\x27\x3e\x5b\x20\x3c\x61\x20\x68\x72\x65\x66\x3d\x27\x70\x61\x6e\x65\x6c\x5f\x65\x64\x69\x74\x6f\x72\x2e\x70\x68\x70"))
(assert (or (= x_13 sigmaStar_2) (= x_13 x_12)))
(assert (= x_15 (str.++ literal_14 x_13)))
(assert (= literal_16 "\x27\x3e"))
(assert (= x_17 (str.++ x_15 literal_16)))
(assert (= x_18 (str.++ x_17 sigmaStar_0)))
(assert (= literal_19 "\x3c\x2f\x61\x3e\x20\x5d\x5c\x6e"))
(assert (= x_20 (str.++ x_18 literal_19)))
(assert (str.in.re x_20 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_20 "\x61" 0)) (str.len x_20)))
(check-sat)
(get-model)
