(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun literal_18 () String)
(declare-fun x_17 () String)
(declare-fun literal_10 () String)
(declare-fun literal_9 () String)
(declare-fun literal_11 () String)
(declare-fun literal_6 () String)
(declare-fun literal_12 () String)
(declare-fun x_19 () String)
(declare-fun literal_21 () String)
(declare-fun x_22 () String)
(declare-fun literal_20 () String)
(declare-fun x_23 () String)
(declare-fun literal_24 () String)
(declare-fun x_25 () String)
(declare-fun literal_28 () String)
(declare-fun x_29 () String)
(declare-fun literal_27 () String)
(declare-fun x_30 () String)
(declare-fun literal_31 () String)
(declare-fun x_32 () String)
(assert (= literal_18 "\x26\x61\x6d\x70\x3b\x6d\x6f\x64\x65\x3d"))
(assert (= literal_10 "\x72\x65\x76\x69\x65\x77"))
(assert (= literal_9 "\x6e\x6f\x72\x6d\x61\x6c"))
(assert (= literal_11 "\x6e\x6f\x72\x6d\x61\x6c"))
(assert (= literal_6 "\x6d\x6f\x64\x65"))
(assert (= literal_12 "\x6e\x6f\x72\x6d\x61\x6c"))
(assert (or (= x_17 literal_10) (= x_17 literal_9) (= x_17 literal_11) (= x_17 literal_6) (= x_17 literal_12)))
(assert (= x_19 (str.++ literal_18 x_17)))
(assert (= literal_21 "\x2f\x6d\x6f\x64\x2f\x73\x63\x6f\x72\x6d\x2f\x70\x6c\x61\x79\x65\x72\x2e\x70\x68\x70\x3f\x69\x64\x3d\x26\x61\x6d\x70\x3b\x63\x75\x72\x72\x65\x6e\x74\x6f\x72\x67\x3d\x63\x75\x72\x72\x65\x6e\x74\x6f\x72\x67"))
(assert (= x_22 (str.++ literal_21 x_19)))
(assert (= literal_20 "\x26\x61\x6d\x70\x3b\x73\x63\x6f\x69\x64\x3d"))
(assert (= x_23 (str.++ x_22 literal_20)))
(assert (= literal_24 "\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x20\x26\x6e\x62\x73\x70\x3b\x3c\x61\x20\x68\x72\x65\x66\x3d\x22"))
(assert (= x_25 (str.++ literal_24 x_23)))
(assert (= literal_28 "\x22\x3e"))
(assert (= x_29 (str.++ x_25 literal_28)))
(assert (= literal_27 "\x6e\x65\x78\x74"))
(assert (= x_30 (str.++ x_29 literal_27)))
(assert (= literal_31 "\x20\x26\x67\x74\x3b\x3c\x2f\x61\x3e"))
(assert (= x_32 (str.++ x_30 literal_31)))
(assert (str.in.re x_32 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_32 "\x61" 0)) (str.len x_32)))
(check-sat)
(get-model)
