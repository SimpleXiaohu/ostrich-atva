(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_14 () String)
(declare-fun sigmaStar_17 () String)
(declare-fun literal_16 () String)
(declare-fun x_18 () String)
(declare-fun literal_19 () String)
(declare-fun x_20 () String)
(declare-fun x_21 () String)
(declare-fun literal_22 () String)
(declare-fun x_23 () String)
(declare-fun literal_24 () String)
(declare-fun x_25 () String)
(assert (= literal_16 "\x70\x65\x72\x70\x61\x67\x65\x3d\x70\x65\x72\x70\x61\x67\x65\x26\x61\x6d\x70\x3b\x6c\x61\x73\x74\x69\x6e\x69\x74\x69\x61\x6c\x3d\x6c\x61\x73\x74\x69\x6e\x69\x74\x69\x61\x6c\x26\x61\x6d\x70\x3b\x66\x69\x72\x73\x74\x69\x6e\x69\x74\x69\x61\x6c\x3d"))
(assert (= x_18 (str.++ literal_16 sigmaStar_14)))
(assert (= literal_19 "\x5c\x22\x3e"))
(assert (= x_20 (str.++ x_18 literal_19)))
(assert (= x_21 (str.++ x_20 sigmaStar_14)))
(assert (= literal_22 "\x3c\x2f\x61\x3e\x20"))
(assert (= x_23 (str.++ x_21 literal_22)))
(assert (= literal_24 "\x20\x3c\x61\x20\x68\x72\x65\x66\x3d\x22\x75\x73\x65\x72\x2e\x70\x68\x70\x3f\x73\x6f\x72\x74\x3d\x66\x69\x72\x73\x74\x6e\x61\x6d\x65\x26\x61\x6d\x70\x3b\x64\x69\x72\x3d\x41\x53\x43\x26\x61\x6d\x70\x3b"))
(assert (= x_25 (str.++ literal_24 x_23)))
(assert (str.in.re x_25 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_25 "\x61" 0)) (str.len x_25)))
(check-sat)
(get-model)
