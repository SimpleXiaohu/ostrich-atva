(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_6 () String)
(declare-fun sigmaStar_7 () String)
(declare-fun literal_11 () String)
(declare-fun x_15 () String)
(declare-fun literal_20 () String)
(declare-fun x_26 () String)
(declare-fun literal_19 () String)
(declare-fun literal_16 () String)
(declare-fun literal_17 () String)
(declare-fun literal_18 () String)
(declare-fun literal_13 () String)
(declare-fun literal_14 () String)
(declare-fun x_27 () String)
(declare-fun literal_28 () String)
(declare-fun x_29 () String)
(assert (= literal_11 "\x43\x6f\x75\x6c\x64\x20\x6e\x6f\x74\x20\x63\x68\x61\x6e\x67\x65\x20\x62\x61\x63\x6b\x20\x74\x6f\x20\x64\x69\x72\x65\x63\x74\x6f\x72\x79\x3a\x20"))
(assert (= x_15 (str.++ literal_11 sigmaStar_7)))
(assert (= literal_20 "\x3c\x70\x3e"))
(assert (= literal_19 "\x4f\x6e\x65\x20\x6f\x72\x20\x6d\x6f\x72\x65\x20\x6f\x66\x20\x74\x68\x65\x20\x66\x69\x6c\x65\x73\x20\x63\x6f\x75\x6c\x64\x20\x6e\x6f\x74\x20\x62\x65\x20\x63\x68\x6d\x6f\x64\x64\x65\x64\x2e\x20\x54\x68\x69\x73\x20\x6d\x65\x61\x6e\x73\x20\x74\x68\x61\x74\x20\x79\x6f\x75\x20\x77\x69\x6c\x6c\x20\x68\x61\x76\x65\x20\x74\x6f\x20\x63\x68\x6d\x6f\x64\x20\x74\x68\x65\x6d\x20\x6d\x61\x6e\x75\x61\x6c\x6c\x79\x2e\x20\x20\x50\x6c\x65\x61\x73\x65\x20\x72\x65\x66\x65\x72\x20\x74\x6f\x20\x74\x68\x65\x20\x64\x6f\x63\x75\x6d\x65\x6e\x74\x61\x74\x69\x6f\x6e\x20\x66\x6f\x72\x20\x6d\x6f\x72\x65\x20\x64\x65\x74\x61\x69\x6c\x73\x2e"))
(assert (= literal_16 "\x43\x6f\x75\x6c\x64\x20\x6e\x6f\x74\x20\x63\x68\x6d\x6f\x64\x20\x66\x69\x6c\x65\x20"))
(assert (= literal_17 "\x44\x6f\x6e\x65\x21"))
(assert (= literal_18 "\x54\x68\x65\x20\x66\x69\x6c\x65\x73\x20\x68\x61\x76\x65\x20\x62\x65\x65\x6e\x20\x63\x68\x6d\x6f\x64\x64\x65\x64\x20\x73\x75\x63\x63\x65\x73\x73\x66\x75\x6c\x6c\x79\x2e\x20\x20\x50\x6c\x65\x61\x73\x65\x20\x63\x6f\x6e\x74\x69\x6e\x75\x65\x20\x77\x69\x74\x68\x20\x74\x68\x65\x20\x69\x6e\x73\x74\x61\x6c\x6c\x61\x74\x69\x6f\x6e\x2e"))
(assert (= literal_13 "\x46\x69\x6c\x65\x2f\x20\x68\x61\x73\x20\x62\x65\x65\x6e\x20\x63\x68\x6d\x6f\x64\x64\x65\x64\x2e"))
(assert (= literal_14 "\x43\x6f\x75\x6c\x64\x20\x6e\x6f\x74\x20\x63\x68\x61\x6e\x67\x65\x20\x69\x6e\x74\x6f\x20\x64\x69\x72\x65\x63\x74\x6f\x72\x79\x3a\x20"))
(assert (or (= x_26 literal_19) (= x_26 literal_16) (= x_26 literal_17) (= x_26 literal_18) (= x_26 x_15) (= x_26 literal_13) (= x_26 literal_14)))
(assert (= x_27 (str.++ literal_20 x_26)))
(assert (= literal_28 "\x3c\x2f\x70\x3e\x5c\x6e"))
(assert (= x_29 (str.++ x_27 literal_28)))
(assert (str.in.re x_29 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_29 "\x61" 0)) (str.len x_29)))
(check-sat)
(get-model)
