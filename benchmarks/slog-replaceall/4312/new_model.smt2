(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun literal_11 () String)
(declare-fun x_14 () String)
(declare-fun x_20 () String)
(declare-fun sigmaStar_19 () String)
(declare-fun literal_18 () String)
(declare-fun x_26 () String)
(declare-fun sigmaStar_28 () String)
(declare-fun literal_27 () String)
(declare-fun x_29 () String)
(declare-fun x_30 () String)
(declare-fun literal_31 () String)
(declare-fun x_32 () String)
(assert (= literal_11 "\x42\x79\x74\x65\x73"))
(assert (= x_14 (str.++ sigmaStar_0 literal_11)))
(assert (= x_20 (str.replaceall sigmaStar_1 "\x2c" "\x20")))
(assert (= literal_18 "\x3c\x74\x72\x3e\x0d\x0a\x3c\x74\x64\x20\x77\x69\x64\x74\x68\x3d\x27\x31\x34\x35\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x32\x27\x3e"))
(assert (= x_26 (str.++ literal_18 sigmaStar_2)))
(assert (= literal_27 "\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x74\x64\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x31\x27\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x66\x69\x6c\x65\x27\x20\x6e\x61\x6d\x65\x3d\x27\x61\x74\x74\x61\x63\x68\x27\x20\x65\x6e\x63\x74\x79\x70\x65\x3d\x27\x6d\x75\x6c\x74\x69\x70\x61\x72\x74\x2f\x66\x6f\x72\x6d\x2d\x64\x61\x74\x61\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x65\x78\x74\x62\x6f\x78\x27\x20\x73\x74\x79\x6c\x65\x3d\x27\x77\x69\x64\x74\x68\x3a\x32\x30\x30\x70\x78\x3b\x27\x3e\x3c\x62\x72\x3e\x0d\x0a\x3c\x73\x70\x61\x6e\x20\x63\x6c\x61\x73\x73\x3d\x27\x73\x6d\x61\x6c\x6c\x32\x27\x3e"))
(assert (= x_29 (str.++ x_26 literal_27)))
(assert (= x_30 (str.++ x_29 sigmaStar_28)))
(assert (= literal_31 "\x3c\x2f\x73\x70\x61\x6e\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x2f\x74\x72\x3e\x5c\x6e"))
(assert (= x_32 (str.++ x_30 literal_31)))
(assert (str.in.re x_32 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (> (* 2 (str.indexof x_20 "\x61" 0)) (str.len x_20)))
(check-sat)
(get-model)
