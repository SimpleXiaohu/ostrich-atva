(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_6 () String)
(declare-fun x_7 () String)
(declare-fun literal_8 () String)
(declare-fun x_9 () String)
(declare-fun literal_10 () String)
(declare-fun x_11 () String)
(declare-fun literal_12 () String)
(declare-fun x_13 () String)
(declare-fun literal_14 () String)
(declare-fun x_15 () String)
(assert (= literal_6 "\x3c\x66\x6f\x72\x6d\x20\x6d\x65\x74\x68\x6f\x64\x3d\x22\x70\x6f\x73\x74\x22\x20\x65\x6e\x63\x74\x79\x70\x65\x3d\x22\x6d\x75\x6c\x74\x69\x70\x61\x72\x74\x2f\x66\x6f\x72\x6d\x2d\x64\x61\x74\x61\x22\x20\x61\x63\x74\x69\x6f\x6e\x3d\x22\x75\x70\x6c\x6f\x61\x64\x75\x73\x65\x72\x2e\x70\x68\x70\x22\x3e\x66\x69\x6c\x65\x26\x6e\x62\x73\x70\x3b\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x22\x68\x69\x64\x64\x65\x6e\x22\x20\x6e\x61\x6d\x65\x3d\x22\x4d\x41\x58\x5f\x46\x49\x4c\x45\x5f\x53\x49\x5a\x45\x22\x20\x76\x61\x6c\x75\x65\x3d\x22"))
(assert (= x_7 (str.++ literal_6 sigmaStar_0)))
(assert (= literal_8 "\x22\x3e"))
(assert (= x_9 (str.++ x_7 literal_8)))
(assert (= literal_10 "\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x22\x68\x69\x64\x64\x65\x6e\x22\x20\x6e\x61\x6d\x65\x3d\x22\x73\x65\x73\x73\x6b\x65\x79\x22\x20\x76\x61\x6c\x75\x65\x3d\x22"))
(assert (= x_11 (str.++ x_9 literal_10)))
(assert (= literal_12 "\x22\x3e"))
(assert (= x_13 (str.++ x_11 literal_12)))
(assert (= literal_14 "\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x22\x66\x69\x6c\x65\x22\x20\x6e\x61\x6d\x65\x3d\x22\x75\x73\x65\x72\x66\x69\x6c\x65\x22\x20\x73\x69\x7a\x65\x3d\x22\x33\x30\x22\x3e"))
(assert (= x_15 (str.++ x_13 literal_14)))
(assert (str.in.re x_15 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_15 "\x61" 0)) (str.len x_15)))
(check-sat)
(get-model)
