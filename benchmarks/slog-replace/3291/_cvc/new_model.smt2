(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_9 () String)
(declare-fun x_8 () String)
(declare-fun epsilon () String)
(declare-fun x_10 () String)
(declare-fun literal_11 () String)
(declare-fun x_12 () String)
(declare-fun x_13 () String)
(declare-fun literal_14 () String)
(declare-fun x_15 () String)
(assert (= literal_9 "\x3c\x2f\x73\x65\x6c\x65\x63\x74\x3e\x0d\x0a\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x2f\x74\x72\x3e\x0d\x0a\x3c\x74\x72\x3e\x0d\x0a\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x63\x6f\x6c\x73\x70\x61\x6e\x3d\x27\x33\x27\x3e\x3c\x62\x72\x3e\x0d\x0a\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x66\x6f\x72\x75\x6d\x5f\x6d\x6f\x64\x73\x27\x3e\x0d\x0a\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x66\x6f\x72\x75\x6d\x5f\x69\x64\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= epsilon ""))
(assert (or (= x_8 epsilon) (= x_8 sigmaStar_0)))
(assert (= x_10 (str.++ literal_9 x_8)))
(assert (= literal_11 "\x27\x3e\x0d\x0a\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x73\x61\x76\x65\x5f\x66\x6f\x72\x75\x6d\x5f\x6d\x6f\x64\x73\x27\x3e\x0d\x0a\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x62\x75\x74\x74\x6f\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x75\x70\x64\x61\x74\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_12 (str.++ x_10 literal_11)))
(assert (= x_13 (str.++ x_12 sigmaStar_1)))
(assert (= literal_14 "\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x62\x75\x74\x74\x6f\x6e\x27\x20\x6f\x6e\x63\x6c\x69\x63\x6b\x3d\x27\x73\x61\x76\x65\x4d\x6f\x64\x73\x28\x29\x3b\x27\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x2f\x74\x72\x3e\x0d\x0a\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x3c\x2f\x66\x6f\x72\x6d\x3e\x5c\x6e"))
(assert (= x_15 (str.++ x_13 literal_14)))
(assert (str.in.re x_15 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_15 "\x61" 0)) (str.len x_15)))
(check-sat)
(get-model)
