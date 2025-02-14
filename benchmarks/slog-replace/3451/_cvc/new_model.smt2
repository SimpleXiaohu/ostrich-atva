(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_5 () String)
(declare-fun x_8 () String)
(declare-fun epsilon () String)
(declare-fun literal_4 () String)
(declare-fun x_9 () String)
(declare-fun literal_10 () String)
(declare-fun x_11 () String)
(assert (= literal_5 "\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x70\x61\x6e\x65\x6c\x5f\x73\x69\x64\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= epsilon ""))
(assert (= literal_4 ""))
(assert (or (= x_8 epsilon) (= x_8 sigmaStar_1) (= x_8 sigmaStar_0) (= x_8 literal_4)))
(assert (= x_9 (str.++ literal_5 x_8)))
(assert (= literal_10 "\x27\x3e\x5c\x6e"))
(assert (= x_11 (str.++ x_9 literal_10)))
(assert (str.in.re x_11 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_11 "\x61" 0)) (str.len x_11)))
(check-sat)
(get-model)
