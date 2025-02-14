(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_3 () String)
(declare-fun x_5 () String)
(declare-fun literal_6 () String)
(declare-fun x_7 () String)
(declare-fun x_8 () String)
(declare-fun epsilon () String)
(declare-fun x_9 () String)
(declare-fun literal_10 () String)
(declare-fun x_11 () String)
(assert (= literal_3 "\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x74\x64\x20\x77\x69\x64\x74\x68\x3d\x27\x31\x25\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x32\x27\x20\x73\x74\x79\x6c\x65\x3d\x27\x77\x68\x69\x74\x65\x2d\x73\x70\x61\x63\x65\x3a\x6e\x6f\x77\x72\x61\x70\x27\x3e\x3c\x62\x3e"))
(assert (= x_5 (str.++ literal_3 sigmaStar_1)))
(assert (= literal_6 "\x3c\x2f\x62\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x74\x64\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x32\x27\x3e"))
(assert (= x_7 (str.++ x_5 literal_6)))
(assert (= epsilon ""))
(assert (or (= x_8 epsilon) (= x_8 sigmaStar_0)))
(assert (= x_9 (str.++ x_7 x_8)))
(assert (= literal_10 "\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x2f\x74\x72\x3e\x0d\x0a\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x5c\x6e"))
(assert (= x_11 (str.++ x_9 literal_10)))
(assert (str.in.re x_11 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_11 "\x61" 0)) (str.len x_11)))
(check-sat)
(get-model)
