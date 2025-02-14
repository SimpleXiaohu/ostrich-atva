(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun literal_7 () String)
(declare-fun x_6 () String)
(declare-fun epsilon () String)
(declare-fun x_8 () String)
(declare-fun sigmaStar_11 () String)
(declare-fun literal_10 () String)
(declare-fun x_12 () String)
(declare-fun x_13 () String)
(declare-fun literal_14 () String)
(declare-fun x_15 () String)
(declare-fun x_16 () String)
(declare-fun literal_17 () String)
(declare-fun x_18 () String)
(declare-fun x_19 () String)
(declare-fun literal_20 () String)
(declare-fun x_21 () String)
(assert (= literal_7 "\x3c\x74\x61\x62\x6c\x65\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x27\x30\x27\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x27\x31\x27\x20\x77\x69\x64\x74\x68\x3d\x27\x31\x30\x30\x25\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x2d\x62\x6f\x72\x64\x65\x72\x27\x3e\x0d\x0a\x3c\x74\x72\x3e\x0d\x0a\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x63\x6f\x6c\x73\x70\x61\x6e\x3d\x27\x32\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x31\x27\x3e\x3c\x62\x3e"))
(assert (= epsilon ""))
(assert (or (= x_6 epsilon)))
(assert (= x_8 (str.++ literal_7 x_6)))
(assert (= literal_10 "\x3c\x2f\x62\x3e\x20\x28"))
(assert (= x_12 (str.++ x_8 literal_10)))
(assert (= x_13 (str.++ x_12 sigmaStar_11)))
(assert (= literal_14 "\x29\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x2f\x74\x72\x3e\x0d\x0a\x3c\x74\x72\x3e\x0d\x0a\x3c\x74\x64\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x32\x27\x3e\x3c\x62\x3e"))
(assert (= x_15 (str.++ x_13 literal_14)))
(assert (= x_16 (str.++ x_15 sigmaStar_0)))
(assert (= literal_17 "\x3c\x2f\x62\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x77\x69\x64\x74\x68\x3d\x27\x31\x25\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x32\x27\x20\x73\x74\x79\x6c\x65\x3d\x27\x77\x68\x69\x74\x65\x2d\x73\x70\x61\x63\x65\x3a\x6e\x6f\x77\x72\x61\x70\x27\x3e\x3c\x62\x3e"))
(assert (= x_18 (str.++ x_16 literal_17)))
(assert (= x_19 (str.++ x_18 sigmaStar_3)))
(assert (= literal_20 "\x3c\x2f\x62\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x2f\x74\x72\x3e\x5c\x6e"))
(assert (= x_21 (str.++ x_19 literal_20)))
(assert (str.in.re x_21 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_21 "\x61" 0)) (str.len x_21)))
(check-sat)
(get-model)
