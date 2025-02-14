(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_45 () String)
(declare-fun x_44 () String)
(declare-fun literal_6 () String)
(declare-fun literal_4 () String)
(declare-fun literal_5 () String)
(declare-fun literal_46 () String)
(declare-fun x_47 () String)
(declare-fun sigmaStar_51 () String)
(declare-fun literal_53 () String)
(declare-fun x_52 () String)
(declare-fun epsilon () String)
(declare-fun literal_50 () String)
(declare-fun x_56 () String)
(declare-fun literal_57 () String)
(declare-fun x_58 () String)
(declare-fun x_61 () String)
(declare-fun literal_60 () String)
(declare-fun x_62 () String)
(assert (= literal_6 "\x2f"))
(assert (= literal_4 "\x77\x64\x69\x72"))
(assert (= literal_5 "\x2f"))
(assert (or (= x_44 literal_6) (= x_44 literal_4) (= x_44 literal_5)))
(assert (= literal_46 "\x2f"))
(assert (= x_47 (str.++ x_44 literal_46)))
(assert (= literal_53 "\x20\x69\x68\x65\x69\x67\x68\x74\x3a\x20\x27"))
(assert (= epsilon ""))
(assert (= literal_50 "\x55\x6e\x6b\x6e\x6f\x77\x6e"))
(assert (or (= x_52 epsilon) (= x_52 literal_50)))
(assert (= x_56 (str.++ literal_53 x_52)))
(assert (= literal_57 "\x27\x2c\x20\x69\x6d\x6f\x64\x69\x66\x69\x65\x64\x3a\x20\x27"))
(assert (= x_58 (str.++ x_56 literal_57)))
(assert (= x_61 (str.++ x_58 sigmaStar_51)))
(assert (= literal_60 "\x27\x20\x7d\x29\x5c\x22\x20\x68\x72\x65\x66\x3d\x5c\x22\x23\x5c\x22\x3e\x3c\x2f\x61\x3e"))
(assert (= x_62 (str.++ x_61 literal_60)))
(assert (str.in.re x_62 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_62 "\x61" 0)) (str.len x_62)))
(check-sat)
(get-model)
