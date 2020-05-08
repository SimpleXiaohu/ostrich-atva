(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_5 () String)
(declare-fun literal_6 () String)
(declare-fun x_4 () String)
(declare-fun epsilon () String)
(declare-fun literal_1 () String)
(declare-fun x_7 () String)
(declare-fun literal_8 () String)
(declare-fun x_9 () String)
(declare-fun x_10 () String)
(declare-fun literal_13 () String)
(declare-fun x_14 () String)
(declare-fun literal_12 () String)
(declare-fun x_15 () String)
(declare-fun literal_16 () String)
(declare-fun x_17 () String)
(assert (= literal_6 "\x3c\x74\x72\x3e\x3c\x74\x64\x3e"))
(assert (= epsilon ""))
(assert (= literal_1 ""))
(assert (or (= x_4 epsilon) (= x_4 literal_1)))
(assert (= x_7 (str.++ literal_6 x_4)))
(assert (= literal_8 "\x3c\x2f\x74\x64\x3e\x3c\x74\x64\x3e\x3c\x61\x20\x68\x72\x65\x66\x3d\x22\x68\x74\x74\x70\x3a\x2f\x2f\x64\x6f\x77\x6e\x6c\x6f\x61\x64\x2e\x6d\x6f\x6f\x64\x6c\x65\x2e\x6f\x72\x67\x2f\x6c\x61\x6e\x67\x31\x36\x2f"))
(assert (= x_9 (str.++ x_7 literal_8)))
(assert (= x_10 (str.++ x_9 x_4)))
(assert (= literal_13 "\x2e\x7a\x69\x70\x22\x3e"))
(assert (= x_14 (str.++ x_10 literal_13)))
(assert (= literal_12 "\x64\x6f\x77\x6e\x6c\x6f\x61\x64"))
(assert (= x_15 (str.++ x_14 literal_12)))
(assert (= literal_16 "\x3c\x2f\x61\x3e"))
(assert (= x_17 (str.++ x_15 literal_16)))
(assert (str.in.re x_17 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_17 "\x61" 0)) (str.len x_17)))
(check-sat)
(get-model)
