(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_12 () String)
(declare-fun x_11 () String)
(declare-fun literal_2 () String)
(declare-fun literal_6 () String)
(declare-fun literal_7 () String)
(declare-fun literal_4 () String)
(declare-fun literal_5 () String)
(declare-fun x_13 () String)
(declare-fun literal_3 () String)
(declare-fun x_14 () String)
(assert (= literal_12 "\x26\x61\x6d\x70\x3b\x6d\x6f\x64\x65\x3d"))
(assert (= literal_2 "\x6d\x6f\x64\x65"))
(assert (= literal_6 "\x6e\x6f\x72\x6d\x61\x6c"))
(assert (= literal_7 "\x6e\x6f\x72\x6d\x61\x6c"))
(assert (= literal_4 "\x6e\x6f\x72\x6d\x61\x6c"))
(assert (= literal_5 "\x72\x65\x76\x69\x65\x77"))
(assert (or (= x_11 literal_2) (= x_11 literal_6) (= x_11 literal_7) (= x_11 literal_4) (= x_11 literal_5)))
(assert (= x_13 (str.++ literal_12 x_11)))
(assert (= literal_3 "\x26\x61\x6d\x70\x3b\x73\x63\x6f\x69\x64\x3d"))
(assert (= x_14 (str.++ literal_3 x_13)))
(assert (str.in.re x_14 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_14 "\x61" 0)) (str.len x_14)))
(check-sat)
(get-model)
