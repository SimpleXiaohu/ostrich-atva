(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_2 () String)
(declare-fun x_3 () String)
(declare-fun epsilon () String)
(declare-fun x_4 () String)
(declare-fun literal_5 () String)
(declare-fun x_6 () String)
(declare-fun x_7 () String)
(declare-fun x_8 () String)
(declare-fun literal_9 () String)
(declare-fun x_10 () String)
(declare-fun literal_11 () String)
(declare-fun x_12 () String)
(declare-fun literal_18 () String)
(declare-fun x_27 () String)
(declare-fun literal_20 () String)
(declare-fun x_19 () String)
(declare-fun literal_15 () String)
(declare-fun literal_14 () String)
(declare-fun x_28 () String)
(declare-fun literal_26 () String)
(declare-fun x_32 () String)
(declare-fun literal_21 () String)
(declare-fun literal_22 () String)
(declare-fun literal_23 () String)
(declare-fun literal_24 () String)
(declare-fun literal_25 () String)
(declare-fun x_34 () String)
(declare-fun sigmaStar_35 () String)
(declare-fun x_36 () String)
(declare-fun literal_37 () String)
(declare-fun x_38 () String)
(declare-fun x_39 () String)
(declare-fun x_40 () String)
(assert (= literal_2 "\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x6c\x65\x66\x74\x27\x3e"))
(assert (= epsilon ""))
(assert (or (= x_3 epsilon) (= x_3 sigmaStar_0)))
(assert (= x_4 (str.++ literal_2 x_3)))
(assert (= literal_5 "\x20"))
(assert (= x_6 (str.++ x_4 literal_5)))
(assert (or (= x_7 epsilon) (= x_7 sigmaStar_1)))
(assert (= x_8 (str.++ x_6 x_7)))
(assert (= literal_9 "\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x3e"))
(assert (= x_10 (str.++ x_8 literal_9)))
(assert (= literal_11 "\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x3e"))
(assert (= x_12 (str.++ x_10 literal_11)))
(assert (= literal_18 "\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x3e"))
(assert (= x_27 (str.++ x_12 literal_18)))
(assert (= literal_20 "\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27"))
(assert (= literal_15 "\x65\x76\x65\x6e"))
(assert (= literal_14 "\x6f\x64\x64"))
(assert (or (= x_19 literal_15) (= x_19 literal_14)))
(assert (= x_28 (str.++ literal_20 x_19)))
(assert (= literal_26 "\x26\x23\x33\x37\x3b\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x3e"))
(assert (= literal_21 "\x41"))
(assert (= literal_22 "\x42"))
(assert (= literal_23 "\x43"))
(assert (= literal_24 "\x44"))
(assert (= literal_25 "\x46"))
(assert (or (= x_32 literal_21) (= x_32 literal_22) (= x_32 literal_23) (= x_32 literal_24) (= x_32 literal_25)))
(assert (= x_34 (str.++ literal_26 x_32)))
(assert (= x_36 (str.++ x_28 x_27)))
(assert (= literal_37 "\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20"))
(assert (= x_38 (str.++ x_34 literal_37)))
(assert (= x_39 (str.++ x_36 sigmaStar_35)))
(assert (= x_40 (str.++ x_39 x_38)))
(assert (str.in.re x_40 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_40 "\x61" 0)) (str.len x_40)))
(check-sat)
(get-model)
