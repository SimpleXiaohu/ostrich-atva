(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun sigmaStar_4 () String)
(declare-fun sigmaStar_5 () String)
(declare-fun sigmaStar_6 () String)
(declare-fun sigmaStar_7 () String)
(declare-fun sigmaStar_8 () String)
(declare-fun sigmaStar_9 () String)
(declare-fun sigmaStar_10 () String)
(declare-fun sigmaStar_11 () String)
(declare-fun literal_12 () String)
(declare-fun x_14 () String)
(declare-fun literal_13 () String)
(declare-fun x_15 () String)
(declare-fun literal_16 () String)
(declare-fun x_25 () String)
(declare-fun literal_17 () String)
(declare-fun x_26 () String)
(declare-fun literal_18 () String)
(declare-fun x_27 () String)
(declare-fun literal_19 () String)
(declare-fun x_28 () String)
(declare-fun literal_20 () String)
(declare-fun x_29 () String)
(declare-fun literal_21 () String)
(declare-fun x_30 () String)
(declare-fun literal_22 () String)
(declare-fun x_31 () String)
(declare-fun literal_23 () String)
(declare-fun x_32 () String)
(declare-fun literal_24 () String)
(declare-fun x_33 () String)
(declare-fun literal_34 () String)
(declare-fun x_41 () String)
(declare-fun literal_35 () String)
(declare-fun x_42 () String)
(declare-fun x_43 () String)
(declare-fun literal_36 () String)
(declare-fun x_44 () String)
(declare-fun literal_37 () String)
(declare-fun x_45 () String)
(declare-fun literal_38 () String)
(declare-fun x_46 () String)
(declare-fun literal_39 () String)
(declare-fun x_47 () String)
(declare-fun x_48 () String)
(declare-fun literal_40 () String)
(declare-fun x_49 () String)
(declare-fun literal_59 () String)
(declare-fun x_58 () String)
(declare-fun x_60 () String)
(declare-fun literal_61 () String)
(declare-fun x_62 () String)
(assert (= literal_12 "\x3c\x62\x3e"))
(assert (= x_14 (str.++ literal_12 sigmaStar_6)))
(assert (= literal_13 "\x3c\x62\x3e"))
(assert (= x_15 (str.++ literal_13 sigmaStar_11)))
(assert (= literal_16 "\x3c\x62\x3e"))
(assert (= x_25 (str.++ literal_16 sigmaStar_4)))
(assert (= literal_17 "\x3c\x62\x3e"))
(assert (= x_26 (str.++ literal_17 sigmaStar_3)))
(assert (= literal_18 "\x3c\x2f\x62\x3e\x3c\x62\x72\x3e\x5c\x6e"))
(assert (= x_27 (str.++ x_14 literal_18)))
(assert (= literal_19 "\x3c\x62\x3e"))
(assert (= x_28 (str.++ literal_19 sigmaStar_5)))
(assert (= literal_20 "\x3c\x62\x3e"))
(assert (= x_29 (str.++ literal_20 sigmaStar_2)))
(assert (= literal_21 "\x3c\x62\x3e"))
(assert (= x_30 (str.++ literal_21 sigmaStar_10)))
(assert (= literal_22 "\x3c\x62\x3e"))
(assert (= x_31 (str.++ literal_22 sigmaStar_8)))
(assert (= literal_23 "\x3c\x2f\x62\x3e\x3c\x62\x72\x3e\x5c\x6e"))
(assert (= x_32 (str.++ x_15 literal_23)))
(assert (= literal_24 "\x3c\x62\x3e"))
(assert (= x_33 (str.++ literal_24 sigmaStar_0)))
(assert (= literal_34 "\x3c\x2f\x62\x3e"))
(assert (= x_41 (str.++ x_25 literal_34)))
(assert (= literal_35 "\x3c\x2f\x62\x3e"))
(assert (= x_42 (str.++ x_26 literal_35)))
(assert (= x_43 (str.++ x_27 sigmaStar_9)))
(assert (= literal_36 "\x3c\x2f\x62\x3e"))
(assert (= x_44 (str.++ x_28 literal_36)))
(assert (= literal_37 "\x3c\x2f\x62\x3e"))
(assert (= x_45 (str.++ x_29 literal_37)))
(assert (= literal_38 "\x3c\x2f\x62\x3e"))
(assert (= x_46 (str.++ x_30 literal_38)))
(assert (= literal_39 "\x3c\x2f\x62\x3e"))
(assert (= x_47 (str.++ x_31 literal_39)))
(assert (= x_48 (str.++ x_32 sigmaStar_7)))
(assert (= literal_40 "\x3c\x2f\x62\x3e"))
(assert (= x_49 (str.++ x_33 literal_40)))
(assert (= literal_59 "\x3c\x64\x69\x76\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x3e"))
(assert (or (= x_58 x_44) (= x_58 x_43) (= x_58 x_42) (= x_58 x_41) (= x_58 sigmaStar_1) (= x_58 x_49) (= x_58 x_48) (= x_58 x_47) (= x_58 x_46) (= x_58 x_45)))
(assert (= x_60 (str.++ literal_59 x_58)))
(assert (= literal_61 "\x3c\x2f\x64\x69\x76\x3e\x5c\x6e"))
(assert (= x_62 (str.++ x_60 literal_61)))
(assert (str.in.re x_62 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_62 "\x61" 0)) (str.len x_62)))
(check-sat)
(get-model)
