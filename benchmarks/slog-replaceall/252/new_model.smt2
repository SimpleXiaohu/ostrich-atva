(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_4 () String)
(declare-fun literal_3 () String)
(declare-fun x_2 () String)
(declare-fun epsilon () String)
(declare-fun x_6 () String)
(declare-fun literal_7 () String)
(declare-fun x_8 () String)
(declare-fun literal_5 () String)
(declare-fun x_10 () String)
(declare-fun literal_9 () String)
(declare-fun x_11 () String)
(declare-fun x_12 () String)
(declare-fun x_14 () String)
(declare-fun sigmaStar_15 () String)
(declare-fun literal_16 () String)
(declare-fun x_17 () String)
(declare-fun x_18 () String)
(declare-fun literal_19 () String)
(declare-fun x_20 () String)
(declare-fun sigmaStar_21 () String)
(declare-fun sigmaStar_23 () String)
(declare-fun sigmaStar_24 () String)
(declare-fun sigmaStar_27 () String)
(declare-fun sigmaStar_30 () String)
(declare-fun sigmaStar_32 () String)
(declare-fun sigmaStar_35 () String)
(declare-fun x_31 () String)
(declare-fun literal_29 () String)
(declare-fun literal_37 () String)
(declare-fun x_36 () String)
(declare-fun x_38 () String)
(declare-fun literal_39 () String)
(declare-fun x_40 () String)
(assert (= literal_3 "\x2d\x61\x20\x2d\x48\x20\x2d\x2d\x6c\x61\x6e\x67\x3d"))
(assert (= epsilon ""))
(assert (or (= x_2 epsilon) (= x_2 sigmaStar_0)))
(assert (= x_6 (str.++ literal_3 x_2)))
(assert (= literal_7 "\x20\x2d\x2d\x65\x6e\x63\x6f\x64\x69\x6e\x67\x3d\x75\x74\x66\x2d\x38"))
(assert (= x_8 (str.++ x_6 literal_7)))
(assert (= literal_5 "\x20\x2d\x2d\x61\x64\x64\x2d\x65\x78\x74\x72\x61\x2d\x64\x69\x63\x74\x73\x3d"))
(assert (= x_10 (str.++ x_8 literal_5)))
(assert (= literal_9 "\x20"))
(assert (= x_11 (str.++ sigmaStar_4 literal_9)))
(assert (or (= x_12 x_8) (= x_12 x_10)))
(assert (= x_14 (str.++ x_11 x_12)))
(assert (= literal_16 "\x20\x3c\x20"))
(assert (= x_17 (str.++ x_14 literal_16)))
(assert (= x_18 (str.++ x_17 sigmaStar_15)))
(assert (= literal_19 "\x20\x32\x3e\x26\x31"))
(assert (= x_20 (str.++ x_18 literal_19)))
(assert (= literal_29 ""))
(assert (or (= x_31 sigmaStar_30) (= x_31 literal_29)))
(assert (= x_36 (str.replaceall x_31 "\x2f\x27\x2f" "\x5c\x27")))
(assert (= literal_37 "\x27"))
(assert (= x_38 (str.++ literal_37 x_36)))
(assert (= literal_39 "\x27"))
(assert (= x_40 (str.++ x_38 literal_39)))
(assert (str.in.re x_40 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (> (* 2 (str.indexof x_38 "\x61" 0)) (str.len x_38)))
(check-sat)
(get-model)
