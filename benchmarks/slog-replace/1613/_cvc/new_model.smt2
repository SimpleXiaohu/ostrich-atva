(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun x_5 () String)
(declare-fun literal_2 () String)
(declare-fun literal_3 () String)
(declare-fun literal_1 () String)
(declare-fun literal_6 () String)
(declare-fun x_7 () String)
(declare-fun x_10 () String)
(declare-fun literal_11 () String)
(declare-fun x_13 () String)
(declare-fun sigmaStar_15 () String)
(declare-fun sigmaStar_20 () String)
(declare-fun literal_18 () String)
(declare-fun x_21 () String)
(declare-fun literal_12 () String)
(declare-fun x_26 () String)
(declare-fun literal_19 () String)
(declare-fun x_22 () String)
(declare-fun x_27 () String)
(declare-fun literal_23 () String)
(declare-fun x_28 () String)
(declare-fun literal_29 () String)
(declare-fun x_32 () String)
(declare-fun literal_30 () String)
(declare-fun x_33 () String)
(declare-fun literal_31 () String)
(declare-fun x_34 () String)
(declare-fun x_35 () String)
(declare-fun x_37 () String)
(declare-fun x_36 () String)
(declare-fun x_38 () String)
(declare-fun x_42 () String)
(assert (= literal_2 "\x26"))
(assert (= literal_3 ""))
(assert (= literal_1 "\x3f"))
(assert (or (= x_5 literal_2) (= x_5 literal_3) (= x_5 literal_1)))
(assert (= literal_6 "\x61\x69\x63\x63\x5f\x73\x69\x64\x3d"))
(assert (= x_7 (str.++ x_5 literal_6)))
(assert (= x_10 (str.++ x_7 sigmaStar_0)))
(assert (= literal_11 "\x26\x61\x69\x63\x63\x5f\x75\x72\x6c\x3d"))
(assert (= x_13 (str.++ x_10 literal_11)))
(assert (= literal_18 "\x2f\x66\x69\x6c\x65\x2e\x70\x68\x70\x3f\x66\x69\x6c\x65\x3d\x2f\x2f"))
(assert (= literal_12 "\x6d\x6f\x64\x64\x61\x74\x61\x2f\x73\x63\x6f\x72\x6d\x2f"))
(assert (or (= x_21 sigmaStar_15) (= x_21 literal_12)))
(assert (= x_26 (str.++ literal_18 x_21)))
(assert (= literal_19 "\x2f\x66\x69\x6c\x65\x2e\x70\x68\x70\x2f\x2f"))
(assert (or (= x_22 sigmaStar_15) (= x_22 literal_12)))
(assert (= x_27 (str.++ literal_19 x_22)))
(assert (= literal_23 "\x2f\x6d\x6f\x64\x2f\x73\x63\x6f\x72\x6d\x2f\x61\x69\x63\x63\x2e\x70\x68\x70"))
(assert (= x_28 (str.++ x_13 literal_23)))
(assert (= literal_29 "\x2f"))
(assert (= x_32 (str.++ x_26 literal_29)))
(assert (= literal_30 "\x2f"))
(assert (= x_33 (str.++ x_27 literal_30)))
(assert (= literal_31 "\x2f"))
(assert (= x_34 (str.++ sigmaStar_20 literal_31)))
(assert (or (= x_35 literal_2) (= x_35 literal_3) (= x_35 x_28) (= x_35 literal_1)))
(assert (= x_37 (str.++ x_32 x_35)))
(assert (or (= x_36 literal_2) (= x_36 literal_3) (= x_36 x_28) (= x_36 literal_1)))
(assert (= x_38 (str.++ x_33 x_36)))
(assert (or (= x_42 literal_2) (= x_42 literal_3) (= x_42 x_28) (= x_42 x_38) (= x_42 literal_1) (= x_42 x_37) (= x_42 x_34)))
(assert (str.in.re x_42 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_42 "\x61" 0)) (str.len x_42)))
(check-sat)
(get-model)
