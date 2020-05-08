(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun x_44 () String)
(declare-fun literal_6 () String)
(declare-fun literal_4 () String)
(declare-fun literal_5 () String)
(declare-fun literal_45 () String)
(declare-fun x_46 () String)
(declare-fun sigmaStar_47 () String)
(declare-fun literal_57 () String)
(declare-fun x_58 () String)
(declare-fun epsilon () String)
(declare-fun literal_56 () String)
(declare-fun x_59 () String)
(declare-fun literal_60 () String)
(declare-fun x_61 () String)
(assert (= literal_6 "\x2f"))
(assert (= literal_4 "\x77\x64\x69\x72"))
(assert (= literal_5 "\x2f"))
(assert (or (= x_44 literal_6) (= x_44 literal_4) (= x_44 literal_5)))
(assert (= literal_45 "\x2f"))
(assert (= x_46 (str.++ x_44 literal_45)))
(assert (= literal_57 "\x20\x69\x73\x69\x7a\x65\x3a\x20\x27\x27\x2c\x20\x69\x74\x79\x70\x65\x3a\x20\x27\x74\x79\x70\x65\x27\x2c\x20\x69\x77\x69\x64\x74\x68\x3a\x20\x27"))
(assert (= epsilon ""))
(assert (= literal_56 "\x55\x6e\x6b\x6e\x6f\x77\x6e"))
(assert (or (= x_58 epsilon) (= x_58 literal_56)))
(assert (= x_59 (str.++ literal_57 x_58)))
(assert (= literal_60 "\x27\x2c"))
(assert (= x_61 (str.++ x_59 literal_60)))
(assert (str.in.re x_61 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_61 "\x61" 0)) (str.len x_61)))
(check-sat)
(get-model)
