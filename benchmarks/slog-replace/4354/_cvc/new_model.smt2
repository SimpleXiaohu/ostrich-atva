(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_3 () String)
(declare-fun x_5 () String)
(declare-fun sigmaStar_9 () String)
(declare-fun sigmaStar_11 () String)
(declare-fun literal_8 () String)
(declare-fun x_13 () String)
(declare-fun x_12 () String)
(declare-fun x_14 () String)
(declare-fun literal_15 () String)
(declare-fun x_16 () String)
(declare-fun x_18 () String)
(declare-fun x_17 () String)
(declare-fun x_19 () String)
(declare-fun literal_20 () String)
(declare-fun x_21 () String)
(assert (= literal_3 "\x3c\x73\x70\x61\x6e\x20\x63\x6c\x61\x73\x73\x3d\x27\x61\x6c\x74\x27\x3e"))
(assert (= x_5 (str.++ literal_3 sigmaStar_0)))
(assert (= literal_8 "\x3c\x2f\x73\x70\x61\x6e\x3e\x20"))
(assert (= x_13 (str.++ x_5 literal_8)))
(assert (or (= x_12 sigmaStar_9) (= x_12 sigmaStar_11)))
(assert (= x_14 (str.++ x_13 x_12)))
(assert (= literal_15 "\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x74\x64\x3e\x0d\x0a\x3c\x74\x61\x62\x6c\x65\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x27\x30\x27\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x27\x30\x27\x20\x77\x69\x64\x74\x68\x3d\x27\x31\x30\x30\x25\x27\x3e\x0d\x0a\x3c\x74\x72\x3e\x0d\x0a\x3c\x74\x64\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x31\x27\x3e"))
(assert (= x_16 (str.++ x_14 literal_15)))
(assert (= x_18 (str.++ x_16 sigmaStar_1)))
(assert (or (= x_17 sigmaStar_9) (= x_17 sigmaStar_11)))
(assert (= x_19 (str.++ x_18 x_17)))
(assert (= literal_20 "\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x31\x27\x3e\x5c\x6e"))
(assert (= x_21 (str.++ x_19 literal_20)))
(assert (str.in.re x_21 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_21 "\x61" 0)) (str.len x_21)))
(check-sat)
(get-model)
