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
(declare-fun literal_23 () String)
(declare-fun x_56 () String)
(declare-fun epsilon () String)
(declare-fun literal_10 () String)
(declare-fun literal_15 () String)
(declare-fun literal_16 () String)
(declare-fun literal_14 () String)
(declare-fun x_57 () String)
(declare-fun literal_58 () String)
(declare-fun x_59 () String)
(assert (= literal_23 "\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x5c\x22\x68\x69\x64\x64\x65\x6e\x5c\x22\x20\x6e\x61\x6d\x65\x3d\x5c\x22\x70\x61\x67\x65\x69\x64\x5c\x22\x20\x76\x61\x6c\x75\x65\x3d\x5c\x22"))
(assert (= epsilon ""))
(assert (= literal_10 "\x70\x61\x67\x65\x69\x64"))
(assert (= literal_15 "\x30"))
(assert (= literal_16 "\x30"))
(assert (= literal_14 "\x6c\x65\x73\x73\x6f\x6e\x5f\x61\x6e\x73\x77\x65\x72\x73"))
(assert (or (= x_56 epsilon) (= x_56 sigmaStar_8) (= x_56 literal_10) (= x_56 sigmaStar_3) (= x_56 literal_15) (= x_56 sigmaStar_2) (= x_56 literal_16) (= x_56 sigmaStar_1) (= x_56 literal_14)))
(assert (= x_57 (str.++ literal_23 x_56)))
(assert (= literal_58 "\x5c\x22\x3e\x5c\x6e"))
(assert (= x_59 (str.++ x_57 literal_58)))
(assert (str.in.re x_59 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_59 "\x61" 0)) (str.len x_59)))
(check-sat)
(get-model)
