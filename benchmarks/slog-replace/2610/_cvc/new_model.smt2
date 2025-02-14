(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun literal_8 () String)
(declare-fun x_7 () String)
(declare-fun epsilon () String)
(declare-fun literal_5 () String)
(declare-fun x_9 () String)
(declare-fun literal_10 () String)
(declare-fun x_11 () String)
(declare-fun literal_12 () String)
(declare-fun x_13 () String)
(assert (= literal_8 "\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x5c\x22\x74\x65\x78\x74\x5c\x22\x20\x6e\x61\x6d\x65\x3d\x5c\x22\x61\x75\x74\x68\x5f"))
(assert (= epsilon ""))
(assert (= literal_5 "\x61\x75\x74\x68"))
(assert (or (= x_7 epsilon) (= x_7 sigmaStar_3) (= x_7 literal_5)))
(assert (= x_9 (str.++ literal_8 x_7)))
(assert (= literal_10 "\x5f\x63\x68\x61\x6e\x67\x65\x70\x61\x73\x73\x77\x6f\x72\x64\x75\x72\x6c\x5c\x22\x20\x73\x69\x7a\x65\x3d\x5c\x22\x34\x30\x5c\x22\x20\x76\x61\x6c\x75\x65\x3d\x5c\x22"))
(assert (= x_11 (str.++ x_9 literal_10)))
(assert (= literal_12 "\x5c\x22\x20\x2f\x3e"))
(assert (= x_13 (str.++ x_11 literal_12)))
(assert (str.in.re x_13 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_13 "\x61" 0)) (str.len x_13)))
(check-sat)
(get-model)
