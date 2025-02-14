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
(assert (= literal_8 "\x3c\x74\x65\x78\x74\x61\x72\x65\x61\x20\x6e\x61\x6d\x65\x3d\x5c\x22\x61\x75\x74\x68\x5f"))
(assert (= epsilon ""))
(assert (= literal_5 "\x61\x75\x74\x68"))
(assert (or (= x_7 epsilon) (= x_7 sigmaStar_3) (= x_7 literal_5)))
(assert (= x_9 (str.++ literal_8 x_7)))
(assert (= literal_10 "\x5f\x63\x68\x61\x6e\x67\x65\x70\x61\x73\x73\x77\x6f\x72\x64\x68\x65\x6c\x70\x5c\x22\x20\x63\x6f\x6c\x73\x3d\x5c\x22\x33\x30\x5c\x22\x20\x72\x6f\x77\x73\x3d\x5c\x22\x31\x30\x5c\x22\x20\x77\x72\x61\x70\x3d\x5c\x22\x76\x69\x72\x74\x75\x61\x6c\x5c\x22\x3e"))
(assert (= x_11 (str.++ x_9 literal_10)))
(assert (str.in.re x_11 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_11 "\x61" 0)) (str.len x_11)))
(check-sat)
(get-model)
