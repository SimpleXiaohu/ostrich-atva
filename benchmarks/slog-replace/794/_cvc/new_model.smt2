(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun literal_4 () String)
(declare-fun x_5 () String)
(declare-fun literal_6 () String)
(declare-fun x_7 () String)
(declare-fun literal_8 () String)
(declare-fun x_9 () String)
(assert (= literal_4 "\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x22\x72\x61\x64\x69\x6f\x22\x20\x6e\x61\x6d\x65\x3d\x22\x61\x6e\x73\x77\x65\x72\x22\x20\x76\x61\x6c\x75\x65\x3d\x22\x22\x20\x61\x6c\x74\x3d\x22"))
(assert (= x_5 (str.++ literal_4 sigmaStar_3)))
(assert (= literal_6 "\x22"))
(assert (= x_7 (str.++ x_5 literal_6)))
(assert (= literal_8 "\x20\x2f\x3e"))
(assert (= x_9 (str.++ x_7 literal_8)))
(assert (str.in.re x_9 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_9 "\x61" 0)) (str.len x_9)))
(check-sat)
(get-model)
