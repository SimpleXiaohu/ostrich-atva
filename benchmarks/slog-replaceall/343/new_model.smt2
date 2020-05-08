(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_5 () String)
(declare-fun x_2 () String)
(declare-fun literal_0 () String)
(declare-fun literal_1 () String)
(declare-fun sigmaStar_9 () String)
(declare-fun x_6 () String)
(declare-fun x_10 () String)
(declare-fun sigmaStar_12 () String)
(declare-fun sigmaStar_15 () String)
(declare-fun sigmaStar_16 () String)
(declare-fun sigmaStar_19 () String)
(declare-fun sigmaStar_22 () String)
(declare-fun sigmaStar_26 () String)
(declare-fun x_23 () String)
(declare-fun sigmaStar_30 () String)
(declare-fun x_27 () String)
(declare-fun sigmaStar_34 () String)
(declare-fun x_31 () String)
(declare-fun x_36 () String)
(declare-fun x_35 () String)
(assert (= literal_0 "\x70\x72\x69\x6e\x74\x5f\x68\x65\x61\x64\x65\x72\x28\x29\x20\x77\x61\x73\x20\x63\x61\x6c\x6c\x65\x64\x20\x6d\x6f\x72\x65\x20\x74\x68\x61\x6e\x20\x6f\x6e\x63\x65\x20\x2d\x20\x74\x68\x69\x73\x20\x73\x68\x6f\x75\x6c\x64\x20\x6e\x6f\x74\x20\x68\x61\x70\x70\x65\x6e\x2e\x20\x20\x50\x6c\x65\x61\x73\x65\x20\x63\x68\x65\x63\x6b\x20\x74\x68\x65\x20\x63\x6f\x64\x65\x20\x66\x6f\x72\x20\x74\x68\x69\x73\x20\x70\x61\x67\x65\x20\x63\x6c\x6f\x73\x65\x6c\x79\x2e\x20\x4e\x6f\x74\x65\x3a\x20\x65\x72\x72\x6f\x72\x28\x29\x20\x61\x6e\x64\x20\x72\x65\x64\x69\x72\x65\x63\x74\x28\x29\x20\x61\x72\x65\x20\x6e\x6f\x77\x20\x73\x61\x66\x65\x20\x74\x6f\x20\x63\x61\x6c\x6c\x20\x61\x66\x74\x65\x72\x20\x70\x72\x69\x6e\x74\x5f\x68\x65\x61\x64\x65\x72\x28\x29\x2e"))
(assert (= literal_1 "\x53\x45\x43\x55\x52\x49\x54\x59\x20\x57\x41\x52\x4e\x49\x4e\x47\x3a\x20\x6c\x6f\x67\x67\x65\x64\x20\x69\x6e\x74\x72\x75\x73\x69\x6f\x6e\x20\x61\x74\x74\x65\x6d\x70\x74\x20\x61\x67\x61\x69\x6e\x73\x74\x20\x6c\x69\x62\x2f\x61\x64\x6f\x64\x62\x2f\x74\x65\x73\x74\x73\x2f\x74\x6d\x73\x73\x71\x6c\x2e\x70\x68\x70"))
(assert (or (= x_2 literal_0) (= x_2 literal_1)))
(assert (= x_6 (str.replaceall x_2 "\x2f\x28\x26\x23\x5b\x30\x2d\x39\x5d\x2b\x29\x28\x3b\x3f\x29\x2f" "\x5c\x31\x3b")))
(assert (= x_10 (str.replaceall x_6 "\x2f\x28\x26\x23\x78\x5b\x30\x2d\x39\x61\x2d\x66\x41\x2d\x46\x5d\x2b\x29\x28\x3b\x3f\x29\x2f" "\x5c\x31\x3b")))
(assert (or (= x_23 sigmaStar_22) (= x_23 literal_1)))
(assert (= x_27 (str.replaceall x_23 "\x5c\x5c\x27" "\x27")))
(assert (= x_31 (str.replaceall x_27 "\x5c\x5c\x22" "\x22")))
(assert (= x_35 (str.replaceall x_31 "\x5c\x5c\x5c\x5c" "\x5c\x5c")))
(assert (or (= x_36 x_35) (= x_36 x_23)))
(assert (str.in.re x_36 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (> (* 2 (str.indexof x_10 "\x61" 0)) (str.len x_10)))
(check-sat)
(get-model)
