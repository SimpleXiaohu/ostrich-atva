(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_4 () String)
(declare-fun literal_6 () String)
(declare-fun x_7 () String)
(declare-fun literal_5 () String)
(declare-fun x_8 () String)
(declare-fun x_11 () String)
(declare-fun literal_10 () String)
(declare-fun x_12 () String)
(declare-fun literal_13 () String)
(declare-fun x_14 () String)
(declare-fun x_16 () String)
(declare-fun x_18 () String)
(declare-fun literal_21 () String)
(declare-fun x_30 () String)
(declare-fun literal_20 () String)
(declare-fun x_19 () String)
(declare-fun literal_17 () String)
(declare-fun x_31 () String)
(declare-fun x_39 () String)
(declare-fun literal_26 () String)
(declare-fun literal_27 () String)
(declare-fun literal_28 () String)
(declare-fun literal_29 () String)
(declare-fun literal_22 () String)
(declare-fun literal_23 () String)
(declare-fun literal_24 () String)
(declare-fun literal_25 () String)
(declare-fun x_41 () String)
(declare-fun literal_40 () String)
(declare-fun x_42 () String)
(declare-fun literal_43 () String)
(declare-fun x_44 () String)
(declare-fun x_45 () String)
(declare-fun x_46 () String)
(assert (= literal_6 "\x2f"))
(assert (= x_7 (str.++ sigmaStar_4 literal_6)))
(assert (= literal_5 "\x20\x2f\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x0d\x0a\x20\x20\x20\x3c\x62\x72\x3e\x0d\x0a\x0d\x0a\x20\x20\x20\x3c\x74\x61\x62\x6c\x65\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x30\x27\x20\x62\x6f\x72\x64\x65\x72\x3d\x27\x30\x27\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x77\x69\x64\x74\x68\x3d\x27\x34\x35\x30\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x3e\x0d\x0a\x09\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x62\x75\x74\x74\x6f\x6e\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x45\x64\x69\x74\x20\x54\x65\x72\x6d\x27\x20\x6f\x6e\x43\x6c\x69\x63\x6b\x3d\x27\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x74\x65\x72\x6d\x2e\x65\x64\x69\x74\x74\x65\x72\x6d\x2e\x76\x61\x6c\x75\x65\x3d\x31\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x74\x65\x72\x6d\x2e\x70\x61\x67\x65\x32\x2e\x76\x61\x6c\x75\x65\x3d\x36\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x74\x65\x72\x6d\x2e\x73\x75\x62\x6d\x69\x74\x28\x29\x3b\x27\x3e\x0d\x0a\x09\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x62\x75\x74\x74\x6f\x6e\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x43\x61\x6e\x63\x65\x6c\x27\x20\x6f\x6e\x43\x6c\x69\x63\x6b\x3d\x27\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x74\x65\x72\x6d\x2e\x70\x61\x67\x65\x32\x2e\x76\x61\x6c\x75\x65\x3d\x36\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x74\x65\x72\x6d\x2e\x73\x75\x62\x6d\x69\x74\x28\x29\x3b\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x65\x64\x69\x74\x74\x65\x72\x6d\x27\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x74\x65\x72\x6d\x69\x64\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_8 (str.++ literal_5 sigmaStar_1)))
(assert (= x_11 (str.++ x_7 sigmaStar_4)))
(assert (= literal_10 "\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x70\x61\x67\x65\x32\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_12 (str.++ x_8 literal_10)))
(assert (= literal_13 "\x2f"))
(assert (= x_14 (str.++ x_11 literal_13)))
(assert (= x_16 (str.++ x_12 sigmaStar_2)))
(assert (= x_18 (str.++ x_14 sigmaStar_4)))
(assert (= literal_21 "\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x6c\x6f\x67\x6f\x75\x74\x27\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x70\x61\x67\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_30 (str.++ x_16 literal_21)))
(assert (= literal_20 "\x3c\x68\x31\x3e\x45\x64\x69\x74\x20\x54\x65\x72\x6d\x3c\x2f\x68\x31\x3e\x0d\x0a\x0d\x0a\x20\x20\x3c\x66\x6f\x72\x6d\x20\x6e\x61\x6d\x65\x3d\x27\x65\x64\x69\x74\x74\x65\x72\x6d\x27\x20\x61\x63\x74\x69\x6f\x6e\x3d\x27\x2e\x2f\x69\x6e\x64\x65\x78\x2e\x70\x68\x70\x27\x20\x6d\x65\x74\x68\x6f\x64\x3d\x27\x50\x4f\x53\x54\x27\x3e\x0d\x0a\x20\x20\x3c\x62\x72\x3e\x3c\x62\x72\x3e\x3c\x62\x72\x3e\x0d\x0a\x20\x20\x3c\x74\x61\x62\x6c\x65\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x27\x30\x27\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x27\x35\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x64\x79\x6e\x61\x6d\x69\x63\x6c\x69\x73\x74\x27\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x77\x69\x64\x74\x68\x3d\x27\x34\x35\x30\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x68\x65\x61\x64\x65\x72\x27\x3e\x0d\x0a\x09\x3c\x74\x68\x3e\x54\x65\x72\x6d\x20\x4e\x61\x6d\x65\x3c\x2f\x74\x68\x3e\x0d\x0a\x09\x3c\x74\x68\x3e\x53\x74\x61\x72\x74\x20\x44\x61\x74\x65\x3c\x2f\x74\x68\x3e\x0d\x0a\x09\x3c\x74\x68\x3e\x45\x6e\x64\x20\x44\x61\x74\x65\x3c\x2f\x74\x68\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x6e\x61\x6d\x65\x3d\x27\x74\x69\x74\x6c\x65\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x31\x35\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x20\x2f\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x74\x65\x78\x74\x27\x20\x6e\x61\x6d\x65\x3d\x27\x73\x74\x61\x72\x74\x64\x61\x74\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= literal_17 ""))
(assert (or (= x_19 x_18) (= x_19 literal_17)))
(assert (= x_31 (str.++ literal_20 x_19)))
(assert (= literal_26 "\x31"))
(assert (= literal_27 "\x30"))
(assert (= literal_28 "\x32"))
(assert (= literal_29 "\x30"))
(assert (= literal_22 "\x32"))
(assert (= literal_23 "\x34"))
(assert (= literal_24 "\x30"))
(assert (= literal_25 "\x35"))
(assert (or (= x_39 literal_26) (= x_39 literal_27) (= x_39 literal_28) (= x_39 literal_29) (= x_39 sigmaStar_0) (= x_39 literal_22) (= x_39 literal_23) (= x_39 literal_24) (= x_39 literal_25)))
(assert (= x_41 (str.++ x_30 x_39)))
(assert (= literal_40 "\x27\x20\x2f\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x6e\x61\x6d\x65\x3d\x27\x65\x6e\x64\x64\x61\x74\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_42 (str.++ x_31 literal_40)))
(assert (= literal_43 "\x3e\x0d\x0a\x0d\x0a\x20\x3c\x2f\x66\x6f\x72\x6d\x3e\x0d\x0a\x0d\x0a\x20\x3c\x74\x61\x62\x6c\x65\x20\x77\x69\x64\x74\x68\x3d\x35\x32\x30\x27\x20\x62\x6f\x72\x64\x65\x72\x3d\x30\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x30\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x30\x20\x68\x65\x69\x67\x68\x74\x3d\x31\x3e\x0d\x0a\x20\x20\x3c\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x20\x76\x61\x6c\x69\x67\x6e\x3d\x27\x74\x6f\x70\x27\x3e\x0d\x0a\x09\x26\x6e\x62\x73\x70\x3b\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x20"))
(assert (= x_44 (str.++ x_41 literal_43)))
(assert (= x_45 (str.++ x_42 x_19)))
(assert (= x_46 (str.++ x_45 x_44)))
(assert (str.in.re x_46 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_46 "\x61" 0)) (str.len x_46)))
(check-sat)
(get-model)
