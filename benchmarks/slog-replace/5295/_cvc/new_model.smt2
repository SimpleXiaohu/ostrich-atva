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
(declare-fun x_19 () String)
(declare-fun literal_18 () String)
(declare-fun x_28 () String)
(declare-fun x_37 () String)
(declare-fun literal_20 () String)
(declare-fun literal_21 () String)
(declare-fun literal_26 () String)
(declare-fun literal_27 () String)
(declare-fun literal_22 () String)
(declare-fun literal_23 () String)
(declare-fun literal_24 () String)
(declare-fun literal_25 () String)
(declare-fun x_40 () String)
(declare-fun literal_42 () String)
(declare-fun x_43 () String)
(declare-fun literal_41 () String)
(declare-fun x_38 () String)
(declare-fun literal_29 () String)
(declare-fun x_44 () String)
(declare-fun x_45 () String)
(assert (= literal_6 "\x2f"))
(assert (= x_7 (str.++ sigmaStar_4 literal_6)))
(assert (= literal_5 "\x20\x2f\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x0d\x0a\x20\x20\x20\x3c\x62\x72\x3e\x0d\x0a\x0d\x0a\x20\x20\x20\x3c\x74\x61\x62\x6c\x65\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x30\x27\x20\x62\x6f\x72\x64\x65\x72\x3d\x27\x30\x27\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x77\x69\x64\x74\x68\x3d\x27\x36\x30\x30\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x3e\x0d\x0a\x09\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x62\x75\x74\x74\x6f\x6e\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x45\x64\x69\x74\x20\x41\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x27\x20\x6f\x6e\x43\x6c\x69\x63\x6b\x3d\x27\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x61\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x61\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x2e\x76\x61\x6c\x75\x65\x3d\x31\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x61\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x2e\x70\x61\x67\x65\x32\x2e\x76\x61\x6c\x75\x65\x3d\x34\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x61\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x2e\x73\x75\x62\x6d\x69\x74\x28\x29\x3b\x27\x3e\x0d\x0a\x09\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x62\x75\x74\x74\x6f\x6e\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x43\x61\x6e\x63\x65\x6c\x27\x20\x6f\x6e\x43\x6c\x69\x63\x6b\x3d\x27\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x61\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x2e\x70\x61\x67\x65\x32\x2e\x76\x61\x6c\x75\x65\x3d\x34\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x61\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x2e\x73\x75\x62\x6d\x69\x74\x28\x29\x3b\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x65\x64\x69\x74\x61\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x27\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x61\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x69\x64\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_8 (str.++ literal_5 sigmaStar_2)))
(assert (= x_11 (str.++ x_7 sigmaStar_4)))
(assert (= literal_10 "\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x70\x61\x67\x65\x32\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_12 (str.++ x_8 literal_10)))
(assert (= literal_13 "\x2f"))
(assert (= x_14 (str.++ x_11 literal_13)))
(assert (= x_16 (str.++ x_12 sigmaStar_0)))
(assert (= x_19 (str.++ x_14 sigmaStar_4)))
(assert (= literal_18 "\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x6c\x6f\x67\x6f\x75\x74\x27\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x70\x61\x67\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_28 (str.++ x_16 literal_18)))
(assert (= literal_20 "\x32"))
(assert (= literal_21 "\x34"))
(assert (= literal_26 "\x32"))
(assert (= literal_27 "\x30"))
(assert (= literal_22 "\x30"))
(assert (= literal_23 "\x35"))
(assert (= literal_24 "\x31"))
(assert (= literal_25 "\x30"))
(assert (or (= x_37 literal_20) (= x_37 literal_21) (= x_37 literal_26) (= x_37 literal_27) (= x_37 sigmaStar_1) (= x_37 literal_22) (= x_37 literal_23) (= x_37 literal_24) (= x_37 literal_25)))
(assert (= x_40 (str.++ x_28 x_37)))
(assert (= literal_42 "\x3e\x0d\x0a\x0d\x0a\x20\x3c\x2f\x66\x6f\x72\x6d\x3e\x0d\x0a\x0d\x0a\x20\x3c\x74\x61\x62\x6c\x65\x20\x77\x69\x64\x74\x68\x3d\x35\x32\x30\x27\x20\x62\x6f\x72\x64\x65\x72\x3d\x30\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x30\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x30\x20\x68\x65\x69\x67\x68\x74\x3d\x31\x3e\x0d\x0a\x20\x20\x3c\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x20\x76\x61\x6c\x69\x67\x6e\x3d\x27\x74\x6f\x70\x27\x3e\x0d\x0a\x09\x26\x6e\x62\x73\x70\x3b\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x20"))
(assert (= x_43 (str.++ x_40 literal_42)))
(assert (= literal_41 "\x3c\x68\x31\x3e\x45\x64\x69\x74\x20\x41\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x3c\x2f\x68\x31\x3e\x0d\x0a\x0d\x0a\x20\x20\x3c\x66\x6f\x72\x6d\x20\x6e\x61\x6d\x65\x3d\x27\x65\x64\x69\x74\x61\x6e\x6e\x6f\x75\x6e\x63\x65\x6d\x65\x6e\x74\x27\x20\x61\x63\x74\x69\x6f\x6e\x3d\x27\x2e\x2f\x69\x6e\x64\x65\x78\x2e\x70\x68\x70\x27\x20\x6d\x65\x74\x68\x6f\x64\x3d\x27\x50\x4f\x53\x54\x27\x3e\x0d\x0a\x20\x20\x3c\x62\x72\x3e\x3c\x62\x72\x3e\x3c\x62\x72\x3e\x0d\x0a\x20\x20\x3c\x74\x61\x62\x6c\x65\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x27\x30\x27\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x27\x35\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x64\x79\x6e\x61\x6d\x69\x63\x6c\x69\x73\x74\x27\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x77\x69\x64\x74\x68\x3d\x27\x36\x30\x30\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x68\x65\x61\x64\x65\x72\x27\x3e\x0d\x0a\x09\x3c\x74\x68\x3e\x54\x69\x74\x6c\x65\x3c\x2f\x74\x68\x3e\x0d\x0a\x09\x3c\x74\x68\x3e\x4d\x65\x73\x73\x61\x67\x65\x3c\x2f\x74\x68\x3e\x0d\x0a\x09\x3c\x74\x68\x3e\x44\x61\x74\x65\x3c\x2f\x74\x68\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x20\x76\x61\x6c\x69\x67\x6e\x3d\x27\x74\x6f\x70\x27\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x6e\x61\x6d\x65\x3d\x27\x74\x69\x74\x6c\x65\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x31\x35\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x20\x2f\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x74\x65\x78\x74\x61\x72\x65\x61\x20\x6e\x61\x6d\x65\x3d\x6d\x65\x73\x73\x61\x67\x65\x27\x20\x72\x6f\x77\x73\x3d\x27\x35\x27\x20\x63\x6f\x6c\x73\x3d\x27\x33\x30\x27\x3e\x3c\x2f\x74\x65\x78\x74\x61\x72\x65\x61\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x6e\x61\x6d\x65\x3d\x27\x64\x61\x74\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= literal_29 ""))
(assert (or (= x_38 x_19) (= x_38 literal_29)))
(assert (= x_44 (str.++ literal_41 x_38)))
(assert (= x_45 (str.++ x_44 x_43)))
(assert (str.in.re x_45 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_45 "\x61" 0)) (str.len x_45)))
(check-sat)
(get-model)
