(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun literal_4 () String)
(declare-fun x_5 () String)
(declare-fun literal_6 () String)
(declare-fun x_7 () String)
(declare-fun x_8 () String)
(declare-fun literal_10 () String)
(declare-fun x_11 () String)
(declare-fun x_13 () String)
(declare-fun sigmaStar_17 () String)
(declare-fun literal_15 () String)
(declare-fun x_18 () String)
(declare-fun literal_19 () String)
(declare-fun x_20 () String)
(declare-fun sigmaStar_23 () String)
(declare-fun x_26 () String)
(declare-fun literal_25 () String)
(declare-fun x_27 () String)
(declare-fun literal_24 () String)
(declare-fun x_29 () String)
(declare-fun literal_28 () String)
(declare-fun x_30 () String)
(declare-fun x_33 () String)
(declare-fun literal_31 () String)
(declare-fun x_35 () String)
(declare-fun literal_36 () String)
(declare-fun x_45 () String)
(declare-fun x_34 () String)
(declare-fun literal_32 () String)
(declare-fun x_46 () String)
(declare-fun x_54 () String)
(declare-fun literal_40 () String)
(declare-fun literal_41 () String)
(declare-fun literal_42 () String)
(declare-fun literal_43 () String)
(declare-fun literal_37 () String)
(declare-fun literal_38 () String)
(declare-fun literal_39 () String)
(declare-fun literal_44 () String)
(declare-fun x_56 () String)
(declare-fun literal_55 () String)
(declare-fun x_57 () String)
(declare-fun literal_58 () String)
(declare-fun x_59 () String)
(declare-fun x_60 () String)
(declare-fun x_61 () String)
(assert (= literal_4 "\x20\x2f\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x0d\x0a\x20\x20\x20\x3c\x62\x72\x3e\x0d\x0a\x0d\x0a\x20\x20\x20\x3c\x74\x61\x62\x6c\x65\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x30\x27\x20\x62\x6f\x72\x64\x65\x72\x3d\x27\x30\x27\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x77\x69\x64\x74\x68\x3d\x27\x37\x30\x30\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x3e\x0d\x0a\x09\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x62\x75\x74\x74\x6f\x6e\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x45\x64\x69\x74\x20\x41\x73\x73\x69\x67\x6e\x6d\x65\x6e\x74\x27\x20\x6f\x6e\x43\x6c\x69\x63\x6b\x3d\x27\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x61\x73\x73\x69\x67\x6e\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x61\x73\x73\x69\x67\x6e\x6d\x65\x6e\x74\x2e\x76\x61\x6c\x75\x65\x3d\x31\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x61\x73\x73\x69\x67\x6e\x6d\x65\x6e\x74\x2e\x70\x61\x67\x65\x32\x2e\x76\x61\x6c\x75\x65\x3d\x32\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x61\x73\x73\x69\x67\x6e\x6d\x65\x6e\x74\x2e\x73\x75\x62\x6d\x69\x74\x28\x29\x3b\x27\x3e\x0d\x0a\x09\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x62\x75\x74\x74\x6f\x6e\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x43\x61\x6e\x63\x65\x6c\x27\x20\x6f\x6e\x43\x6c\x69\x63\x6b\x3d\x27\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x61\x73\x73\x69\x67\x6e\x6d\x65\x6e\x74\x2e\x70\x61\x67\x65\x32\x2e\x76\x61\x6c\x75\x65\x3d\x32\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x61\x73\x73\x69\x67\x6e\x6d\x65\x6e\x74\x2e\x73\x75\x62\x6d\x69\x74\x28\x29\x3b\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x65\x64\x69\x74\x61\x73\x73\x69\x67\x6e\x6d\x65\x6e\x74\x27\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x61\x73\x73\x69\x67\x6e\x6d\x65\x6e\x74\x69\x64\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_5 (str.++ literal_4 sigmaStar_3)))
(assert (= literal_6 "\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x70\x61\x67\x65\x32\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_7 (str.++ x_5 literal_6)))
(assert (= x_8 (str.++ x_7 sigmaStar_2)))
(assert (= literal_10 "\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x73\x65\x6c\x65\x63\x74\x63\x6c\x61\x73\x73\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_11 (str.++ x_8 literal_10)))
(assert (= x_13 (str.++ x_11 sigmaStar_0)))
(assert (= literal_15 "\x20\x2f\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x6c\x6f\x67\x6f\x75\x74\x27\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x77\x61\x73\x74\x6f\x74\x61\x6c\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_18 (str.++ x_13 literal_15)))
(assert (= literal_19 "\x2f"))
(assert (= x_20 (str.++ sigmaStar_17 literal_19)))
(assert (= x_26 (str.++ x_20 sigmaStar_17)))
(assert (= literal_25 "\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x77\x61\x73\x64\x61\x74\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_27 (str.++ x_18 literal_25)))
(assert (= literal_24 "\x3c\x68\x31\x3e\x45\x64\x69\x74\x20\x41\x73\x73\x69\x67\x6e\x6d\x65\x6e\x74\x3c\x2f\x68\x31\x3e\x0d\x0a\x0d\x0a\x20\x20\x3c\x66\x6f\x72\x6d\x20\x6e\x61\x6d\x65\x3d\x27\x65\x64\x69\x74\x61\x73\x73\x69\x67\x6e\x6d\x65\x6e\x74\x27\x20\x61\x63\x74\x69\x6f\x6e\x3d\x27\x2e\x2f\x69\x6e\x64\x65\x78\x2e\x70\x68\x70\x27\x20\x6d\x65\x74\x68\x6f\x64\x3d\x27\x50\x4f\x53\x54\x27\x3e\x0d\x0a\x20\x20\x3c\x62\x72\x3e\x3c\x62\x72\x3e\x3c\x62\x72\x3e\x0d\x0a\x20\x20\x3c\x74\x61\x62\x6c\x65\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x27\x30\x27\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x27\x35\x27\x20\x63\x6c\x61\x73\x73\x3d\x27\x64\x79\x6e\x61\x6d\x69\x63\x6c\x69\x73\x74\x27\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x77\x69\x64\x74\x68\x3d\x27\x37\x30\x30\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x68\x65\x61\x64\x65\x72\x27\x3e\x0d\x0a\x09\x3c\x74\x68\x3e\x54\x69\x74\x6c\x65\x3c\x2f\x74\x68\x3e\x0d\x0a\x09\x3c\x74\x68\x3e\x41\x73\x73\x69\x67\x6e\x65\x64\x20\x54\x61\x73\x6b\x3c\x2f\x74\x68\x3e\x0d\x0a\x09\x3c\x74\x68\x3e\x54\x6f\x74\x61\x6c\x20\x50\x6f\x69\x6e\x74\x73\x3c\x2f\x74\x68\x3e\x0d\x0a\x09\x3c\x74\x68\x3e\x44\x61\x74\x65\x20\x41\x73\x73\x69\x67\x6e\x65\x64\x3c\x2f\x74\x68\x3e\x0d\x0a\x09\x3c\x74\x68\x3e\x44\x61\x74\x65\x20\x44\x75\x65\x3c\x2f\x74\x68\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x20\x76\x61\x6c\x69\x67\x6e\x3d\x27\x74\x6f\x70\x27\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x6e\x61\x6d\x65\x3d\x27\x74\x69\x74\x6c\x65\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x31\x35\x27\x20\x73\x69\x7a\x65\x3d\x27\x31\x35\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x20\x2f\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x74\x65\x78\x74\x61\x72\x65\x61\x20\x6e\x61\x6d\x65\x3d\x74\x61\x73\x6b\x27\x3e\x3c\x2f\x74\x65\x78\x74\x61\x72\x65\x61\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x6e\x61\x6d\x65\x3d\x27\x74\x6f\x74\x61\x6c\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x36\x27\x20\x73\x69\x7a\x65\x3d\x27\x31\x35\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_29 (str.++ literal_24 sigmaStar_23)))
(assert (= literal_28 "\x2f"))
(assert (= x_30 (str.++ x_26 literal_28)))
(assert (= x_33 (str.++ x_30 sigmaStar_17)))
(assert (= literal_31 "\x27\x20\x2f\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x6e\x61\x6d\x65\x3d\x27\x61\x73\x73\x69\x67\x6e\x65\x64\x64\x61\x74\x65\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x31\x30\x27\x20\x73\x69\x7a\x65\x3d\x27\x31\x35\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_35 (str.++ x_29 literal_31)))
(assert (= literal_36 "\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x70\x61\x67\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_45 (str.++ x_27 literal_36)))
(assert (= literal_32 ""))
(assert (or (= x_34 x_33) (= x_34 literal_32)))
(assert (= x_46 (str.++ x_35 x_34)))
(assert (= literal_40 "\x35"))
(assert (= literal_41 "\x31"))
(assert (= literal_42 "\x30"))
(assert (= literal_43 "\x32"))
(assert (= literal_37 "\x32"))
(assert (= literal_38 "\x34"))
(assert (= literal_39 "\x30"))
(assert (= literal_44 "\x30"))
(assert (or (= x_54 literal_40) (= x_54 literal_41) (= x_54 literal_42) (= x_54 literal_43) (= x_54 literal_37) (= x_54 literal_38) (= x_54 sigmaStar_1) (= x_54 literal_39) (= x_54 literal_44)))
(assert (= x_56 (str.++ x_45 x_54)))
(assert (= literal_55 "\x27\x20\x2f\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x6e\x61\x6d\x65\x3d\x27\x64\x75\x65\x64\x61\x74\x65\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x31\x30\x27\x20\x73\x69\x7a\x65\x3d\x27\x31\x35\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_57 (str.++ x_46 literal_55)))
(assert (= literal_58 "\x3e\x0d\x0a\x0d\x0a\x20\x3c\x2f\x66\x6f\x72\x6d\x3e\x0d\x0a\x0d\x0a\x20\x3c\x74\x61\x62\x6c\x65\x20\x77\x69\x64\x74\x68\x3d\x35\x32\x30\x27\x20\x62\x6f\x72\x64\x65\x72\x3d\x30\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x30\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x30\x20\x68\x65\x69\x67\x68\x74\x3d\x31\x3e\x0d\x0a\x20\x20\x3c\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x20\x76\x61\x6c\x69\x67\x6e\x3d\x27\x74\x6f\x70\x27\x3e\x0d\x0a\x09\x26\x6e\x62\x73\x70\x3b\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x20"))
(assert (= x_59 (str.++ x_56 literal_58)))
(assert (= x_60 (str.++ x_57 x_34)))
(assert (= x_61 (str.++ x_60 x_59)))
(assert (str.in.re x_61 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_61 "\x61" 0)) (str.len x_61)))
(check-sat)
(get-model)
