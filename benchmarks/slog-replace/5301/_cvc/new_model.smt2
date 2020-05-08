(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun sigmaStar_4 () String)
(declare-fun sigmaStar_8 () String)
(declare-fun literal_10 () String)
(declare-fun x_11 () String)
(declare-fun x_12 () String)
(declare-fun literal_9 () String)
(declare-fun x_13 () String)
(declare-fun x_14 () String)
(declare-fun literal_5 () String)
(declare-fun x_16 () String)
(declare-fun literal_18 () String)
(declare-fun x_21 () String)
(declare-fun literal_20 () String)
(declare-fun x_19 () String)
(declare-fun literal_17 () String)
(declare-fun literal_6 () String)
(declare-fun x_23 () String)
(declare-fun x_26 () String)
(declare-fun sigmaStar_27 () String)
(declare-fun literal_25 () String)
(declare-fun x_28 () String)
(declare-fun literal_29 () String)
(declare-fun x_31 () String)
(declare-fun x_34 () String)
(declare-fun x_35 () String)
(declare-fun literal_33 () String)
(declare-fun x_38 () String)
(declare-fun literal_39 () String)
(declare-fun x_42 () String)
(declare-fun x_41 () String)
(declare-fun literal_37 () String)
(declare-fun literal_36 () String)
(declare-fun x_44 () String)
(declare-fun x_46 () String)
(declare-fun sigmaStar_47 () String)
(declare-fun literal_43 () String)
(declare-fun x_48 () String)
(declare-fun literal_49 () String)
(declare-fun x_58 () String)
(declare-fun x_59 () String)
(declare-fun x_67 () String)
(declare-fun literal_51 () String)
(declare-fun literal_52 () String)
(declare-fun literal_53 () String)
(declare-fun literal_54 () String)
(declare-fun literal_50 () String)
(declare-fun literal_55 () String)
(declare-fun literal_56 () String)
(declare-fun literal_57 () String)
(declare-fun x_69 () String)
(declare-fun literal_68 () String)
(declare-fun x_71 () String)
(declare-fun literal_72 () String)
(declare-fun x_74 () String)
(declare-fun x_73 () String)
(declare-fun literal_70 () String)
(declare-fun x_75 () String)
(declare-fun x_76 () String)
(assert (= literal_10 "\x2f"))
(assert (= x_11 (str.++ sigmaStar_8 literal_10)))
(assert (= x_12 (str.++ x_11 sigmaStar_8)))
(assert (= literal_9 "\x2f"))
(assert (= x_13 (str.++ x_12 literal_9)))
(assert (= x_14 (str.++ x_13 sigmaStar_8)))
(assert (= literal_5 "\x20\x2f\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x73\x74\x75\x64\x65\x6e\x74\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_16 (str.++ literal_5 sigmaStar_1)))
(assert (= literal_18 "\x20\x2f\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x61\x73\x73\x69\x67\x6e\x6d\x65\x6e\x74\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_21 (str.++ x_16 literal_18)))
(assert (= literal_20 "\x09\x3c\x2f\x74\x64\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x6e\x61\x6d\x65\x3d\x27\x67\x72\x61\x64\x65\x64\x61\x74\x65\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x31\x30\x27\x20\x73\x69\x7a\x65\x3d\x27\x31\x30\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= literal_17 ""))
(assert (= literal_6 ""))
(assert (or (= x_19 literal_17) (= x_19 literal_6) (= x_19 x_14)))
(assert (= x_23 (str.++ literal_20 x_19)))
(assert (= x_26 (str.++ x_21 sigmaStar_4)))
(assert (= literal_25 "\x27\x20\x2f\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x6e\x61\x6d\x65\x3d\x27\x70\x6f\x69\x6e\x74\x73\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x35\x27\x20\x73\x69\x7a\x65\x3d\x27\x35\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_28 (str.++ x_23 literal_25)))
(assert (= literal_29 "\x20\x2f\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x73\x65\x6c\x65\x63\x74\x63\x6c\x61\x73\x73\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_31 (str.++ x_26 literal_29)))
(assert (= x_34 (str.++ x_28 sigmaStar_27)))
(assert (= x_35 (str.++ x_31 sigmaStar_3)))
(assert (= literal_33 "\x20\x2f\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x74\x65\x78\x74\x61\x72\x65\x61\x20\x63\x6f\x6c\x73\x3d\x32\x30\x27\x20\x72\x6f\x77\x73\x3d\x27\x33\x27\x20\x6e\x61\x6d\x65\x3d\x27\x63\x6f\x6d\x6d\x65\x6e\x74\x27\x3e\x3c\x2f\x74\x65\x78\x74\x61\x72\x65\x61\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x09\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x63\x68\x65\x63\x6b\x62\x6f\x78\x27\x20\x6e\x61\x6d\x65\x3d\x27\x6c\x61\x74\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x31\x27"))
(assert (= x_38 (str.++ x_34 literal_33)))
(assert (= literal_39 "\x20\x2f\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x70\x61\x67\x65\x32\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_42 (str.++ x_35 literal_39)))
(assert (= literal_37 ""))
(assert (= literal_36 "\x43\x48\x45\x43\x4b\x45\x44"))
(assert (or (= x_41 literal_37) (= x_41 literal_36)))
(assert (= x_44 (str.++ x_38 x_41)))
(assert (= x_46 (str.++ x_42 sigmaStar_0)))
(assert (= literal_43 "\x20\x2f\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x0d\x0a\x20\x20\x20\x3c\x62\x72\x3e\x0d\x0a\x0d\x0a\x20\x20\x20\x3c\x74\x61\x62\x6c\x65\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x27\x30\x27\x20\x62\x6f\x72\x64\x65\x72\x3d\x27\x30\x27\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x77\x69\x64\x74\x68\x3d\x27\x35\x30\x30\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x62\x75\x74\x74\x6f\x6e\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x45\x64\x69\x74\x20\x47\x72\x61\x64\x65\x27\x20\x6f\x6e\x43\x6c\x69\x63\x6b\x3d\x27\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x67\x72\x61\x64\x65\x2e\x65\x64\x69\x74\x67\x72\x61\x64\x65\x2e\x76\x61\x6c\x75\x65\x3d\x31\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x67\x72\x61\x64\x65\x2e\x70\x61\x67\x65\x32\x2e\x76\x61\x6c\x75\x65\x3d\x33\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x67\x72\x61\x64\x65\x2e\x73\x75\x62\x6d\x69\x74\x28\x29\x3b\x27\x3e\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x62\x75\x74\x74\x6f\x6e\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x43\x61\x6e\x63\x65\x6c\x27\x20\x6f\x6e\x43\x6c\x69\x63\x6b\x3d\x27\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x67\x72\x61\x64\x65\x2e\x70\x61\x67\x65\x32\x2e\x76\x61\x6c\x75\x65\x3d\x33\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x65\x64\x69\x74\x67\x72\x61\x64\x65\x2e\x73\x75\x62\x6d\x69\x74\x28\x29\x3b\x27\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x65\x64\x69\x74\x67\x72\x61\x64\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x27\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x67\x72\x61\x64\x65\x69\x64\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x20\x2f\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x77\x61\x73\x67\x72\x61\x64\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_48 (str.++ x_44 literal_43)))
(assert (= literal_49 "\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x64\x61\x74\x65\x27\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x6c\x6f\x67\x6f\x75\x74\x27\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x70\x61\x67\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_58 (str.++ x_46 literal_49)))
(assert (= x_59 (str.++ x_48 sigmaStar_47)))
(assert (= literal_51 "\x34"))
(assert (= literal_52 "\x30"))
(assert (= literal_53 "\x35"))
(assert (= literal_54 "\x31"))
(assert (= literal_50 "\x32"))
(assert (= literal_55 "\x30"))
(assert (= literal_56 "\x32"))
(assert (= literal_57 "\x30"))
(assert (or (= x_67 literal_51) (= x_67 literal_52) (= x_67 literal_53) (= x_67 literal_54) (= x_67 literal_50) (= x_67 sigmaStar_2) (= x_67 literal_55) (= x_67 literal_56) (= x_67 literal_57)))
(assert (= x_69 (str.++ x_58 x_67)))
(assert (= literal_68 "\x27\x20\x2f\x3e\x0d\x0a\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x77\x61\x73\x64\x61\x74\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_71 (str.++ x_59 literal_68)))
(assert (= literal_72 "\x3e\x0d\x0a\x0d\x0a\x20\x3c\x2f\x66\x6f\x72\x6d\x3e\x0d\x0a\x0d\x0a\x20\x3c\x74\x61\x62\x6c\x65\x20\x77\x69\x64\x74\x68\x3d\x35\x32\x30\x27\x20\x62\x6f\x72\x64\x65\x72\x3d\x30\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x30\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x30\x20\x68\x65\x69\x67\x68\x74\x3d\x31\x3e\x0d\x0a\x20\x20\x3c\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x20\x76\x61\x6c\x69\x67\x6e\x3d\x27\x74\x6f\x70\x27\x3e\x0d\x0a\x09\x26\x6e\x62\x73\x70\x3b\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x20"))
(assert (= x_74 (str.++ x_69 literal_72)))
(assert (= literal_70 ""))
(assert (or (= x_73 literal_70) (= x_73 literal_6) (= x_73 x_14)))
(assert (= x_75 (str.++ x_71 x_73)))
(assert (= x_76 (str.++ x_75 x_74)))
(assert (str.in.re x_76 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_76 "\x61" 0)) (str.len x_76)))
(check-sat)
(get-model)
