(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun literal_3 () String)
(declare-fun x_5 () String)
(declare-fun literal_6 () String)
(declare-fun x_7 () String)
(declare-fun literal_9 () String)
(declare-fun x_10 () String)
(declare-fun literal_12 () String)
(declare-fun x_13 () String)
(declare-fun literal_15 () String)
(declare-fun x_16 () String)
(declare-fun sigmaStar_19 () String)
(declare-fun literal_18 () String)
(declare-fun x_20 () String)
(declare-fun x_22 () String)
(declare-fun sigmaStar_25 () String)
(declare-fun literal_24 () String)
(declare-fun x_26 () String)
(declare-fun x_29 () String)
(declare-fun sigmaStar_32 () String)
(declare-fun literal_31 () String)
(declare-fun x_33 () String)
(declare-fun x_36 () String)
(declare-fun literal_35 () String)
(declare-fun x_39 () String)
(declare-fun sigmaStar_40 () String)
(declare-fun literal_38 () String)
(declare-fun x_41 () String)
(declare-fun literal_42 () String)
(declare-fun x_43 () String)
(declare-fun x_44 () String)
(declare-fun x_47 () String)
(declare-fun sigmaStar_48 () String)
(declare-fun literal_46 () String)
(declare-fun x_49 () String)
(declare-fun literal_50 () String)
(declare-fun x_51 () String)
(declare-fun x_52 () String)
(declare-fun x_53 () String)
(assert (= literal_3 "\x3c\x74\x61\x62\x6c\x65\x20\x77\x69\x64\x74\x68\x3d\x27\x31\x30\x30\x25\x27\x20\x62\x6f\x72\x64\x65\x72\x3d\x30\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x31\x30\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x30\x3e\x0d\x0a\x3c\x74\x72\x3e\x0d\x0a\x3c\x74\x64\x3e\x0d\x0a\x0d\x0a\x20\x3c\x68\x31\x3e\x4d\x61\x6e\x61\x67\x65\x20\x53\x63\x68\x6f\x6f\x6c\x20\x49\x6e\x66\x6f\x72\x6d\x61\x74\x69\x6f\x6e\x3c\x2f\x68\x31\x3e\x0d\x0a\x20\x3c\x62\x72\x3e\x0d\x0a\x0d\x0a\x20\x3c\x66\x6f\x72\x6d\x20\x6e\x61\x6d\x65\x3d\x27\x69\x6e\x66\x6f\x27\x20\x6d\x65\x74\x68\x6f\x64\x3d\x27\x50\x4f\x53\x54\x27\x20\x61\x63\x74\x69\x6f\x6e\x3d\x27\x2e\x2f\x69\x6e\x64\x65\x78\x2e\x70\x68\x70\x27\x3e\x0d\x0a\x0d\x0a\x20\x3c\x74\x61\x62\x6c\x65\x20\x62\x6f\x72\x64\x65\x72\x3d\x30\x20\x77\x69\x64\x74\x68\x3d\x35\x30\x30\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x30\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x27\x33\x27\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x30\x20\x63\x6c\x61\x73\x73\x3d\x27\x64\x79\x6e\x61\x6d\x69\x63\x6c\x69\x73\x74\x27\x3e\x0d\x0a\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x3e\x0d\x0a\x20\x20\x20\x53\x63\x68\x6f\x6f\x6c\x20\x4e\x61\x6d\x65\x3a\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x6c\x65\x66\x74\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_5 (str.++ literal_3 sigmaStar_1)))
(assert (= literal_6 "\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x35\x30\x27\x20\x6e\x61\x6d\x65\x3d\x27\x73\x63\x68\x6f\x6f\x6c\x6e\x61\x6d\x65\x27\x20\x73\x69\x7a\x65\x3d\x34\x30\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x3e\x0d\x0a\x20\x20\x20\x41\x64\x64\x72\x65\x73\x73\x3a\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x6c\x65\x66\x74\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_7 (str.++ x_5 literal_6)))
(assert (= literal_9 "\x20\x6e\x61\x6d\x65\x3d\x73\x63\x68\x6f\x6f\x6c\x61\x64\x64\x72\x65\x73\x73\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x35\x30\x27\x20\x73\x69\x7a\x65\x3d\x34\x30\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x3e\x0d\x0a\x20\x20\x20\x50\x68\x6f\x6e\x65\x20\x23\x3a\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x6c\x65\x66\x74\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_10 (str.++ x_7 literal_9)))
(assert (= literal_12 "\x20\x6e\x61\x6d\x65\x3d\x73\x63\x68\x6f\x6f\x6c\x70\x68\x6f\x6e\x65\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x31\x34\x27\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x3e\x0d\x0a\x20\x20\x20\x53\x65\x6d\x65\x73\x74\x65\x72\x73\x20\x50\x65\x72\x20\x59\x65\x61\x72\x3a\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x6c\x65\x66\x74\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_13 (str.++ x_10 literal_12)))
(assert (= literal_15 "\x20\x6e\x61\x6d\x65\x3d\x6e\x75\x6d\x73\x65\x6d\x65\x73\x74\x65\x72\x73\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x33\x27\x20\x73\x69\x7a\x65\x3d\x33\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x3e\x0d\x0a\x20\x20\x20\x50\x65\x72\x69\x6f\x64\x73\x20\x50\x65\x72\x20\x44\x61\x79\x3a\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x6c\x65\x66\x74\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_16 (str.++ x_13 literal_15)))
(assert (= literal_18 "\x20\x6e\x61\x6d\x65\x3d\x6e\x75\x6d\x70\x65\x72\x69\x6f\x64\x73\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x33\x27\x20\x73\x69\x7a\x65\x3d\x33\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x3e\x0d\x0a\x20\x20\x20\x50\x6f\x69\x6e\x74\x73\x20\x66\x6f\x72\x20\x41\x3a\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x6c\x65\x66\x74\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_20 (str.++ x_16 literal_18)))
(assert (= x_22 (str.++ x_20 sigmaStar_19)))
(assert (= literal_24 "\x27\x20\x6e\x61\x6d\x65\x3d\x27\x61\x70\x6f\x69\x6e\x74\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x33\x27\x20\x73\x69\x7a\x65\x3d\x33\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x3e\x0d\x0a\x20\x20\x20\x50\x6f\x69\x6e\x74\x73\x20\x66\x6f\x72\x20\x42\x3a\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x6c\x65\x66\x74\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_26 (str.++ x_22 literal_24)))
(assert (= x_29 (str.++ x_26 sigmaStar_25)))
(assert (= literal_31 "\x27\x20\x6e\x61\x6d\x65\x3d\x27\x62\x70\x6f\x69\x6e\x74\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x33\x27\x20\x73\x69\x7a\x65\x3d\x33\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x3e\x0d\x0a\x20\x20\x20\x50\x6f\x69\x6e\x74\x73\x20\x66\x6f\x72\x20\x43\x3a\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x6c\x65\x66\x74\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_33 (str.++ x_29 literal_31)))
(assert (= x_36 (str.++ x_33 sigmaStar_32)))
(assert (= literal_35 "\x20\x6e\x61\x6d\x65\x3d\x66\x70\x6f\x69\x6e\x74\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x33\x27\x20\x73\x69\x7a\x65\x3d\x33\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x20\x76\x61\x6c\x69\x67\x6e\x3d\x27\x74\x6f\x70\x27\x3e\x0d\x0a\x20\x20\x20\x54\x65\x78\x74\x20\x46\x6f\x72\x20\x4c\x6f\x67\x69\x6e\x20\x50\x61\x67\x65\x3a\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x6c\x65\x66\x74\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x65\x78\x74\x61\x72\x65\x61\x20\x6e\x61\x6d\x65\x3d\x27\x73\x69\x74\x65\x74\x65\x78\x74\x27\x20\x63\x6f\x6c\x73\x3d\x34\x30\x20\x72\x6f\x77\x73\x3d\x31\x30\x3e\x3c\x2f\x74\x65\x78\x74\x61\x72\x65\x61\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x20\x76\x61\x6c\x69\x67\x6e\x3d\x27\x74\x6f\x70\x27\x3e\x54\x6f\x64\x61\x79\x27\x73\x20\x4d\x65\x73\x73\x61\x67\x65\x3a\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x6c\x65\x66\x74\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x65\x78\x74\x61\x72\x65\x61\x20\x6e\x61\x6d\x65\x3d\x27\x73\x69\x74\x65\x6d\x65\x73\x73\x61\x67\x65\x27\x20\x63\x6f\x6c\x73\x3d\x34\x30\x20\x72\x6f\x77\x73\x3d\x31\x30\x3e\x3c\x2f\x74\x65\x78\x74\x61\x72\x65\x61\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x3c\x62\x72\x3e\x0d\x0a\x20\x3c\x74\x61\x62\x6c\x65\x20\x77\x69\x64\x74\x68\x3d\x27\x35\x30\x30\x27\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x27\x30\x27\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x27\x30\x27\x20\x62\x6f\x72\x64\x65\x72\x3d\x27\x30\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x63\x65\x6e\x74\x65\x72\x27\x3e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x62\x75\x74\x74\x6f\x6e\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x20\x55\x70\x64\x61\x74\x65\x20\x27\x20\x6f\x6e\x43\x6c\x69\x63\x6b\x3d\x27\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x69\x6e\x66\x6f\x2e\x69\x6e\x66\x6f\x75\x70\x64\x61\x74\x65\x2e\x76\x61\x6c\x75\x65\x3d\x31\x3b\x64\x6f\x63\x75\x6d\x65\x6e\x74\x2e\x69\x6e\x66\x6f\x2e\x73\x75\x62\x6d\x69\x74\x28\x29\x3b\x27\x3e\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x0d\x0a\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x69\x6e\x66\x6f\x75\x70\x64\x61\x74\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27\x27\x3e\x0d\x0a\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x70\x61\x67\x65\x32\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_39 (str.++ literal_35 sigmaStar_0)))
(assert (= literal_38 "\x27\x20\x6e\x61\x6d\x65\x3d\x27\x63\x70\x6f\x69\x6e\x74\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x33\x27\x20\x73\x69\x7a\x65\x3d\x33\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x3e\x0d\x0a\x20\x20\x20\x50\x6f\x69\x6e\x74\x73\x20\x66\x6f\x72\x20\x44\x3a\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x6c\x65\x66\x74\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_41 (str.++ x_36 literal_38)))
(assert (= literal_42 "\x3e\x0d\x0a\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x6c\x6f\x67\x6f\x75\x74\x27\x3e\x0d\x0a\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x68\x69\x64\x64\x65\x6e\x27\x20\x6e\x61\x6d\x65\x3d\x27\x70\x61\x67\x65\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_43 (str.++ x_39 literal_42)))
(assert (= x_44 (str.++ x_41 sigmaStar_40)))
(assert (= x_47 (str.++ x_43 sigmaStar_2)))
(assert (= literal_46 "\x27\x20\x6e\x61\x6d\x65\x3d\x27\x64\x70\x6f\x69\x6e\x74\x27\x20\x6d\x61\x78\x6c\x65\x6e\x67\x74\x68\x3d\x27\x33\x27\x20\x73\x69\x7a\x65\x3d\x33\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x74\x72\x20\x63\x6c\x61\x73\x73\x3d\x27\x65\x76\x65\x6e\x27\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x72\x69\x67\x68\x74\x27\x3e\x0d\x0a\x20\x20\x20\x50\x6f\x69\x6e\x74\x73\x20\x66\x6f\x72\x20\x46\x3a\x0d\x0a\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x74\x64\x20\x61\x6c\x69\x67\x6e\x3d\x27\x6c\x65\x66\x74\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x27\x74\x65\x78\x74\x27\x20\x76\x61\x6c\x75\x65\x3d\x27"))
(assert (= x_49 (str.++ x_44 literal_46)))
(assert (= literal_50 "\x3e\x0d\x0a\x20\x3c\x2f\x66\x6f\x72\x6d\x3e\x0d\x0a\x0d\x0a\x20\x3c\x74\x61\x62\x6c\x65\x20\x77\x69\x64\x74\x68\x3d\x35\x32\x30\x27\x20\x62\x6f\x72\x64\x65\x72\x3d\x30\x20\x63\x65\x6c\x6c\x73\x70\x61\x63\x69\x6e\x67\x3d\x30\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x30\x20\x68\x65\x69\x67\x68\x74\x3d\x31\x3e\x0d\x0a\x20\x20\x3c\x74\x72\x3e\x0d\x0a\x20\x20\x20\x3c\x74\x64\x20\x76\x61\x6c\x69\x67\x6e\x3d\x27\x74\x6f\x70\x27\x3e\x0d\x0a\x20\x20\x20\x3c\x65\x6d\x70\x74\x79\x3e\x0d\x0a\x20\x20\x20\x3c\x2f\x74\x64\x3e\x0d\x0a\x20\x20\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x0d\x0a\x3c\x2f\x74\x64\x3e\x0d\x0a\x3c\x2f\x74\x72\x3e\x0d\x0a\x20\x3c\x2f\x74\x61\x62\x6c\x65\x3e\x0d\x0a\x20"))
(assert (= x_51 (str.++ x_47 literal_50)))
(assert (= x_52 (str.++ x_49 sigmaStar_48)))
(assert (= x_53 (str.++ x_52 x_51)))
(assert (str.in.re x_53 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_53 "\x61" 0)) (str.len x_53)))
(check-sat)
(get-model)
