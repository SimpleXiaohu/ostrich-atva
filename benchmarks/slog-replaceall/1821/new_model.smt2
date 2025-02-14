(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun sigmaStar_8 () String)
(declare-fun literal_11 () String)
(declare-fun x_10 () String)
(declare-fun x_12 () String)
(declare-fun sigmaStar_42 () String)
(declare-fun sigmaStar_46 () String)
(declare-fun literal_32 () String)
(declare-fun literal_39 () String)
(declare-fun x_49 () String)
(declare-fun literal_44 () String)
(declare-fun x_50 () String)
(declare-fun literal_45 () String)
(declare-fun x_51 () String)
(declare-fun literal_48 () String)
(declare-fun x_52 () String)
(declare-fun x_47 () String)
(declare-fun x_54 () String)
(declare-fun x_59 () String)
(declare-fun epsilon () String)
(declare-fun literal_53 () String)
(declare-fun literal_60 () String)
(declare-fun x_61 () String)
(declare-fun sigmaStar_62 () String)
(declare-fun literal_63 () String)
(declare-fun x_64 () String)
(assert (= literal_11 "\x5c\x4c\x61\x72\x67\x65\x20"))
(assert (or (= x_10 sigmaStar_8)))
(assert (= x_12 (str.++ literal_11 x_10)))
(assert (= literal_32 "\x2f\x2f\x6d\x69\x6d\x65\x74\x65\x78\x2e\x65\x78\x65"))
(assert (= x_47 (str.replaceall literal_32 "\x20" "\x5e\x20")))
(assert (= literal_39 "\x20\x2b\x2b\x20\x2d\x65\x20\x20\x5c\x22\x2f\x2f\x2e\x67\x69\x66\x5c\x22\x20"))
(assert (= x_49 (str.++ literal_39 sigmaStar_42)))
(assert (= literal_44 "\x5c\x22\x2f\x2f\x6d\x69\x6d\x65\x74\x65\x78\x2e\x64\x61\x72\x77\x69\x6e\x5c\x22\x20\x2d\x65\x20\x5c\x22\x2f\x2f\x2e\x67\x69\x66\x5c\x22\x20"))
(assert (= x_50 (str.++ literal_44 sigmaStar_42)))
(assert (= literal_45 "\x5c\x22\x2f\x2f\x6d\x69\x6d\x65\x74\x65\x78\x2e\x6c\x69\x6e\x75\x78\x5c\x22\x20\x2d\x65\x20\x5c\x22\x2f\x2f\x2e\x67\x69\x66\x5c\x22\x20"))
(assert (= x_51 (str.++ literal_45 sigmaStar_42)))
(assert (= literal_48 "\x2f\x2f\x6d\x69\x6d\x65\x74\x65\x78\x20\x2d\x65\x20\x2f\x2f\x2e\x67\x69\x66\x20"))
(assert (= x_52 (str.++ literal_48 sigmaStar_42)))
(assert (= x_54 (str.++ x_47 x_49)))
(assert (= epsilon ""))
(assert (= literal_53 ""))
(assert (or (= x_59 epsilon) (= x_59 x_54) (= x_59 literal_53) (= x_59 x_52) (= x_59 x_51) (= x_59 x_50)))
(assert (= literal_60 "\x20\x32\x3e\x26\x31"))
(assert (= x_61 (str.++ x_59 literal_60)))
(assert (= literal_63 "\x3c\x62\x72\x20\x2f\x3e\x5c\x6e"))
(assert (= x_64 (str.++ sigmaStar_62 literal_63)))
(assert (str.in.re x_64 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (> (* 2 (str.indexof x_54 "\x61" 0)) (str.len x_54)))
(check-sat)
(get-model)
