(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun sigmaStar_2 () String)
(declare-fun sigmaStar_3 () String)
(declare-fun sigmaStar_4 () String)
(declare-fun literal_27 () String)
(assert (= literal_27 "\x3c\x74\x72\x3e\x3c\x74\x68\x20\x63\x6f\x6c\x73\x70\x61\x6e\x3d\x5c\x22\x33\x5c\x22\x20\x6e\x6f\x77\x72\x61\x70\x3d\x5c\x22\x6e\x6f\x77\x72\x61\x70\x5c\x22\x20\x63\x6c\x61\x73\x73\x3d\x5c\x22\x68\x65\x61\x64\x65\x72\x5c\x22\x3e\x6f\x72\x64\x65\x72\x3c\x2f\x74\x68\x3e\x3c\x74\x68\x20\x63\x6c\x61\x73\x73\x3d\x5c\x22\x68\x65\x61\x64\x65\x72\x5c\x22\x3e\x23\x3c\x2f\x74\x68\x3e\x3c\x74\x68\x20\x61\x6c\x69\x67\x6e\x3d\x5c\x22\x6c\x65\x66\x74\x5c\x22\x20\x77\x69\x64\x74\x68\x3d\x5c\x22\x31\x30\x30\x25\x5c\x22\x20\x6e\x6f\x77\x72\x61\x70\x3d\x5c\x22\x6e\x6f\x77\x72\x61\x70\x5c\x22\x20\x63\x6c\x61\x73\x73\x3d\x5c\x22\x68\x65\x61\x64\x65\x72\x5c\x22\x3e\x71\x75\x65\x73\x74\x69\x6f\x6e\x6e\x61\x6d\x65\x3c\x2f\x74\x68\x3e\x3c\x74\x68\x20\x6e\x6f\x77\x72\x61\x70\x3d\x5c\x22\x6e\x6f\x77\x72\x61\x70\x5c\x22\x20\x63\x6c\x61\x73\x73\x3d\x5c\x22\x68\x65\x61\x64\x65\x72\x5c\x22\x3e\x74\x79\x70\x65\x3c\x2f\x74\x68\x3e\x3c\x74\x68\x20\x6e\x6f\x77\x72\x61\x70\x3d\x5c\x22\x6e\x6f\x77\x72\x61\x70\x5c\x22\x20\x63\x6c\x61\x73\x73\x3d\x5c\x22\x68\x65\x61\x64\x65\x72\x5c\x22\x3e\x67\x72\x61\x64\x65\x3c\x2f\x74\x68\x3e\x3c\x74\x68\x20\x61\x6c\x69\x67\x6e\x3d\x5c\x22\x63\x65\x6e\x74\x65\x72\x5c\x22\x20\x77\x69\x64\x74\x68\x3d\x5c\x22\x36\x30\x5c\x22\x20\x6e\x6f\x77\x72\x61\x70\x3d\x5c\x22\x6e\x6f\x77\x72\x61\x70\x5c\x22\x20\x63\x6c\x61\x73\x73\x3d\x5c\x22\x68\x65\x61\x64\x65\x72\x5c\x22\x3e\x61\x63\x74\x69\x6f\x6e\x3c\x2f\x74\x68\x3e\x3c\x2f\x74\x72\x3e\x5c\x6e"))
(assert (str.in.re literal_27 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_27  "\x61" 0)) (str.len literal_27 )))
(check-sat)
(get-model)
