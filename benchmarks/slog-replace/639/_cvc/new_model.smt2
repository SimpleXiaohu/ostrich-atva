(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_21 () String)
(assert (= literal_21 "\x3c\x66\x6f\x72\x6d\x20\x61\x63\x74\x69\x6f\x6e\x3d\x22\x2f\x63\x6f\x75\x72\x73\x65\x2f\x72\x65\x70\x6f\x72\x74\x2f\x70\x61\x72\x74\x69\x63\x69\x70\x61\x74\x69\x6f\x6e\x2f\x69\x6e\x64\x65\x78\x2e\x70\x68\x70\x22\x20\x6d\x65\x74\x68\x6f\x64\x3d\x22\x67\x65\x74\x22\x3e\x5c\x6e\x3c\x69\x6e\x70\x75\x74\x20\x74\x79\x70\x65\x3d\x22\x68\x69\x64\x64\x65\x6e\x22\x20\x6e\x61\x6d\x65\x3d\x22\x69\x64\x22\x20\x76\x61\x6c\x75\x65\x3d\x22\x22\x20\x2f\x3e\x5c\x6e\x3c\x74\x61\x62\x6c\x65\x20\x61\x6c\x69\x67\x6e\x3d\x22\x63\x65\x6e\x74\x65\x72\x22\x20\x63\x65\x6c\x6c\x70\x61\x64\x64\x69\x6e\x67\x3d\x22\x31\x30\x22\x3e\x3c\x74\x72\x3e\x5c\x6e\x3c\x74\x64\x3e\x5c\x6e\x61\x63\x74\x69\x76\x69\x74\x79\x6d\x6f\x64\x75\x6c\x65\x26\x6e\x62\x73\x70\x3b"))
(assert (str.in.re literal_21 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_21  "\x61" 0)) (str.len literal_21 )))
(check-sat)
(get-model)
