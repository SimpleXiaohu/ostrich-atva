(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun literal_8 () String)
(assert (= literal_8 "\x3c\x61\x20\x68\x72\x65\x66\x3d\x22\x65\x64\x69\x74\x2e\x70\x68\x70\x3f\x64\x3d\x26\x61\x6d\x70\x3b\x69\x6d\x70\x6f\x72\x74\x3d\x31\x22\x3e\x75\x70\x6c\x6f\x61\x64\x72\x65\x63\x6f\x72\x64\x73\x3c\x2f\x61\x3e"))
(assert (str.in.re literal_8 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof literal_8  "\x61" 0)) (str.len literal_8 )))
(check-sat)
(get-model)
