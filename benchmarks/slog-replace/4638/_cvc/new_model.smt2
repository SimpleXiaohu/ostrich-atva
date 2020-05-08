(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun sigmaStar_0 () String)
(declare-fun sigmaStar_1 () String)
(declare-fun literal_2 () String)
(declare-fun x_3 () String)
(declare-fun literal_4 () String)
(declare-fun x_5 () String)
(declare-fun x_6 () String)
(declare-fun literal_7 () String)
(declare-fun x_8 () String)
(assert (= literal_2 "\x3c\x21\x44\x4f\x43\x54\x59\x50\x45\x20\x48\x54\x4d\x4c\x20\x50\x55\x42\x4c\x49\x43\x20\x22\x2d\x2f\x2f\x57\x33\x43\x2f\x2f\x44\x54\x44\x20\x48\x54\x4d\x4c\x20\x34\x2e\x30\x31\x20\x54\x72\x61\x6e\x73\x69\x74\x69\x6f\x6e\x61\x6c\x2f\x2f\x45\x4e\x22\x3e\x0d\x0a\x3c\x68\x74\x6d\x6c\x3e\x0d\x0a\x3c\x68\x65\x61\x64\x3e\x0d\x0a\x3c\x74\x69\x74\x6c\x65\x3e"))
(assert (= x_3 (str.++ literal_2 sigmaStar_0)))
(assert (= literal_4 "\x3c\x2f\x74\x69\x74\x6c\x65\x3e\x0d\x0a\x3c\x6d\x65\x74\x61\x20\x68\x74\x74\x70\x2d\x65\x71\x75\x69\x76\x3d\x27\x43\x6f\x6e\x74\x65\x6e\x74\x2d\x54\x79\x70\x65\x27\x20\x63\x6f\x6e\x74\x65\x6e\x74\x3d\x27\x74\x65\x78\x74\x2f\x68\x74\x6d\x6c\x3b\x20\x63\x68\x61\x72\x73\x65\x74\x3d"))
(assert (= x_5 (str.++ x_3 literal_4)))
(assert (= x_6 (str.++ x_5 sigmaStar_1)))
(assert (= literal_7 "\x27\x3e\x0d\x0a\x3c\x73\x74\x79\x6c\x65\x20\x74\x79\x70\x65\x3d\x22\x74\x65\x78\x74\x2f\x63\x73\x73\x22\x3e\x0d\x0a\x3c\x21\x2d\x2d\x0d\x0a\x61\x20\x7b\x20\x63\x6f\x6c\x6f\x72\x3a\x23\x30\x30\x33\x44\x37\x31\x3b\x20\x74\x65\x78\x74\x2d\x64\x65\x63\x6f\x72\x61\x74\x69\x6f\x6e\x3a\x6e\x6f\x6e\x65\x3b\x20\x7d\x0d\x0a\x61\x3a\x68\x6f\x76\x65\x72\x20\x7b\x20\x63\x6f\x6c\x6f\x72\x3a\x23\x30\x32\x37\x41\x43\x36\x3b\x20\x74\x65\x78\x74\x2d\x64\x65\x63\x6f\x72\x61\x74\x69\x6f\x6e\x3a\x75\x6e\x64\x65\x72\x6c\x69\x6e\x65\x3b\x20\x7d\x0d\x0a\x2e\x62\x75\x74\x74\x6f\x6e\x20\x7b\x0d\x0a\x09\x66\x6f\x6e\x74\x2d\x66\x61\x6d\x69\x6c\x79\x3a\x54\x61\x68\x6f\x6d\x61\x2c\x41\x72\x69\x61\x6c\x2c\x56\x65\x72\x64\x61\x6e\x61\x2c\x53\x61\x6e\x73\x2d\x53\x65\x72\x69\x66\x3b\x0d\x0a\x09\x66\x6f\x6e\x74\x2d\x73\x69\x7a\x65\x3a\x31\x31\x70\x78\x3b\x0d\x0a\x09\x63\x6f\x6c\x6f\x72\x3a\x23\x30\x30\x30\x30\x30\x30\x3b\x20\x09\x0d\x0a\x09\x62\x61\x63\x6b\x67\x72\x6f\x75\x6e\x64\x2d\x63\x6f\x6c\x6f\x72\x3a\x23\x45\x35\x45\x35\x45\x38\x3b\x0d\x0a\x09\x62\x6f\x72\x64\x65\x72\x3a\x23\x37\x46\x39\x38\x41\x37\x20\x31\x70\x78\x20\x73\x6f\x6c\x69\x64\x3b\x0d\x0a\x09\x6d\x61\x72\x67\x69\x6e\x2d\x74\x6f\x70\x3a\x32\x70\x78\x3b\x0d\x0a\x7d\x0d\x0a\x2e\x74\x65\x78\x74\x62\x6f\x78\x20\x7b\x0d\x0a\x09\x66\x6f\x6e\x74\x2d\x66\x61\x6d\x69\x6c\x79\x3a\x56\x65\x72\x64\x61\x6e\x61\x2c\x54\x61\x68\x6f\x6d\x61\x2c\x41\x72\x69\x61\x6c\x2c\x53\x61\x6e\x73\x2d\x53\x65\x72\x69\x66\x3b\x0d\x0a\x09\x66\x6f\x6e\x74\x2d\x73\x69\x7a\x65\x3a\x31\x31\x70\x78\x3b\x0d\x0a\x09\x63\x6f\x6c\x6f\x72\x3a\x23\x30\x30\x30\x3b\x20\x0d\x0a\x09\x62\x61\x63\x6b\x67\x72\x6f\x75\x6e\x64\x2d\x63\x6f\x6c\x6f\x72\x3a\x23\x46\x46\x46\x46\x46\x46\x3b\x0d\x0a\x09\x62\x6f\x72\x64\x65\x72\x3a\x31\x70\x78\x20\x23\x37\x46\x39\x38\x41\x37\x20\x73\x6f\x6c\x69\x64\x3b\x0d\x0a\x7d\x0d\x0a\x74\x64\x20\x7b\x20\x66\x6f\x6e\x74\x2d\x66\x61\x6d\x69\x6c\x79\x3a\x56\x65\x72\x64\x61\x6e\x61\x2c\x54\x61\x68\x6f\x6d\x61\x2c\x41\x72\x69\x61\x6c\x2c\x53\x61\x6e\x73\x2d\x53\x65\x72\x69\x66\x3b\x20\x66\x6f\x6e\x74\x2d\x73\x69\x7a\x65\x3a\x31\x31\x70\x78\x3b\x20\x7d\x0d\x0a\x2e\x74\x62\x6c\x2d\x62\x6f\x72\x64\x65\x72\x20\x7b\x20\x62\x61\x63\x6b\x67\x72\x6f\x75\x6e\x64\x2d\x63\x6f\x6c\x6f\x72\x3a\x23\x44\x31\x44\x38\x44\x44\x3b\x20\x7d\x0d\x0a\x2e\x74\x62\x6c\x31\x20\x7b\x20\x66\x6f\x6e\x74\x2d\x73\x69\x7a\x65\x3a\x31\x31\x70\x78\x3b\x20\x63\x6f\x6c\x6f\x72\x3a\x23\x30\x30\x30\x3b\x20\x62\x61\x63\x6b\x67\x72\x6f\x75\x6e\x64\x2d\x63\x6f\x6c\x6f\x72\x3a\x23\x46\x31\x46\x31\x46\x31\x3b\x20\x70\x61\x64\x64\x69\x6e\x67\x3a\x34\x70\x78\x3b\x20\x7d\x0d\x0a\x2e\x74\x62\x6c\x32\x20\x7b\x09\x66\x6f\x6e\x74\x2d\x73\x69\x7a\x65\x3a\x31\x31\x70\x78\x3b\x20\x63\x6f\x6c\x6f\x72\x3a\x23\x30\x30\x30\x3b\x20\x62\x61\x63\x6b\x67\x72\x6f\x75\x6e\x64\x2d\x63\x6f\x6c\x6f\x72\x3a\x23\x46\x36\x46\x36\x46\x36\x3b\x20\x70\x61\x64\x64\x69\x6e\x67\x3a\x34\x70\x78\x3b\x20\x7d\x0d\x0a\x2d\x2d\x3e\x0d\x0a\x3c\x2f\x73\x74\x79\x6c\x65\x3e\x0d\x0a\x3c\x2f\x68\x65\x61\x64\x3e\x0d\x0a\x3c\x62\x6f\x64\x79\x20\x63\x6c\x61\x73\x73\x3d\x27\x74\x62\x6c\x32\x27\x3e\x5c\x6e"))
(assert (= x_8 (str.++ x_6 literal_7)))
(assert (str.in.re x_8 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x5c\x3c\x53\x43\x52\x49\x50\x54") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_8 "\x61" 0)) (str.len x_8)))
(check-sat)
(get-model)
