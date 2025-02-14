(set-logic QF_S)
(set-option :strings-exp true)
(set-option :produce-models true)
(declare-fun literal_0 () String)
(declare-fun x_2 () String)
(declare-fun epsilon () String)
(declare-fun literal_1 () String)
(declare-fun x_3 () String)
(declare-fun literal_4 () String)
(declare-fun x_5 () String)
(assert (= literal_0 "\x2f\x61\x75\x74\x68\x2f"))
(assert (= epsilon ""))
(assert (= literal_1 "\x6d\x61\x6e\x75\x61\x6c"))
(assert (or (= x_2 epsilon) (= x_2 literal_1)))
(assert (= x_3 (str.++ literal_0 x_2)))
(assert (= literal_4 "\x2f\x6c\x69\x62\x2e\x70\x68\x70"))
(assert (= x_5 (str.++ x_3 literal_4)))
(assert (str.in.re x_5 (re.++ (re.* re.allchar) (re.++ (str.to.re "\x2f\x65\x76\x69\x6c") (re.* re.allchar)))))
(assert (< (* 2 (str.indexof x_5 "\x61" 0)) (str.len x_5)))
(check-sat)
(get-model)
