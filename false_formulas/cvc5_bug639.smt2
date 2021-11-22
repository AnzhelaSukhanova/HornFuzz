(assert (exists ((i Int) (j Int) (k Int) (l Int) (m Int) (n Int) (a (Array Int (Array Int Int))) (b (Array Int (Array Int Int))) (c (Array Int (Array Int Int))) (d (Array Int (Array Int Int))) (e (Array Int (Array Int Int))) (f (Array Int (Array Int Int))) (g (Array Int (Array Int Int))) (h (Array Int (Array Int Int))))
	(and (not (= k 0)) (<= j k) (>= j k) (= b (store a j (store (select a j) 0 0))) (= d (store b 0 (store (select b 0) 0 (select (select d 0) 0)))) (<= i 0) (>= i (select (store (select d j) m 0) 0)) (not (= i 0)))))
(check-sat)

