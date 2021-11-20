(assert (exists ((i (_ BitVec 32)) (j (_ BitVec 32)) (v (_ BitVec 8)) (a (Array (_ BitVec 32) (_ BitVec 8)))) 
	(not (= (select (store a i v) j) (ite (= i j) v (select a j))))))

