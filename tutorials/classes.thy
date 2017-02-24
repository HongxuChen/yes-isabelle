theory classes imports Main
begin

class semigroup =
 fixes mult:: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
 assumes assoc: "(x\<otimes>y)\<otimes>z = x\<otimes>(y\<otimes>z)"

instantiation int::semigroup
begin

definition
mult_int_def: "i\<otimes>j = i + (j::int)"

instance proof
fix i j k :: int
have "(i+j)+k = i+(j+k)" by simp
  then show "(i\<otimes>j)\<otimes>k = i\<otimes>(j\<otimes>k)"
  unfolding mult_int_def .
qed

end

(*nat semigroup*)
instantiation nat::semigroup
begin

primrec mult_nat where
"(0::nat) \<otimes> n = n"
| "(Suc m) \<otimes> n = Suc (m \<otimes> n)"

instance proof
fix m n q :: nat
  show "(m\<otimes>n)\<otimes>q = m\<otimes>(n\<otimes>q)"
  by (induct m) auto
qed

end

(* prod *)

instantiation prod::(semigroup, semigroup) semigroup
begin

definition
mult_prod_def: "p1\<otimes>p2 = (fst p1 \<otimes> fst p2, snd p1 \<otimes> snd p2)"

instance proof
  fix p1 p2 p3 :: "'a::semigroup \<times> 'b::semigroup"
  show "p1\<otimes>p2\<otimes>p3 = p1\<otimes>(p2\<otimes>p3)"
  unfolding mult_prod_def by (simp add:assoc)
qed

end



end