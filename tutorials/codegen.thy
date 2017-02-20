theory codegen
imports Main
begin
  
datatype 'a queue = AQueue "'a list" "'a list"
  
definition empty :: "'a queue" where
  "empty = AQueue [] []"
  
primrec enqueue :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
 "enqueue x (AQueue xs ys) = AQueue (x # xs) ys"

fun lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup [] x = None" |
"lookup ((a,b) # ps) x = (if a = x then Some b else lookup ps x )"

fun dequeue :: "'a queue \<Rightarrow> 'a option \<times> 'a queue" where 
"dequeue (AQueue [] []) = (None, AQueue [] [])"
| "dequeue (AQueue xs (y # ys)) = (Some y, AQueue xs ys)"
| "dequeue (AQueue xs []) = 
  (case (rev xs) of y # ys \<Rightarrow> (Some y, AQueue [] ys))"  

export_code empty dequeue enqueue in Scala
module_name codegen file "codegen.scala"

class semigroup = 
fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
assumes assoc: "(x\<otimes>y)\<otimes>z = x\<otimes>(y\<otimes>z)"

class zero = fixes zero :: 'a ("0")
class one = fixes one :: 'a ("1")
hide_const (open) zero one

class monoid = semigroup +
fixes neutral :: 'a ("1")
assumes neutl: "1 \<otimes> x = x"
and neutr: "x \<otimes> 1 = x "

instantiation nat::monoid
begin

primrec mult-nat where
"0 \<otimes> n = (0::nat)"
| "Suc m \<otimes> n = n + m \<otimes> n"

definition neutral-nat where 1 = Suc 0

lemma add-mult-distrib:
fixes n m q::nat
shows (n+m)\<otimes>q = n\<otimes>q + m\<otimes>q
by (induct n) simp-all

instance proof
fix m n q::nat
show m\<otimes>n\<otimes> = m\<otimes>(n\<otimes>q)
 by (induct m) (simp-all add: add-mult-distrib)
show 1\<otimes>n=n
 by (simp add: neutral-nat-def)
show m\<otimes>1=m
 by (induct m) (simp-all add: neutral-nat-def)

end

end  