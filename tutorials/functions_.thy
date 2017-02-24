theory functions_ imports Main
begin

fun fib:: "nat\<Rightarrow>nat" where
"fib 0 = 1"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"


fun sep:: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"sep a (h1#h2#t) = h1 # a # (sep a (h2#t))"
| "sep a xs = xs"

thm sep.simps

lemma "sep 0 [1, 2, 3] = [1, 0, 2, 0, 3]" by simp

thm sep.induct

lemma "map f (sep x ys) = sep (f x) (map f ys)"
proof (induction x ys rule:sep.induct)
case (1 a h1 h2 t)
then show ?case by auto
next
case ("2_1" a)
then show ?case by auto
next
case ("2_2" a)
then show ?case by auto
qed

function sum:: "nat\<Rightarrow>nat\<Rightarrow>nat" where
"sum i N = (if i>N then 0 else i+ (sum (Suc i) N))"
by pat_completeness auto

function check:: "string \<Rightarrow> bool" where
"check (''good'') = True"
| "s\<noteq>''good'' \<Longrightarrow> check s = False"
by auto
termination by (relation "{}") simp

end