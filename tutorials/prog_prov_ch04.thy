theory prog_prov_ch04 imports Main
begin

lemma "\<not> surj(f::'a \<Rightarrow> 'a set)"
proof
assume "surj f"
hence "\<forall> A. \<exists> a. A = f a" by(simp add:surj_def)
hence "\<exists> a. {x. x \<notin> f x} = f a" by blast
thus "False" by blast
qed

lemma
fixes f:: "'a \<Rightarrow> 'a set"
assumes s: "surj f"
shows "False"
proof -
have "\<exists> a.  {x. x \<notin> f x} = f a" using s
  by(auto simp: surj_def)
thus "False" by blast
qed

lemma "\<not> surj(f:: 'a \<Rightarrow> 'a set)"
proof
assume "surj f"
hence "\<exists> a. {x. x\<notin>f x} = f a" by (auto simp:surj_def)
then obtain a where "{x. x \<notin> f x} = f a" by blast
hence "a \<notin> f a \<longleftrightarrow> a \<in> f a" by blast
thus "False" by blast
qed

(*exercise 4.1 *)
lemma assumes T: "\<forall> x y. T x y \<or> T y x"
  and A: "\<forall> x y. A x y = A y x \<longrightarrow> x = y"
  and TA: "\<forall> x y. T x y \<longrightarrow> A x y"
  and Axy: "A x y"
shows "T x y"
proof cases
  assume "T x y"
  thus "T x y" by simp
next
  assume "\<not> (T x y)"
  hence "T y x" using T by blast
  hence "A y x" using TA by blast
  hence "x = y" using A and Axy by blast
  thus "T x y" using T by blast
qed
  
(* exercise 4.2 *)
lemma "(\<exists> ys zs. xs =  ys @ zs \<and> length ys = length zs)
      \<or> (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof cases
  assume "even (length xs)"
    hence "\<exists> n. length xs = 2 * n" by (auto simp add: dvd_def)
    then  obtain n where "length xs = 2 * n" by blast
    let ?ys = "take n xs"
    let ?zs = "drop n xs"
    have "length ?ys = length ?zs" by (simp add: `length xs = 2 * n`)
    hence "xs = ?ys @ ?zs \<and> length ?ys = length ?zs" by (simp)
    hence "\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs" by blast
    thus ?thesis by blast
  next        
  assume "odd (length xs)"
    hence "\<exists> n. length xs = 2 * n + 1" by (presburger)
    then obtain n where "length xs = 2*n+1" by blast
    let ?ys = "take (n+1) xs"
    let ?zs = "drop (n+1) xs"
    have "length ?ys = length ?zs + 1" by (simp add: `length xs = 2 * n + 1`)
    hence "xs = ?ys @ ?zs \<and> length ?ys = length ?zs + 1" by auto
    hence "\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1" by blast
    thus ?thesis by blast
  qed
    
lemma "length(tl xs) = length xs -1"
proof (cases xs)  
  assume "xs = []"
    thus ?thesis by simp
  next
    fix y ys
    assume "xs = y#ys"
    thus ?thesis by simp
  qed

lemma "length (tl xs) = length xs -1"
proof (cases xs)
  case Nil
  thus ?thesis by simp
  next      
  case (Cons y ys)
  thus ?thesis by simp
qed
  
lemma "\<Sum> {0..n::nat} = n*(n+1) div 2"
proof (induction n)
  show "\<Sum>{0..0::nat} = 0 * (0+1) div 2" by simp    
next
  fix n
  assume "\<Sum>{0..n::nat} = n*(n+1) div 2"
  thus "\<Sum>{0..(Suc n)::nat} = (Suc n)*(Suc n + 1) div 2" by simp
qed
  
lemma "\<Sum> {0..n::nat} = n * (n+1) div 2" (is "?P n")
proof (induction n)
 show "?P 0" by simp  
next
 fix n
 assume "?P n"
 thus "?P (Suc n)" by simp
qed

lemma "\<Sum> {0..n::nat} = n*(n+1) div 2"
proof (induction n)
 case 0
 show ?case by simp
next
 case (Suc n)
 thus ?case by simp
qed

inductive ev:: "nat\<Rightarrow>bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn:: "nat\<Rightarrow>bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc (Suc n)) = evn n"

lemma "ev n \<Longrightarrow> evn n"
proof (induction rule: ev.induct)
case ev0
show ?case by simp
next
case evSS
thus ?case by simp
qed

lemma "ev n \<Longrightarrow> evn n"
proof (induction rule:ev.induct)
 case ev0 show ?case by simp
next
 case (evSS m)
 have "evn (Suc (Suc m)) = evn m" by simp
 thus ?case using `evn m` by blast
qed

lemma "ev  n \<Longrightarrow> ev (n - 2)"
proof -
assume "ev n"
hence "ev (n-2)"
proof cases
 case ev0
 thus "ev (n-2)" by (simp add: ev.ev0)
 next
 case (evSS k)
 thus "ev (n-2)" by (simp add: ev.evSS)
qed
thus ?thesis by blast
qed

lemma "\<not> ev (Suc 0)"
proof
 assume "ev (Suc 0)"
 thus "False" by cases
qed

lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof
 assume "ev (Suc (Suc (Suc 0)))"
 thus False
 proof cases
  assume "ev (Suc 0)"
  hence "False" by cases
  thus "False" by blast
 qed
qed

lemma "ev (Suc m) \<Longrightarrow> \<not> (ev m)"
proof(induction "Suc m" arbitrary: m rule:ev.induct)
fix n
assume IH: "\<And>m. n = Suc m \<Longrightarrow> \<not> ev m"
show "\<not> ev (Suc n)"
proof -- contradiction
assume "ev (Suc n)"
thus False
 proof (cases "Suc n" -- rule)
  fix k
  assume "n = Suc k" and "ev k"
  thus False using IH by auto
 qed
qed
qed

(* exercise 4.3 TODO *)

(* exercise 4.4 TODO *)

(* exercise 4.5 TODO *)

(* exercise 4.6 TODO *)

(* exercise 4.7 TODO *)

end