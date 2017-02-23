theory prog_prov_ch03
imports Main
begin

text{*
  Section 3: Logic and Proof Beyond Equality
*}

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set:: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}"
| "set (Node l e r) = (set l) \<union> {e} \<union> (set r)"

fun ord:: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l e r) = ((ord l) \<and> (ord r) \<and> (\<forall>x\<in> (set l). x<e) \<and> (\<forall>x\<in>(set r). e<x))"

fun ins:: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins a Tip = (Node Tip a Tip)"
| "ins a (Node l e r) = (if a < e then Node (ins a l) e r else if a=e then Node l e r else Node l e (ins a r))"

lemma ins_union: "set (ins x t) = {x} \<union> (set t)"
apply(induction t rule:ins.induct)
apply(auto)
done

lemma ins_ord: "ord t \<Longrightarrow> ord (ins x t)"
apply(induction t)
apply(auto simp add:ins_union)
done

lemma "\<forall> x. \<exists> y. x = y" by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C" by auto

lemma "A \<and> B \<Longrightarrow> B \<and> A"
apply (rule conjI)
apply simp_all
done

lemma "\<lbrakk>\<forall> xs \<in> A. \<exists> ys. xs = ys @ ys; us \<in> A \<rbrakk> \<Longrightarrow> \<exists> n. List.length us = n + n"
  by fastforce
    
lemma "\<lbrakk>\<forall> x y. T x y \<or> T y x; \<forall> x y. A x y \<and> A y x \<longrightarrow> x = y; \<forall> x y. T x y \<longrightarrow> A x y \<rbrakk> \<Longrightarrow> 
\<forall> x y. A x y \<longrightarrow> T x y" by blast

lemma "\<lbrakk> xs @ ys = ys @ xs; length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys"
by (metis append_eq_conv_conj)

lemma "\<lbrakk> (a::nat)\<le>x+b; 2*x < c\<rbrakk> \<Longrightarrow> 2*a +1 \<le> 2*b +c " by arith

lemma "\<lbrakk> (a::nat) \<le> b; b\<le>c; c\<le>d; d\<le>e\<rbrakk> \<Longrightarrow> a\<le>e"
apply (blast intro:le_trans)
done

thm conjI[OF refl[of "a"] refl[of "b"]]

lemma "Suc (Suc (Suc a)) \<le> b \<Longrightarrow> a \<le> b" by (blast dest:Suc_leD)

inductive ev :: "nat\<Rightarrow>bool" where 
ev0 : "ev 0"
| evSS : "ev n \<Longrightarrow> ev (Suc (Suc n))"

fun evn:: "nat\<Rightarrow>bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc (Suc n)) = evn n"

lemma "ev (Suc (Suc (Suc (Suc 0))))"
apply (rule evSS)
apply (rule evSS)
apply (rule ev0)
done

lemma "ev n \<Longrightarrow> evn n"
apply(induction rule:ev.induct)
apply(auto)
done

lemma "evn n \<Longrightarrow> ev n"
apply(induction n rule: evn.induct)
apply(simp_all)
apply(rule ev0)
apply(rule evSS)
apply(simp)
done

inductive star:: "('a\<Rightarrow>'a\<Rightarrow>bool)\<Rightarrow>'a\<Rightarrow>'a\<Rightarrow>bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
apply(induction rule:star.induct)
apply(assumption)
apply(metis step)
done

lemma star_rev: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
apply(induction rule:star.induct)
apply(rule step)
apply(simp_all)
apply(rule refl)
apply(rule step)
apply(simp_all)
done

(* exercise 3.2 *)

inductive palindrome:: "'a list \<Rightarrow> bool" where
empty_p: "palindrome []" |
single_p: "palindrome [x]" |
step_p: "palindrome xs \<Longrightarrow> palindrome (a # (xs@[a]))"

(* exercise 3.3 *)
inductive star':: "('a\<Rightarrow>'a\<Rightarrow>bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma "star' r x y \<Longrightarrow> star r x y"
apply(induction rule:star'.induct)
apply(rule refl)
apply(simp add:star_rev)
done

lemma star'_rev : "star' r y z  \<Longrightarrow>  r x y  \<Longrightarrow>  star' r x z"
apply(induction rule: star'.induct)
apply(auto intro: step' refl')
done

lemma "star r x y \<Longrightarrow> star' r x y"
apply(induction rule:star.induct)
apply(rule refl')
apply(auto simp add:star'_rev)
done

(* exercise 3.4 TODO *)
(* inductive iter:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where *)

(* exercise 3.5 TODO *)

end