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

(* TODO *)
(* fun ord:: "int tree \<Rightarrow> bool" where *)
(* "ord Tip = true" | *)
(* "ord (Node l e r) = (\<forall> t\<in>(set l). t \<le> e) \<and> (\<forall> t\<in>(set r). t\<ge>e)" *)

lemma "\<forall> x. \<exists> y. x = y" by auto

lemma "A \<subseteq> B \<inter> C \<Longrightarrow> A \<subseteq> B \<union> C" by auto

lemma "\<lbrakk>\<forall> xs \<in> A. \<exists> ys. xs = ys @ ys; us \<in> A \<rbrakk> \<Longrightarrow> \<exists> n. List.length us = n + n"
  by fastforce
    
lemma "\<lbrakk>\<forall> x y. T x y \<or> T y x; \<forall> x y. A x y \<and> A y x \<longrightarrow> x = y; \<forall> x y. T x y \<longrightarrow> A x y \<rbrakk> \<Longrightarrow> 
\<forall> x y. A x y \<longrightarrow> T x y" by blast

lemma "\<lbrakk> xs @ ys = ys @ xs; length xs = length ys \<rbrakk> \<Longrightarrow> xs = ys"
by (metis append_eq_conv_conj)

lemma "\<lbrakk> (a::nat)\<le>x+b; 2*x < c\<rbrakk> \<Longrightarrow> 2*a +1 \<le> 2*b +c " by arith

inductive ev :: "nat\<Rightarrow>bool" where 
  ev0 : "ev 0"
  | evSS : "ev n \<Longrightarrow> ev (n+2)"

end