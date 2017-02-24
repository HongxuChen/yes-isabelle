theory nitpick_ imports Main
begin

lemma "P \<longleftrightarrow> Q"
apply auto
nitpick 1
nitpick 2
oops

lemma "\<exists>!x. x\<in>A \<Longrightarrow> (THE y. y\<in>A)\<in>A"
nitpick [card 'a=1-50]
nitpick[dont_specialize,show_consts]
sledgehammer
using theI by fastforce

lemma "\<exists>g.\<forall>x. g(f x) = x \<Longrightarrow> \<forall>y. \<exists>x. y = f x"
nitpick
oops

lemma "\<forall>x. \<forall>f. f x = x"
nitpick
oops

lemma "refl r = sym r"
nitpick
oops

lemma "\<lbrakk>i\<le>j;n\<le>(m::int)\<rbrakk> \<Longrightarrow> i*n+j*m\<le>i*m+j*n"
nitpick
nitpick[binary_ints, bits=16]
oops

lemma "\<forall>n. Suc n \<noteq> n \<Longrightarrow> P"
nitpick[card nat=50]
oops

lemma "P Suc"
nitpick
oops

lemma "P (op +::nat \<Rightarrow> nat \<Rightarrow> nat)"
nitpick[card nat=2]
oops

lemma "hd (xs@[y,y]) = hd xs"
nitpick[show_consts,show_types]
oops

lemma "\<lbrakk>length xs=1;length ys=1\<rbrakk> \<Longrightarrow> xs = ys"
nitpick[show_types]
oops

end