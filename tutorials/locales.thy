theory locales imports Main
begin

locale partial_order = 
    fixes le:: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
    assumes refl [intro, simp]: "x\<sqsubseteq>x"
    and anti_sym [intro]: "\<lbrakk> x\<sqsubseteq>y; y\<sqsubseteq>x \<rbrakk> \<Longrightarrow> x = y"
    and trans [trans]: "\<lbrakk> x\<sqsubseteq>y; y\<sqsubseteq>z \<rbrakk> \<Longrightarrow> x\<sqsubseteq>z"

print_locale! partial_order

thm partial_order_def

print_statement partial_order.trans

definition (in partial_order)
 less:: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubset>" 50)
 where "x\<sqsubset>y = (x\<sqsubseteq>y \<and> x\<noteq>y)"


print_statement partial_order.less_def

context partial_order
begin

  definition
  is_inf where "is_inf x y i = (i\<sqsubseteq>x \<and> i\<sqsubseteq>y \<and> (\<forall> z. z\<sqsubseteq>x \<and> z\<sqsubseteq>y \<longrightarrow> z\<sqsubseteq>i))"

  definition
  is_sup where "is_sup x y s = (x\<sqsubseteq>s \<and> y\<sqsubseteq>s \<and> (\<forall> z. x\<sqsubseteq>z \<and> y\<sqsubseteq>z \<longrightarrow> s\<sqsubseteq>z))"

  theorem is_inf_uniq: "\<lbrakk>is_inf x y i; is_inf x y i'\<rbrakk> \<Longrightarrow> i=i'"
  by (simp add: anti_sym is_inf_def)

  theorem is_sup_uniq: "\<lbrakk>is_sup x y s; is_sup x y s'\<rbrakk> \<Longrightarrow> s=s'"
  by (simp add: anti_sym is_sup_def)

end

locale lattice = partial_order +
  assumes ex_inf: "\<exists> inf. is_inf x y inf"
      and ex_sup: "\<exists> sup. is_sup x y sup"
begin
  definition
  meet (infixl "\<sqinter>" 70) where "x\<sqinter>y = (THE inf. is_inf x y inf)"

  definition
  join (infixl "\<squnion>" 65) where "x\<squnion>y = (THE sup. is_sup x y sup)"

  lemma meet_left: "x\<sqinter>y\<sqsubseteq>x"
  by (metis is_inf_def is_inf_uniq lattice.ex_inf local.lattice_axioms meet_def the_equality)

  lemma join_right: "x\<sqsubseteq>(x\<squnion>y)"
  by (metis ex_sup is_sup_def is_sup_uniq join_def the_equality)

end

locale total_order = partial_order +
  assumes total: "x\<sqsubseteq>y \<or> y\<sqsubseteq>x"

lemma (in total_order) less_order: "x\<sqsubset>y \<or> y\<sqsubset>x \<or> x=y"
  using less_def total by auto

locale distrib_lattice = lattice +
  assumes meet_distr: "x\<sqinter>(y\<squnion>z) = (x\<sqinter>y)\<squnion>(x\<sqinter>z)"

lemma (in distrib_lattice) join_distr: "x\<squnion>(y\<sqinter>z) = (x\<squnion>y) \<sqinter> (x\<squnion>z)"
sorry

sublocale total_order \<subseteq> lattice
proof unfold_locales
fix x y
from total have "is_inf x y (if x\<sqsubseteq>y then x else y)" by (auto simp: is_inf_def)
then show "\<exists> inf. is_inf x y inf" ..
from total have "is_sup x y (if x\<sqsubseteq>y then y else x)" by (auto simp: is_sup_def)
then show "\<exists> sup. is_sup x y sup" ..
qed

sublocale total_order \<subseteq> distrib_lattice
sorry

interpretation int:partial_order "op\<le> :: int \<Rightarrow> int \<Rightarrow> bool"
rewrites "int.less x y = (x < y)"
proof -
show "partial_order (op \<le> :: int \<Rightarrow> int \<Rightarrow> bool)" by unfold_locales auto
then
show "partial_order.less op \<le> x y = (x < y)"
unfolding partial_order.less_def [OF \<open>partial_order op\<le>\<close>] by auto
qed

interpretation int:partial_order "op\<le> ::[int, int] \<Rightarrow> bool"
rewrites "int.less x y = (x < y)"
proof -
show "partial_order (op \<le> :: int \<Rightarrow> int \<Rightarrow> bool)"
by unfold_locales auto
then interpret int:partial_order "op\<le> :: [int, int] \<Rightarrow> bool" .
show "int.less x y = (x < y)"
unfolding int.less_def by auto
qed

interpretation int:lattice "op\<le> ::int \<Rightarrow> int \<Rightarrow> bool"
 rewrites int_min_eq: "int.meet x y = min x y" and int_max_eq: "int.join x y = max x y"
proof -
show "lattice (op \<le> :: int \<Rightarrow> int \<Rightarrow> bool)"
apply unfold_locales
apply (unfold int.is_inf_def int.is_sup_def)
by arith+
then interpret int: lattice "op\<le> :: int \<Rightarrow> int \<Rightarrow> bool" .
 show "int.meet x y = min x y"
  by (bestsimp simp: int.meet_def int.is_inf_def)
 show "int.join x y = max x y"
  by (bestsimp simp: int.join_def int.is_sup_def)
qed

interpretation int: total_order "op\<le> :: int \<Rightarrow> int \<Rightarrow> bool"
by unfold_locales arith

print_interps partial_order

end