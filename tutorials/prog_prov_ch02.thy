theory prog_prov_ch02
imports Main
begin

text{*
Section 2: Programming and Proving
*}

fun add :: "nat\<Rightarrow>nat\<Rightarrow>nat" where
"add 0 m = m"
| "add (Suc m) n = Suc (add m n)"

datatype 'a list = Nil | Cons 'a "'a  list"

fun app:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys"
| "app (Cons x xs) ys = Cons x (app xs ys)"

fun rev:: "'a list \<Rightarrow> 'a list" where
" rev Nil = Nil"
| " rev (Cons x xs) = app (rev xs) (Cons x Nil)"

lemma app_Nil2 [simp]: "app xs Nil = xs"
apply (induction xs)
apply(auto)
done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
apply (induction xs)
apply(auto)
done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"  
apply(induction xs)
apply(auto)
done

(* exercise 2.1 *)
value "1+(2::nat)"
value "1+(2::int)"
value "1-(2::nat)"
value "1-(2::int)"

lemma add_assoc [simp]: "add (add a b) c = add a (add b c)"
apply(induction a)
apply(auto)
done

lemma add_right_0 [simp]: "b = add b 0"
apply(induction b)
apply(auto)
done

lemma add_suc [simp]: "add b (Suc a) = Suc (add b a)"
apply(induction b)
apply(auto)
done

lemma add_comm [simp]: "add a b = add b a"
apply(induction a)
apply(auto)
done

fun double:: "nat\<Rightarrow>nat" where
"double 0 = 0"
| "double (Suc a) = Suc (Suc (double a))"

lemma double_eq_add_twice: "double m = add m m"
apply(induction m)
apply(auto)
done

(*exercise 2.3*)
fun length:: "'a list \<Rightarrow> nat" where
"length Nil = 0"
| "length (Cons x xs) = Suc (length xs)"

fun count:: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count m Nil = 0"
| "count m (Cons x xs) = (if m = x then Suc (count m xs) else count m xs)"

lemma count_leq_length: "count a l \<le> length l"
apply(induction l)
apply(auto)
done

(* exercise 2.4 *)
fun snoc:: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc Nil a = Cons a Nil"
| "snoc (Cons x xs) a = Cons x (snoc xs a)"

fun reverse:: "'a list \<Rightarrow> 'a list" where
"reverse Nil = Nil"
| "reverse (Cons x xs) = snoc (reverse xs) x"

lemma rev_snoc [simp]: "reverse (snoc xs x) = Cons x (reverse xs)"
apply(induction xs)
apply(auto)
done

lemma rev_rev_is_origin: "reverse (reverse l) = l"
apply(induction l)
apply(auto)
done

(* exercise 2.5 *)
fun sum_upto:: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0"
| "sum_upto (Suc n) = (Suc n) + (sum_upto n)"

lemma sum_upto_res: "sum_upto n = n * (n + 1) div 2"
apply(induction n)
apply(auto)
done

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror:: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror (mirror t) = t"
apply(induction t)
apply(auto)
done

datatype 'a option = None | Some 'a

fun lookup:: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
"lookup Nil x = None" |
"lookup (Cons (a, b) ps) x = (if a=x then Some b else lookup ps x)"

definition sq :: "nat \<Rightarrow> nat" where
"sq n = n * n"

abbreviation sq' :: "nat \<Rightarrow> nat" where
"sq' n \<equiv> n * n"

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0"
| "div2 (Suc 0) = 0"
| "div2 (Suc(Suc n)) = Suc (div2 n)"

lemma "div2(n) = n div 2"
apply(induction n rule: div2.induct)
apply(auto)
done

(* exercise 2.6 *)

fun contents:: "'a tree \<Rightarrow> 'a list" where
"contents Tip = Nil"
| "contents (Node l a r) = app (app (contents l) (Cons a Nil) ) (contents r)"

fun listsum:: "nat list \<Rightarrow> nat" where
"listsum Nil = 0"
| "listsum (Cons x xs) = x + (listsum xs)"

fun treesum:: "nat tree \<Rightarrow> nat" where
"treesum Tip = 0"
| "treesum (Node l a r) = (treesum l) + a + (treesum r)"

lemma listsum_app [simp]: "listsum (app x1 x2) = listsum x1 + listsum x2"
apply(induction x1)
apply(auto)
done

lemma tree_list_sum: "(treesum t) = listsum (contents t)"
apply(induction t rule: tree.induct)
apply(auto)
done

(* exercise 2.7 *)
datatype 'a tree2 = Tip2 | Node2 "'a tree2" 'a "'a tree2"

fun mirror2:: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror2 Tip2 = Tip2"
| "mirror2 (Node2 l a r) = Node2 (mirror2 r) a (mirror2 l)"

fun pre_order:: "'a tree2 \<Rightarrow> 'a list" where
"pre_order Tip2 = Nil"
| "pre_order (Node2 l a r) = Cons a (app (pre_order l) (pre_order r))"

fun post_order:: "'a tree2 \<Rightarrow> 'a list" where
"post_order Tip2 = Nil"
| "post_order (Node2 l a r) = app (app (post_order l) (post_order r)) (Cons a Nil)"

lemma mirror_pre_post: "pre_order (mirror2 t) = rev (post_order t)"
apply(induction t rule: tree2.induct)
apply(auto)
done

(*exercise 2.8 *)
fun intersperse:: "'a \<Rightarrow> 'a List.list \<Rightarrow> 'a List.list" where
"intersperse a [] = []"
| "intersperse a [x] = [x]"
| "intersperse a (x1 # x2 # xs) = [x1, a] @ (intersperse a (x2 # xs))"

value "intersperse 0 []"
value "intersperse 0 [1]"
value "intersperse 0 [1,2,3]"

lemma intersperse_map: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
apply(induction xs rule: intersperse.induct)
apply(auto)
done

fun itrev :: "'a List.list \<Rightarrow> 'a List.list \<Rightarrow> 'a List.list" where
"itrev [] ys = ys"
| "itrev (x # xs) ys = itrev xs (x#ys)"

lemma itrev_rev_app [simp]: "itrev xs ys = (List.rev xs) @ ys"
apply(induction xs arbitrary:ys)
apply(auto)
done

lemma itrev_rev: "itrev xs [] = List.rev xs"
apply(induction xs)
apply(auto)
done

(* exercise 2.9*)
fun itadd :: "nat\<Rightarrow>nat\<Rightarrow>nat" where
"itadd 0 acc = acc"
| "itadd (Suc a) acc = itadd a (Suc acc)"

value "itadd 2  3"

lemma itadd_add: "itadd m n = add m n"
apply(induction m arbitrary:n)
apply(auto)
done

(* exercise 2.10 *)
datatype tree0 = Leaf | Inner tree0 tree0

fun nodes:: "tree0 \<Rightarrow> nat" where
"nodes Leaf = 1"
| "nodes (Inner l r) = (nodes l) + (nodes r)"

fun explode:: "nat\<Rightarrow>tree0\<Rightarrow>tree0" where
"explode 0 t = t"
| "explode (Suc n) t = explode n (Inner t t)"

value "nodes (explode 1 t)" 
value "nodes (explode 2 t)"
value "nodes (explode 3 t)"
value "nodes (explode 5 t)"

lemma nodes_explode: "nodes (explode n t) = (2^n) * (nodes t)"
apply(induction n arbitrary:t)
apply(auto simp add:algebra_simps)
done

(* exercise 2.11; always assume the polynomial is of regular form *)
(* only 1 Var; coefficients are from 0 to N-1, no omits *)
(* ref; https://github.com/lunaryorn/exercises/blob/master/concrete-semantics/02.thy#L332 *)
datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval:: "exp\<Rightarrow>int\<Rightarrow>int" where
"eval Var x = x"
| "eval (Const i) x = i"
| "eval (Add e1 e2) x = (eval e1 x) + (eval e2 x)"
| "eval (Mult e1 e2) x = (eval e1 x) * (eval e2 x)"

(* ((4+2x)+(-x^2))+3x^3 *)
value "eval (Add (Const 4) (Mult (Const 2) Var)) 1"
value "eval (Mult Var Var) 1"
value "eval (Const (-1)) 1"
value "eval (Mult (Const (-1)) (Mult Var Var)) 1"
value "eval (Add (Add (Const 4) (Mult (Const 2) Var)) (Mult (Const (-1)) (Mult Var Var))) 3"

definition myterm:: "exp" where
"myterm \<equiv> (Add
  (Add 
   (Add (Const 4) (Mult (Const 2) Var))
   (Mult (Const (-1)) (Mult Var Var))
  )
  (Mult (Const 3) (Mult (Mult Var Var) Var)))"

value "eval myterm 2"

fun evalp' :: "int List.list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
"evalp' [] e x = 0" |
"evalp' (h#t) e x = (h * (x ^ e)) + (evalp' t (Suc e) x)"

fun evalp:: "int List.list \<Rightarrow> int \<Rightarrow> int" where
"evalp coeffs x = evalp' coeffs 0 x"

lemma evalp_suc: "x * (evalp' l e x) = (evalp' (0#l) e x)"
  apply (induction l arbitrary: e)
  apply (auto simp add: algebra_simps)
done

lemma evalp_factorise_simple: "evalp' l (Suc e) x = x * evalp' l e x"
apply (induction e arbitrary:l)
apply (auto simp add: algebra_simps evalp_suc)
done

lemma evalp_commut_simple: "(evalp' l 0 x) * (evalp' r e x) = (evalp' r 0 x) * (evalp' l e x)"
apply(induction e)
apply(auto simp add:algebra_simps evalp_factorise_simple)
done

value "evalp [4,2,-1,3] 2"

fun addp:: "int List.list \<Rightarrow> int List.list \<Rightarrow> int List.list" where
"addp [] r = r"
| "addp l [] = l"
| "addp (lh#lt) (rh#rt) = (lh+rh) # (addp lt rt)"

lemma addp_evalp: "evalp' (addp l r) e x = (evalp' l e x) + (evalp' r e x)"
apply(induction l r arbitrary:e rule:addp.induct)
apply(auto simp add:algebra_simps)
done

fun multc :: "int \<Rightarrow> int List.list \<Rightarrow> int List.list" where
  "multc c [] = []" |
  "multc c (h#t) = (c * h)#(multc c t)"

lemma evalp_multc: "evalp' (multc c l) e x = c * (evalp' l e x)"
  apply (induction l arbitrary:e)
  apply (auto simp add: algebra_simps)
done

value "multc 3 [1,2,3]"

fun multp:: "int List.list \<Rightarrow> int List.list \<Rightarrow> int List.list" where
"multp [] r = []"
| "multp (h#t) r = addp (multc h r) (multp t (0 # r))"

lemma multp_evalp: "evalp' (multp l r) 0 x = (evalp' l 0 x) * (evalp' r 0 x)"
apply(induction l r rule:multp.induct)
apply(auto simp add:algebra_simps evalp_multc addp_evalp evalp_commut_simple)
done

fun coeffs:: "exp \<Rightarrow> int List.list" where
"coeffs (Const i) = [i]"
| "coeffs Var = [0,1]"
| "coeffs (Add l r) = addp (coeffs l) (coeffs r)"
| "coeffs (Mult l r) =  multp (coeffs l) (coeffs r)"

value "coeffs myterm"

lemma eval_evalp: "evalp (coeffs e) x = eval e x"
apply(induction e rule:coeffs.induct)
apply(auto simp add:algebra_simps multp_evalp addp_evalp)
done

end