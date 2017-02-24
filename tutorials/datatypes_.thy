theory datatypes_ imports Main
begin

datatype trool = Truue | Faalse | Perhaaps

datatype 'a option = None | Some 'a

datatype ('a, 'b, 'c) triple = Triple 'a 'b 'c

datatype ('a, 'b) tlist = TNil 'b | TCons 'a "('a, 'b) tlist"

datatype even_nat = Even__Zero | Even__Succ odd_nat
and odd_nat = Odd__Succ even_nat

value "Even__Succ (Odd__Succ (Even__Zero))"

datatype ('a, 'b) exp = Term "('a, 'b) terrm" | Sum "('a,'b) terrm" "('a, 'b) exp"
and ('a, 'b) terrm = Factor "('a, 'b) fact" | Prod "('a, 'b) fact" "('a, 'b) terrm"
and ('a, 'b) fact = Const 'a | Var 'b | Expr "('a, 'b) exp"

datatype 'a btree = 
BNode 'a "'a btree option" "'a btree option"

datatype 'a ftree = FTLeaf 'a | FTNode "'a \<Rightarrow> 'a ftree"

datatype ('a,'b) prod (infixl "*" 20) = Pair 'a 'b
datatype (set: 'a) llist =
null: Nil ("[]")
| Cons (hd:'a) (tl:"'a llist") (infixl "#" 65)
for
map: map
rel: list_all2
pred: list_all

value "null (Cons 1 Nil)"
value "hd (Cons abc Nil)"
value "tl Nil"
value "tl (Cons 2 Nil)"
value "set (Cons 7 (Cons 2 (Cons 1 Nil)))"
value "map (\<lambda> x. x*2) (Cons 1 Nil)"
value list.list_all
value list.list_all2

primrec (nonexhaustive) bool__of__trool:: "trool \<Rightarrow> bool" where
"bool__of__trool Faalse \<longleftrightarrow> False"
| "bool__of__trool Truue \<longleftrightarrow> True"

primrec the__list ::"'a option \<Rightarrow> 'a List.list" where
"the__list None = List.Nil"
| "the__list (Some a) = List.Cons a List.Nil"

primrec the__default:: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
"the__default d None = d"
| "the__default _ (Some a) = a"

primrec mirrror:: "('a,'b,'c) triple \<Rightarrow> ('c,'b,'a) triple" where
"mirrror (Triple a b c) = (Triple c b a)"

primrec replicate:: "nat\<Rightarrow>'a\<Rightarrow>'a List.list" where
"replicate 0 _ = List.Nil"
| "replicate (Suc n) x = List.Cons x (replicate n x)"

value "replicate 3 {1}"

primrec
nat__of__even__nat::"even_nat\<Rightarrow>nat" and
nat__of__odd__nat::"odd_nat\<Rightarrow>nat"
where
"nat__of__even__nat Even__Zero = 0"
| "nat__of__even__nat (Even__Succ n) = Suc (nat__of__odd__nat n)"
| "nat__of__odd__nat (Odd__Succ n) = Suc (nat__of__even__nat n)"

(*codatatype*)

codatatype enat = EZero | ESucc enat

codatatype 'a process =
Fail
| Skip (cont: "'a process")
| Action (prefix:'a)(cont:"'a process")
| Choice (left: "'a process")(right: "'a process")

codatatype even_enat = Even_EZero | Even_ESucc odd_enat
and odd_enat = Odd_ESucc even_enat


end
