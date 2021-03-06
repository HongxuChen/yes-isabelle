theory Meta
imports Complex_Main
begin

theorem sqrt2_not_rational:
  "sqrt (real 2) \<notin> \<rat>"
proof
  let ?x = "sqrt (real 2)"
  assume "?x \<in> \<rat>"
  then obtain m n :: nat where
    sqrt_rat: "\<bar>?x\<bar> = real m / real n" and lowest_terms: "coprime m n"
    by (rule Rats_abs_nat_div_natE)
  hence "real (m^2) = ?x^2 * real (n^2)" by (auto simp add: power2_eq_square)
  hence eq: "m^2 = 2 * n^2" using of_nat_eq_iff power2_eq_square by fastforce
  hence "2 dvd m^2" by simp
  hence "2 dvd m" by simp
  have "2 dvd n" proof-
    from \<open>2 dvd m\<close> obtain k where "m = 2 * k" ..
    with eq have "2 * n^2 = 2^2 * k^2" by simp
    hence "2 dvd n^2" by simp
    thus "2 dvd n" by simp
  qed
  with \<open>2 dvd m\<close> have "2 dvd gcd m n" by (rule gcd_greatest)
  with lowest_terms have "2 dvd 1" by simp
  thus False using odd_one by blast
qed

end