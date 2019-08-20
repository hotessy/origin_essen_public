theory v1_distinctness
  imports Main "../QML_S5"

begin 


consts makeTable :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("T")
abbreviation overlap ::  "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  ("O")
  where "O x y \<equiv> x \<^bold>=\<^sup>L y" 

lemma necessity_of_distinctness: "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<forall>y.\<^bold>\<not> \<^bold>\<diamond>(x\<^bold>=\<^sup>Ly) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x\<^bold>=\<^sup>Ly)))\<rfloor>" by auto
lemma necessity_of_identity: "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<diamond>(x\<^bold>=\<^sup>Ly) \<^bold>\<rightarrow> \<^bold>\<box>(x\<^bold>=\<^sup>Ly))\<rfloor>" by auto

lemma mLeibeq_subst:
  assumes xxw: "(x' \<^bold>=\<^sup>L x) w"
  assumes "(F x') w"
  shows "(F x) w"
proof -
  from xxw have "(F x' \<^bold>\<rightarrow> F x) w"..
  thus "(F x) w" using `(F x') w`..
qed

lemma mLeibeq_reflexive: "(x \<^bold>=\<^sup>L x) w"
proof
  fix F
  show "(F x \<^bold>\<rightarrow> F x) w"
  proof
    assume "(F x) w"
    thus "(F x) w".
  qed
qed

lemma mLeibeq_symmetric:
  assumes bla: "(x' \<^bold>=\<^sup>L x) w"
  shows  "(x \<^bold>=\<^sup>L x') w"
proof
  fix F
  show "(F x \<^bold>\<rightarrow> F x') w"
  proof
    assume "(F x) w"
    show "(F x') w"
    proof (rule ccontr)
      assume "\<not> (F x') w"
      moreover from bla have "(\<^bold>\<not> F x' \<^bold>\<rightarrow> \<^bold>\<not> F x) w"..
      ultimately have "\<not> (F x) w" by (rule rev_mp)
      thus "False" using `(F x) w`..
    qed
  qed
qed

lemma
  assumes compossibilty: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>x'. ((T x y) \<^bold>\<and> \<^bold>\<not>(O y z) \<^bold>\<and> \<^bold>\<diamond>(T x' z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (T x' z)))\<rfloor>" 
  assumes origin_uniqueness: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(O y z)))\<rfloor>"
  shows distinctness_of_output: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>x'. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>(O y z ) \<^bold>\<and> ((T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x \<^bold>=\<^sup>L x'))\<rfloor>"

proof (rule allI)
  fix w
  show "(\<^bold>\<forall>x. \<^bold>\<forall>x'. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>(O y z ) \<^bold>\<and> ((T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x \<^bold>=\<^sup>L x'))) w"
  proof (rule allI)
    fix x
    show "(\<^bold>\<forall>x'. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>(O y z ) \<^bold>\<and> ((T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x \<^bold>=\<^sup>L x'))) w"
 proof (rule allI)
    fix x'
    show "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>(O y z ) \<^bold>\<and> ((T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x \<^bold>=\<^sup>L x'))) w"
 proof (rule allI)
    fix y
    show "(\<^bold>\<forall>z. \<^bold>\<not>(O y z ) \<^bold>\<and> ((T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x \<^bold>=\<^sup>L x'))) w"
 proof (rule allI)
    fix z
    show "(\<^bold>\<not>(O y z ) \<^bold>\<and> ((T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x \<^bold>=\<^sup>L x'))) w"
    proof (rule impI)
      assume antecedent: "(\<^bold>\<not>(O y z ) \<^bold>\<and> ((T x y) \<^bold>\<and> (T x' z))) w"
      show "(\<^bold>\<box>(\<^bold>\<not>(x \<^bold>=\<^sup>L x'))) w"
      proof (rule allI)
        fix v 
        show "(\<^bold>\<not>(x \<^bold>=\<^sup>L x')) v"
        proof
          assume identity_assm: "(x \<^bold>=\<^sup>L x') v"
          then have "(x \<^bold>=\<^sup>L x') w" using necessity_of_identity by auto
          
          from antecedent have "(\<^bold>\<not>(O y z )) w" by auto
          from antecedent have "(T x y) w" by auto

          from antecedent have "(T x' z) w" by auto
(*          then have "(T x z) w" using `(x \<^bold>=\<^sup>L x') w` by auto *)

          from compossibilty have "((\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>x'. ((T x y) \<^bold>\<and> \<^bold>\<not>(O y z) \<^bold>\<and> \<^bold>\<diamond>(T x' z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (T x' z)))) w"..
          then have "((\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>x'. ((T x y) \<^bold>\<and> \<^bold>\<not>(O y z) \<^bold>\<and> \<^bold>\<diamond>(T x' z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (T x' z)))) w" by (rule allE)
          then have "((\<^bold>\<forall>z. \<^bold>\<forall>x'. ((T x y) \<^bold>\<and> \<^bold>\<not>(O y z) \<^bold>\<and> \<^bold>\<diamond>(T x' z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (T x' z)))) w" by (rule allE)
          then have "((\<^bold>\<forall>x'. ((T x y) \<^bold>\<and> \<^bold>\<not>(O y z) \<^bold>\<and> \<^bold>\<diamond>(T x' z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (T x' z)))) w" by (rule allE)
          then have "((((T x y) \<^bold>\<and> \<^bold>\<not>(O y z) \<^bold>\<and> \<^bold>\<diamond>(T x' z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (T x' z)))) w" by (rule allE)

          then have "(\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x' z))) w" 
            using `T x y w` and `(\<^bold>\<not>(O y z)) w` and `T x' z w` by auto
          then obtain u where u: "((T x y) \<^bold>\<and> ((T x' z))) u" by (rule exE)
          then have "(T x' z u)" by (rule conjE)
          
          from identity_assm have "(x \<^bold>=\<^sup>L x') w" by auto (* looks like you need to use necessity of identity here *)





          then have "(T x y) u \<and> (T x z) u" using `(T x z) u` by auto
          then have impossible_arg: "(T x y \<^bold>\<and> T x z \<^bold>\<and> (\<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" using non_overlapping by auto
          
          from antecedent have "((\<^bold>\<not>(O y z)) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z)) w"  by auto
          then have "((\<^bold>\<not>(O y z)) \<^bold>\<and> (T x y) \<^bold>\<and> (T x z)) w" using `T x z w` by blast
          then show False using origin_uniqueness by blast
          oops

end
