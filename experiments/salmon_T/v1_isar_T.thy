theory v1_isar_T
  imports Main "../../QML"
begin

consts makeTable ::  "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  ("T") (* (T x y) \<equiv> x made from y *)

(* abbreviation refl :: "bool"
  where "refl \<equiv> (\<forall>x. x r x)"
 *)

axiomatization where refl :"(\<forall>x. x r x)"

lemma 
  (* assumes refl : "(\<forall>x. x r x)" *)
  assumes compossibilty1: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. ((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z))))\<rfloor>" 
  assumes origin_uniqueness: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>(\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))))\<rfloor>" 
  assumes sufficiency1: "\<lfloor>(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<diamond>(T x' y) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. (T x y) \<^bold>\<rightarrow> (x\<^bold>=\<^sup>Lx')))\<rfloor>"  
  shows origin_essentialism1: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. (((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y))) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z)))\<rfloor>" 
proof (rule allI)
  fix w (* for the outer \<lfloor> \<rfloor> *)
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. ((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
  proof (rule allI)
    fix x (* for table x *)
    show "(\<^bold>\<forall>y. \<^bold>\<forall>z. ((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
    proof (rule allI)
      fix y (* for material y *)
      show "(\<^bold>\<forall>z. ((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
      proof (rule allI)
        fix z (* for material z *)
        show "(((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
        proof (rule impI)
          assume antecedent: "(((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y))) w"
          show "(\<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
          proof(rule notI)
            assume table_x_from_z: "(\<^bold>\<diamond>(T x z)) w"
              from antecedent have "(((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y))) w" by simp
              then have non_overlapping: "(\<^bold>\<not>(y \<^bold>=\<^sup>L z)) w" by (rule conjE)
              have table_x_from_y: "T x y w" 
                using `((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y)) w` by (rule conjE)

              have compossibilty1_ante: "((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) w" 
                using antecedent and table_x_from_z by auto

              from compossibilty1 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. ((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w"..
              then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. ((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w" 
                by (rule allE)
              then have "(\<^bold>\<forall>z. ((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w" 
                by (rule allE)
              then have "(((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w" 
                by (rule allE)
              then have "(\<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w" 
                using compossibilty1_ante by (rule mp)
              then obtain u where u:  "(w r u) \<and> (((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z))) u)" 
                by (rule exE)
              then have "((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z))) u" by simp
              then have "(\<exists>t. T t z u)" by (rule conjE)
              then obtain x' where x': "T x' z u" by (rule exE)
              then have  "T x' z u" by simp

(* Relation between u, v and w, prove "w r u" *)
              have "w r u" 
                using `(w r u) \<and> (((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z))) u)` by (rule conjE)

              from sufficiency1 have "(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<diamond>(T x' y) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. (T x y) \<^bold>\<rightarrow> (x\<^bold>=\<^sup>Lx'))) w"..
              then have "(\<^bold>\<forall>x'. \<^bold>\<diamond>(T x' z) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. (T x z) \<^bold>\<rightarrow> (x\<^bold>=\<^sup>Lx'))) w" 
                by (rule allE)
              then have "(\<^bold>\<diamond>(T x z) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (T t z) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" 
                by (rule allE)
              then have  "(\<^bold>\<box>(\<^bold>\<forall>t. (T t z) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w"
                using `(\<^bold>\<diamond>(T x z)) w` by (rule mp)
              then have "(\<^bold>\<forall>t. (T t z) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx)) u" 
                using `w r u` by (simp add: `(\<^bold>\<box>(\<^bold>\<forall>t. (T t z) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w`)

              then have "((T x' z) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx)) u" by (rule allE)
              then have "(x' \<^bold>=\<^sup>L x) u" 
                using `T x' z u` by (rule mp)
              then have "(T x z) u" 
                using `(T x' z) u` by auto
              have "(T x y) u" using u by blast
              then have "(T x y) u \<and> (T x z) u" 
                using `(T x z) u` by (rule conjI)
              then have impossible_arg: "(T x y \<^bold>\<and> T x z \<^bold>\<and> (\<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" 
                using non_overlapping by auto
 
              from origin_uniqueness have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>(\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))) u".. 
              then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>(\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))) u" 
                by (rule allE)
              then have "(\<^bold>\<forall>z. \<^bold>\<not>(\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))) u" 
                by (rule allE)
              then have "(\<^bold>\<not>(\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))) u" 
                by (rule allE)
              then have "\<^bold>\<box>(\<^bold>\<not>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" 
                by auto 
              then have "(\<^bold>\<not>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" 
                using refl by blast
              then show "False" using impossible_arg by (rule notE)
            qed
          qed
        qed                      
      qed
        qed
      qed      
end
