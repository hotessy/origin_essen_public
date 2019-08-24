theory v1_isar
  imports Main "../QML_S5"
begin

text \<open>
@{text "Compossibility\<^sub>1"}: If a table @{term x} is originally made from matter @{term y} and it
is possible for any table to be originally made from matter @{term z} such that @{term y} and @{term z} 
are distinct, then it is  possible for table @{term x} to be originally made from matter @{term y}
and in addition some table @{term x'} to be originally made from matter @{term z}.
\<close>

text \<open>
@{text "Origin Uniqueness\<^sub>1"}: It is impossible that a single table @{term x}, is originally made from 
matter @{term y} and originally made from matter @{term z} such that @{term y} and @{term z} are distinct.
\<close>


text \<open>
@{text "Sufficiency\<^sub>1"}: If it is possible that a table @{term x'} is originally made from matter @{term y}, 
then necessarily any table, say @{term x}, originally made from matter @{term y} is the very table @{term x'}.
\<close>

text \<open>
@{text "Origin Essentialism\<^sub>1"}: If it is possible that a table @{term x} is originally made from matter 
@{term y} and that matter @{term y} and matter @{term z} are distinct, then it is impossible that 
table @{term x} be originally made from any @{term z}.
\<close>

consts makeTable ::  "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  ("T") (* (T x y) \<equiv> x made from y *)
abbreviation overlap ::  "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  ("O")
  where "O x y \<equiv> x \<^bold>=\<^sup>L y" 


lemma self_identity: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<box>(x \<^bold>=\<^sup>L x) \<rfloor>" by auto
lemma necessity_of_identity: "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<diamond>(x\<^bold>=\<^sup>Ly) \<^bold>\<rightarrow> \<^bold>\<box>(x\<^bold>=\<^sup>Ly))\<rfloor>" by auto
lemma necessity_of_distinctness: "\<lfloor>\<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<forall>y.\<^bold>\<not>\<^bold>\<diamond>(x\<^bold>=\<^sup>Ly) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x\<^bold>=\<^sup>Ly)))\<rfloor>" by auto

lemma 
  assumes compossibilty1: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. ((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z))))\<rfloor>" 
  assumes origin_uniqueness: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))\<rfloor>" 
  assumes sufficiency1: "\<lfloor>(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<diamond>(T x' y) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. (T x y) \<^bold>\<rightarrow> (x\<^bold>=\<^sup>Lx')))\<rfloor>"  
  shows origin_essentialism1: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. (\<^bold>\<diamond>((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y))) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z)))\<rfloor>" 
proof (rule allI)
  fix w (* for the outer \<lfloor> \<rfloor> *)
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<diamond>((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
  proof (rule allI)
    fix x (* for table x *)
    show "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<diamond>((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
    proof (rule allI)
      fix y (* for material y *)
      show "(\<^bold>\<forall>z. \<^bold>\<diamond>((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
      proof (rule allI)
        fix z (* for material z *)
        show "(\<^bold>\<diamond>((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
        proof (rule impI)
          assume antecedent: "(\<^bold>\<diamond>((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y))) w"
          show "(\<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
            proof (rule notI)
              assume "(\<^bold>\<diamond>(T x z)) w" 
              from antecedent obtain w where w: "((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y)) w" 
                by (rule exE) (* Expanding \<diamond> in the same world *)
              then have non_overlapping: "((\<^bold>\<not>(y \<^bold>=\<^sup>L z))) w"  
                by (rule conjE)
              have table_x_from_y: "(T x y w)" 
                using `((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (T x y)) w` by (rule conjE)
              have compossibilty1_ante: "((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) w" 
                using table_x_from_y and `(\<^bold>\<diamond>(T x z)) w` and non_overlapping by auto
             
              
              from compossibilty1 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. ((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w"..
              then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. ((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w" 
                by (rule allE)
              then have "(\<^bold>\<forall>z. ((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w" 
                by (rule allE)
              then have "(((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w" 
                by (rule allE)
              then have "\<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z))) w" 
                using compossibilty1_ante by (rule mp)
              then obtain u where u: "(T x y u  \<and> (\<exists>t. T t z u)) " 
                by (rule exE)
              then have "(\<exists>t. T t z u)" by (rule conjE)
              then obtain x' where x': "T x' z u" by (rule exE)

              from sufficiency1 have "(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<diamond>(T x' y) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. (T x y) \<^bold>\<rightarrow> (x\<^bold>=\<^sup>Lx'))) w"..
              then have "(\<^bold>\<forall>x'. \<^bold>\<diamond>(T x' z) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. (T x z) \<^bold>\<rightarrow> (x\<^bold>=\<^sup>Lx'))) w" 
                by (rule allE)
              then have "(\<^bold>\<diamond>(T x z) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (T t z) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" 
                by (rule allE)
              then have "\<^bold>\<box>(\<^bold>\<forall>t. (T t z) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx)) w" 
                using `(\<^bold>\<diamond>(T x z)) w` by (rule mp)
              then have "(\<^bold>\<forall>t. (T t z) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx)) u" by (rule allE)
              then have "((T x' z) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx)) u" by (rule allE)
              then have "(x' \<^bold>=\<^sup>L x) u" 
                using `T x' z u` by (rule mp)
              then have "(T x z) u" 
                using `(T x' z) u` by auto
              moreover from u have "(T x y) u"..
              then have "(T x y) u \<and> (T x z) u" 
                using `(T x z) u` by (rule conjI)
              then have impossible_arg: "(T x y \<^bold>\<and> T x z \<^bold>\<and> (\<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" 
                using non_overlapping by auto

              from origin_uniqueness have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u"..
              then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" 
                by (rule allE)
              then have "(\<^bold>\<forall>z. \<^bold>\<not>\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" 
                by (rule allE)
              then have "(\<^bold>\<not>\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" 
                by (rule allE)
              then have "\<^bold>\<box>(\<^bold>\<not>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" 
                by auto 
              then have "(\<^bold>\<not>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" 
                by (rule allE) 
              then show "False" 
                using impossible_arg by (rule notE)
            qed
          qed
        qed
      qed
    qed
  qed


end
