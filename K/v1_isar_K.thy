theory v1_isar_K
  imports Main "../QML"
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

consts makeTable ::  "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  ("T") 
(* (T x y) \<equiv> x made from y *)
 

lemma 
  assumes compossibilty1: 
"\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. ((T x y) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. T x' z))\<rfloor>" 
assumes origin_uniqueness1: 
"\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>(\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))\<rfloor>" 
assumes sufficiency1: 
"\<lfloor>\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<diamond>(T x' y) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. (T x y) \<^bold>\<rightarrow> (x\<^bold>=\<^sup>Lx'))\<rfloor>"  
shows origin_essentialism1: 
"\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))\<rfloor>"
  text \<open>\<^item> Setting-up the worlds\<close>
(*<*)
proof (rule allI)
  fix w (* for the outer \<lfloor> \<rfloor> *)
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
  proof (rule allI)
    fix x (* for table x *)
    show "(\<^bold>\<forall>y. \<^bold>\<forall>z. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
    proof (rule allI)
      fix y (* for material y *)
      show "(\<^bold>\<forall>z. ((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
      proof (rule allI)
        fix z (* for material z *)
        show "(((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(T x z))) w"
(*>*)
        proof (rule impI)
          assume antecedent: "((y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> (T x y)) w"
          show "\<^bold>\<not>(\<^bold>\<diamond>(T x z)) w"
          proof(rule notI)
            assume sufficiency1_ante: "(\<^bold>\<diamond>(T x z)) w"
            then have compossibilty1_ante: "((T x y) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) w" 
              using antecedent by auto
            from antecedent have non_overlapping: "(y\<^bold>\<noteq>\<^sup>Lz) w" by (rule conjE)
            text\<open>\<^item> Deriving @{text "T x' z"} in @{term u} using @{term compossibilty1}\<close>
            from compossibilty1 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. ((T x y) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w"..
(*<*)
            then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. ((T x y) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w" 
              by (rule allE)
            then have "(\<^bold>\<forall>z. ((T x y) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w" 
              by (rule allE)
            then have "(((T x y) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w" 
              by (rule allE)
(*>*)
            then have "(\<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z)))) w" 
              using compossibilty1_ante by (rule mp)
            then obtain u where u: "(w r u) \<and> (((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z))) u)" 
              by (rule exE)
            then have "((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z))) u" by simp
            then have "(\<^bold>\<exists>x'. T x' z) u" by (rule conjE)
            then obtain x' where x': "T x' z u" by (rule exE)
            from u have "w r u" by (rule conjE)
            text \<open>\<^item> Deriving @{text "x' \<^bold>=\<^sup>L x"} in @{term u} using @{term sufficiency1}\<close>
            from sufficiency1 have "(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<diamond>(T x' y) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. (T x y) \<^bold>\<rightarrow> (x\<^bold>=\<^sup>Lx'))) w"..
(*<*)
            then have "(\<^bold>\<forall>x'. \<^bold>\<diamond>(T x' z) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. (T x z) \<^bold>\<rightarrow> (x\<^bold>=\<^sup>Lx'))) w" 
              by (rule allE)
            then have "(\<^bold>\<diamond>(T x z) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (T t z) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" 
              by (rule allE)
(*>*)
            then have  "(\<^bold>\<box>(\<^bold>\<forall>t. (T t z) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w"
              using sufficiency1_ante by (rule mp)
            then have "w r u \<longrightarrow> ((\<^bold>\<forall>t. (T t z) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx)) u)" by (rule allE)
            then have "((\<^bold>\<forall>t. (T t z) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx)) u)" using `w r u` by (rule mp)
            then have "((T x' z) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx)) u" by (rule allE)
            then have "(x' \<^bold>=\<^sup>L x) u" 
              using `T x' z u` by (rule mp)
            then have "(T x z) u" 
              using `(T x' z) u` by auto
            text\<open>\<^item> Framing the @{term impossible_arg}\<close>
            from u have "(T x y) u" by simp
            then have "(T x y \<^bold>\<and> T x z) u" 
              using `(T x z) u` by (rule conjI)
            then have impossible_arg: "(T x y \<^bold>\<and> T x z \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)) u" 
              using non_overlapping by auto
            text\<open>\<^item> Falsifying the @{term impossible_arg} using @{term origin_uniqueness1}\<close>
            from origin_uniqueness1 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>(\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w"..
(*<*)
            then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>(\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" 
              by (rule allE)
            then have "(\<^bold>\<forall>z. \<^bold>\<not>(\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" 
              by (rule allE)
            then have "(\<^bold>\<not>(\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz)))) w" 
              by (rule allE)
(*>*)
            then have "\<^bold>\<box>(\<^bold>\<not>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz))) w" 
              by auto 
            then have "(\<^bold>\<not>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> (y\<^bold>\<noteq>\<^sup>Lz))) u" 
              using `w r u` by auto
            then show "False" using impossible_arg by (rule notE)
(*<*)
          qed
        qed
      qed
    qed
  qed
qed
(*>*)




end
