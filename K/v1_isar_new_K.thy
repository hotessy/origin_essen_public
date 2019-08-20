theory v1_isar_new_K
  imports Main "../QML"
begin

text \<open>
@{text "Compossibility\<^sub>6'"}: Necessarily, given a table,  @{term x}, made from a hunk, @{term y}, 
for any table, @{term x'} which might be made from a hunk, @{term z}, distinct from @{term y}, it 
is also possible that both @{term x} is a table made from @{term y} and @{term x'} is a table made 
from @{term z}.


@{text "Origin Uniqueness\<^sub>6'"}:
Necessarily, if  @{term x} is a table made from  @{term y} and  @{term x'} is a table made
from  @{term z} and @{text "y\<noteq>z"}, then @{text "x\<noteq>x'"}.
\<close>

text \<open>
@{text "Origin Essentialism\<^sub>6'"}: Necessarily, given a table, @{term x}, made from a hunk, @{term y}, any table, @{term x'}, 
which might be made from a hunk, @{term z}, distinct from @{term y}, is distinct from @{term x}.
\<close>


(* (T x y) \<equiv> x made from y *)
consts makeTable ::  "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  ("T") 
(* lemma necessity_of_distinctness: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y.(\<^bold>\<not>(x\<^bold>=\<^sup>Ly) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x\<^bold>=\<^sup>Ly))))\<rfloor>" by auto *)

lemma 
  assumes compossibilty1: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y\<^bold>=\<^sup>Lz)) \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z)))\<rfloor>"
  assumes origin_uniqueness1: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. ((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<not>(x\<^bold>=\<^sup>Lx')))\<rfloor>" 
  shows origin_essentialism1: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<not>(x\<^bold>=\<^sup>Lx')))\<rfloor>"

proof(rule allI)
  fix w
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<not>(x\<^bold>=\<^sup>Lx'))) w" 
  proof(rule allI)
    fix x
    show "(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<not>(x\<^bold>=\<^sup>Lx'))) w" 
    proof(rule allI)
      fix y
      show  "(\<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<not>(x\<^bold>=\<^sup>Lx'))) w" 
      proof(rule allI)
        fix x'
        show  "(\<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<not>(x\<^bold>=\<^sup>Lx'))) w" 
        proof(rule allI)
          fix z
          show  "(T x y \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<not>(x\<^bold>=\<^sup>Lx'))) w"
          proof(rule impI)
            assume table_x1_from_y1: "T x y w"
            show  "(\<^bold>\<box>((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<not>(x\<^bold>=\<^sup>Lx'))) w"
            proof(rule allI)
              fix v
              show  "(w r v) \<longrightarrow> ((((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<not>(x\<^bold>=\<^sup>Lx'))) v)"
              proof (rule impI)
                assume "(w r v)"
                show "((((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> \<^bold>\<not>(x\<^bold>=\<^sup>Lx'))) v)"
                proof(rule impI)
                  assume antecedent: "((\<^bold>\<not>(y\<^bold>=\<^sup>Lz)) \<^bold>\<and> T x' z) v"
                  show "(\<^bold>\<not>(x\<^bold>=\<^sup>Lx')) v"
                  proof(rule notI)
                    assume identity: "(x\<^bold>=\<^sup>Lx') v"
  
                    from antecedent have table_x2_from_y2: "T x' z v" by (rule conjE)
                    from antecedent have non_overlapping: "\<^bold>\<not>(y\<^bold>=\<^sup>Lz) v" by (rule conjE)
  
                    from compossibilty1 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y\<^bold>=\<^sup>Lz)) \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) w"..
                    then have "(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y\<^bold>=\<^sup>Lz)) \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) w" by (rule allE)
                    then have "(\<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y\<^bold>=\<^sup>Lz)) \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) w" by (rule allE)
                    then have "(\<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y\<^bold>=\<^sup>Lz)) \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) w" by (rule allE)
                    then have "(T x y \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y\<^bold>=\<^sup>Lz)) \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) w" by (rule allE)
                    then have "(\<^bold>\<box>(((\<^bold>\<not>(y\<^bold>=\<^sup>Lz)) \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) w" 
                      using table_x1_from_y1 by (rule mp)
                    then have "((((\<^bold>\<not>(y\<^bold>=\<^sup>Lz)) \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z))) v" using `w r v` by auto
                    then have "(\<^bold>\<diamond>(T x y \<^bold>\<and> T x' z)) v" using antecedent by (rule mp)
                    then obtain u where u: "v r u \<and> ((T x y \<^bold>\<and> T x' z) u)" by (rule exE)
                    then have origin_uniqueness1_ante: "((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z))) u" 
                      using non_overlapping by auto
                    from u have "v r u" by (rule conjE)
  
  
                    from origin_uniqueness1 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. ((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (\<^bold>\<not>(x\<^bold>=\<^sup>Lx')))) u"..
                    then have "(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. ((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (\<^bold>\<not>(x\<^bold>=\<^sup>Lx')))) u" by (rule allE)
                    then have "(\<^bold>\<forall>x'. \<^bold>\<forall>z. ((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (\<^bold>\<not>(x\<^bold>=\<^sup>Lx')))) u" by (rule allE)
                    then have "(\<^bold>\<forall>z. ((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (\<^bold>\<not>(x\<^bold>=\<^sup>Lx')))) u" by (rule allE)
                    then have "(((\<^bold>\<not>(y\<^bold>=\<^sup>Lz) \<^bold>\<and> (T x y) \<^bold>\<and> (T x' z)) \<^bold>\<rightarrow> (\<^bold>\<not>(x\<^bold>=\<^sup>Lx')))) u" by (rule allE) 
                    then have "(\<^bold>\<not>(x\<^bold>=\<^sup>Lx')) u" using origin_uniqueness1_ante by (rule mp)
                    then show "False" using identity and `v r u` by auto
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed


end
