theory v1_isar_new
  imports Main "../../QML_S5"
begin

consts makeTable ::  "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  ("T") (* (T x y) \<equiv> x made from y *)
lemma necessity_of_distinctness: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<box>((\<^bold>\<not>(x\<^bold>=\<^sup>Ly)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x\<^bold>=\<^sup>Ly))))\<rfloor>" by auto 

lemma 
  assumes compossibilty1: "\<lfloor>(\<^bold>\<forall>x1. \<^bold>\<forall>y1. \<^bold>\<forall>x2. \<^bold>\<forall>y2. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2)))\<rfloor>"
  assumes origin_uniqueness1: "\<lfloor>(\<^bold>\<forall>x1. \<^bold>\<forall>y1. \<^bold>\<forall>x2. \<^bold>\<forall>y2. ((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x1 y1) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> (\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))))\<rfloor>" 
  shows origin_essentialism1: "\<lfloor>(\<^bold>\<forall>x1. \<^bold>\<forall>y1. \<^bold>\<forall>x2. \<^bold>\<forall>y2. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)))\<rfloor>"

proof(rule allI)
  fix w
  show "(\<^bold>\<forall>x1. \<^bold>\<forall>y1. \<^bold>\<forall>x2. \<^bold>\<forall>y2. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) w" 
  proof(rule allI)
    fix x1
    show "(\<^bold>\<forall>y1. \<^bold>\<forall>x2. \<^bold>\<forall>y2. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) w" 
    proof(rule allI)
      fix y1
      show  "(\<^bold>\<forall>x2. \<^bold>\<forall>y2. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) w" 
      proof(rule allI)
        fix x2
        show  "(\<^bold>\<forall>y2. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) w" 
        proof(rule allI)
          fix y2
          show  "(T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) w"
          proof(rule impI)
            assume table_x1_from_y1: "T x1 y1 w"
            show  "(\<^bold>\<box>((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) w"
            proof(rule allI)
              fix v
              show "(((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) v"
              proof(rule impI)
                assume antecedent: "((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) v"
                show "(\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)) v"
                proof(rule notI)
                  assume "(x1\<^bold>=\<^sup>Lx2) v"

                  from antecedent have table_x2_from_y2: "T x2 y2 v" by (rule conjE)
                  from antecedent have non_overlapping: "(\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) v" by (rule conjE)

                  from compossibilty1 have "(\<^bold>\<forall>x1. \<^bold>\<forall>y1. \<^bold>\<forall>x2. \<^bold>\<forall>y2. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2))) w"..
                  then have "(\<^bold>\<forall>y1. \<^bold>\<forall>x2. \<^bold>\<forall>y2. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2))) w" by (rule allE)
                  then have "(\<^bold>\<forall>x2. \<^bold>\<forall>y2. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2))) w" by (rule allE)
                  then have "(\<^bold>\<forall>y2. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2))) w" by (rule allE)
                  then have "(T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2))) w" by (rule allE)
                  then have "(\<^bold>\<box>(((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2))) w" 
                    using table_x1_from_y1 by (rule mp)
                  then have "((((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2))) v" by (rule allE)
                  then have "(\<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2)) w" using antecedent by (rule mp)
                  then obtain u where u: "(T x1 y1 \<^bold>\<and> T x2 y2) u" by (rule exE)
                  have "(\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) u" using non_overlapping by auto
                  then have origin_uniqueness1_ante: "((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x1 y1) \<^bold>\<and> (T x2 y2))) u" 
                    using `(T x1 y1 \<^bold>\<and> T x2 y2) u` by (rule conjI)

                  from origin_uniqueness1 have "(\<^bold>\<forall>x1. \<^bold>\<forall>y1. \<^bold>\<forall>x2. \<^bold>\<forall>y2. ((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x1 y1) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> (\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)))) u"..
                  then have "(\<^bold>\<forall>y1. \<^bold>\<forall>x2. \<^bold>\<forall>y2. ((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x1 y1) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> (\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)))) u" by (rule allE)
                  then have "(\<^bold>\<forall>x2. \<^bold>\<forall>y2. ((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x1 y1) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> (\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)))) u" by (rule allE)
                  then have "(\<^bold>\<forall>y2. ((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x1 y1) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> (\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)))) u" by (rule allE)
                  then have "(((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x1 y1) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> (\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)))) u" by (rule allE) 
                  then have "(\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)) u" using origin_uniqueness1_ante by (rule mp)
                  then have "(\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)) v" using necessity_of_distinctness by auto
                  then show "False" using `(x1\<^bold>=\<^sup>Lx2) v` by (rule notE)
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
