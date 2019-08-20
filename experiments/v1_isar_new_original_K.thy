theory v1_isar_new_original_K
  imports Main "../../QML"
begin

(* (T x y) \<equiv> x made from y *)
consts makeTable ::  "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  ("T") 
(* lemma necessity_of_distinctness: "\<lfloor>(\<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<box>(\<^bold>\<forall>y. \<^bold>\<box>(\<^bold>\<not>(x\<^bold>=\<^sup>Ly) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x\<^bold>=\<^sup>Ly))))))\<rfloor>" by auto *)

lemma 
  assumes compossibilty1: "\<lfloor>(\<^bold>\<box>(\<^bold>\<forall>x1. \<^bold>\<forall>y1. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. ((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2))))\<rfloor>"
  assumes origin_uniqueness1: "\<lfloor>(\<^bold>\<box>(\<^bold>\<forall>x1. \<^bold>\<forall>y1. \<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. \<^bold>\<box>((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x1 y1) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> (\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))))))\<rfloor>" 
  shows origin_essentialism1: "\<lfloor>(\<^bold>\<box>(\<^bold>\<forall>x1. \<^bold>\<forall>y1. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. (\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))))\<rfloor>"

proof(rule allI)
  fix a
  show "(\<^bold>\<box>(\<^bold>\<forall>x1. \<^bold>\<forall>y1. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. (\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)))) a"
  proof(rule allI)
    fix b
    show "a r b \<longrightarrow> ((\<^bold>\<forall>x1. \<^bold>\<forall>y1. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. (\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) b)"
    proof(rule impI)
      assume "a r b"
      show "((\<^bold>\<forall>x1. \<^bold>\<forall>y1. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. (\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) b)"
      proof(rule allI)
        fix x1
        show "((\<^bold>\<forall>y1. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. (\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) b)"
        proof(rule allI)
          fix y1
          show "((T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. (\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) b)"
          proof (rule impI)
            assume table_x1_from_y1: "T x1 y1 b"          
            show "((\<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. (\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) b)"
            proof(rule allI)
              fix c            
              show "b r c \<longrightarrow> (((\<^bold>\<forall>x2. \<^bold>\<forall>y2. (\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) c)"
              proof (rule impI)
                assume "b r c"              
                show "(((\<^bold>\<forall>x2. \<^bold>\<forall>y2. (\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) c)"
                proof (rule allI)
                  fix x2 
                  show "(((\<^bold>\<forall>y2. (\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) c)"
                  proof (rule allI)
                    fix y2 
                    show "((((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> \<^bold>\<not>(x1\<^bold>=\<^sup>Lx2))) c)"
                    proof (rule impI)
                      assume antecedent: "((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> (T x2 y2)) c"
                      show "(\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)) c"
                      proof (rule notI)
                        assume "(x1\<^bold>=\<^sup>Lx2) c"
                        from antecedent have table_x2_from_y2: "T x2 y2 c" by (rule conjE)
                        from antecedent have non_overlapping: "(\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) c" by (rule conjE)

                        from compossibilty1 have "(\<^bold>\<box>(\<^bold>\<forall>x1. \<^bold>\<forall>y1. T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. ((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2)))) a"..
                        then have "((T x1 y1 \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. ((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2))) b)" 
                          using `a r b` by auto
                        then have "((\<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. ((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2))) b)" 
                          using table_x1_from_y1 by auto
                        then have "((((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2)) \<^bold>\<and> T x2 y2) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2)) c)" 
                          using `b r c` by auto
                        then have "(\<^bold>\<diamond>(T x1 y1 \<^bold>\<and> T x2 y2)) c" 
                          using antecedent by auto
                        then obtain d where d: "c r d \<and> (((T x1 y1 \<^bold>\<and> T x2 y2)) d)" by (rule exE)
                        then have "c r d" by (rule conjE)
                        have "(T x1 y1 \<^bold>\<and> T x2 y2) d" 
                          using `c r d \<and> (((T x1 y1 \<^bold>\<and> T x2 y2)) d)` by (rule conjE) 

                        from  origin_uniqueness1 have "(\<^bold>\<box>(\<^bold>\<forall>x1. \<^bold>\<forall>y1. \<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. \<^bold>\<box>((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x1 y1) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> (\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)))))) a"..
                        then have "((\<^bold>\<box>(\<^bold>\<forall>x2. \<^bold>\<forall>y2. \<^bold>\<box>((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x1 y1) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> (\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)))))) b" 
                          using `a r b` by auto
                        then have "(((\<^bold>\<box>((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x1 y1) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> (\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)))))) c"  
                          using `b r c` by metis
                        then have "(((((\<^bold>\<not>(y1\<^bold>=\<^sup>Ly2) \<^bold>\<and> (T x1 y1) \<^bold>\<and> (T x2 y2)) \<^bold>\<rightarrow> (\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)))))) d" 
                          using `c r d` by auto
                        then have "(\<^bold>\<not>(x1\<^bold>=\<^sup>Lx2)) d" 
                          using `(T x1 y1 \<^bold>\<and> T x2 y2) d` and table_x1_from_y1 and `b r c` and `c r d` by (meson antecedent)
                        then show False using `(x1\<^bold>=\<^sup>Lx2) c` and `c r d` by auto
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
  qed
qed


end
