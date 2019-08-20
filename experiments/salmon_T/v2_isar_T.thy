(*<*)
theory v2_isar_T
  imports Main "../../QML"
begin
(*>*)

consts planTable :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("P") 
(* (P x y p) \<equiv> x made from y according to p *)

axiomatization where refl :"(\<forall>x. x r x)"

lemma 
assumes compossibilty2: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))\<rfloor>"  
assumes origin_uniqueness2: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))))\<rfloor>"
assumes sufficiency2: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<diamond>(P x y p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x'. (P x' y p) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx)))\<rfloor>"
shows origin_essentialism2: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p))) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p')))\<rfloor>"
proof (rule allI)
  fix w (* for the outer \<lfloor> \<rfloor> *)
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. (\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
  proof (rule allI)
    fix x (* for table x *)
    show "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. (\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
    proof (rule allI)
      fix y (* for material y *)
      show "(\<^bold>\<forall>z. \<^bold>\<forall>p. (\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
      proof (rule allI)
        fix z (* for material z *)
        show "(\<^bold>\<forall>p. (\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
        proof (rule allI)
          fix p (* for plan p *)
          show "((\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p)) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
          proof (rule impI)
            assume antecedent:  "((\<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> (P x y p))) w"
            show  "(\<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
              proof (rule notI)
                assume "((\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w"
                from antecedent have "((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (P x y p)) w" 
                  by simp
                then have non_overlapping: "\<not>(y \<^bold>=\<^sup>L z) w" by (rule conjE)
                have table_x_from_y: "(P x y p w)" 
                  using `((\<^bold>\<not>(y \<^bold>=\<^sup>L z)) \<^bold>\<and> (P x y p)) w` by (rule conjE)

                have compossibilty2_ante: "((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) w" 
                  using table_x_from_y and `((\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w` and non_overlapping by auto 

                have "((\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w" using `((\<^bold>\<diamond>(\<^bold>\<forall>p'. P x z p'))) w` by simp
                then obtain v where v: "w r v \<and> (((\<^bold>\<forall>p'. P x z p')) v)" by (rule exE)
                then have sufficiency2_ante: "(\<^bold>\<diamond>(P x z p)) w" by auto
                (* have "w r v" using `w r v \<and> (((\<^bold>\<forall>p'. P x z p')) v)` by (rule conjE) *)

                from compossibilty2 have "((\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))) w"..
                then have "((\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))) w" by (rule allE)
                then have "((\<^bold>\<forall>z. \<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))) w" by (rule allE)
                then have "((\<^bold>\<forall>p. ((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))))) w" by (rule allE)
                then have "(((P x y p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. P t z p)) \<^bold>\<rightarrow> \<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p)))) w" by (rule allE)
                then have "\<^bold>\<diamond>((P x y p) \<^bold>\<and> (\<^bold>\<exists>x'. (P x' z p))) w" using compossibilty2_ante by (rule mp)
                then obtain u where u: "w r u \<and> ((P x y p \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p)) u)" by (rule exE)
                then have "(\<^bold>\<exists>x'. P x' z p) u" by auto
                then obtain x' where x': "P x' z p u" by (rule exE)
                
                have "w r u" 
                  using `w r u \<and> ((P x y p \<^bold>\<and> (\<^bold>\<exists>x'. P x' z p)) u)` by (rule conjE)
  
                from sufficiency2 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<diamond>(P x y p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (P t y p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w".. 
                then have "(\<^bold>\<forall>y. \<^bold>\<forall>p. \<^bold>\<diamond>(P x y p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (P t y p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have "(\<^bold>\<forall>p. \<^bold>\<diamond>(P x z p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (P t z p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have "(\<^bold>\<diamond>(P x z p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>t. (P t z p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" by (rule allE)
                then have "(\<^bold>\<box>(\<^bold>\<forall>t. (P t z p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx))) w" using sufficiency2_ante by (rule mp)
                then have "w r u \<longrightarrow> ((\<^bold>\<forall>t. (P t z p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx)) u)" by (rule allE)
                then have "((\<^bold>\<forall>t. (P t z p) \<^bold>\<rightarrow> (t\<^bold>=\<^sup>Lx)) u)" 
                  using `w r u` by (rule mp)
                then have "((P x' z p) \<^bold>\<rightarrow> (x'\<^bold>=\<^sup>Lx)) u" by (rule allE)
                then have "(x' \<^bold>=\<^sup>L x) u" using `P x' z p u` by (rule mp)
                then have "(P x z p) u" using `(P x' z p) u` by auto 
                moreover from u have "(P x y p) u" by simp 
                then have "(P x y p) u \<and> (P x z p) u" using `(P x z p) u` by (rule conjI)
                then have conj_existence: "(P x y p \<^bold>\<and> P x z p) u" by simp 
                then have impossible_arg: "(P x y p u) \<and> (P x z p u) \<and> \<not>((y \<^bold>=\<^sup>L z) u)" 
                  using non_overlapping by auto 
  
               from origin_uniqueness2 have "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))) u"..
               then have "(\<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))) u" by (rule allE)
               then have "(\<^bold>\<forall>z. \<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))) u" by (rule allE)
               then have "(\<^bold>\<forall>p. \<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))) u" by (rule allE)
               then have "(\<^bold>\<not>(\<^bold>\<diamond>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))) u" by (rule allE)
               then have "(\<^bold>\<box>(\<^bold>\<not>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z)))) u" by auto 
               then have "(\<^bold>\<not>((P x y p) \<^bold>\<and> (P x z p) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))) u" using refl by blast
               then show "False" using impossible_arg by (rule notE)
              qed
            qed
          qed
        qed
      qed
    qed
  qed

(*<*)
end
(*>*)
