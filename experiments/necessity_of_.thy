theory "necessity_of_"
  imports Main "../QML"
begin



axiomatization where refl :"(\<forall>x. x r x)"
axiomatization where symm : "(\<forall>x y. x r y \<longrightarrow> y r x)"
axiomatization where transitive :"(\<forall>x y z. ((x r y) \<and> (y r z) \<longrightarrow> (x r z)))"
axiomatization where euclidean :"(\<forall>x y z. ((x r y) \<and> (x r z) \<longrightarrow> (y r z)))"


consts makeTable ::  "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  ("T") 

lemma 
  assumes compossibilty1: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. ((T x y) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z) \<^bold>\<and> \<^bold>\<diamond>(\<^bold>\<exists>t. T t z)) \<^bold>\<rightarrow> \<^bold>\<diamond>((T x y) \<^bold>\<and> (\<^bold>\<exists>x'. (T x' z))))\<rfloor>" 
  assumes origin_uniqueness: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>z. \<^bold>\<not>(\<^bold>\<diamond>((T x y) \<^bold>\<and> (T x z) \<^bold>\<and> \<^bold>\<not>(y \<^bold>=\<^sup>L z))))\<rfloor>"
  assumes sufficiency1: "\<lfloor>(\<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<diamond>(T x' y) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. (T x y) \<^bold>\<rightarrow> (x\<^bold>=\<^sup>Lx')))\<rfloor>"  
  shows independence: "\<lfloor>(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<forall>x'. \<^bold>\<forall>z. T x y \<^bold>\<rightarrow> \<^bold>\<box>(((\<^bold>\<not>(y\<^bold>=\<^sup>Lz)) \<^bold>\<and> T x' z) \<^bold>\<rightarrow> \<^bold>\<diamond>(T x y \<^bold>\<and> T x' z)))\<rfloor>"
  oops

lemma necessity_of_distinctness_leib: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<diamond>(\<^bold>\<not>(x \<^bold>=\<^sup>L y)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x \<^bold>=\<^sup>L y))\<rfloor>"
  by auto

lemma necessity_of_identity_leib: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. ((x \<^bold>=\<^sup>L y)) \<^bold>\<rightarrow> \<^bold>\<box>((x \<^bold>=\<^sup>L y))\<rfloor>"
  by auto

lemma
  assumes indiscernibility_of_identicals: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. (x \<^bold>\<leftrightarrow> y) \<^bold>\<and> (\<^bold>\<forall>F. F x \<^bold>\<rightarrow> F y)\<rfloor>"
  shows necessity_of_identity: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. (x \<^bold>\<leftrightarrow> y) \<^bold>\<rightarrow> \<^bold>\<box>(x \<^bold>\<leftrightarrow> y)\<rfloor>"
proof (rule allI)
  fix w
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. (x \<^bold>\<leftrightarrow> y) \<^bold>\<rightarrow> \<^bold>\<box>(x \<^bold>\<leftrightarrow> y)) w"
  proof (rule allI)
    fix x
    show "(\<^bold>\<forall>y. (x \<^bold>\<leftrightarrow> y) \<^bold>\<rightarrow> \<^bold>\<box>(x \<^bold>\<leftrightarrow> y)) w"
    proof (rule allI)
      fix y
      show "((x \<^bold>\<leftrightarrow> y) \<^bold>\<rightarrow> \<^bold>\<box>(x \<^bold>\<leftrightarrow> y)) w" 
      proof (rule impI)
        assume "(x \<^bold>\<leftrightarrow> y) w"
        show "(\<^bold>\<box>(x \<^bold>\<leftrightarrow> y)) w"
        proof (rule allI)
          fix v
          show "w r v \<longrightarrow> ((x \<^bold>\<leftrightarrow> y) v)"  
          proof (rule impI)
            assume "w r v"
            show "(x \<^bold>\<leftrightarrow> y) v"
            proof(rule iffI)
              from indiscernibility_of_identicals have "(\<^bold>\<forall>x. \<^bold>\<forall>y. (x \<^bold>\<leftrightarrow> y) \<^bold>\<and> (\<^bold>\<forall>F. F x \<^bold>\<rightarrow> F y)) v"..
              then have "(\<^bold>\<forall>y. (x \<^bold>\<leftrightarrow> y) \<^bold>\<and> (\<^bold>\<forall>F. F x \<^bold>\<rightarrow> F y)) v" by (rule allE)
              then have "((x \<^bold>\<leftrightarrow> y) \<^bold>\<and> (\<^bold>\<forall>F. F x \<^bold>\<rightarrow> F y)) v" by (rule allE)
              then have "(x \<^bold>\<leftrightarrow> y) v" by (rule conjE)
              then show "(y v \<Longrightarrow> x v)" by simp 
            next  (* show "(x v \<Longrightarrow> y v)" using `(x \<^bold>\<leftrightarrow> y) v` by simp *)
              from indiscernibility_of_identicals have "(\<^bold>\<forall>x. \<^bold>\<forall>y. (x \<^bold>\<leftrightarrow> y) \<^bold>\<and> (\<^bold>\<forall>F. F x \<^bold>\<rightarrow> F y)) v"..
              then have "(\<^bold>\<forall>y. (x \<^bold>\<leftrightarrow> y) \<^bold>\<and> (\<^bold>\<forall>F. F x \<^bold>\<rightarrow> F y)) v" by (rule allE)
              then have "((x \<^bold>\<leftrightarrow> y) \<^bold>\<and> (\<^bold>\<forall>F. F x \<^bold>\<rightarrow> F y)) v" by (rule allE)          
              then have "(x \<^bold>\<leftrightarrow> y) v" by (rule conjE)
              then show "(x v \<Longrightarrow> y v)" by simp 
            qed
          qed
        qed
      qed
    qed
  qed
qed




 
lemma
  assumes necessity_of_identity: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. (x \<^bold>\<leftrightarrow> y) \<^bold>\<rightarrow> \<^bold>\<box>(x \<^bold>\<leftrightarrow> y)\<rfloor>"
  shows necessity_of_distinctness: "\<lfloor>\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<diamond>(\<^bold>\<not>(x \<^bold>\<leftrightarrow> y)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x \<^bold>\<leftrightarrow> y))\<rfloor>"
proof (rule allI)
  fix w 
  show "(\<^bold>\<forall>x. \<^bold>\<forall>y. \<^bold>\<diamond>(\<^bold>\<not>(x \<^bold>\<leftrightarrow> y)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x \<^bold>\<leftrightarrow> y))) w"
  proof (rule allI)
    fix x
    show "(\<^bold>\<forall>y. \<^bold>\<diamond>(\<^bold>\<not>(x \<^bold>\<leftrightarrow> y)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x \<^bold>\<leftrightarrow> y))) w"
    proof (rule allI)
      fix y
      show "(\<^bold>\<diamond>(\<^bold>\<not>(x \<^bold>\<leftrightarrow> y)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(x \<^bold>\<leftrightarrow> y))) w"
      proof (rule impI)
        assume possibility: "(\<^bold>\<diamond>(\<^bold>\<not>(x \<^bold>\<leftrightarrow> y))) w"
        show "\<^bold>\<box>(\<^bold>\<not>(x \<^bold>\<leftrightarrow> y)) w"
        proof (rule allI)
          fix v 
          show "w r v \<longrightarrow> ((\<^bold>\<not>(x \<^bold>\<leftrightarrow> y)) v)"  
          proof (rule impI)
            assume "w r v"
            show "(\<^bold>\<not>(x \<^bold>\<leftrightarrow> y)) v"
            proof (rule notI)
              assume "((x \<^bold>\<leftrightarrow> y)) v"
              
              from possibility have "(\<^bold>\<diamond>(\<^bold>\<not>(x \<^bold>\<leftrightarrow> y))) w" by simp
              then obtain u where u: " w r u \<and> ((\<^bold>\<not>(x \<^bold>\<leftrightarrow> y)) u)" by (rule exE)
              then have "\<^bold>\<not>(x \<^bold>\<leftrightarrow> y) u" by (rule conjE)
              from u have "w r u" by (rule conjE)
    
              have "(x \<^bold>\<leftrightarrow> y) u"
                by (smt `w r v` `((x \<^bold>\<leftrightarrow> y)) v` local.necessity_of_identity symm `w r u`)
              then show "False" using `\<^bold>\<not>(x \<^bold>\<leftrightarrow> y) u` by auto
            qed
          qed
        qed
      qed
    qed
  qed
qed






end
