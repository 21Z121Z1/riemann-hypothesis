import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3169
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3215

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransCancel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem square_map_comp {S : Scheme.{0}} {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [GrpObj C] [IsCommMonObj C] (f : A ⟶ B) (g : B ⟶ C) :
    Hecke.sq2 f ≫ Hecke.sq2 g = Hecke.sq2 (f ≫ g) := by
  unfold Hecke.sq2
  rw [← Over.comp_left]
  congr 1
  ext <;> simp

private theorem square_map_id {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] :
    Hecke.sq2 (𝟙 A) = 𝟙 _ := by
  simp [Hecke.sq2]

private theorem cls_pow' {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) (n : ℕ) (h : (Hecke.lbPow P n).IsLB) :
    GlobalTheory.CechPic.cls (Hecke.lbPow P n) h = n • GlobalTheory.CechPic.cls P hP := by
  unfold Hecke.lbPow at h ⊢
  rw [GlobalTheory.CechPic.cls_linComb hP]
  simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

private theorem bundle_cancel {S : Scheme.{0}} {A B C : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    [GrpObj C] [IsCommMonObj C] (θ : A ⟶ B) [IsIso θ] (χ : B ⟶ C) (P : LB (G2 A).left) (Q : LB (G2 B).left)
    (T : LB (G2 C).left) (hP : P.IsLB) (hQ : Q.IsLB) (hT : T.IsLB) (c : ℕ)
    (h₁ : LBIso (Hecke.lbPow P 1) (Q.pull (Hecke.sq2 θ)))
    (h₂ : LBIso (Hecke.lbPow P c) (T.pull (Hecke.sq2 (θ ≫ χ)))) :
    LBIso (Hecke.lbPow Q c) (T.pull (Hecke.sq2 χ)) := by
  have hQθ := pull_isLB hQ (Hecke.sq2 θ)
  have hTχ := pull_isLB hT (Hecke.sq2 χ)
  have hTθχ := pull_isLB hT (Hecke.sq2 (θ ≫ χ))
  have hP1 : (Hecke.lbPow P 1).IsLB := LB.isLB_linComb hP _ _
  have hPc : (Hecke.lbPow P c).IsLB := LB.isLB_linComb hP _ _
  have hQc : (Hecke.lbPow Q c).IsLB := LB.isLB_linComb hQ _ _
  rw [← GlobalTheory.CechPic.cls_eq_iff hP1 hQθ, cls_pow' hP, GlobalTheory.CechPic.cls_pull hQ] at h₁
  rw [← GlobalTheory.CechPic.cls_eq_iff hPc hTθχ, cls_pow' hP, GlobalTheory.CechPic.cls_pull hT] at h₂
  rw [← GlobalTheory.CechPic.cls_eq_iff hQc hTχ, cls_pow' hQ, GlobalTheory.CechPic.cls_pull hT]
  have key : ∀ x, GlobalTheory.CechPic.pull (Hecke.sq2 (inv θ)) (GlobalTheory.CechPic.pull (Hecke.sq2 θ) x) = x := by
    intro x
    rw [← GlobalTheory.CechPic.pull_comp, square_map_comp, IsIso.inv_hom_id, square_map_id, GlobalTheory.CechPic.pull_id]
  rw [← key (c • _), ← key (GlobalTheory.CechPic.pull (Hecke.sq2 χ) _), map_nsmul, ← h₁, one_smul, h₂,
    ← square_map_comp, GlobalTheory.CechPic.pull_comp]

theorem UpperTheory.Gal.G3.pTransCancel :
    MultBasic → RelComp → TateDiff → TateTwist → TransIso → TransCancel := by
  intro hMB hRC hTD hTT hTI p _ D G L R _ _ gb S s M N' N o o₁ o₂ θ χ h hint hadm hθ hθχ
  have hθiso : IsIso θ := hTI p D G L R gb S s M N' o o₁ θ 1 (one_mem _) hθ
  obtain ⟨hθm, hθa, ⟨θ', d₁, hθ'm, hθ'a, hθθ', hθ'θ, hd₁⟩, ⟨c₁, hc₁, ⟨hPθ⟩, t₁, t₁', ht₁, ht₁', htt₁, hc₁e⟩, hθpt⟩ := hθ
  obtain ⟨hχm₀, hχa₀, ⟨ω, d, hωm, hωa, hχω, hωχ, hd⟩, ⟨c, hc, ⟨hPχ⟩, t, t', ht, ht', htt, hce⟩, hχpt⟩ := hθχ
  have hinvm : IsMonHom (inv θ) := by
    constructor
    · rw [← cancel_mono θ]
      simp
    · rw [← cancel_mono θ]
      simp [IsMonHom.mul_hom]
  have hχm : IsMonHom χ := by
    have e : χ = inv θ ≫ (θ ≫ χ) := by simp
    rw [e]
    infer_instance
  have hc1 : c₁ = 1 :=
    (hMB p).1 _ c₁ 1 hc₁ (Nat.coprime_one_left p) ⟨t₁, t₁', ht₁, ht₁', htt₁, hc₁e⟩
      ((hMB p).2.2 D G L 1 (one_mem _))
  subst hc1
  refine ⟨hχm, ?_, ⟨ω ≫ θ, d, inferInstance, ?_, ?_, ?_, hd⟩,
    ⟨c, hc, ⟨bundle_cancel θ χ o.P o₁.P o₂.P o.isLB o₁.isLB o₂.isLB c hPθ hPχ⟩, t, t', ht, ht', htt, hce⟩, ?_⟩
  · intro e
    rw [← cancel_epi θ, ← Category.assoc, ← hθa e, Category.assoc, hχa₀ e, Category.assoc]
  · intro e
    rw [← Category.assoc, hωa e, Category.assoc, hθa e, Category.assoc]
  · rw [← cancel_epi θ]
    simp only [← Category.assoc]
    rw [hχω, MonObj.pow_comp, MonObj.comp_pow]
    simp
  · rw [Category.assoc]
    exact hωχ
  · intro k _ _ tt β htβ
    obtain ⟨I, I₁, hI, hI₁, hr₁⟩ := hθpt k tt β htβ
    obtain ⟨J, J₂, hJ, hJ₂, hr₂⟩ := hχpt k tt β htβ
    obtain ⟨u, hu, hIJ⟩ := hTD p D G L R gb S s M o k tt I J hI hJ
    obtain ⟨J', hJ', hJJ'⟩ := hTT p D G L R gb S s N o₂ k tt J₂ hJ₂ (h * u⁻¹ * h⁻¹) (hadm _ (inv_mem hu))
    have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
    have hu'1 : h * u⁻¹ * h⁻¹ ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) (hadm _ (inv_mem hu))
    have r0 : UpperTheory.Gal.G3.Rel L I₁ I (inv θ) 1 := by
      intro n hn hnp x y
      have e : I₁.ev n x ≫ inv θ = I.ev n y ↔ I.ev n y ≫ θ = I₁.ev n x := by
        constructor
        · intro e
          rw [← e]
          simp
        · intro e
          rw [← e]
          simp
      rw [e, hr₁ n hn hnp y x]
      simp only [map_one, Module.End.one_apply]
      constructor
      · rintro ⟨v, hv, e⟩
        exact ⟨-v, neg_mem hv, by rw [e]; simp⟩
      · rintro ⟨v, hv, e⟩
        exact ⟨-v, neg_mem hv, by rw [e]; simp⟩
    have r1 := (hRC p D G L R gb S s N' M M o₁ o o k tt I₁ I J (inv θ) (𝟙 o.A) 1 u inferInstance
      inferInstance (UpperTheory.Gal.Int.Geo.integ_of_mem hu1)).2 r0 hIJ
    have r2 := (hRC p D G L R gb S s N' M N o₁ o o₂ k tt I₁ J J₂ (inv θ ≫ 𝟙 o.A) (θ ≫ χ) (u * 1) h
      inferInstance inferInstance hint).2 r1 hr₂
    have r3 := (hRC p D G L R gb S s N' N N o₁ o₂ o₂ k tt I₁ J₂ J' ((inv θ ≫ 𝟙 o.A) ≫ (θ ≫ χ))
      (𝟙 o₂.A) (h * (u * 1)) (h * u⁻¹ * h⁻¹) inferInstance inferInstance
      (UpperTheory.Gal.Int.Geo.integ_of_mem hu'1)).2 r2 hJJ'
    have e1 : ((inv θ ≫ 𝟙 o.A) ≫ (θ ≫ χ)) ≫ 𝟙 o₂.A = χ := by simp
    have e2 : h * u⁻¹ * h⁻¹ * (h * (u * 1)) = h := by group
    rw [e1, e2] at r3
    exact ⟨I₁, J', hI₁, hJ', r3⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransComp :
    MultBasic → RelComp → TateDiff → TateTwist → TransComp := by
  intro hMB hRC hTD hTT p _ D G L R _ _ gb S s N₁ N₂ N₃ o₁ o₂ o₃ ψ₁ ψ₂ h₁ h₂ hI hA t1 t2
  obtain ⟨m1, a1, ⟨ψ₁', d₁, m1', a1', e1, e1', cp1⟩, ⟨c₁, cc1, ⟨iso1⟩, hm1⟩, g1⟩ := t1
  obtain ⟨m2, a2, ⟨ψ₂', d₂, m2', a2', e2, e2', cp2⟩, ⟨c₂, cc2, ⟨iso2⟩, hm2⟩, g2⟩ := t2
  haveI := m1
  haveI := m2
  haveI := m1'
  haveI := m2'
  refine ⟨inferInstance, ?_, ⟨ψ₂' ≫ ψ₁', d₁ * d₂, inferInstance, ?_, ?_, ?_, Nat.Coprime.mul cp1 cp2⟩,
    ⟨c₂ * c₁, Nat.Coprime.mul cc2 cc1, ⟨?_⟩, ?_⟩, ?_⟩
  · intro c
    rw [← Category.assoc, a1 c, Category.assoc, a2 c, Category.assoc]
  · intro c
    rw [← Category.assoc, a2' c, Category.assoc, a1' c, Category.assoc]
  · rw [Category.assoc, ← Category.assoc ψ₂, e2, MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, e1, pow_mul]
  · rw [Category.assoc, ← Category.assoc ψ₁', e1', MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, e2', mul_comm, pow_mul]
  · have hlb : (Hecke.lbPow o₁.P (c₂ * c₁)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hpl : (o₃.P.pull (Hecke.sq2 (ψ₁ ≫ ψ₂))).IsLB := pull_isLB o₃.isLB _
    have hl1 : (Hecke.lbPow o₁.P c₁).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hl2 : (Hecke.lbPow o₂.P c₂).IsLB := LB.isLB_linComb o₂.isLB _ _
    have k1 := (GlobalTheory.CechPic.cls_eq_iff hl1 (pull_isLB o₂.isLB (Hecke.sq2 ψ₁))).2 iso1
    have k2 := (GlobalTheory.CechPic.cls_eq_iff hl2 (pull_isLB o₃.isLB (Hecke.sq2 ψ₂))).2 iso2
    rw [Hecke.Comp.cls_lbPow' o₁.isLB, GlobalTheory.CechPic.cls_pull o₂.isLB] at k1
    rw [Hecke.Comp.cls_lbPow' o₂.isLB, GlobalTheory.CechPic.cls_pull o₃.isLB] at k2
    apply (GlobalTheory.CechPic.cls_eq_iff hlb hpl).1
    rw [Hecke.Comp.cls_lbPow' o₁.isLB, GlobalTheory.CechPic.cls_pull o₃.isLB, Hecke.Comp.grpSchemeSquareProductMap_comp,
      GlobalTheory.CechPic.pull_comp, ← k2, map_nsmul, ← k1, smul_smul]
  · exact (hMB p).2.1 _ _ _ _ hm2 hm1
  · intro k _ _ t β hts
    obtain ⟨I1', I1'', ind1', ind1'', rel1⟩ := g1 k t β hts
    obtain ⟨I2', I2'', ind2', ind2'', rel2⟩ := g2 k t β hts
    obtain ⟨u, hu, ru⟩ := hTD p D G L R gb S s N₂ o₂ k t I1'' I2' ind1'' ind2'
    have hint : ∀ {M : ℕ} {g : G.GAf}, g ∈ L.KN M → Integ L g := fun hg =>
      UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hg)
    have rA := (hRC p D G L R gb S s N₁ N₂ N₂ o₁ o₂ o₂ k t I1' I1'' I2' ψ₁ (𝟙 _) h₁ u
      inferInstance inferInstance (hint hu)).2 rel1 ru
    have rB := (hRC p D G L R gb S s N₁ N₂ N₃ o₁ o₂ o₃ k t I1' I2' I2'' (ψ₁ ≫ 𝟙 _) ψ₂ (u * h₁) h₂
      inferInstance inferInstance hI).2 rA rel2
    have hu' : (h₂ * u * h₂⁻¹)⁻¹ ∈ L.KN N₃ := inv_mem (hA u hu)
    obtain ⟨J, indJ, rJ⟩ := hTT p D G L R gb S s N₃ o₃ k t I2'' ind2'' _ hu'
    have rC := (hRC p D G L R gb S s N₁ N₃ N₃ o₁ o₃ o₃ k t I1' I2'' J ((ψ₁ ≫ 𝟙 _) ≫ ψ₂) (𝟙 _)
      (h₂ * (u * h₁)) _ inferInstance inferInstance (hint hu')).2 rB rJ
    have hg : (h₂ * u * h₂⁻¹)⁻¹ * (h₂ * (u * h₁)) = h₂ * h₁ := by group
    rw [hg] at rC
    simp only [Category.comp_id] at rC
    exact ⟨I1', J, ind1', indJ, rC⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDesc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem epi_of_isGrpPullback_etale_surjective {S S' : Scheme} (c : S' ⟶ S) [Etale c] [Surjective c] (A : Over S)
    (A' : Over S') [GrpObj A] [GrpObj A'] (a : A'.left ⟶ A.left) (ha : IsGrpPullback A' A c a) : Epi a := by
  haveI : Etale a := MorphismProperty.of_isPullback (P := @Etale) ha.1.flip ‹Etale c›
  haveI : Surjective a := MorphismProperty.of_isPullback (P := @Surjective) ha.1.flip ‹Surjective c›
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective a

private theorem comp_eq_comp_of_over_left_comm {S S' : Scheme} {A B : Over S} {A' B' : Over S'}
    (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left) [Epi a] (u : A ⟶ A) (v : B ⟶ B) (u' : A' ⟶ A')
    (v' : B' ⟶ B') (f : A ⟶ B) (f' : A' ⟶ B')
    (hf : Over.Hom.left f' ≫ b = a ≫ Over.Hom.left f)
    (hu : Over.Hom.left u' ≫ a = a ≫ Over.Hom.left u)
    (hv : Over.Hom.left v' ≫ b = b ≫ Over.Hom.left v) (h' : u' ≫ f' = f' ≫ v') : u ≫ f = f ≫ v := by
  apply Over.OverMorphism.ext
  rw [← cancel_epi a]
  have e3 : Over.Hom.left u' ≫ Over.Hom.left f' = Over.Hom.left f' ≫ Over.Hom.left v' := by
    rw [← Over.comp_left, h', Over.comp_left]
  simp only [Over.comp_left]
  calc a ≫ Over.Hom.left u ≫ Over.Hom.left f
        = Over.Hom.left u' ≫ Over.Hom.left f' ≫ b := by rw [← reassoc_of% hu, ← hf]
    _ = Over.Hom.left f' ≫ Over.Hom.left v' ≫ b := by rw [reassoc_of% e3]
    _ = a ≫ Over.Hom.left f ≫ Over.Hom.left v := by rw [hv, reassoc_of% hf]

theorem UpperTheory.Gal.G3.pTransDesc :
    IsogFEt → TatePull → HomDesc → PolDesc → TransDesc := by
  intro hIsog hTate hHom hPol p _ D G L R _ _ gb S S' _ s s' c _ _ _ hcs N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' h hsq hT
  obtain ⟨hmon', hact', ⟨χ', d, hχmon', hχact', hd1', hd2', hdp⟩, ⟨e, hep, hpol', hint⟩, hgeo'⟩ := hT
  haveI : Epi m₁.φ := epi_of_isGrpPullback_etale_surjective c o₁.A o₁'.A m₁.φ m₁.cart
  haveI : Epi m₂.φ := epi_of_isGrpPullback_etale_surjective c o₂.A o₂'.A m₂.φ m₂.cart
  have hH := hHom S S' c o₁.A o₂.A o₁'.A o₂'.A o₁.ab o₂.ab o₂'.ab m₁.φ m₂.φ m₁.cart m₂.cart ψ ψ' hsq hmon'
  have hmon : IsMonHom ψ := hH.1
  have hdpos : 0 < d := Nat.pos_of_ne_zero (by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' ((Nat.coprime_zero_left p).mp hdp))
  obtain ⟨hfin, -, hsurj⟩ := hIsog R S' s' o₁'.A o₂'.A o₁'.ab o₂'.ab ψ' χ' d hdpos hmon' hχmon' hd1' hd2'
  obtain ⟨χ, hχsq, hd1, hd2⟩ := hH.2 χ' d hχmon' hsurj hfin hd1' hd2'
  have hχmon : IsMonHom χ := (hHom S S' c o₂.A o₁.A o₂'.A o₁'.A o₂.ab o₁.ab o₁'.ab m₂.φ m₁.φ
    m₂.cart m₁.cart χ χ' hχsq hχmon').1
  refine ⟨hmon, fun b => comp_eq_comp_of_over_left_comm m₁.φ m₂.φ _ _ _ _ ψ ψ' hsq (m₁.act b) (m₂.act b) (hact' b),
    ⟨χ, d, hχmon, fun b => comp_eq_comp_of_over_left_comm m₂.φ m₁.φ _ _ _ _ χ χ' hχsq (m₂.act b) (m₁.act b) (hχact' b),
      hd1, hd2, hdp⟩,
    ⟨e, hep, hPol D.toG R gb S S' s s' c N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' hmon hsq e hpol', hint⟩, ?_⟩
  intro k _ _ t β htβ
  obtain ⟨v, hv⟩ := ‹Surjective c›.surj (UpperTheory.Gal.TranscendenceTraces.pt t)
  obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds c k t v hv
  subst hz
  have hz' : z ≫ s' = spMap β := by
    rw [← hcs, ← Category.assoc]
    exact htβ
  obtain ⟨I₁', I₂', hI₁', hI₂', hiff'⟩ := hgeo' k z β hz'
  obtain ⟨-, hT1⟩ := hTate p D R gb S S' s s' c N₁ o₁ o₁' m₁ k z
  obtain ⟨-, hT2⟩ := hTate p D R gb S S' s s' c N₂ o₂ o₂' m₂ k z
  obtain ⟨I₁, hInd₁, hev₁⟩ := hT1 I₁'
  obtain ⟨I₂, hInd₂, hev₂⟩ := hT2 I₂'
  refine ⟨I₁, I₂, hInd₁ hI₁', hInd₂ hI₂', fun n hn hnp x y => ?_⟩
  have e1 : Over.Hom.left (I₁'.ev n x) ≫ m₁.φ = Over.Hom.left (I₁.ev n x) := hev₁ n x
  have e2 : Over.Hom.left (I₂'.ev n y) ≫ m₂.φ = Over.Hom.left (I₂.ev n y) := hev₂ n y
  rw [← hiff' n hn hnp x y]
  constructor
  · intro hxy
    apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hsq, ← Category.assoc, e1, ← Over.comp_left, hxy, e2]
    · rw [Over.w, Over.w]
  · intro hxy
    apply Over.OverMorphism.ext
    rw [Over.comp_left, ← e1, ← e2, Category.assoc, ← hsq, ← Category.assoc, ← Over.comp_left, hxy]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransIso :
    IsoPts → IsogFEt → TransIso := by
  intro IP IF p _ D G L R _ _ gb S s N' N o' o ψ u hu T
  obtain ⟨hmon, -, ⟨ψ', d, hψ', -, hd, hd', hdp⟩, -, tate⟩ := T
  haveI := hmon
  haveI := hψ'
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h0
    · rw [Nat.coprime_zero_left] at hdp
      exact absurd hdp (Fact.out : p.Prime).one_lt.ne'
    · exact h0
  obtain ⟨hfin, het, hsurj⟩ := IF R S s o'.A o.A o'.ab o.ab ψ ψ' d hd0 hmon hψ' hd hd'
  haveI := het
  haveI := hfin
  have hiso : IsIso ψ.left := by
    apply IP ψ.left
    intro Ω _ _ z
    obtain ⟨v, hv⟩ := hsurj.surj (UpperTheory.Gal.TranscendenceTraces.pt z)
    obtain ⟨y, hy, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds ψ.left Ω z v hv
    refine ⟨y, hy, fun y₂ hy₂ => ?_⟩
    let t : sp Ω ⟶ S := y ≫ o'.A.hom
    have ht2 : y₂ ≫ o'.A.hom = t := by
      rw [← Over.w ψ, ← Category.assoc, hy₂, ← hy, Category.assoc, Over.w ψ]
    let a₁ : Over.mk t ⟶ o'.A := Over.homMk y rfl
    let a₂ : Over.mk t ⟶ o'.A := Over.homMk y₂ ht2
    have hc : a₁ ≫ ψ = a₂ ≫ ψ := by
      ext
      simp [a₁, a₂, hy, hy₂]
    have ha : (a₂ * a₁⁻¹) ≫ ψ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, ← hc, mul_inv_cancel]
    have had : (a₂ * a₁⁻¹) ^ d = 1 := by
      have e : (a₂ * a₁⁻¹) ^ d = (a₂ * a₁⁻¹) ≫ ψ ≫ ψ' := by
        rw [hd, MonObj.comp_pow, Category.comp_id]
      rw [e, ← Category.assoc, ha, MonObj.one_comp]
    let β : R →+* Ω := (Spec.preimage (t ≫ s)).hom
    have hβ : t ≫ s = spMap β := by
      simp [β, spMap, Spec.map_preimage]
    obtain ⟨I', I'', -, -, hrel⟩ := tate Ω t β hβ
    obtain ⟨x, hx⟩ := (I'.onto d hd0 _).mp had
    have h0 : I'.ev d x ≫ ψ = I''.ev d 0 := by
      rw [hx, ha, HeckeRestrict.ev_zero]
    obtain ⟨w, hw, hxw⟩ := (hrel d hd0 hdp x 0).mp h0
    have hinv : u⁻¹ ∈ L.KN 1 := Subgroup.inv_mem _ hu
    have hdw : d • w = L.actG u (inAf D x) := by
      rw [hxw]
      simp [inAf]
    have hxa : inAf D x = d • L.actG u⁻¹ w := by
      rw [← map_nsmul, hdw, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    obtain ⟨z', hz'⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D x d hd0 hdp _
      (UpperTheory.Gal.Int.Geo.integ_of_mem hinv w hw) hxa
    have h1 : a₂ * a₁⁻¹ = 1 := by
      rw [← hx]
      exact (I'.ker d hd0 x).mpr ⟨z', hz'⟩
    have h2 : a₂ = a₁ := mul_inv_eq_one.mp h1
    exact congrArg Over.Hom.left h2
  have : IsIso ((Over.forget S).map ψ) := hiso
  exact isIso_of_reflects_iso ψ (Over.forget S)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

section

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {R : Type} [CommRing R] [Algebra ℚ R]
  {gb : GBase D.toG R} {S : Scheme.{0}} {s : S ⟶ Sp R}

private theorem comp_pow_overScheme_grpObj {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    f ≫ x ^ n = (f ≫ x) ^ n := MonObj.comp_pow x n f

private theorem pow_comp_monHom_overScheme_grpObj {A B T : Over S} [GrpObj A] [GrpObj B] (φ : A ⟶ B) [IsMonHom φ] (x : T ⟶ A) (n : ℕ) :
    (x ^ n) ≫ φ = (x ≫ φ) ^ n := MonObj.pow_comp x n φ

private theorem pt_transfer {N' N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {o : GObj gb N' s} {o₁ o₂ : GObj gb N s}
    {ψ₁ : o.A ⟶ o₁.A} {ψ₂ : o.A ⟶ o₂.A} {ψ' : o₁.A ⟶ o.A} {d : ℕ} (hψ' : IsMonHom ψ')
    (hd : ψ₁ ≫ ψ' = (𝟙 o.A) ^ d) (hdp : d.Coprime p) {h : G.GAf} {k : Type} [Field k] {t : Sp k ⟶ S}
    (I : UpperTheory.Gal.Int.Geo.TIso o t) (J₁ : UpperTheory.Gal.Int.Geo.TIso o₁ t) (J₂ : UpperTheory.Gal.Int.Geo.TIso o₂ t)
    (H₁ : Rel L I J₁ ψ₁ h) (H₂ : Rel L I J₂ ψ₂ h) (a : Over.mk t ⟶ o.A) (y : D.La)
    (ha : a ≫ ψ₁ = J₁.ev N y) : a ≫ ψ₂ = J₂.ev N y := by
  haveI := hψ'
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h0
    · rw [Nat.coprime_zero_left] at hdp
      exact absurd hdp (Fact.out : p.Prime).one_lt.ne'
    · exact h0
  have hn : 0 < N * d := Nat.mul_pos hN hd0
  have hnp : (N * d).Coprime p := Nat.Coprime.mul hNp hdp
  have h1 : (a ≫ ψ₁) ^ N = 1 := by
    rw [ha]
    exact (J₁.onto N hN _).mpr ⟨y, rfl⟩
  have h2 : a ^ d = (a ≫ ψ₁) ≫ ψ' := by
    rw [Category.assoc, hd, comp_pow_overScheme_grpObj, Category.comp_id]
  have h3 : a ^ (N * d) = 1 := by
    rw [mul_comm, pow_mul, h2, ← pow_comp_monHom_overScheme_grpObj, h1, MonObj.one_comp]
  obtain ⟨x, hx⟩ := (I.onto (N * d) hn a).mp h3
  let y' : D.toG.La := y
  have hJ₁ : J₁.ev N y' = J₁.ev (N * d) (d • y') := by
    rw [HeckeRestrict.ev_nsmul, J₁.tower N d hN hd0]
  have hJ₂ : J₂.ev N y' = J₂.ev (N * d) (d • y') := by
    rw [HeckeRestrict.ev_nsmul, J₂.tower N d hN hd0]
  change a ≫ ψ₁ = J₁.ev N y' at ha
  change a ≫ ψ₂ = J₂.ev N y'
  rw [← hx] at ha ⊢
  rw [hJ₂]
  rw [hJ₁] at ha
  exact (H₂ (N * d) hn hnp x (d • y')).mpr ((H₁ (N * d) hn hnp x (d • y')).mp ha)

end

theorem UpperTheory.Gal.G3.pTransKer :
    RelComp → TateDiff → TateTwist → TransKer := by
  intro RC TD TT p _ D G L R _ _ gb S s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm T₁ T₂ k _ _ t
  let β : R →+* k := (Spec.preimage (t ≫ s)).hom
  have hβ : t ≫ s = spMap β := by
    simp [β, spMap, Spec.map_preimage]
  have key : ∀ (q₁ q₂ : GObj gb (↑N) s) (φ₁ : o.A ⟶ q₁.A) (φ₂ : o.A ⟶ q₂.A),
      IsTrans L h o q₁ φ₁ → IsTrans L h o q₂ φ₂ → ∀ (a : Over.mk t ⟶ o.A) (y : D.La),
      a ≫ φ₁ = toUnit (Over.mk t) ≫ q₁.eta y → a ≫ φ₂ = toUnit (Over.mk t) ≫ q₂.eta y := by
    intro q₁ q₂ φ₁ φ₂ U₁ U₂ a y ha
    obtain ⟨-, -, ⟨φ', d, hφ', -, hd, -, hdp⟩, -, tate₁⟩ := U₁
    obtain ⟨hmon₂, -, -, -, tate₂⟩ := U₂
    obtain ⟨I₁, J₁, hI₁, hJ₁, R₁⟩ := tate₁ k t β hβ
    obtain ⟨I₂, J₂, hI₂, hJ₂, R₂⟩ := tate₂ k t β hβ
    obtain ⟨u, hu, hR⟩ := TD p D G L R gb S s N' o k t I₁ I₂ hI₁ hI₂
    have hc₁ := (RC p D G L R gb S s (↑N') (↑N') (↑N) o o q₂ k t I₁ I₂ J₂ (𝟙 _) φ₂ u h
      inferInstance hmon₂ hint).2 hR R₂
    have hw : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hadm _ (Subgroup.inv_mem _ hu)
    obtain ⟨J₃, hJ₃, hR₃⟩ := TT p D G L R gb S s N q₂ k t J₂ hJ₂ _ hw
    have hwi : Integ L (h * u⁻¹ * h⁻¹) :=
      UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hw)
    have hc₂ := (RC p D G L R gb S s (↑N') (↑N) (↑N) o q₂ q₂ k t I₁ J₂ J₃ (𝟙 _ ≫ φ₂) (𝟙 _) (h * u) _
      inferInstance inferInstance hwi).2 hc₁ hR₃
    have hg : h * u⁻¹ * h⁻¹ * (h * u) = h := by group
    rw [hg, Category.id_comp, Category.comp_id] at hc₂
    have hN : 0 < (N : ℕ) := lt_of_lt_of_le (by norm_num) N.2.1
    rw [hJ₁ y] at ha
    rw [hJ₃ y]
    exact pt_transfer hN N.2.2 hφ' hd hdp I₁ J₁ J₃ R₁ hc₂ a y ha
  have hz : ∀ q : GObj gb (↑N) s, toUnit (Over.mk t) ≫ q.eta (0 : D.La) = 1 := by
    intro q
    rw [show q.eta (0 : D.La) = 1 from q.eta_zero, MonObj.comp_one]
  refine ⟨fun a => ⟨fun h1 => ?_, fun h2 => ?_⟩, fun a y => ⟨key o₁ o₂ ψ₁ ψ₂ T₁ T₂ a y, key o₂ o₁ ψ₂ ψ₁ T₂ T₁ a y⟩⟩
  · have := key o₁ o₂ ψ₁ ψ₂ T₁ T₂ a 0 (by rw [h1, hz])
    rwa [hz] at this
  · have := key o₂ o₁ ψ₂ ψ₁ T₂ T₁ a 0 (by rw [h2, hz])
    rwa [hz] at this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransOfMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem tiso_congr {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase D.toG R}
    {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k] {t t' : Sp k ⟶ S} (e : t = t')
    (I : UpperTheory.Gal.Int.Geo.TIso o t) (hI : Ind o I) :
    ∃ J : UpperTheory.Gal.Int.Geo.TIso o t', Ind o J ∧ ∀ n x, (J.ev n x).left = (I.ev n x).left := by
  subst e
  exact ⟨I, hI, fun _ _ => rfl⟩

private theorem lbIso_hecke_lbPow_one {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) : LBIso (Hecke.lbPow P 1) P := by
  have h1 : (Hecke.lbPow P 1).IsLB := LB.isLB_linComb hP _ _
  have h2 : (lbPow P 1).IsLB := GlobalTheory.isLB_lbPow hP 1
  have h3 : ((Hecke.lbPow P 1).pull (𝟙 X)).IsLB := pull_isLB h1 _
  exact LBIso.trans h1 h2 hP
    (LBIso.trans h1 h3 h2 (GlobalTheory.DescendedPrincipal.lbIso_pull_id h1).symm
      (GlobalTheory.BiextPairing.lbIso_lbPow_hecke hP 1).symm)
    (GlobalTheory.lbIso_lbPow_one hP)

theorem UpperTheory.Gal.G3.pTransOfMap :
    MultBasic → RelComp → TatePull → TransOfMap := by
  intro MB RC TP p _ D G L R _ _ gb S s N o o' m
  have hw : m.φ ≫ o'.A.hom = o.A.hom := by simpa using m.cart.1.w
  let θ : o.A ⟶ o'.A := Over.homMk m.φ hw
  have hθ : θ.left = m.φ := rfl
  refine ⟨θ, rfl, ?_⟩
  have hmon : IsMonHom θ :=
    GlobalTheory.AmpleRigid.isMonHom_of_mul_comp θ
      (fun T => GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id (T := T) θ m.cart)
  have hact : ∀ c, o.act.act c ≫ θ = θ ≫ o'.act.act c := by
    intro c
    ext
    simpa [θ] using m.act c
  haveI : IsIso m.φ := m.cart.1.isIso_fst_of_isIso
  haveI : IsIso θ := by
    have : IsIso ((Over.forget S).map θ) := by
      change IsIso m.φ
      infer_instance
    exact isIso_of_reflects_iso θ (Over.forget S)
  have hsq : Hecke.sq2 θ = m.φ₂ := by
    apply Hecke.ProdGalois.grpScheme_square_hom_ext_fst_snd
    · rw [Hecke.ProdGalois.grpSchemeSquareProductMap_comp_fst, m.sq.1, hθ]
    · rw [Hecke.ProdGalois.grpSchemeSquareProductMap_comp_snd, m.sq.2, hθ]
  have hmon' : IsMonHom (asIso θ).hom := hmon
  have hinvmon : IsMonHom (inv θ) := (inferInstance : IsMonHom (asIso θ).inv)
  refine ⟨hmon, hact, ⟨inv θ, 1, hinvmon, ?_, ?_, ?_, by simp⟩, ⟨1, by simp, ?_, ?_⟩, ?_⟩
  · intro c
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hact c, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · rw [pow_one]
    exact IsIso.hom_inv_id θ
  · rw [pow_one]
    exact IsIso.inv_hom_id θ
  · refine ⟨?_⟩
    rw [hsq]
    exact LBIso.trans (LB.isLB_linComb o.isLB _ _) o.isLB (pull_isLB o'.isLB _)
      (lbIso_hecke_lbPow_one o.isLB) m.pol
  · exact (MB p).2.2 D G L 1 (Subgroup.one_mem _)
  · intro k _ _ t β ht
    obtain ⟨I₁, hI₁⟩ := o.geom k t β ht
    obtain ⟨I₂, hind, hev⟩ := (TP p D R gb S S s s (𝟙 S) (↑N) o' o m k t).2 I₁
    obtain ⟨J, hJ, hJe⟩ := tiso_congr o' (Category.comp_id t) I₂ (hind hI₁)
    refine ⟨I₁, J, hI₁, hJ, ?_⟩
    intro n hn hcop x y
    have key : I₁.ev n x ≫ θ = J.ev n x := by
      ext
      exact (hev n x).trans (hJe n x).symm
    rw [key]
    have hint : Integ L 1 := by
      intro v hv
      simpa using hv
    have hR := (RC p D G L R gb S s (↑N) (↑N) (↑N) o' o' o' k t J J J (𝟙 _) (𝟙 _) 1 1
      inferInstance inferInstance hint).1 n hn hcop x y
    simpa using hR
end

