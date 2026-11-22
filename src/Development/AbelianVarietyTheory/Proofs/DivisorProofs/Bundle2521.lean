import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismIntegralMap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvAct

theorem exists_isGrpPullback_extend : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X' V : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X'], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → ∀ (ℓ : V ⟶ X') [IsOpenImmersion ℓ] [IsDominant ℓ] (σ : V ⟶ V) (σ' : X' ⟶ X'), σ ≫ ℓ = ℓ ≫ σ' → ∀ (G' : Over X') [GrpObj G'], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G' → ∀ (A : Over V) [GrpObj A] (κ : A.left ⟶ G'.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A G' ℓ κ → ∀ ν : A.left ⟶ A.left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A A σ ν → ∃ M : G'.left ⟶ G'.left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G' σ' M ∧ κ ≫ M = ν ≫ κ := by
  intro hext X' V _ hS ℓ _ _ σ σ' hσ G' _ hG A _ κ hκ ν hν
  have hGσ : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian ((Over.pullback σ').obj G') := IsSemiAbelian.pullback _ _ hG
  have h1 : IsGrpPullback A G' (ℓ ≫ σ') (ν ≫ κ) := (hν.comp hκ).congr hσ rfl
  have h2 := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor σ' ℓ h1
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  obtain ⟨e, ⟨he, he'⟩, -⟩ := hext.existsUnique_iso_of_isGrpPullback hS hG hGσ hκ h2 (Iso.refl A)
  haveI := he
  refine ⟨e.hom.left ≫ pullback.fst _ _, ?_, ?_⟩
  · exact ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G' σ')).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, ← he']
    exact pullback.lift_fst _ _ _

theorem eq_of_comp_eq_of_isGrpPullback {X' V : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X']
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X') (ℓ : V ⟶ X') [IsOpenImmersion ℓ] [IsDominant ℓ]
    (G' : Over X') [GrpObj G'] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G') (A : Over V) [GrpObj A]
    (κ : A.left ⟶ G'.left) (hκ : IsGrpPullback A G' ℓ κ) (f g : G'.left ⟶ G'.left)
    (h : f ≫ G'.hom = g ≫ G'.hom) (hfg : κ ≫ f = κ ≫ g) : f = g := by
  obtain ⟨_, _⟩ := GlobalTheory.Published.SemiAbelianHomExtension.quasiCompact_and_dominant hS ℓ
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G' hG
  have : IsSchemeTheoreticallyDominant κ := .of_isPullback hκ.1.flip
  exact GlobalTheory.ExtUnique.hom_ext_of_dominant G'.hom h κ hfg

theorem eqvAct_ext : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) → ∃ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m ∧ GlobalTheory.EqvAct.MovesEta TF Z ι ρ ℓ (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullψ TF Z φ) m := by
  intro hP E _ _ _ H Dw l Xo c TF Z hpq hA1 Γ _ ι ρ hact X' _ φ ℓ ρ' hN hproj hℓ hℓφ hρ
  have hA : l.A.Coprime l.M := by rw [hA1]; exact Nat.coprime_one_left _
  obtain ⟨n, hn, hη⟩ := GlobalTheory.T.exists_level_stabilizer_action hP E H Dw l Xo c TF Z hpq hA Γ ι ρ (GlobalTheory.T.interiorLevelAction_eq_restriction_levelMove_inv E H Dw l Xo c TF Z hpq hA Γ ι ρ hact)
  haveI := hℓ
  haveI : AlgebraicGeometry.IsNoetherian X' := isNoetherian_of_isProjOver hproj
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' := (isNormalScheme_iff_pred X').mp hN
  have hne : Nonempty (V₀ TF.Y Z) :=
    ⟨⟨genPt Z, (j_mem_barComp Z _).2 (CompSplitPfB.cspB_genPt_mem Z)⟩⟩
  haveI : IsDominant ℓ := ⟨ℓ.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hG' : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian (pullG TF Z φ) :=
    IsSemiAbelian.pullback _ _ TF.Y.t.semi
  have hcomp : j₀ TF.Y Z ≫ (barComp TF.Y Z).ι = ℓ ≫ φ ≫ (barComp TF.Y Z).ι := by
    rw [← Category.assoc, hℓφ]
  have hκ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (φ ≫ (barComp TF.Y Z).ι) ℓ
    ((isGrpPullback_pullψ TF Z (j₀ TF.Y Z)).congr hcomp rfl)
  obtain ⟨κ, hκ, hκψ⟩ : ∃ κ : (pullG TF Z (j₀ TF.Y Z)).left ⟶ (pullG TF Z φ).left,
      IsGrpPullback (pullG TF Z (j₀ TF.Y Z)) (pullG TF Z φ) ℓ κ ∧ κ ≫ pullψ TF Z φ = pullψ TF Z (j₀ TF.Y Z) :=
    ⟨_, hκ, pullback.lift_fst _ _ _⟩
  have hκw : κ ≫ (pullG TF Z φ).hom = (pullG TF Z (j₀ TF.Y Z)).hom ≫ ℓ := hκ.1.w

  have hM : ∀ γ, ∃ M : (pullG TF Z φ).left ⟶ (pullG TF Z φ).left,
      IsGrpPullback (pullG TF Z φ) (pullG TF Z φ) (ρ' γ).hom M ∧ κ ≫ M = n γ ≫ κ := fun γ =>
    exists_isGrpPullback_extend hP.p22 X' (V₀ TF.Y Z) hS ℓ (ρ γ).hom (ρ' γ).hom (hρ γ) (pullG TF Z φ) hG' (pullG TF Z (j₀ TF.Y Z)) κ hκ
      (n γ) (hn.1 γ)
  choose m hm hmκ using hM
  have huniq := eq_of_comp_eq_of_isGrpPullback hS ℓ (pullG TF Z φ) hG' (pullG TF Z (j₀ TF.Y Z)) κ hκ

  have hact' : ∀ a : 𝓞 E, κ ≫ ((pullAct TF Z φ).act a).left = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ := by
    intro a
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc]
      change κ ≫ (((pullAct TF Z φ).act a).left ≫ pullψ TF Z φ) = _ ≫ (κ ≫ pullψ TF Z φ)
      rw [pullAct_pullψ, ← Category.assoc, hκψ, pullAct_pullψ]
    · rw [Category.assoc, Category.assoc]
      change κ ≫ (((pullAct TF Z φ).act a).left ≫ (pullG TF Z φ).hom) = _ ≫ (κ ≫ (pullG TF Z φ).hom)
      rw [Over.w, hκw, ← Category.assoc, Over.w]
  refine ⟨m, ⟨hm, fun γ a => ?_, fun γ₁ γ₂ => ?_⟩, ?_⟩
  · refine huniq _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, Over.w, (hm γ).1.w, ← Category.assoc, Over.w]
    · calc κ ≫ ((pullAct TF Z φ).act a).left ≫ m γ
          = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ ≫ m γ := by rw [← Category.assoc, hact', Category.assoc]
        _ = ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ n γ ≫ κ := by rw [hmκ]
        _ = n γ ≫ ((pullAct TF Z (j₀ TF.Y Z)).act a).left ≫ κ := by
          rw [← Category.assoc, hn.2.1 γ a, Category.assoc]
        _ = n γ ≫ κ ≫ ((pullAct TF Z φ).act a).left := by rw [hact']
        _ = κ ≫ m γ ≫ ((pullAct TF Z φ).act a).left := by rw [← Category.assoc, ← hmκ, Category.assoc]
  · refine huniq _ _ ?_ ?_
    · rw [(hm _).1.w, Category.assoc, (hm γ₁).1.w, ← Category.assoc, (hm γ₂).1.w, Category.assoc, map_mul,
        Aut.Aut_mul_def]
      rfl
    · calc κ ≫ m (γ₁ * γ₂) = n (γ₁ * γ₂) ≫ κ := hmκ _
        _ = n γ₂ ≫ n γ₁ ≫ κ := by rw [hn.2.2, Category.assoc]
        _ = n γ₂ ≫ κ ≫ m γ₁ := by rw [hmκ]
        _ = κ ≫ m γ₂ ≫ m γ₁ := by rw [← Category.assoc, ← hmκ, Category.assoc]
  · intro γ a b hab w w' hw hw' hwb hwa
    have lift : ∀ v : V₀ TF.Y Z ⟶ (pullG TF Z φ).left, v ≫ (pullG TF Z φ).hom = ℓ →
        ∃ u : V₀ TF.Y Z ⟶ (pullG TF Z (j₀ TF.Y Z)).left, u ≫ (pullG TF Z (j₀ TF.Y Z)).hom = 𝟙 _ ∧
          u ≫ pullψ TF Z (j₀ TF.Y Z) = v ≫ pullψ TF Z φ ∧ u ≫ κ = v := by
      intro v hv
      have e : (v ≫ pullψ TF Z φ) ≫ TF.Y.t.G.hom = 𝟙 _ ≫ j₀ TF.Y Z ≫ (barComp TF.Y Z).ι := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (v ≫ (pullG TF Z φ).hom) ≫ _ = _
        rw [hv, Category.id_comp, hcomp]
      refine ⟨pullback.lift _ _ e, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _, ?_⟩
      apply pullback.hom_ext
      · rw [Category.assoc]
        change _ ≫ (κ ≫ pullψ TF Z φ) = v ≫ pullψ TF Z φ
        rw [hκψ]; exact pullback.lift_fst _ _ _
      · rw [Category.assoc]
        change _ ≫ (κ ≫ (pullG TF Z φ).hom) = v ≫ (pullG TF Z φ).hom
        rw [hκw, ← Category.assoc]
        change (pullback.lift _ _ e ≫ pullback.snd _ _) ≫ ℓ = _
        rw [pullback.lift_snd, Category.id_comp, hv]
    obtain ⟨u, hu1, hu2, hu3⟩ := lift w hw
    obtain ⟨u', hu1', hu2', hu3'⟩ := lift w' hw'
    have := hη γ a b hab u u' hu1 hu1' (by rw [hu2, hwb]) (by rw [hu2', hwa])
    rw [← hu3, ← hu3', Category.assoc, hmκ, ← Category.assoc, this, Category.assoc]

end GlobalTheory.EqvAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionInjectiveAtGeometricPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.TorsSpec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem etaSecL_injective_at (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : Sp Ω ⟶ V₀ TF.Y Z) (c c' : LevelMod Dw l)
    (h : x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ c') : c = c' := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ c'

  have h1 := congrArg (· ≫ GlobalTheory.EqvAct.pullψ TF Z φ) h
  simp only [Category.assoc, etaSecL_ψ] at h1
  set x' := x ≫ i₀ TF.Y Z with hx'
  have hsec : ∀ a : Dw.La, (TF.Y.oF.eta a).left ≫ TF.Y.oF.t.G.hom = (𝟙_ (Over _)).hom := fun a =>
    Over.w (TF.Y.oF.eta a)
  have h2 : x' ≫ (TF.Y.oF.eta b).left = x' ≫ (TF.Y.oF.eta b').left := by
    refine TF.Y.m.cart.1.hom_ext ?_ ?_
    · simpa [hx', Category.assoc] using h1
    · simp only [hx', Category.assoc, hsec]
  let T : Over (Xo.XF c) := Over.mk x'
  have h3 : CartesianMonoidalCategory.toUnit T ≫ TF.Y.oF.eta b = CartesianMonoidalCategory.toUnit T ≫ TF.Y.oF.eta b' := by
    ext
    simp only [Over.comp_left]
    exact h2

  obtain ⟨β, hβ⟩ : ∃ β : KA l →+* Ω, x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β :=
    let f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (KA l)) :=
      x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s
    ⟨(Spec.preimage f).hom, by simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage, f]⟩
  obtain ⟨-, I, -, -, hI⟩ := TF.Y.oF.geom Ω x' β hβ
  obtain ⟨d, hd⟩ : ∃ d : Dw.La, d = b - b' := ⟨_, rfl⟩
  have hmul : TF.Y.oF.eta b = TF.Y.oF.eta b' * TF.Y.oF.eta d := by
    rw [← TF.Y.oF.eta_add, hd, add_sub_cancel]
  have hd1 : CartesianMonoidalCategory.toUnit T ≫ TF.Y.oF.eta d = 1 := by
    rw [hmul, MonObj.comp_mul] at h3
    exact mul_left_cancel (h3.trans (mul_one _).symm)
  have h1top : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1top
  have hud : u • d ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul hu Submodule.mem_top
  have hvd : v • d ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mem_smul hv Submodule.mem_top
  have hsplit : d = u • d + v • d := by rw [← add_smul, huv, one_smul]
  have hev : TF.Y.oF.eta d = TF.Y.oF.eta (v • d) := by
    conv_lhs => rw [hsplit]
    rw [TF.Y.oF.eta_add, TF.Y.oF.eta_ker _ hud, one_mul]
  have hI1 : I.ev l.M (v • d) = 1 := (hI _ hvd).symm.trans (by rw [← hev]; exact hd1)
  obtain ⟨e, he⟩ := (I.ker l.M (by have := l.three_le; omega) (v • d)).1 hI1
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h0 := Ideal.mem_span_singleton_self ((l.M : ℕ) : 𝓞 E)
    rw [← l.prod] at h0
    exact (Ideal.mul_le_inf.trans inf_le_left :
      l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb) h0
  have hvd' : v • d ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [he, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hM Submodule.mem_top
  rw [Submodule.Quotient.eq, ← hd, hsplit]
  exact Submodule.add_mem _ hud hvd'

end GlobalTheory.TorsSpec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionSmulAtGeometricPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false
open CartesianMonoidalCategory MonObj
noncomputable section

namespace GlobalTheory.TorsSpec

theorem etaSecL_smul_geom {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) {X' : Scheme.{0}}
    (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (hℓ : ℓ ≫ φ = j₀ TF.Y Z) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V₀ TF.Y Z) (a : LevelMod Dw l)
    (r : 𝓞 E) (A B : Over.mk (x ≫ ℓ) ⟶ GlobalTheory.EqvAct.pullG TF Z φ) (hA : A.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ a)
    (hB : B.left = x ≫ GlobalTheory.TorsSpec.etaSecL TF Z φ ℓ hℓ (r • a)) : B = A ≫ (GlobalTheory.EqvAct.pullAct TF Z φ).act r := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  have key : x ≫ i₀ TF.Y Z ≫ (TF.Y.oF.eta (r • b)).left =
      x ≫ i₀ TF.Y Z ≫ (TF.Y.oF.eta b).left ≫ (TF.Y.oF.t.act.act r).left := by
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (show (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) from
      l.coprime ▸ Submodule.mem_top)
    have ev : ∀ d : Dw.La, TF.Y.oF.eta d = TF.Y.oF.eta (v • d) := fun d => by
      conv_lhs => rw [← one_smul (𝓞 E) d, ← huv, add_smul, TF.Y.oF.eta_add,
        TF.Y.oF.eta_ker _ (Submodule.smul_mem_smul hu Submodule.mem_top), _root_.one_mul]
    obtain ⟨-, I, -, -, hη⟩ := TF.Y.oF.geom Ω (x ≫ i₀ TF.Y Z)
      (Spec.preimage ((x ≫ i₀ TF.Y Z) ≫ (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s))).hom
      (Spec.map_preimage _).symm
    have e : toUnit (Over.mk (x ≫ i₀ TF.Y Z)) ≫ TF.Y.oF.eta (r • b) =
        (toUnit (Over.mk (x ≫ i₀ TF.Y Z)) ≫ TF.Y.oF.eta b) ≫ TF.Y.oF.t.act.act r := by
      rw [ev (r • b), ev b, hη _ (Submodule.smul_mem_smul hv Submodule.mem_top),
        hη _ (Submodule.smul_mem_smul hv Submodule.mem_top), smul_comm v r b, I.lin]
    have ht : (toUnit (Over.mk (x ≫ i₀ TF.Y Z))).left = x ≫ i₀ TF.Y Z := by
      simpa using Over.w (toUnit (Over.mk (x ≫ i₀ TF.Y Z)))
    have e' := congrArg (fun q => q.left) e
    simp only [Over.comp_left, ht] at e'
    simpa only [Category.assoc] using e'
  apply Over.OverMorphism.ext
  rw [hB, Over.comp_left, hA, ← Submodule.Quotient.mk_smul]
  apply pullback.hom_ext
  · have h1 := etaSecL_ψ TF Z φ ℓ hℓ b
    have h2 := etaSecL_ψ TF Z φ ℓ hℓ (r • b)
    simp only [Category.assoc]
    rw [GlobalTheory.EqvAct.pullAct_pullψ, reassoc_of% h1, h2, ← TF.Y.m.act r, reassoc_of% key]
  · have w1 := etaSecL_w TF Z φ ℓ hℓ (Submodule.Quotient.mk b)
    have w2 := etaSecL_w TF Z φ ℓ hℓ (Submodule.Quotient.mk (r • b))
    have w3 := Over.w ((GlobalTheory.EqvAct.pullAct TF Z φ).act r)
    simp only [Category.assoc]
    erw [w2, w3, w1]

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureGenericFibreSpreadsFgSubalgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelSpread

theorem exists_ring {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁)
    {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (κ : o₁ →+* o₂)
    (hR₁ : R₁.FG) (hfr : ∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) [FiniteDimensional Ω₁ Ω₂]
    (hκ : (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) :
    ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧
      ∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a := by
  obtain ⟨s, hs⟩ := hR₁
  let B := Module.finBasis Ω₁ Ω₂
  let T : Set Ω₂ := (algebraMap Ω₁ Ω₂) '' (s : Set Ω₁) ∪ Set.range B
  let R : Subalgebra o₂ Ω₂ := Algebra.adjoin o₂ T
  have hT : T.Finite := (s.finite_toSet.image _).union (Set.finite_range _)
  have mem : ∀ a ∈ R₁, algebraMap Ω₁ Ω₂ a ∈ R := by
    intro a ha
    rw [← hs] at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)
    | algebraMap r =>
      have := congrArg (fun f => f r) hκ
      simp only [RingHom.comp_apply] at this
      rw [← this]; exact R.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let h : R₁ →+* R := ((algebraMap Ω₁ Ω₂).comp R₁.val.toRingHom).codRestrict R (fun a => mem a a.2)
  refine ⟨R, h, Subalgebra.fg_def.2 ⟨T, hT, rfl⟩, ?_, fun a => rfl⟩
  let D : Ω₂ → Prop := fun x => ∃ a ∈ R, ∃ b ∈ R, x = a / b
  have Dmem : ∀ x ∈ R, D x := fun x hx => ⟨x, hx, 1, R.one_mem, (div_one x).symm⟩
  have Dadd : ∀ x y, D x → D y → D (x + y) := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    by_cases hb0 : b = 0
    · exact ⟨c, hc, d, hd, by simp [hb0]⟩
    by_cases hd0 : d = 0
    · exact ⟨a, ha, b, hb, by simp [hd0]⟩
    exact ⟨a * d + b * c, add_mem (mul_mem ha hd) (mul_mem hb hc), b * d, mul_mem hb hd, div_add_div _ _ hb0 hd0⟩
  have Dmul : ∀ x y, D x → D y → D (x * y) := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    exact ⟨a * c, mul_mem ha hc, b * d, mul_mem hb hd, div_mul_div_comm _ _ _ _⟩
  have Dbase : ∀ c : Ω₁, D (algebraMap Ω₁ Ω₂ c) := by
    intro c
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr c
    exact ⟨_, mem a ha, _, mem b hb, map_div₀ _ _ _⟩
  intro x
  rw [← B.sum_repr x]
  refine Finset.sum_induction _ D Dadd (Dmem 0 R.zero_mem) fun i _ => ?_
  rw [Algebra.smul_def]
  exact Dmul _ _ (Dbase _) (Dmem _ (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)))

theorem step {Ω : Type} [Field Ω] {A B : Type} [CommRing A] [CommRing B] (a : A →+* Ω) (b : B →+* Ω)
    (g : A →+* B) (hg : b.comp g = a) (Q : PolAV (Sp Ω)) (P : PolAV (Sp A)) (φ : Q.A.left ⟶ P.A.left)
    (hQ : IsGrpPullback Q.A P.A (spMap a) φ) (eQ : LBIso Q.L (P.L.pull φ)) :
    ∃ φ' : Q.A.left ⟶ (StrictPull.polPull P (spMap g)).A.left,
      φ' ≫ pullback.fst P.A.hom (spMap g) = φ ∧ φ' ≫ pullback.snd P.A.hom (spMap g) = Q.A.hom ≫ spMap b ∧
      IsGrpPullback Q.A (StrictPull.polPull P (spMap g)).A (spMap b) φ' ∧
      LBIso Q.L ((StrictPull.polPull P (spMap g)).L.pull φ') := by
  have e : spMap b ≫ spMap g = spMap a := by rw [← hg, ← Spec.map_comp]; rfl
  let φ' : Q.A.left ⟶ (StrictPull.polPull P (spMap g)).A.left :=
    pullback.lift φ (Q.A.hom ≫ spMap b) (by rw [hQ.1.w, Category.assoc, e])
  have h1 : φ' ≫ pullback.fst P.A.hom (spMap g) = φ := pullback.lift_fst _ _ _
  refine ⟨φ', h1, pullback.lift_snd _ _ _, IsGrpPullback.cancel (isGrpPullback_pullback P.A (spMap g)) (hQ.congr e.symm h1.symm)
    (pullback.lift_snd _ _ _), ?_⟩
  exact LBIso.trans Q.isLB (pull_isLB P.isLB _) (pull_isLB (StrictPull.polPull P (spMap g)).isLB _) eQ
    (GenSpread.lbIso_pull_pull P.isLB φ' h1.symm)

theorem stepBase {S₁ S : Scheme.{0}} (P₁ : PolAV S₁) (P : PolAV S) (t : S ⟶ S₁) (ψ : P.A.left ⟶ P₁.A.left)
    (hP : IsGrpPullback P.A P₁.A t ψ) (eP : LBIso P.L (P₁.L.pull ψ)) {S' : Scheme.{0}} (f : S' ⟶ S) :
    IsGrpPullback (StrictPull.polPull P f).A P₁.A (f ≫ t) (pullback.fst P.A.hom f ≫ ψ) ∧
      LBIso (StrictPull.polPull P f).L (P₁.L.pull (pullback.fst P.A.hom f ≫ ψ)) :=
  ⟨(isGrpPullback_pullback P.A f).comp hP,
    LBIso.trans (pull_isLB P.isLB _) (pull_isLB (pull_isLB P₁.isLB ψ) _) (pull_isLB P₁.isLB _)
      (GenSpread.lbIso_pullback eP _) (GenSpread.lbIso_pull_pull P₁.isLB _ rfl).symm⟩

theorem indep_cast {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} {n m K : ℕ} (h : n = m)
    (y : Fin m → (T ⟶ A))
    (H : ∀ c c' : Fin m → Fin K, linComb y (fun i => (c i : ℕ)) = linComb y (fun i => (c' i : ℕ)) → c = c') :
    ∀ c c' : Fin n → Fin K, linComb (fun i => y (Fin.cast h i)) (fun i => (c i : ℕ)) =
      linComb (fun i => y (Fin.cast h i)) (fun i => (c' i : ℕ)) → c = c' := by
  subst h; exact H

theorem level_spreads : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁) (P₁ : PolAV (Sp R₁)) {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra Ω₁ Ω₂] (κ : o₁ →+* o₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (K : ℕ) (ze : o₂ˣ), R₁.FG → (∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) → FiniteDimensional Ω₁ Ω₂ → (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) → IsUnit (K : o₂) → Q.g = P₁.g → IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp R₁.val.toRingHom)) φ → LBIso Q.L (P₁.L.pull φ) → Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze))) → ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R) (P : PolAV (Sp R)) (ψ : P.A.left ⟶ P₁.A.left), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a) ∧ P.g = P₁.g ∧ IsGrpPullback P.A P₁.A (spMap h) ψ ∧ LBIso P.L (P₁.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ((Units.map (algebraMap o₂ R : o₂ →* R)) ze))) := by
  intro o₁ Ω₁ _ _ _ R₁ P₁ o₂ Ω₂ _ _ _ hB _ κ Q φ K ze hR₁ hfr hfd hκ hK hg hQ eQ hlev
  obtain ⟨lev⟩ := hlev
  have := hB.ded
  obtain ⟨R₀, h₀, hR₀, hfr₀, hh₀⟩ := exists_ring R₁ κ hR₁ hfr hκ
  let a₁ : R₁ →+* Ω₂ := (algebraMap Ω₁ Ω₂).comp R₁.val.toRingHom
  have c₀ : (algebraMap R₀ Ω₂).comp h₀ = a₁ := RingHom.ext hh₀
  let P₀ := StrictPull.polPull P₁ (spMap h₀)
  obtain ⟨φ₀, -, -, hQ₀, eQ₀⟩ := step a₁ (algebraMap R₀ Ω₂) h₀ c₀ Q P₁ φ hQ eQ
  have hP₀ : IsGrpPullback P₀.A P₁.A (spMap h₀) (pullback.fst P₁.A.hom (spMap h₀)) := isGrpPullback_pullback P₁.A _
  have eP₀ : LBIso P₀.L (P₁.L.pull (pullback.fst P₁.A.hom (spMap h₀))) := lbIso_refl P₀.isLB
  have := GenSpread.isFractionRing_of_forall_div hfr₀
  have := GenSpread.isNoetherianRing_of_fg hR₀
  have := P₀.isAb.smooth
  have := P₀.isAb.proper

  choose b hb Hpt using fun i => GenSpread.exists_hom (𝟙 (Sp R₀)) P₀.A.hom (φ := spMap (algebraMap R₀ Ω₂))
    (p₀ := 𝟙 (Sp Ω₂)) (IsPullback.of_vert_isIso ⟨by simp⟩) ((lev.pt i).left ≫ φ₀)
    (by rw [Category.assoc, hQ₀.1.w, Over.w_assoc]; simp)
  obtain ⟨R₂, g₂, le₂, hR₂, c₂, u₂, -, -, -⟩ := GenSpread.exists_shrink hR₀ b hb hQ₀.1
  let P₂ := StrictPull.polPull P₀ (spMap g₂)
  obtain ⟨φ₂, hφ₂, w₂, hQ₂, eQ₂⟩ := step (algebraMap R₀ Ω₂) (algebraMap R₂ Ω₂) g₂ c₂ Q P₀ φ₀ hQ₀ eQ₀
  obtain ⟨hP₂, eP₂⟩ := stepBase P₁ P₀ _ _ hP₀ eP₀ (spMap g₂)
  have es₂ : spMap (algebraMap R₂ Ω₂) ≫ spMap g₂ = spMap (algebraMap R₀ Ω₂) := by
    rw [← c₂, ← Spec.map_comp]; rfl
  have pts : ∀ i, ∃ y : baseOver (Sp R₂) ⟶ P₂.A, (lev.pt i).left ≫ φ₂ = spMap (algebraMap R₂ Ω₂) ≫ y.left := by
    intro i
    obtain ⟨u, hu, hu'⟩ := Hpt i R₂ g₂ (u₂ i) (Sp R₂) (spMap g₂) (𝟙 _) (by simp)
    have q₂ := IsPullback.of_hasPullback P₀.A.hom (spMap g₂)
    refine ⟨Over.homMk (q₂.lift u (𝟙 _) (by simpa using hu)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((lev.pt i).left ≫ ·) hφ₂).trans ((hu' _ es₂).symm.trans
        ((congrArg (spMap (algebraMap R₂ Ω₂) ≫ ·) (q₂.lift_fst _ _ _)).symm.trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg ((lev.pt i).left ≫ ·) w₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ spMap (algebraMap R₂ Ω₂)) (Over.w (lev.pt i))).trans ((Category.id_comp _).trans
        ((Category.comp_id _).symm.trans ((congrArg (spMap (algebraMap R₂ Ω₂) ≫ ·) (q₂.lift_snd _ _ _)).symm.trans
        (Category.assoc _ _ _).symm))))))
  choose y hy using pts
  have hfr₂ : ∀ x : Ω₂, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₀ x
    exact ⟨a, le₂ ha, b, le₂ hb, e⟩
  have := GenSpread.isFractionRing_of_forall_div hfr₂
  have := GenSpread.isNoetherianRing_of_fg hR₂
  have := P₂.isAb.proper
  obtain ⟨d, hd, Hi⟩ := GlobalTheory.T.exists_pointIndependence_spread_to_geometricFibres R₂ Ω₂ P₂.A Q.A φ₂ inferInstance hQ₂ _ K y lev.pt hy fun c c' h => by
    refine lev.indep (AlgebraicClosure Ω₂) (spMap (algebraMap Ω₂ _)) c c' ?_
    rw [← GenSpread.comp_linComb, ← GenSpread.comp_linComb, h]
  obtain ⟨R₃, g₃, le₃, hR₃, c₃, u₃, -, -, -⟩ :=
    GenSpread.exists_shrink hR₂ (fun _ : PUnit => d) (fun _ => hd) hQ₂.1
  let P₃ := StrictPull.polPull P₂ (spMap g₃)
  obtain ⟨φ₃, hφ₃, w₃, hQ₃, eQ₃⟩ := step (algebraMap R₂ Ω₂) (algebraMap R₃ Ω₂) g₃ c₃ Q P₂ φ₂ hQ₂ eQ₂
  obtain ⟨hP₃, eP₃⟩ := stepBase P₁ P₂ _ _ hP₂ eP₂ (spMap g₃)
  have es₃ : spMap (algebraMap R₃ Ω₂) ≫ spMap g₃ = spMap (algebraMap R₂ Ω₂) := by
    rw [← c₃, ← Spec.map_comp]; rfl
  have q₃ := IsPullback.of_hasPullback P₂.A.hom (spMap g₃)
  let y' : Fin (2 * Q.g) → (baseOver (Sp R₃) ⟶ P₃.A) := fun i =>
    Over.homMk (q₃.lift (spMap g₃ ≫ (y i).left) (𝟙 _) (by simp)) (q₃.lift_snd _ _ _)
  have hy' : ∀ i, (y' i).left ≫ pullback.fst P₂.A.hom (spMap g₃) = spMap g₃ ≫ (y i).left := fun i =>
    q₃.lift_fst _ _ _
  have hy₃ : ∀ i, (lev.pt i).left ≫ φ₃ = spMap (algebraMap R₃ Ω₂) ≫ (y' i).left := by
    intro i
    refine q₃.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg ((lev.pt i).left ≫ ·) hφ₃).trans ((hy i).trans
        ((by rw [reassoc_of% es₃] : spMap (algebraMap R₂ Ω₂) ≫ (y i).left =
          spMap (algebraMap R₃ Ω₂) ≫ spMap g₃ ≫ (y i).left).trans
        ((congrArg (spMap (algebraMap R₃ Ω₂) ≫ ·) (hy' i)).symm.trans (Category.assoc _ _ _).symm))))
    · exact (Category.assoc _ _ _).trans ((congrArg ((lev.pt i).left ≫ ·) w₃).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ spMap (algebraMap R₃ Ω₂)) (Over.w (lev.pt i))).trans ((Category.id_comp _).trans
        ((Category.comp_id _).symm.trans ((congrArg (spMap (algebraMap R₃ Ω₂) ≫ ·) (q₃.lift_snd _ _ _)).symm.trans
        (Category.assoc _ _ _).symm))))))
  have Hi₃ := Hi R₃ g₃ (u₃ ⟨⟩) P₃.A (pullback.fst _ _) y' (isGrpPullback_pullback P₂.A (spMap g₃)) hy'
  have hfr₃ : ∀ x : Ω₂, ∃ a ∈ R₃, ∃ b ∈ R₃, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₂ x
    exact ⟨a, le₃ ha, b, le₃ hb, e⟩
  have := GenSpread.isFractionRing_of_forall_div hfr₃
  have := GenSpread.isNoetherianRing_of_fg hR₃
  have hgg : 2 * P₃.g = 2 * Q.g := congrArg (2 * ·) hg.symm
  obtain ⟨lev', -⟩ := GlobalTheory.T.isLevelStructure_of_generic_of_fibrewise_indep abelianSchemeLaws_all.1 R₃ Ω₂ P₃ Q φ₃ hQ₃ eQ₃ hg.symm K
    (Units.map (algebraMap o₂ R₃ : o₂ →* R₃) ze) (Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze)
    (by simpa using hK.map (algebraMap o₂ R₃)) rfl lev (fun i => y' (Fin.cast hgg i))
    (fun i₀ i hi => by obtain rfl : i₀ = Fin.cast hgg i := Fin.ext hi; exact hy₃ _)
    (fun F _ _ s c c' h => indep_cast hgg _ (Hi₃ F s) c c' h)
  have hh : ∀ a, (((g₃.comp (g₂.comp h₀)) a : R₃) : Ω₂) = algebraMap Ω₁ Ω₂ a := fun a =>
    (RingHom.congr_fun c₃ _).trans ((RingHom.congr_fun c₂ _).trans (hh₀ a))
  have hsp : spMap g₃ ≫ spMap g₂ ≫ spMap h₀ = spMap (g₃.comp (g₂.comp h₀)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  exact ⟨R₃, g₃.comp (g₂.comp h₀), P₃, _, hR₃, hfr₃, hh, rfl, hP₃.congr hsp rfl, eP₃, ⟨lev'⟩⟩

end GlobalTheory.LevelSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageCorrespondence
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RealMult.Obj

theorem lieCorr_of_isLieImage (P : GlobalTheory.Published.AbelianDeRham) {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left} (hX : X'.IsPullBy X (spMap σ) φ)
    (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) φ) {x : HdR X.A} {x' : HdR X'.A}
    (hx : m.Corr x x') {v : X.Lie} {v' : X'.Lie} (hv : IsLieImage x v.hom) (hv' : IsLieImage x' v'.hom) :
    Obj.LieCorr σ φ v v' := by
  letI : Algebra R R' := σ.toAlgebra
  obtain ⟨-, PH, PB, -, -⟩ := P
  have hφ : IsGrpPullback X'.A X.A (spMap (algebraMap R R')) φ := hX.grp
  obtain ⟨-, hF⟩ := PB R X.A _ X.ab X.dim R' X'.A φ hφ
  have hL := (PH R' X'.A _ X'.ab X'.dim).1
  have hc : (Chart.dualMapR σ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp σ := by
    ext r <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (spMap (Chart.dualMapR σ) ≫ v.hom.left) ≫ X.A.hom = (epsR R').hom ≫ spMap σ := by
    rw [Category.assoc, Over.w v.hom]
    change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← Cris.spMap_comp, ← Cris.spMap_comp, hc]
  let u : epsR R' ⟶ X'.A := Over.homMk (hφ.1.lift _ _ w) (hφ.1.lift_snd _ _ w)
  have hu : u.left ≫ φ = spMap (Chart.dualMapR σ) ≫ v.hom.left := hφ.1.lift_fst _ _ w
  have e : (GlobalTheory.Published.AbelianDeRham.bcMor hφ).Corr x x' := hx
  have hiu : IsLieImage x' u := IsLieImage.baseChange (hφ := hφ) hF hL e hu hv
  have : u = v'.hom := (hL.1 x').unique hiu hv'
  unfold Obj.LieCorr
  rw [← this]
  exact hu

end GlobalTheory.RealMult.Obj
end

