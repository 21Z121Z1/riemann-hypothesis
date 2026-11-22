import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0649
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0652
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0722
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0723
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitSmulDirectionStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeJet_split_smul_direction : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet k (split 𝔞 𝔟 x) κ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_split_smul_direction | exact GlobalTheory.HilbFam.jet_split_smul_direction | (intros; apply GlobalTheory.HilbFam.jet_split_smul_direction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationCompIsoLiftIff
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem schemeFil_comp_iso (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (σ : A₀ ⟶ B₀) [IsMonHom σ] [IsIso σ] (X : Over (Sp R)) (j : B₀.left ⟶ X.left)
    (wj : j ≫ X.hom = B₀.hom ≫ spMap π) (w : (σ.left ≫ j) ≫ X.hom = A₀.hom ≫ spMap π) (d : Crys κ (spMap π) A₀) :
    d ∈ schemeFil κ A₀ X (σ.left ≫ j) w ↔ push κ (spMap π) σ d ∈ schemeFil κ B₀ X j wj := by
  haveI : IsMonHom (inv σ) :=
    { one_hom := by rw [← cancel_mono σ]; simp
      mul_hom := by
        rw [← cancel_mono σ]
        simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, IsIso.inv_hom_id] }

  have mK : IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (RingHom.id R) (σ.left ≫ j) :=
    IsMor.of_dividedPowersZeroIdeal (s := X.hom ≫ 𝟙 _) κ (s' := A₀.hom ≫ spMap π) (σ := RingHom.id R) (φ := σ.left ≫ j)
      (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, w])
  have mJ : IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ (B₀.hom ≫ spMap π) (RingHom.id R) j :=
    IsMor.of_dividedPowersZeroIdeal (s := X.hom ≫ 𝟙 _) κ (s' := B₀.hom ≫ spMap π) (σ := RingHom.id R) (φ := j)
      (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, wj])
  have key : ∀ a, (homMor κ (spMap π) σ).isMor.pull1 (mJ.pull1 a) = mK.pull1 a := fun a ↦
    IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) rfl a
  have key' : ∀ a, (homMor κ (spMap π) (inv σ)).isMor.pull1 (mK.pull1 a) = mJ.pull1 a := fun a ↦
    IsMor.pullback1_comp _ _ _ (fun _ ↦ rfl) (by rw [← Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left,
      Category.id_comp]) a
  have back : ∀ c : prim κ (spMap π) A₀, primPull κ (spMap π) σ (primPull κ (spMap π) (inv σ) c) = c := fun c ↦ by
    refine Subtype.ext ?_
    change (homMor κ (spMap π) σ).isMor.pull1 ((homMor κ (spMap π) (inv σ)).isMor.pull1 c.1) = c.1
    rw [IsMor.pullback1_comp _ _ (IsMor.id κ (A₀.hom ≫ spMap π)) (fun _ ↦ rfl)
      (by rw [← Over.comp_left, IsIso.hom_inv_id, Over.id_left])]
    exact IsMor.pullCohomologyOne_id _ _
  simp only [schemeFil, primitiveCrystalHodgeLiftClasses, Submodule.mem_dualAnnihilator, Submodule.mem_comap, Submodule.mem_map,
    Submodule.subtype_apply, push_apply]
  constructor
  · rintro H c ⟨a, ha, e⟩
    refine H _ ⟨a, ha, ?_⟩
    change mK.pull1 a = _
    rw [← key, e]; rfl
  · rintro H c ⟨a, ha, e⟩
    have := H (primPull κ (spMap π) (inv σ) c) ⟨a, ha, ?_⟩
    · rwa [back] at this
    · change mJ.pull1 a = (homMor κ (spMap π) (inv σ)).isMor.pull1 c.1
      rw [← key', e]

end GlobalTheory.SqLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationMiddleEqReductionOfTop
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FilRed

theorem filtration_reduction : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _)) (F : Submodule R (HdR A)) (F₁ : Submodule R₁ (HdR A₁)),
      (∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y) →
      (∀ d₁, crysToDR κ₁ h₁ d₁ ∈ F₁ ↔ ∃ d, crysToDR κ h d ∈ F ∧ M.Corr d d₁) ∧
      ((∀ y : HdR A₁, y ∈ Fil A₁ ↔ ∃ x ∈ Fil A, (redMor h₂).Corr x y)) := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ hS g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h e hA hg M F F₁ hF
  have hπ : Function.Surjective π := hS.comp ▸ hS.surj₁.comp hS.surj
  have H := canonical_of_abelianDeRham P hS.nil hπ hS.ker
  have hb := H.crysToDR_bijective h hA hg
  have hs := (H g A₀ A i h hA hg).1.2
  have e' : i₁ ≫ i₂ = 𝟙 _ ≫ i := by rw [e, Category.id_comp]
  have key : ∀ d d₁, (redMor h₂).Corr (crysToDR κ h d) (crysToDR κ₁ h₁ d₁) ↔ M.Corr d d₁ := by
    intro d d₁
    refine ⟨fun H' c' ↦ ?_, fun H' ↦ crysToDR_corr κ h h₁ M (redMor h₂) e' H'⟩
    obtain ⟨c, rfl⟩ := hs c'
    have k := (liftMor κ h).comp M
    rw [GrpMor.pull_pull (liftMor κ h) M k (fun _ ↦ rfl) rfl c,
      ← GrpMor.pull_pull (redMor h₂) (liftMor κ₁ h₁) k (fun _ ↦ rfl) e' c]
    exact H' c
  refine ⟨fun d₁ ↦ ?_, (canonical_of_abelianDeRham P (isDPNilpotent_squareZero hJ) hS.surj hS.kerJ g A₁ A i₂ h₂ hA hg).2.2⟩
  rw [hF]
  constructor
  · rintro ⟨x, hx, c⟩
    obtain ⟨d, rfl⟩ := hb.2 x
    exact ⟨d, hx, (key d d₁).1 c⟩
  · rintro ⟨d, hd, c⟩
    exact ⟨_, hd, (key d d₁).2 c⟩

end GlobalTheory.FilRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationTensorLiftsIffProjections
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift.ProdFil

variable {R : Type} [CommRing R] {I : Ideal R}

theorem left_ext {B : Scheme.{0}} {X Y : Over B} {T : Scheme.{0}} (g h : T ⟶ (X ⊗ Y).left)
    (h1 : g ≫ (fst X Y).left = h ≫ (fst X Y).left) (h2 : g ≫ (snd X Y).left = h ≫ (snd X Y).left) :
    g = h := by
  have w : h ≫ (X ⊗ Y).hom = g ≫ (X ⊗ Y).hom := by
    rw [← Over.w (fst X Y), ← Category.assoc, ← Category.assoc, h1]
  have := CartesianMonoidalCategory.hom_ext (Over.homMk g rfl : Over.mk (g ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y)
    (Over.homMk h w) (Over.OverMorphism.ext (by simpa using h1)) (Over.OverMorphism.ext (by simpa using h2))
  exact congrArg (fun f => f.left) this

theorem primitive_pullback_mem_hodgeFiltration_of_monHom (κ : DividedPowers I) {S : Scheme.{0}} {t : S ⟶ Sp R} {A A' : Over S} [GrpObj A]
    [GrpObj A'] (f : A' ⟶ A) [IsMonHom f] {X X' : Over (Sp R)} {i : A.left ⟶ X.left} {i' : A'.left ⟶ X'.left}
    (w : i ≫ X.hom = A.hom ≫ t) (w' : i' ≫ X'.hom = A'.hom ≫ t) (m : X'.left ⟶ X.left) (hm : m ≫ X.hom = X'.hom)
    (e : f.left ≫ i = i' ≫ m) {c : prim κ t A} (hc : c ∈ primitiveCrystalHodgeLiftClasses κ A X i w) :
    primPull κ t f c ∈ primitiveCrystalHodgeLiftClasses κ A' X' i' w' := by
  obtain ⟨a, ha, hac⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hc)
  have hmor : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (X'.hom ≫ 𝟙 _) (RingHom.id R) m :=
    IsMor.of_over (dp0 R) (by rw [← Category.assoc, hm])
  refine Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨hmor.pull1 a, hmor.pullback1_mem_hodgeFiltration ha, ?_⟩)
  have hfi : IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ (A'.hom ≫ t) (RingHom.id R) (f.left ≫ i) :=
    IsMor.of_dividedPowersZeroIdeal κ (by rw [Cris.spMap_id, Category.comp_id, Category.comp_id, Category.assoc, w,
      ← Category.assoc, Over.w f])
  rw [IsMor.pullback1_comp _ _ hfi (fun _ ↦ rfl) e.symm]
  change _ = (homMor κ t f).isMor.pull1 c.1
  rw [show (c : Cris.H1 κ (A.hom ≫ t)) = _ from hac.symm]
  exact (IsMor.pullback1_comp _ _ hfi (fun _ ↦ rfl) rfl a).symm

theorem schemeFil_tensor_iff : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I) (π : R →+* R₀)
    (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (X Y : Over (Sp R)) (i : A₀.left ⟶ X.left) (j : B₀.left ⟶ Y.left)
    (wi : i ≫ X.hom = A₀.hom ≫ spMap π) (wj : j ≫ Y.hom = B₀.hom ≫ spMap π)
    (e : Sp R ⟶ X.left) (e' : Sp R ⟶ Y.left), e ≫ X.hom = 𝟙 _ → e' ≫ Y.hom = 𝟙 _ →
    (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ i = spMap π ≫ e → (1 : Over.mk (𝟙 (Sp R₀)) ⟶ B₀).left ≫ j = spMap π ≫ e' →
    ∀ (l : (A₀ ⊗ B₀).left ⟶ (X ⊗ Y).left), l ≫ (fst X Y).left = (fst A₀ B₀).left ≫ i → l ≫ (snd X Y).left = (snd A₀ B₀).left ≫ j →
    ∀ (wl : l ≫ (X ⊗ Y).hom = (A₀ ⊗ B₀).hom ≫ spMap π) (d : Crys κ (spMap π) (A₀ ⊗ B₀)),
    d ∈ schemeFil κ (A₀ ⊗ B₀) (X ⊗ Y) l wl ↔
      push κ (spMap π) (fst A₀ B₀) d ∈ schemeFil κ A₀ X i wi ∧ push κ (spMap π) (snd A₀ B₀) d ∈ schemeFil κ B₀ Y j wj := by
  intro R R₀ _ _ I κ π A₀ B₀ _ _ X Y i j wi wj e e' he he' h1 h1' l hl1 hl2 wl d
  have hAB : IsMonHom (1 : A₀ ⟶ B₀) := inferInstanceAs (IsMonHom (toUnit A₀ ≫ η[B₀]))
  have hBA : IsMonHom (1 : B₀ ⟶ A₀) := inferInstanceAs (IsMonHom (toUnit B₀ ≫ η[A₀]))
  have one_left : ∀ (C D : Over (Sp R₀)) [GrpObj C] [GrpObj D],
      (1 : C ⟶ D).left = C.hom ≫ (1 : Over.mk (𝟙 (Sp R₀)) ⟶ D).left := by
    intro C D _ _
    have : (1 : C ⟶ D) = (Over.homMk C.hom (by simp) : C ⟶ Over.mk (𝟙 (Sp R₀))) ≫ 1 := by simp
    rw [this]; rfl
  constructor
  · intro H
    constructor
    · refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_
      rw [push_apply]
      exact (Submodule.mem_dualAnnihilator _).1 H _
        (primitive_pullback_mem_hodgeFiltration_of_monHom κ (fst A₀ B₀) wi wl (fst X Y).left (Over.w _) hl1.symm hc)
    · refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_
      rw [push_apply]
      exact (Submodule.mem_dualAnnihilator _).1 H _
        (primitive_pullback_mem_hodgeFiltration_of_monHom κ (snd A₀ B₀) wj wl (snd X Y).left (Over.w _) hl2.symm hc)
  · rintro ⟨H1, H2⟩
    refine (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_
    let ι₁ : A₀ ⟶ A₀ ⊗ B₀ := lift (𝟙 A₀) 1
    let ι₂ : B₀ ⟶ A₀ ⊗ B₀ := lift 1 (𝟙 B₀)
    have hmul : (fst A₀ B₀ ≫ ι₁) * (snd A₀ B₀ ≫ ι₂) = 𝟙 _ := by
      ext
      · rw [MonObj.mul_comp]; simp [ι₁, ι₂]
      · rw [MonObj.mul_comp]; simp [ι₁, ι₂]
    have hdec : c = primPull κ _ (fst A₀ B₀) (primPull κ _ ι₁ c) + primPull κ _ (snd A₀ B₀) (primPull κ _ ι₂ c) := by
      apply Subtype.ext
      have := c.2 (A₀ ⊗ B₀) (fst A₀ B₀ ≫ ι₁) (snd A₀ B₀ ≫ ι₂)
      rw [hmul, ← pullOver_pullOver, ← pullOver_pullOver] at this
      have hid : pullOver κ (spMap π) (𝟙 (A₀ ⊗ B₀)) (c : Cris.H1 κ ((A₀ ⊗ B₀).hom ≫ spMap π)) = c :=
        IsMor.pullCohomologyOne_id _ _
      rw [← hid, this]; rfl

    let mX : X ⟶ X ⊗ Y := lift (𝟙 X) (Over.homMk (X.hom ≫ e') (by simp [he']))
    let mY : Y ⟶ X ⊗ Y := lift (Over.homMk (Y.hom ≫ e) (by simp [he])) (𝟙 Y)
    have eX : ι₁.left ≫ l = i ≫ mX.left := by
      apply left_ext
      · rw [Category.assoc, hl1, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp [ι₁, mX]
      · rw [Category.assoc, hl2, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp only [ι₁, mX, lift_snd, Over.homMk_left]
        rw [one_left, Category.assoc, h1', ← Category.assoc, ← wi, Category.assoc]
    have eY : ι₂.left ≫ l = j ≫ mY.left := by
      apply left_ext
      · rw [Category.assoc, hl1, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp only [ι₂, mY, lift_fst, Over.homMk_left]
        rw [one_left, Category.assoc, h1, ← Category.assoc, ← wj, Category.assoc]
      · rw [Category.assoc, hl2, Category.assoc, ← Over.comp_left, ← Category.assoc, ← Over.comp_left]
        simp [ι₂, mY]
    have k1 := primitive_pullback_mem_hodgeFiltration_of_monHom κ ι₁ wl wi mX.left (Over.w _) eX hc
    have k2 := primitive_pullback_mem_hodgeFiltration_of_monHom κ ι₂ wl wj mY.left (Over.w _) eY hc
    rw [hdec, map_add, ← push_apply κ _ (fst A₀ B₀) d, ← push_apply κ _ (snd A₀ B₀) d, (Submodule.mem_dualAnnihilator _).1 H1 _ k1,
      (Submodule.mem_dualAnnihilator _).1 H2 _ k2, add_zero]

end GlobalTheory.SqLift.ProdFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparatedStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicPoint_ext_of_isSeparated : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}, X.IsSeparated → ∀ x x' : Sp (Hol W) ⟶ X, (∀ (p : E) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = spMap (Hol.ev p hp).toRingHom ≫ x') → x = x' := by
  first | exact @GlobalTheory.AnPer.point_hol_ext_of_isSeparated | exact GlobalTheory.AnPer.point_hol_ext_of_isSeparated | (intros; apply GlobalTheory.AnPer.point_hol_ext_of_isSeparated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCocycleAdditiveLawReductionCoboundary
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option maxHeartbeats 800000

namespace GlobalTheory.LazardHomog

theorem lift_addLaw (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (d : ℕ) :
    (fun i => Katz.lift p (addLaw k d i)) = addLaw (Fr p k) d := by
  funext i
  ext α
  rw [coeff_lift]
  simp only [addLaw, map_add, coeff_X]
  have hne : (Finsupp.single (Sum.inl i) 1 : Fin d ⊕ Fin d →₀ ℕ) ≠ Finsupp.single (Sum.inr i) 1 := by
    rw [Ne, Finsupp.single_left_inj one_ne_zero]; simp
  by_cases h1 : α = Finsupp.single (Sum.inl i) 1
  · simp [h1, hne]
  · by_cases h2 : α = Finsupp.single (Sum.inr i) 1
    · simp [h2, hne.symm]
    · simp [h1, h2]

theorem homogCoc_red_cob : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d N : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) k), 2 ≤ N → IsCoc (addLaw k d) c → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree ≠ N → coeff γ c = 0) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ Red p (cob1 (addLaw (Fr p k) d) h) c := by
  intro p _ k _ _ _ d N c hN hc hhom
  have hconst : ∀ (R : Type) [CommRing R] (i : Fin d), constantCoeff (addLaw R d i) = 0 := by
    intro R _ i; simp [addLaw]
  have hc0 : constantCoeff c = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact hhom 0 (by simp; omega)
  obtain ⟨b, hb⟩ := GlobalTheory.T.symmetricCocycle_additive_eq_coboundary_add k d c hc hc0
  set cm : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k := fun m => at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) k)) (Pi.single m (X (Sum.inr m))) with hcm
  set bN := homogeneousComponent N b with hbN
  have hbNc : ∀ α, coeff α bN = if α.degree = N then coeff α b else 0 := fun α =>
    coeff_homogeneousComponent N α b

  have hdec : c = cob1 (addLaw k d) bN + ∑ m, cm m := by
    ext γ
    by_cases hγ : γ.degree = N
    · have e1 : coeff γ (cob1 (addLaw k d) b) = coeff γ (cob1 (addLaw k d) bN) := by
        have := formalCoboundary_add (hconst k) bN (b - bN)
        rw [add_sub_cancel] at this
        rw [this, map_add, GlobalTheory.T.coeff_coboundaryOne_additive_eq_zero_of_degree k d N (b - bN) (fun α hα => by
          rw [map_sub, hbNc, if_pos hα, sub_self]) γ hγ, add_zero]
      conv_lhs => rw [hb]
      rw [map_add, map_add, e1]
    · rw [hhom γ hγ, map_add, map_sum, (GlobalTheory.T.additive_formal_group_coboundary_homogeneous k d N).1 bN (fun α hα => by
        rw [hbNc, if_neg hα]) γ hγ, zero_add]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      simp only [cm]
      rw [GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_single_pair]
      split_ifs <;> simp [hhom γ hγ]

  set a : Fin d → ℕ → k := fun m n => coeff (Finsupp.single (Sum.inl m) n + Finsupp.single (Sum.inr m) (N - n)) c with ha
  have hsym : ∀ m n, n ≤ N → a m n = a m (N - n) := by
    intro m n hn
    simp only [ha]
    conv_lhs => rw [← hc.2]
    rw [(GlobalTheory.T.additive_formal_group_coboundary_homogeneous k d N).2.2.1, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single, Nat.sub_sub_self hn, add_comm]
    rfl
  have hrel : ∀ m i j l, 0 < i → 0 < j → 0 < l → i + j + l = N → a m (i + j) * ((i + j).choose i : k) = a m i * ((j + l).choose j : k) := by
    intro m i j l hi hj hl hs
    simp only [ha]
    have e1 : N - (i + j) = l := by omega
    have e2 : N - i = j + l := by omega
    rw [e1, e2]
    exact (GlobalTheory.T.additiveTwoCocycle_coeff_relations_one_pair k d c hc.1 m).2 i j l hi hj hl
  have ht := fun m => GlobalTheory.T.lazard_one_variable_exists_witt_lift p k N (a m) hN (hsym m) (hrel m)
  choose t ht using ht
  have hzero : ∀ m, coeff (Finsupp.single (Sum.inl m) N) c = 0 :=
    fun m => (GlobalTheory.T.additiveTwoCocycle_coeff_relations_one_pair k d c hc.1 m).1 N (by omega)
  have hzero' : ∀ m, coeff (Finsupp.single (Sum.inr m) N) c = 0 := by
    intro m
    have := hsym m 0 (Nat.zero_le _)
    simp only [ha, Finsupp.single_zero, zero_add, Nat.sub_zero, Nat.sub_self, add_zero] at this
    rw [this, hzero]
  have hconstFr := hconst (Fr p k)
  have redSum : ∀ (s : Finset (Fin d)) (F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k))
      (G : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ m ∈ s, Red p (F m) (G m)) →
      Red p (∑ m ∈ s, F m) (∑ m ∈ s, G m) := by
    intro s F G hFG
    induction s using Finset.induction_on with
    | empty => intro α; exact ⟨0, by simp⟩
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      exact ((GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k _).2.2.2.1 _ _ _ _ (hFG x (Finset.mem_insert_self _ _))
        (ih fun m hm => hFG m (Finset.mem_insert_of_mem hm))).1
  have cob0 : cob1 (addLaw (Fr p k) d) 0 = 0 := by
    have := formalCoboundary_smul hconstFr (0 : Fr p k) 0
    simpa using this
  have cobSum : ∀ (s : Finset (Fin d)) (F : Fin d → MvPowerSeries (Fin d) (Fr p k)),
      cob1 (addLaw (Fr p k) d) (∑ m ∈ s, F m) = ∑ m ∈ s, cob1 (addLaw (Fr p k) d) (F m) := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simpa using cob0
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, formalCoboundary_add hconstFr, ih]
  have redm : ∀ m, Red p (t m • cob1 (addLaw (Fr p k) d) (X m ^ N)) (cm m) := by
    intro m α
    rw [GlobalTheory.T.cob1_addLaw_X_pow_eq_sum_choose (Fr p k) d N m (by omega)]
    simp only [cm]
    rw [GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_single_pair, map_smul, map_sum]
    simp only [coeff_monomial, smul_eq_mul]
    set i := α (Sum.inl m) with hi
    set j := α (Sum.inr m) with hj
    have key : ∀ i', α = Finsupp.single (Sum.inl m) i' + Finsupp.single (Sum.inr m) (N - i') →
        i = i' ∧ j = N - i' := by
      intro i' h
      constructor
      · rw [hi, h]; simp
      · rw [hj, h]; simp
    by_cases hs : α = Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) j
    · rw [if_pos hs]
      by_cases hin : 0 < i ∧ i < N ∧ j = N - i
      · obtain ⟨w, hw1, hw2⟩ := ht m i hin.1 hin.2.1
        refine ⟨w, ?_, ?_⟩
        · rw [Finset.sum_eq_single_of_mem i (Finset.mem_Ioo.2 ⟨hin.1, hin.2.1⟩)]
          · rw [if_pos (hs.trans (by rw [hin.2.2])), hw1]
          · intro i' _ hne; rw [if_neg]; intro h; exact hne (key i' h).1.symm
        · rw [hw2]; simp only [ha]; rw [← hin.2.2, ← hs]
      · refine ⟨0, ?_, ?_⟩
        · rw [Finset.sum_eq_zero, mul_zero, map_zero]
          intro i' hi'; rw [if_neg]; intro h
          obtain ⟨e1, e2⟩ := key i' h
          rw [Finset.mem_Ioo] at hi'
          exact hin ⟨e1 ▸ hi'.1, e1 ▸ hi'.2, e1 ▸ e2⟩
        · rw [map_zero]
          by_cases hd : i + j = N
          · have : i = 0 ∨ i = N := by omega
            rcases this with h0 | h0
            · have : α = Finsupp.single (Sum.inr m) N := by
                rw [hs, h0, Finsupp.single_zero, zero_add]; congr 1; omega
              rw [this, hzero']
            · have : α = Finsupp.single (Sum.inl m) N := by
                rw [hs, h0, (by omega : j = 0), Finsupp.single_zero, add_zero]
              rw [this, hzero]
          · refine (hhom α ?_).symm
            rw [hs, map_add, Finsupp.degree_single, Finsupp.degree_single]; exact hd
    · rw [if_neg hs]
      refine ⟨0, ?_, by simp⟩
      rw [Finset.sum_eq_zero, mul_zero, map_zero]
      intro i' _; rw [if_neg]; intro h
      apply hs; obtain ⟨e1, e2⟩ := key i' h; rw [e1, e2]; exact h
  refine ⟨Katz.lift p bN + ∑ m, t m • (X m ^ N : MvPowerSeries (Fin d) (Fr p k)), ?_, ?_⟩
  · intro α hα
    rw [map_add, map_sum, coeff_lift, hbNc, if_neg hα, WittVector.teichmuller_zero, map_zero,
      zero_add]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [map_smul, coeff_X_pow, if_neg, smul_zero]
    intro h; apply hα; rw [h, Finsupp.degree_single]
  · have h1 : Red p (cob1 (addLaw (Fr p k) d) (Katz.lift p bN)) (cob1 (addLaw k d) bN) := by
      rw [← lift_addLaw p k d]
      exact ((GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d (addLaw k d) (hconst k)).2.1 _ _
        ((GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k _).2.2.1 bN)).1
    have h2 : Red p (∑ m, cob1 (addLaw (Fr p k) d) (t m • (X m ^ N : MvPowerSeries (Fin d) (Fr p k))))
        (∑ m, cm m) := by
      refine redSum _ _ _ fun m _ => ?_
      rw [formalCoboundary_smul hconstFr]; exact redm m
    have := ((GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k _).2.2.2.1 _ _ _ _ h1 h2).1
    rw [formalCoboundary_add hconstFr, cobSum]
    rwa [← hdec] at this

end GlobalTheory.LazardHomog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HormanderEstimateOnBallConstLeviBoundStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hormander_estimate_on_ball_const_levi_bound : ∀ (n : ℕ) (c : V n) (r t : ℝ) (φ : V n → ℝ) (F0 : V n → ℂ), 0 < t → ContDiffOn ℝ ∞ φ (ball c r) → ContDiffOn ℝ ∞ F0 (ball c r) → (∀ v ∈ ball c r, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n (fun w => (φ w : ℂ)) v ξ).re) → ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball c r) ∧ ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - F v‖ ^ 2 * Real.exp (-φ v)) ≤ ENNReal.ofReal t⁻¹ * ∫⁻ v in ball c r, ENNReal.ofReal ((∑ j, ‖wdb n j F0 v‖ ^ 2) * Real.exp (-φ v)) := by
  first | exact @GlobalTheory.HormanderBall.hormander_ball | exact GlobalTheory.HormanderBall.hormander_ball | (intros; apply GlobalTheory.HormanderBall.hormander_ball <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2GeneratedByCupsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyper_h2_generated_by_cups : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) → WedgeO F → ∀ z : Hyp2 F, ∃ (n : ℕ) (a b : Fin n → Hyp1 F), z = ∑ k, cupHyp F (a k) (b k) := by
  first | exact @GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp | exact GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp | (intros; apply GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  first | exact @GlobalTheory.FinProjComplete.isAdicComplete_span_natCast | exact GlobalTheory.FinProjComplete.isAdicComplete_span_natCast | (intros; apply GlobalTheory.FinProjComplete.isAdicComplete_span_natCast <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacterHarishChandraProductCuspidalGLOfRegul
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

open Polynomial SemidirectProduct in
open scoped Classical in

theorem _root_.GlobalTheory.Shin.isChar_J_of_reg : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ _root_.GlobalTheory.Shin.Reg (Nat.card F) p.1 p.2) → ∀ n, n = _root_.GlobalTheory.Shin.deg L → _root_.GlobalTheory.BI.IsChar ℂ ℂ (_root_.GlobalTheory.Shin.J θ L n) := by
  intro F _ _ θ hθ L
  induction L with
  | nil =>
    intro _ n _
    rw [_root_.GlobalTheory.Shin.J_nil]
    exact _root_.GlobalTheory.BI.isChar_one ℂ ℂ _
  | cons p L ih =>
    intro hL n hn
    rw [_root_.GlobalTheory.Shin.J_cons]
    have hp := hL p List.mem_cons_self
    refine _root_.GlobalTheory.Shin.HCChar.hc_isChar F _ _ n ?_ _ _
      (_root_.GlobalTheory.Shin.isChar_cusp_and_norm_of_reg F θ hθ p.1 p.2 hp.1 hp.2).1
      (ih (fun q hq => hL q (List.mem_cons_of_mem p hq)) _ rfl)
    rw [hn]
    simp [_root_.GlobalTheory.Shin.deg]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCrystallineChernOnAnalyticThickeningsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrystallineChern_on_analytic_thickenings : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X) (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ z : SecondDeRham s, IsChern (dp0 B) s M z → ∃ (i : K.Obj → M.ι) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) ∧ (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) ∧ (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ ((show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) ∧ r.coef.pull2 z = GlobalTheory.CatCoh.H2.mk K.Oc ℓ := by
  first | exact @GlobalTheory.AnPer.isChern_real | exact GlobalTheory.AnPer.isChern_real | (intros; apply GlobalTheory.AnPer.isChern_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIdentityComponentsSmoothGroupSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → IsOpen {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.IdCompOpen.isOpen_identityComponent | exact GlobalTheory.IdCompOpen.isOpen_identityComponent | (intros; apply GlobalTheory.IdCompOpen.isOpen_identityComponent <;> assumption)
end

