import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0144
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2494
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelLevelStructureMumfordFamilyTautologi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem lbIso_pull_both {X X' Y Z : Scheme.{0}} {L : LB X} {M : LB X'} {a : Y ⟶ X} {b : Y ⟶ X'}
    (h : LBIso (L.pull a) (M.pull b)) (j : Z ⟶ Y) {a' : Z ⟶ X} {b' : Z ⟶ X'} (ea : a' = j ≫ a) (eb : b' = j ≫ b) :
    LBIso (L.pull a') (M.pull b') :=
  LBIso.chartPull (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => ea)
    (Geo.Tor.chartPullSame M _ (fun _ => b) _ j fun _ => eb) h

theorem isSquare_eq {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ φ' : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ' b) (e : φ = φ') : a = b := by
  subst e
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm

set_option backward.isDefEq.respectTransparency false in

theorem IsMumPol.exists_isMumfordFam {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {R : Type} [CommRing R]
    [IsDomain R] [IsLocalRing R] {Q : Data R} {G₁ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] {P : LB (G2 G₁).left}
    (h : IsMumPol Q G₁ P) {T : Scheme.{0}} {i : T ⟶ Sp R} {l : Sp (FractionRing R) ⟶ T} (hl : l ≫ i = jK R)
    {A₀ : Over T} [GrpObj A₀] [IsCommMonObj A₀] {P₀ : LB (G2 A₀).left} (hP₀ : P₀.IsLB)
    {a : A₀.left ⟶ G₁.left} {a₂ : (G2 A₀).left ⟶ (G2 G₁).left} (ha : IsGrpPullback A₀ G₁ i a) (ha₂ : IsSquare a a₂)
    (hPa : LBIso P₀ (P.pull a₂)) {yU : T ⟶ F.X} {φ : A₀.left ⟶ F.univ.A.left} {φ₂ : (G2 A₀).left ⟶ (G2 F.univ.A).left}
    (hφ : IsGrpPullback A₀ F.univ.A yU φ) (hφ₂ : IsSquare φ φ₂) (hPφ : LBIso P₀ (F.univ.P.pull φ₂)) :
    ∃ α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left, IsGenFibre F (l ≫ yU) α₁ ∧ IsMumfordFam F (l ≫ yU) α₁ Q := by
  obtain ⟨hR, hpos, -, hbi, hU⟩ := h
  have w : pullback.fst G₁.hom (jK R) ≫ G₁.hom = (pullback.snd G₁.hom (jK R) ≫ l) ≫ i := by
    rw [Category.assoc, hl, pullback.condition]
  obtain ⟨ω, ω₁, ω₂⟩ : ∃ ω : pullback G₁.hom (jK R) ⟶ A₀.left, ω ≫ a = pullback.fst G₁.hom (jK R) ∧
      ω ≫ A₀.hom = pullback.snd G₁.hom (jK R) ≫ l := ⟨ha.1.lift _ _ w, ha.1.lift_fst _ _ w, ha.1.lift_snd _ _ w⟩
  have h₁ := isGrpPullback_pullback G₁ (jK R)
  have hω : IsGrpPullback ((Over.pullback (jK R)).obj G₁) A₀ l ω := ha.cancel (h₁.congr hl.symm ω₁.symm) ω₂
  refine ⟨ω ≫ φ, hω.comp hφ, hR, hpos, fun R' _ _ _ ρ hR' hρ hf D ε hD => ?_⟩
  obtain ⟨G', _, _, π, π₂, A, U, hπ, hπ₂, hL⟩ := hU R' ρ hR' hρ hf D ε hD
  obtain ⟨κ, hκ⟩ := exists_genericMap hρ
  letI := A.isAb.comm
  have w' : (pullback.fst G'.hom (jK R') ≫ π) ≫ G₁.hom = (pullback.snd G'.hom (jK R') ≫ κ) ≫ jK R := by
    rw [Category.assoc, hπ.1.w, Category.assoc, hκ, pullback.condition_assoc]
  obtain ⟨πK, p₁, p₂⟩ : ∃ πK : pullback G'.hom (jK R') ⟶ pullback G₁.hom (jK R),
      πK ≫ pullback.fst G₁.hom (jK R) = pullback.fst G'.hom (jK R') ≫ π ∧
      πK ≫ pullback.snd G₁.hom (jK R) = pullback.snd G'.hom (jK R') ≫ κ :=
    ⟨pullback.lift _ _ w', pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have h₂ := isGrpPullback_pullback G' (jK R')
  have hπK : IsGrpPullback ((Over.pullback (jK R')).obj G') ((Over.pullback (jK R)).obj G₁) κ πK :=
    h₁.cancel ((h₂.comp hπ).congr hκ.symm p₁.symm) p₂
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hi := isGrpPullback_of_iso U.gen.symm
  have e₁ : U.gen.hom.left ≫ U.gen.symm.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.symm_hom, U.gen.hom_inv_id, Over.id_left]
  have e₂ : U.gen.symm.hom.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.symm_hom, U.gen.inv_hom_id, Over.id_left]
  have hβ := hi.comp (hπK.comp hω)
  have hδ := hi.comp h₂
  obtain ⟨β₂, hβ₂⟩ : ∃ β₂, IsSquare _ β₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hβ.1.w⟩
  obtain ⟨δ₂, hδ₂⟩ : ∃ δ₂, IsSquare _ δ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hδ.1.w⟩
  have r : LBIso A.L (U.LG.L.pull (U.gen.symm.hom.left ≫ pullback.fst G'.hom (jK R'))) :=
    LBIso.trans A.isLB (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _)
      (LBIso.chartPull (chartPullId A.L) (Geo.Tor.chartPullPull A.L (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl A.isLB))
      (lbIso_pull_both U.ext U.gen.symm.hom.left e₂.symm rfl)
  have l₁ := GlobalTheory.LamPull.lbIso_lam_pull hδ U.LG.isLB A.isLB r hδ₂
  have i₁ : (abelian₂ G' U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have i₀ : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have e₃ : β₂ ≫ a₂ = δ₂ ≫ π₂ := isSquare_eq (isSquare_comp hβ₂ ha₂) (isSquare_comp hδ₂ hπ₂) (by
    simp only [Category.assoc]
    rw [ω₁, p₁])
  have l₂ := lbIso_pull_comp hL δ₂ e₃
  have l₃ := (lbIso_pull_comp hPa β₂ rfl).symm
  have l₄ := lbIso_pull_comp hPφ β₂ rfl
  refine ⟨G', inferInstance, inferInstance, π, A, U, hπ, κ, πK, (U.gen.symm.hom.left ≫ πK ≫ ω) ≫ φ, β₂ ≫ φ₂, hκ, p₁,
    (hβ.comp hφ).congr (by simp only [Category.id_comp, Category.assoc]) rfl, isSquare_comp hβ₂ hφ₂,
    LBIso.trans i₀ (pull_isLB i₁ _) (pull_isLB F.univ.isLB _) l₁
      (LBIso.trans (pull_isLB i₁ _) (pull_isLB hbi.1 _) (pull_isLB F.univ.isLB _) l₂
        (LBIso.trans (pull_isLB hbi.1 _) (pull_isLB hP₀ _) (pull_isLB F.univ.isLB _) l₃ l₄)), ?_⟩
  simp only [Category.assoc]
  rw [← Category.assoc, e₁, Category.id_comp]

theorem dense_generic_away {o R : Type} [CommRing o] [CommRing R] [IsDomain R] {b : o →+* R} (hb : Function.Injective b)
    {f : R} (hf : f ≠ 0) :
    Dense {x : Sp (Localization.Away f) | (spMap ((algebraMap R (Localization.Away f)).comp b) x).asIdeal = ⊥} := by
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective ((algebraMap R (Localization.Away f)).comp b) :=
    (IsLocalization.injective (Localization.Away f) hle).comp hb
  let p : PrimeSpectrum (Localization.Away f) := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : Dense ({p} : Set (PrimeSpectrum (Localization.Away f))) := by
    rw [dense_iff_closure_eq, PrimeSpectrum.closure_singleton]
    simp [p]
  refine Dense.mono ?_ hp
  rintro x rfl
  exact (RingHom.injective_iff_ker_eq_bot _).1 hinj

set_option backward.isDefEq.respectTransparency false in

theorem Taut.exists_isFam_of_siegPre : ∀ (g n : ℕ) (φ : InvFun ℤ), 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsMumPol C.Q G₁ P → (∀ p : Sp C.R, p ∈ abLocus G₁ ↔ ∏ k, C.t k ∉ p.asIdeal) → ∀ c : SiegPre g n (zetaAway n) (spMap ((algebraMap C.R (Localization.Away (∏ k, C.t k))).comp C.b)), c.Principal → (∃ (a : c.A.left ⟶ G₁.left) (a₂ : (G2 c.A).left ⟶ (G2 G₁).left), IsGrpPullback c.A G₁ (spMap (algebraMap C.R (Localization.Away (∏ k, C.t k)))) a ∧ IsSquare a a₂ ∧ LBIso c.P (P.pull a₂)) → ∃ (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (yU : Sp (Localization.Away (∏ k, C.t k)) ⟶ F.X) (l : Localization.Away (∏ k, C.t k) →+* FractionRing C.R), C.IsFam F G₁ y α₁ ∧ SiegPB c F.univ yU ∧ l.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = algebraMap C.R (FractionRing C.R) ∧ y = spMap l ≫ yU := by
  intro g n φ hn _ F C G₁ _ _ P hM hab c hc ⟨a, a₂, ha, ha₂, hPa⟩
  obtain ⟨-, -, hinj, -, hrel, -⟩ := Taut.isRegularLocalRing_and_isRelParam g n φ hn C
  have hf : ∏ k, C.t k ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ne_zero_of_isRelParam hrel i
  haveI : IsDomain (Localization.Away (∏ k, C.t k)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  obtain ⟨yU, hs, hPB⟩ := F.rep _ _ c inferInstance (dense_generic_away hinj hf) hc
  have hu : IsUnit (algebraMap C.R (FractionRing C.R) (∏ k, C.t k)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C.R _)).2 hf)
  let l : Localization.Away (∏ k, C.t k) →+* FractionRing C.R := IsLocalization.Away.lift _ hu
  have hl : l.comp (algebraMap C.R (Localization.Away (∏ k, C.t k))) = algebraMap C.R (FractionRing C.R) :=
    IsLocalization.Away.lift_comp _ hu
  have hl' : spMap l ≫ spMap (algebraMap C.R (Localization.Away (∏ k, C.t k))) = jK C.R := by
    rw [← Geo.Tor.spMap_comp, hl]
  obtain ⟨ψ, ψ₂, h₁, h₂, h₃, h₄⟩ := hPB
  obtain ⟨α₁, hα, hF⟩ := hM.exists_isMumfordFam F hl' c.isLB ha ha₂ hPa h₁ h₂ h₃
  refine ⟨spMap l ≫ yU, α₁, yU, l, ⟨hM.2.2.1, hab, hα, hF, ?_⟩, ⟨ψ, ψ₂, h₁, h₂, h₃, h₄⟩, hl, rfl⟩
  rw [Category.assoc, hs, Geo.Tor.spMap_comp, ← Category.assoc, hl']

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLocalFactorization
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

open scoped TensorProduct

namespace GlobalTheory.AffChartSmooth

theorem mem_of_closedPoint_mem {R : Type} [CommRing R] [IsLocalRing R] {U : Set (Sp R)}
    (hU : IsOpen U) (h : IsLocalRing.closedPoint R ∈ U) (x : Sp R) : x ∈ U := by
  have hx : (x : PrimeSpectrum R) ⤳ IsLocalRing.closedPoint R :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal x.2.ne_top)
  exact hx.mem_open hU h

theorem exists_smooth_chart : ∀ (Λ : Type) [CommRing Λ] (ι₀ : Λ →+* ℂ) (M : Scheme.{0}) (s : M ⟶ Sp Λ) (V : M.Opens) (d : ℕ),
    SmoothOfRelativeDimension d (V.ι ≫ s) → ∀ (R : Type) [CommRing R] [Algebra ℂ R] [IsLocalRing R] (b : Sp R ⟶ M),
    (∀ x, b.base x ∈ V) → b ≫ s = spMap ((algebraMap ℂ R).comp ι₀) →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra ℂ B) (_ : Algebra.Smooth ℂ B) (g : Sp B ⟶ M) (j : B →ₐ[ℂ] R),
      spMap (j : B →+* R) ≫ g = b := by
  intro Λ _ ι₀ M s V d hd R _ _ _ b hbV hbs
  haveI : Smooth (V.ι ≫ s) := SmoothOfRelativeDimension.smooth d _
  obtain ⟨W, hW, hxW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp M.isBasis_affineOpens)
    (hbV (IsLocalRing.closedPoint R))
  have hbW : ∀ x, b.base x ∈ W := fun x =>
    mem_of_closedPoint_mem (U := b.base ⁻¹' (W : Set M)) (W.2.preimage b.base.hom.continuous) hxW x
  haveI : Smooth ((Scheme.Opens.ι (X := M) W) ≫ s) := by
    rw [← Scheme.homOfLE_ι M hWV, Category.assoc]; infer_instance
  have hWa : IsAffineOpen W := hW
  let e := hWa.isoSpec
  let f : Spec Γ(M, W) ⟶ Sp Λ := e.inv ≫ (Scheme.Opens.ι (X := M) W) ≫ s
  have hf : Smooth f := inferInstance
  let φ := Spec.preimage f
  have hφ : φ.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 (by rw [Spec.map_preimage]; exact hf)

  letI : Algebra Λ Γ(M, W) := φ.hom.toAlgebra
  haveI : Algebra.Smooth Λ Γ(M, W) := RingHom.smooth_algebraMap.1 hφ
  letI : Algebra Λ ℂ := ι₀.toAlgebra
  have hrange : Set.range b.base ⊆ Set.range (Scheme.Opens.ι (X := M) W).base := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hbW x
  let b' : Sp R ⟶ W := IsOpenImmersion.lift (Scheme.Opens.ι (X := M) W) b hrange
  have hb' : b' ≫ (Scheme.Opens.ι (X := M) W) = b := IsOpenImmersion.lift_fac _ _ _
  let ψ := Spec.preimage (b' ≫ e.hom)
  have hψ : Spec.map ψ = b' ≫ e.hom := Spec.map_preimage _
  have hcomp : φ ≫ ψ = CommRingCat.ofHom ((algebraMap ℂ R).comp ι₀) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, Spec.map_preimage]
    simp only [f, Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% hb', hbs]
  letI : Algebra Λ R := ((algebraMap ℂ R).comp ι₀).toAlgebra
  haveI : IsScalarTower Λ ℂ R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g' : Γ(M, W) →ₐ[Λ] R :=
    { ψ.hom with
      commutes' := fun r => by
        have := congrArg (fun h => h.hom r) hcomp
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
        exact this }
  let j : ℂ ⊗[Λ] Γ(M, W) →ₐ[ℂ] R :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ R) g' (fun _ _ => Commute.all _ _)
  refine ⟨ℂ ⊗[Λ] Γ(M, W), inferInstance, inferInstance, inferInstance,
    spMap (Algebra.TensorProduct.includeRight (R := Λ) (A := ℂ) (B := Γ(M, W))).toRingHom ≫ e.inv ≫ (Scheme.Opens.ι (X := M) W), j, ?_⟩
  have hj : (j : ℂ ⊗[Λ] Γ(M, W) →+* R).comp (Algebra.TensorProduct.includeRight (R := Λ) (A := ℂ) (B := Γ(M, W))).toRingHom = ψ.hom := by
    ext a
    simp [j, g']
  rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hj]
  change Spec.map ψ ≫ _ = _
  rw [hψ, Category.assoc, Iso.hom_inv_id_assoc, hb']

end GlobalTheory.AffChartSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningFamilyMulTwistingSectionStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spanning_family_mul_twistingSection : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G G₀ : WTZ D.host.E) (t : GlobalTheory.FlatTw.TwSec U x Z G₀), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → Even G.2 → (∀ w, 0 ≤ t.lo w) → ∀ s₀ : Set (Rul Xo c), s₀ ⊆ (cuspW Xo c U G : Set (Rul Xo c)) → (∀ f ∈ s₀, ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) → cuspW Xo c U G ≤ Submodule.span c.F s₀ → ∃ s : Set (cuspOn U Z (G + G₀)), s ⊆ (latOn U Z (G + G₀) : Set (cuspOn U Z (G + G₀))) ∧ Submodule.span c.F s = ⊤ ∧ ∀ y ∈ s, ∃ f ∈ s₀, ∀ σ, normOn U x V dict Z (G + G₀) σ y ≤ t.cInf σ * petOn U x V dict Z G σ f := by
  first | exact @GlobalTheory.SpanShortProd.exists_span_mul_twSec | exact GlobalTheory.SpanShortProd.exists_span_mul_twSec | (intros; apply GlobalTheory.SpanShortProd.exists_span_mul_twSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSemiAbelianModelAfterExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Ex.OneGen
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SplitSemiAbModel

theorem exists_split_model : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (P : PolAV (Sp (FractionRing V))), ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (f : V →+* W) (fK : FractionRing V →+* FractionRing W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ f.IsIntegral ∧ Function.Injective f ∧ (∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) ∧ ∃ (A : PolAV (Sp (FractionRing W))) (β : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap fK) β ∧ LBIso A.L (P.L.pull β) ∧ ∃ (G : Over (Sp W)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK W)).obj G ≅ A.A), IsSemiAbelian G ∧ IsMonHom gen.hom ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField W)), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj G) := by
  intro V _ _ _ hV P
  obtain ⟨V₁, _, _, _, f₁, fK₁, hV₁, hinj₁, -, hfin₁, hK₁, A₁, β₁, hpb₁, -, G₁, _, _, gen₁, hG₁, hgen₁⟩ :=
    GlobalTheory.PolSemiAbModel.exists_model V hV P
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff V₁).1 hV₁
  obtain ⟨W, _, _, _, _, g, hcW, hgi, hginj, -, E, hE⟩ :=
    GlobalTheory.SplitExtDVR.exists_complete_dvr_split_ext V₁ hcpl G₁ hG₁
  have hj : Function.Injective ((algebraMap W (FractionRing W)).comp g) :=
    (IsFractionRing.injective W (FractionRing W)).comp hginj
  obtain ⟨fK₂, hK₂'⟩ : ∃ fK₂ : FractionRing V₁ →+* FractionRing W,
      ∀ a, fK₂ (algebraMap V₁ (FractionRing V₁) a) = algebraMap W (FractionRing W) (g a) :=
    ⟨IsFractionRing.lift (A := V₁) (K := FractionRing V₁) hj,
      fun a => IsFractionRing.lift_algebraMap (K := FractionRing V₁) hj a⟩
  have hK₂ : fK₂.comp (algebraMap V₁ (FractionRing V₁)) = (algebraMap W (FractionRing W)).comp g :=
    RingHom.ext hK₂'
  obtain ⟨A, β, hpb, -, hLB⟩ := GlobalTheory.KeyFam.SameLam.exists_polPB P (fK₂.comp fK₁)
  have hG : IsSemiAbelian ((Over.pullback (spMap g)).obj G₁) := IsSemiAbelian.pullback _ G₁ hG₁
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, g.comp f₁, fK₂.comp fK₁, hcW,
    RingHom.IsIntegral.trans _ _ hfin₁.to_isIntegral hgi, hginj.comp hinj₁, ?_, A, β, hpb, hLB, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hK₁]
    exact hK₂' _
  · let G := (Over.pullback (spMap g)).obj G₁
    let X := (Over.pullback (jK V₁)).obj G₁
    let T := (Over.pullback (spMap fK₂)).obj X
    have h₁ := (isGrpPullback_pullback G (jK W)).comp (isGrpPullback_pullback G₁ (spMap g))
    have hTX := isGrpPullback_pullback X (spMap fK₂)
    have hXG := isGrpPullback_pullback G₁ (jK V₁)
    have hsq : spMap fK₂ ≫ jK V₁ = jK W ≫ spMap g := by
      show spMap fK₂ ≫ spMap (algebraMap V₁ _) = spMap (algebraMap W _) ≫ spMap g
      rw [GlobalTheory.PolSemiAbModel.spMap_comp', GlobalTheory.PolSemiAbModel.spMap_comp', hK₂]
    have hTG := (hTX.comp hXG).congr hsq rfl
    obtain ⟨e₁, he₁, -⟩ := grpPullback_iso h₁ hTG
    have hXY := isGrpPullback_of_iso gen₁
    have hTP := (hTX.comp (hXY.comp hpb₁)).congr
      (by rw [Category.id_comp, GlobalTheory.PolSemiAbModel.spMap_comp']) rfl
    obtain ⟨e₂, he₂, -⟩ := grpPullback_iso hTP hpb
    exact ⟨G, inferInstance, hG.comm, e₁ ≪≫ e₂, hG, by simp only [Iso.trans_hom]; infer_instance, E, hE⟩

end GlobalTheory.SplitSemiAbModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtLatticeHomFiniteExtensionComplete
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootHom

theorem exists_sqrt_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h : X → (FractionRing R)ˣ) (m : ℕ) (t : Fin m → R), IsCN R → (∀ a b, h (a + b) = h a * h b) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (gam : FractionRing R →+* FractionRing R') (r : Fin m → R') (eta : X → (FractionRing R')ˣ), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x)) ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ (∀ a b, eta (a + b) = eta a * eta b) ∧ ∀ a, eta a ^ 2 = Units.map gam.toMonoidHom (h a) := by
  intro R _ _ _ X _ _ _ h m t hR hh
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hpq : ∀ k, ∃ p q : R, q ∈ nonZeroDivisors R ∧
      algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q = (h (b k) : FractionRing R) :=
    fun k => IsFractionRing.div_surjective R _
  choose p q hq hpq using hpq
  obtain ⟨R', _, _, _, ρ, r, hR', hinj, hfin, hloc, hr⟩ :=
    GlobalTheory.T.exists_finite_completeNormal_ext_sqrt_family R (Fin m ⊕ Module.Free.ChooseBasisIndex ℤ X) (Sum.elim t (fun k => p k * q k)) hR
  have hι : Function.Injective (algebraMap R' (FractionRing R')) := IsFractionRing.injective R' (FractionRing R')
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) := hι.comp hinj
  let gam : FractionRing R →+* FractionRing R' := IsFractionRing.lift hinj'
  have hgam : ∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x) := fun x => IsFractionRing.lift_algebraMap hinj' x
  have hq0 : ∀ k, algebraMap R' (FractionRing R') (ρ (q k)) ≠ 0 := by
    intro k h0
    have : ρ (q k) = 0 := hι (by simpa using h0)
    exact nonZeroDivisors.ne_zero (hq k) (hinj (by simpa using this))
  have hp0 : ∀ k, p k ≠ 0 := by
    intro k h0
    have := hpq k
    rw [h0, map_zero, zero_div] at this
    exact (h (b k)).ne_zero this.symm
  have hs : ∀ k, (r (Sum.inr k)) ^ 2 = ρ (p k * q k) := fun k => by simpa using hr (Sum.inr k)
  have hs0 : ∀ k, algebraMap R' (FractionRing R') (r (Sum.inr k)) ≠ 0 := by
    intro k h0
    have h1 : r (Sum.inr k) = 0 := hι (by simpa using h0)
    have h2 := hs k
    rw [h1, zero_pow two_ne_zero] at h2
    exact mul_ne_zero (hp0 k) (nonZeroDivisors.ne_zero (hq k)) (hinj (by simpa using h2.symm))
  let e : Module.Free.ChooseBasisIndex ℤ X → (FractionRing R')ˣ := fun k =>
    Units.mk0 (algebraMap R' _ (r (Sum.inr k)) / algebraMap R' _ (ρ (q k))) (div_ne_zero (hs0 k) (hq0 k))
  let L : X →ₗ[ℤ] Additive (FractionRing R')ˣ := b.constr ℤ (fun k => Additive.ofMul (e k))
  let H : X →+ Additive (FractionRing R)ˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (h a)) (fun a c => by
    simp [hh a c])
  let G : X →+ Additive (FractionRing R')ˣ := (MonoidHom.toAdditive (Units.map gam.toMonoidHom)).comp H
  have hLG : L + L = G.toIntLinearMap := by
    refine b.ext fun k => ?_
    simp only [LinearMap.add_apply, L, Module.Basis.constr_basis, AddMonoidHom.coe_toIntLinearMap, G, H,
      AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.mk'_apply, MonoidHom.toAdditive_apply_apply]
    rw [← ofMul_mul]
    congr 1
    ext
    simp only [Units.val_mul, e, Units.val_mk0, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, toMul_ofMul]
    rw [← hpq k, map_div₀, hgam, hgam, div_mul_div_comm, div_eq_div_iff (mul_ne_zero (hq0 k) (hq0 k)) (hq0 k)]
    have := congrArg (algebraMap R' (FractionRing R')) (hs k)
    rw [map_pow, map_mul, map_mul] at this
    rw [← sq, this]
    ring
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, gam, fun i => r (Sum.inl i), fun a => Additive.toMul (L a),
    hR', hinj, hfin, hloc, hgam, fun i => by simpa using hr (Sum.inl i), fun a c => by simp [map_add], fun a => ?_⟩
  have h2 : Additive.toMul (L a + L a) = Units.map gam.toMonoidHom (h a) := by
    rw [← LinearMap.add_apply, LinearMap.congr_fun hLG a]
    rfl
  rw [sq, ← toMul_add]
  exact h2

end GlobalTheory.RootHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricBalancedGeneratorPsiZeroLocalRing
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UTau0

theorem exists_symmetric_balanced_generator_psi_zero_localRing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ : DegPre R) (O : Type) [CommRing O]
    [StarRing O] [Module O D₀.X] [Module.Projective O D₀.X] [Module.Finite O D₀.X] (onB : D₀.P.OAct O),
    (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) → ∀ w0 : O, w0 + star w0 = 1 →
    (∃ u : LB.Gen (LB.LinComb D₀.P.L (K := Fin 4) ![(padd D₀.P.A (𝟙 _) (onB.act w0)).left, 𝟙 D₀.P.A.left,
        (onB.act w0).left, (toUnit D₀.P.A ≫ η[D₀.P.A]).left] ![1, -2, -1, 2]),
      u.IsGen ∧ LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (eSec D₀.P.A)) (LB.oneGen D₀.P.L)) →
    ∃ (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => ptK (D₀.c y)) (fun _ => -1)))
      (h : ∀ y, (ψ y).IsGen),
      letI : Module O ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).X := ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).OAct O, oa.onB = onB ∧
        ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := ψ, psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := ψ, psi_gen := h } : DegPre R) y Set.univ := by
  intro R _ _ _ D₀ O _ _ _ _ _ onB hlin w0 hw ⟨uw, huw, huw0⟩
  have cadd : ∀ y y' : D₀.X, D₀.c (y + y') = D₀.c y * D₀.c y' := fun y y' => D₀.c_add y y'
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_balanced_bimultiplicative_generator_lambda_inv R D₀.P.A D₀.P.isAb ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub O onB.toRingAct
    onB.rosati D₀.X D₀.c cadd hlin
  obtain ⟨τ', hτ', hτs⟩ := GlobalTheory.T.symmetric_trivialisation_of_balanced_bimultiplicative R D₀.P.A D₀.P.isAb ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub O
    onB.toRingAct onB.rosati D₀.X D₀.c cadd hlin w0 hw τ hτ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_psi_generators_degenerationLaws_symmetricBalanced R D₀ O onB hlin w0 hw uw huw huw0 τ' hτ' hτs
  obtain ⟨h, rest⟩ := GlobalTheory.T.degenerationPreData_laws_of_generator_values R D₀ O onB hlin w0 uw huw huw0 ψ hψ
  exact ⟨_, h, rest⟩

end GlobalTheory.UTau0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricPolarisationFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg.SymPol

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem inv_comm (h : IsGrpPullback G' G f φ) : (ι[G']).left ≫ φ = φ ≫ (ι[G]).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine Eq.trans e ?_
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_half (h : IsGrpPullback G' G f φ) (a : 𝟙_ (Over S) ⟶ G) (b : Over.mk f ⟶ G) (hb : b ^ 2 = toUnit _ ≫ a) :
    ∃ b' : 𝟙_ (Over S') ⟶ G',
      ((toUnit G' ≫ b' ^ 2) * 𝟙 G').left ≫ φ = φ ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
  have w : b.left ≫ G.hom = 𝟙 S' ≫ f := (Over.w b).trans (Category.id_comp _).symm
  let b' : 𝟙_ (Over S') ⟶ G' := Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ _)
  have hb' : b'.left ≫ φ = b.left := h.1.lift_fst _ _ _
  let j : Over.mk (G'.hom ≫ f) ⟶ Over.mk f := Over.homMk G'.hom rfl
  have hu : (toUnit G').left = G'.hom := (Category.comp_id _).symm.trans (Over.w (toUnit G'))
  have e₁ : pushHom h G' (toUnit G' ≫ b') = j ≫ b := Over.OverMorphism.ext (by
    show ((toUnit G').left ≫ b'.left) ≫ φ = G'.hom ≫ b.left
    rw [Category.assoc, hb', hu])
  have e₂ : pushHom h G' ((toUnit G' ≫ b' ^ 2) * 𝟙 G') = pushHom h G' (𝟙 G') ≫ ((toUnit G ≫ a) * 𝟙 G) := by
    rw [map_mul, MonObj.comp_pow, map_pow, e₁, ← MonObj.comp_pow, hb, MonObj.comp_mul, Category.comp_id,
      ← Category.assoc, ← Category.assoc, toUnit_unique (j ≫ toUnit _) (pushHom h G' (𝟙 G') ≫ toUnit G)]
  refine ⟨b', (congrArg (fun z => z.left) e₂).trans ?_⟩
  show (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem exists_gen_theta_pull [IsCommMonObj G] [IsCommMonObj G'] (h : IsGrpPullback G' G f φ) {L : LB G.left}
    (ht : ∃ t : LB.Gen (Theta G L), t.IsGen) : ∃ t : LB.Gen (Theta G' (L.pull φ)), t.IsGen := by
  obtain ⟨t, ht⟩ := ht
  exact gen_chartPull (chartPullLinComb L φ _ _ _ (cubeMapOf h).F3 fun I => (cubeMapOf h).psum_comm I.down) t ht

end GlobalTheory.PolDeg.SymPol

open GlobalTheory.PolDeg.SymPol GlobalTheory.CechPic in

theorem GlobalTheory.PolDeg.exists_symmetric_pol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ IsGrpPullback P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) := by
  intro R _ _ _ Q hR
  haveI := hR.1
  have hM := Q.M.isLB
  have hΘ : ∃ t : LB.Gen (Theta Q.B Q.M.L), t.IsGen := ⟨Q.cub.t, Q.cub.isGen⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.primitive_bundle_eq_translate_ample_noetherian_local R Q.B Q.g Q.M.L _ Q.isAb Q.smoothDim hM Q.ample Q.ktriv hΘ
    (LB.isLB_linComb hM _ _) (GlobalTheory.T.exists_generator_mumfordBundle_inv_pullback_primitive R Q.B Q.M Q.cub Q.isAb)
  have ea := (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)).2 ha
  rw [cls_linComb hM, cls_linComb hM, Fin.sum_univ_two, Fin.sum_univ_two] at ea
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, add_left_inj] at ea
  obtain ⟨R', _, _, _, ρ, b, hR', hinj, hfin, hloc, hb⟩ := GlobalTheory.T.exists_halving_point_abelianScheme_finite_ext R Q.B a hR Q.isAb
  haveI := hR'.1
  have h := isGrpPullback_pullback Q.B (spMap ρ)
  have hA := PolPull.isAbelianScheme_of_isGrpPullback Q.isAb h
  haveI := hA.comm
  obtain ⟨b', hb'⟩ := exists_half h a b hb
  have hM' := pull_isLB hM (pullback.fst Q.B.hom (spMap ρ))
  have hid := (cls_eq_iff hM' hM').1 rfl
  obtain ⟨w, hw⟩ := id hid
  obtain ⟨L, hL, hrig, hsym, hamp, hK, hΛ⟩ := GlobalTheory.T.exists_symmetric_rigidified_translate_ample_K_trivial R' _ _ b' hA hM'
    (relAmple_pull h.1 hM hM' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) Q.ample)
    (kTriv_pull h hM hM' ((isGen_iff w).1 hw) Q.ktriv) (exists_gen_theta_pull h hΘ)
    ((cls_eq_iff (pull_isLB hM' _) (pull_isLB hM' _)).1 (by
      rw [cls_pull hM', cls_pull hM', cls_pull hM, ← pull_comp, ← pull_comp, inv_comm h, hb', pull_comp, pull_comp, ea]))
  obtain ⟨β₂, hβ₂⟩ := SiegPull.exists_isSquare h.1.w
  exact ⟨R', _, _, _, ρ,
    { A := (Over.pullback (spMap ρ)).obj Q.B, isAb := hA, g := Q.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim
      L := L, isLB := hL, rigid := hrig, sym := hsym, ample := hamp, ktriv := hK }, _, β₂, hR', hinj, hfin, hloc, h, hβ₂,
    LBIso.trans (LB.isLB_linComb hL _ _) (LB.isLB_linComb hM' _ _) (pull_isLB (LB.isLB_linComb hM _ _) _) hΛ
      (SiegPull.lbIso_lam_pull h hid hβ₂)⟩

end
end

