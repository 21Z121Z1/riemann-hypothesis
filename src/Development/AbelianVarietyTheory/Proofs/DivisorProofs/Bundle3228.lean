import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3186
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3200
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2846
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoInclLast
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceIntersectionNumberAdjacentSwapNeg
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem interPoly_swap_adjacent : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), IsGraded E' gr → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q : MvPolynomial (Root m) ℝ, Y.interPoly gr (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - Y.interPoly gr Q := by
  intro F _ X Y ι _ m E E' φ f hR gr hgr τ a b hab Q
  obtain ⟨B, hB, hBg⟩ := hgr
  have hlt : a < b := by
    show (a : ℕ) < b
    omega
  obtain ⟨ψ₂, hgen, hφ, hpar⟩ := GlobalTheory.T.exists_generic_pair_flags_differing_one_step F X Y ι m E E' φ f hR B hB τ a b hlt
  obtain ⟨W, j, h1, h2⟩ := GlobalTheory.T.exists_doubleSpace_of_genericFunctionFieldPair F Y _ _ _ hgen
  have hs : W.Small := GlobalTheory.T.doubleSpace_small_of_functionField_embeds_ratFunc F Y W j h1
  have e1 : ∀ u, j (W.α₁ u) = algebraMap Y.Fn (RatFunc Y.Fn) u := fun u => DFunLike.congr_fun h1 u
  have e2 : ∀ u, j (W.α₂ u) = ψ₂ u := fun u => DFunLike.congr_fun h2 u
  have hα : ∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u) := fun u =>
    j.injective (by rw [e1, e2, hφ])
  have m1 : (B.map W.α₁).map j = B.map (algebraMap Y.Fn (RatFunc Y.Fn)) := by
    funext σ; ext i k; exact e1 _
  have m2 : (B.map W.α₂).map j = B.map ψ₂ := by
    funext σ; ext i k; exact e2 _
  have hlow : AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) := by
    refine GlobalTheory.T.isAlmostLowerTriangular_of_shear_parabolic ι m τ a b hab _ _ j RatFunc.X RatFunc.X_ne_zero _ ?_
    rw [Mat.map_mul, Mat.map_inv, m1, m2]
    exact hpar
  obtain ⟨D₁, D₂, Θ, h⟩ := GlobalTheory.T.exists_divisors_doubleFlagSpace F X Y ι m E E' φ f hR gr B hB hBg W hα τ a b hab hlow
  have hne : (⟨τ, a⟩ : Root m) ≠ ⟨τ, b⟩ := fun h => hlt.ne (eq_of_heq (Sigma.mk.inj h).2)
  have := GlobalTheory.T.intersectionNumber_swap_of_doubleSpace F Y W hs (Root m) _ _ hne gr D₁ D₂ Θ h Q
  convert this

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartPresentsLevelsModIdeal
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

theorem coeff_mem_of_mem_smul_top {O σ : Type} [CommRing O] (I : Ideal O)
    {h : MvPowerSeries σ O} (hh : h ∈ I • (⊤ : Submodule O (MvPowerSeries σ O))) (α : σ →₀ ℕ) :
    coeff α h ∈ I := by
  refine Submodule.smul_induction_on hh (fun a ha x _ => ?_) (fun x y hx hy => ?_)
  · rw [MvPowerSeries.coeff_smul]
    exact I.mul_mem_right _ ha
  · rw [map_add]
    exact I.add_mem hx hy

theorem presents_quotient :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
      (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I →
      ∃ hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i),
        (∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n)
          (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f) ∧
        Presents (O ⧸ I) (B := fun n => (O ⧸ I) ⊗[O] G.A n) (fun n i => 1 ⊗ₜ[O] c.x n i) hx := by
  intro p _ O _ G d c I m hm
  have hp : ∀ n, ((p : (O ⧸ I) ⊗[O] G.A n)) ^ m = 0 := fun n => by
    have h0 : ((p : O ⧸ I)) ^ m = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hm
    rw [← map_natCast (algebraMap (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n)), ← map_pow, h0, map_zero]
  have hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i) := fun n i => by
    obtain ⟨N, y, hy⟩ := c.nil n i
    refine ⟨N * m, ?_⟩
    have : (1 : O ⧸ I) ⊗ₜ[O] c.x n i = Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I)
      (c.x n i) := rfl
    rw [this, ← map_pow, pow_mul, hy, mul_pow, map_mul, map_pow, map_natCast, hp, zero_mul]
  have hev : ∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n)
      (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f := fun n f =>
    (GlobalTheory.algHom_eval_comp_eq_evA_map p m O (G.A n) (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n) (Fin d) (c.x n) (c.ev n) (c.isEval n)
      (Ideal.Quotient.mk I)
      (Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I)).toRingHom
      (fun a => by
        change Algebra.TensorProduct.includeRight (R := O) (A := O ⧸ I) (algebraMap O (G.A n) a) = _
        rw [AlgHom.commutes]
        exact IsScalarTower.algebraMap_apply O (O ⧸ I) ((O ⧸ I) ⊗[O] G.A n) a)
      (hp n) (hx n) f).symm
  refine ⟨hx, hev, fun n y => ?_, fun N => ?_⟩
  · obtain ⟨b, rfl⟩ := (GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A n) I).1 y
    obtain ⟨f, rfl⟩ := c.surj n b
    exact ⟨_, hev n f⟩
  · obtain ⟨n, hn⟩ := c.ker m N
    refine ⟨n, fun g hg α hα => ?_⟩
    obtain ⟨f, rfl, -⟩ := (GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I).1 g
    rw [hev] at hg
    have h1 : c.ev n f ∈ I • (⊤ : Submodule O (G.A n)) := ((GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A n) I).2.1 _).1 hg
    have h2 : c.ev n f ∈ (I • (⊤ : Submodule O (MvPowerSeries (Fin d) O))).map
        (c.ev n).toLinearMap := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (c.surj n)]
      exact h1
    obtain ⟨h, hh, he⟩ := h2
    have h3 : c.ev n (f - h) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact he.symm
    have h4 : coeff α (f - h) ∈ I := by
      obtain ⟨z, hz⟩ := hn (f - h) h3 α hα
      rw [hz]
      exact I.mul_mem_right _ hm
    have h5 : coeff α f ∈ I := by
      have := I.add_mem h4 (coeff_mem_of_mem_smul_top I hh α)
      rwa [map_sub, sub_add_cancel] at this
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem]
    exact h5

end GlobalTheory.QLog.Chart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsReducedOfField
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isReduced_of_isRegularRing (R : Type) [CommRing R] [IsRegularRing R] : IsReduced R :=
  isReduced_ofLocalizationMaximal R fun P _ => by
    haveI := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing (R := Localization.AtPrime P)
    infer_instance

theorem tensor_map_injective_of_field (A M K L : Type) [CommRing A] [CommRing M] [Algebra A M]
    [Field K] [Field L] [Algebra A K] [Algebra A L] (ι : K →ₐ[A] L) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id A M) ι) := by
  letI : Algebra K L := ι.toRingHom.toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a => (ι.commutes a).symm
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hcomp : (r.restrictScalars A) ∘ₗ ι.toLinearMap = LinearMap.id := by
    ext k
    exact LinearMap.congr_fun hr k
  intro x y hxy
  have h := congrArg (LinearMap.lTensor M (r.restrictScalars A)) hxy
  have key : ∀ z : M ⊗[A] K,
      LinearMap.lTensor M (r.restrictScalars A) (Algebra.TensorProduct.map (AlgHom.id A M) ι z) = z := by
    intro z
    have : (LinearMap.lTensor M (r.restrictScalars A)) ∘ₗ (LinearMap.lTensor M ι.toLinearMap) =
        LinearMap.id := by
      rw [← LinearMap.lTensor_comp, hcomp, LinearMap.lTensor_id]
    have e : Algebra.TensorProduct.map (AlgHom.id A M) ι z = LinearMap.lTensor M ι.toLinearMap z := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add a b ha hb => rw [map_add, map_add, ha, hb]
    rw [e]
    exact LinearMap.congr_fun this z
  rwa [key, key] at h

end GlobalTheory

namespace GlobalTheory

theorem formalFibre_isReduced_of_field :
    ∀ (A L : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [Field L] [Algebra A L],
      IsReduced (AdicCompletion (maximalIdeal A) A ⊗[A] L) := by
  intro A L _ _ _ _ _
  classical
  refine ⟨fun x hx => ?_⟩
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  set T : Subalgebra A L := Algebra.adjoin A ((S.image Prod.snd : Finset L) : Set L) with hT
  haveI : Algebra.FiniteType A T := (Subalgebra.fg_iff_finiteType T).mp (Subalgebra.fg_adjoin_finset _)
  let K := FractionRing T
  haveI : Algebra.EssFiniteType T K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors T)
  haveI : Algebra.EssFiniteType A K := Algebra.EssFiniteType.comp A T K
  have hinj : Function.Injective (IsScalarTower.toAlgHom T T L) := Subtype.val_injective
  let ι : K →ₐ[A] L := (IsFractionRing.liftAlgHom (K := K) hinj).restrictScalars A
  have hι : ∀ t : T, ι (algebraMap T K t) = t := fun t => by
    simp [ι, IsFractionRing.liftAlgHom_apply]
  have hmem : ∀ i ∈ S, i.2 ∈ T := fun i hi =>
    Algebra.subset_adjoin (by simpa using ⟨i.1, hi⟩)
  let y : AdicCompletion (maximalIdeal A) A ⊗[A] K :=
    ∑ i ∈ S.attach, i.1.1 ⊗ₜ[A] algebraMap T K ⟨i.1.2, hmem i.1 i.2⟩
  let Φ := Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (maximalIdeal A) A)) ι
  have hΦ : Φ y = ∑ i ∈ S, i.1 ⊗ₜ[A] i.2 := by
    simp only [y, map_sum, Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hι]
    exact Finset.sum_attach S (fun i => i.1 ⊗ₜ[A] i.2)
  haveI : IsRegularRing (AdicCompletion (maximalIdeal A) A ⊗[A] K) :=
    formalFibre_isRegularRing_of_essFiniteType_int A K
  haveI := isReduced_of_isRegularRing (AdicCompletion (maximalIdeal A) A ⊗[A] K)
  obtain ⟨n, hn⟩ := hx
  have hy : IsNilpotent y := ⟨n, tensor_map_injective_of_field A _ K L ι (by rw [map_pow, map_zero, hΦ, hn])⟩
  rw [← hΦ, IsReduced.eq_zero y hy, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeFlagBundleSmoothRelativeDim
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagFreeSmooth

open Limits

theorem exists_widePullback_smooth {B : Scheme.{0}} (ι : Type) [Fintype ι] :
    ∀ (Z : ι → Scheme.{0}) (ρ : ∀ a, Z a ⟶ B) (d : ι → ℕ), (∀ a, SmoothOfRelativeDimension (d a) (ρ a)) →
      ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (p : ∀ a, Y ⟶ Z a), (∀ a, p a ≫ ρ a = π) ∧
        SmoothOfRelativeDimension (∑ a, d a) π ∧
        ∀ (T : Scheme.{0}) (g : T ⟶ B) (h : ∀ a, T ⟶ Z a), (∀ a, h a ≫ ρ a = g) →
          ∃! g' : T ⟶ Y, g' ≫ π = g ∧ ∀ a, g' ≫ p a = h a := by
  refine @Fintype.induction_empty_option (fun α _ => ∀ (Z : α → Scheme.{0}) (ρ : ∀ a, Z a ⟶ B) (d : α → ℕ),
      (∀ a, SmoothOfRelativeDimension (d a) (ρ a)) →
      ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (p : ∀ a, Y ⟶ Z a), (∀ a, p a ≫ ρ a = π) ∧
        SmoothOfRelativeDimension (∑ a, d a) π ∧
        ∀ (T : Scheme.{0}) (g : T ⟶ B) (h : ∀ a, T ⟶ Z a), (∀ a, h a ≫ ρ a = g) →
          ∃! g' : T ⟶ Y, g' ≫ π = g ∧ ∀ a, g' ≫ p a = h a) ?_ ?_ ?_ ι _
  · intro α β _ e ih Z ρ d hρ
    letI : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨Y, π, p, hp, hY, H⟩ := ih (fun a => Z (e a)) (fun a => ρ (e a)) (fun a => d (e a)) fun a => hρ _
    let p' : ∀ b, Y ⟶ Z b := Equiv.piCongrLeft (fun b => Y ⟶ Z b) e p
    have hp' (a : α) : p' (e a) = p a := Equiv.piCongrLeft_apply_apply _ _ _ _
    have hs : ∑ a, d (e a) = ∑ b, d b := Equiv.sum_comp e d
    rw [hs] at hY
    refine ⟨Y, π, p', e.forall_congr_right.1 fun a => by rw [hp', hp], hY, fun T g h hh => ?_⟩
    obtain ⟨g', ⟨h₁, h₂⟩, u⟩ := H T g (fun a => h (e a)) fun a => hh _
    exact ⟨g', ⟨h₁, e.forall_congr_right.1 fun a => by rw [hp', h₂]⟩,
      fun y hy => u y ⟨hy.1, fun a => by rw [← hp', hy.2]⟩⟩
  · intro Z ρ d _
    have h0 : (∑ a : PEmpty, d a) = 0 := by simp
    rw [h0]
    exact ⟨B, 𝟙 B, fun a => a.elim, fun a => a.elim, inferInstance,
      fun T g _ _ => ⟨g, ⟨Category.comp_id g, fun a => a.elim⟩, fun y hy => (Category.comp_id y).symm.trans hy.1⟩⟩
  · intro α _ ih Z ρ d hρ
    obtain ⟨Y, π, p, hp, hY, H⟩ := ih (fun a => Z (some a)) (fun a => ρ (some a)) (fun a => d (some a))
      fun a => hρ _
    have : SmoothOfRelativeDimension (d none) (pullback.fst π (ρ none)) :=
      haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := d none)
      MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension (d none)) π (ρ none) (hρ none)
    have hs : SmoothOfRelativeDimension (∑ a, d a) (pullback.fst π (ρ none) ≫ π) := by
      rw [Fintype.sum_option]
      infer_instance
    refine ⟨pullback π (ρ none), pullback.fst _ _ ≫ π,
      fun a => Option.rec (pullback.snd _ _) (fun a => pullback.fst _ _ ≫ p a) a, ?_, hs, fun T g h hh => ?_⟩
    · rintro (_ | a)
      · exact pullback.condition.symm
      · exact (Category.assoc _ _ _).trans (congrArg _ (hp a))
    · obtain ⟨g', ⟨h₁, h₂⟩, u⟩ := H T g (fun a => h (some a)) fun a => hh _
      refine ⟨pullback.lift g' (h none) (h₁.trans (hh none).symm), ⟨by rw [pullback.lift_fst_assoc, h₁], ?_⟩,
        fun y hy => ?_⟩
      · rintro (_ | a)
        · exact pullback.lift_snd _ _ _
        · exact (pullback.lift_fst_assoc _ _ _ _).trans (h₂ a)
      · refine pullback.hom_ext ?_ ?_
        · rw [pullback.lift_fst]
          exact u _ ⟨(Category.assoc _ _ _).trans hy.1, fun a => (Category.assoc _ _ _).trans (hy.2 (some a))⟩
        · rw [pullback.lift_snd]
          exact hy.2 none

end GlobalTheory.FlagFreeSmooth

namespace GlobalTheory.FlagFreeSmooth

theorem smooth_flStr_unit (n : ℕ) : SmoothOfRelativeDimension (n * (n - 1) / 2) (GlobalTheory.FlagZ.flStr Unit n) := by
  have h := (GlobalTheory.FlagZ.smooth_dim_isArithVar_part Unit (Unit × Fin (n + 1)) n Prod.fst Prod.snd).1
  rw [(GlobalTheory.FlagZ.Count.card_cellVar Unit n).1] at h
  unfold dimFl at h
  simpa using h

end GlobalTheory.FlagFreeSmooth

namespace GlobalTheory.FlagFreeSmooth

open GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ

def univFlag (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) :
    Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (GlobalTheory.QCoh.freeModule (X := Sp ℤ) (Fin N))) N where
  F := F ι N τ
  ι := incl ι N τ
  isSubbundle i := (GlobalTheory.T.tautological_subbundle_rank ι N τ i).2
  isVB i := (GlobalTheory.T.tautological_subbundle_rank ι N τ i).1
  step := step ι N τ
  step_ι := step_incl ι N τ
  isIso_last := isIso_incl_last ι N τ

theorem isFlagBundle_univFlag (ι : Type) [Fintype ι] (N : ℕ) :
    IsFlagBundle (flStr ι N) (fun _ : ι => SheafOfModules.free (R := (Sp ℤ).ringCatSheaf) (Fin N)) (fun _ => N)
      (univFlag ι N) := by
  intro T g fl'
  obtain ⟨g', hg'⟩ := GlobalTheory.T.flag_variety_lift_exists ι N T g fl'
  exact ⟨g', hg', fun y hy => GlobalTheory.T.flag_variety_lift_unique ι N T g fl' y g' hy hg'⟩

theorem exists_single_int : ∀ (n : ℕ), ∃ (Y : Scheme.{0}) (π : Y ⟶ Sp ℤ) (fl : ∀ _ : Unit, Vert.Flag ((Scheme.Modules.pullback π).obj (SheafOfModules.free (R := (Sp ℤ).ringCatSheaf) (Fin n))) n), IsFlagBundle π (fun _ : Unit => SheafOfModules.free (R := (Sp ℤ).ringCatSheaf) (Fin n)) (fun _ => n) fl ∧ SmoothOfRelativeDimension (n * (n - 1) / 2) π := fun n =>
  ⟨Fl Unit n, flStr Unit n, univFlag Unit n, isFlagBundle_univFlag Unit n, smooth_flStr_unit n⟩

end GlobalTheory.FlagFreeSmooth

namespace GlobalTheory.FlagFreeSmooth

open Limits

theorem exists_single (B : Scheme.{0}) (n : ℕ) :
    ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ _ : Unit, Vert.Flag ((Scheme.Modules.pullback π).obj
      (SheafOfModules.free (R := B.ringCatSheaf) (Fin n))) n),
      IsFlagBundle π (fun _ : Unit => SheafOfModules.free (R := B.ringCatSheaf) (Fin n)) (fun _ => n) fl ∧
      SmoothOfRelativeDimension (n * (n - 1) / 2) π := by
  obtain ⟨Y, π, fl, hfl, hs⟩ := exists_single_int n
  let g : B ⟶ Sp ℤ := specZIsTerminal.from B
  have hbc := GlobalTheory.T.isFlagBundle_pullback' (Sp ℤ) Y B π g Unit _ (fun _ => n) fl hfl
  obtain ⟨e⟩ := GlobalTheory.T.pullback_free_module_iso B (Sp ℤ) g n
  have hiso := GlobalTheory.FlagIsoBundle.isFlagBundle_of_iso B (pullback π g) (pullback.snd π g) Unit _
    (fun _ : Unit => SheafOfModules.free (R := B.ringCatSheaf) (Fin n)) (fun _ => n) _ (fun _ => e) hbc
  have : SmoothOfRelativeDimension (n * (n - 1) / 2) (pullback.snd π g) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := n * (n - 1) / 2)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension (n * (n - 1) / 2)) π g hs
  exact ⟨_, _, _, hiso, this⟩

theorem main : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (r : ι → ℕ), ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a)))) (r a)), IsFlagBundle π (fun a => SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a))) r fl ∧ SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2) π := by
  intro B ι _ r
  choose Z ρ fl hfl hs using fun a => exists_single B (r a)
  obtain ⟨Y, π, p, hp, hY, H⟩ := exists_widePullback_smooth ι Z ρ (fun a => r a * (r a - 1) / 2) hs
  exact ⟨Y, π, _, GlobalTheory.FlagFamily.isFlagBundle_of_widePullback
    (fun a => SheafOfModules.free (R := B.ringCatSheaf) (Fin (r a))) r ρ fl hfl π p hp H, hY⟩

end GlobalTheory.FlagFreeSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTateGaloisAction
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem frob_tend_galT (K : Type) [Field K] [Fintype K] (l : ℕ) [Fact l.Prime] (A : AbVar K) :
    tend l A (frob A) = galT l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  have h := (GlobalTheory.T.frobenius_endomorphism_unique K A).1
  refine LinearMap.ext fun t => Tate.ext fun n => ?_
  exact h (t.lev n)

theorem frob_tate (K : Type) [Field K] [Fintype K] (l : ℕ) [Fact l.Prime] (A : AbVar K) :
    tend l A (frob A) = galT l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) ∧
    vend l A (toEnd0 A (frob A)) = galV l A (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) := by
  refine ⟨frob_tend_galT K l A, ?_⟩
  have hv : vend l A (toEnd0 A (frob A)) =
      (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)) (tend l A (frob A)) := by
    simp [vend, toEnd0, Algebra.TensorProduct.lift_tmul]
  rw [hv, frob_tend_galT K l A]
  rfl

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyWeightIncrementSemiPositiveCurvature
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace GlobalTheory.HSAmp

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y

theorem semiPos_up_of_isCan : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x →
    ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (up P.L u).SemiPos D := by
  intro k _ X _ p D _ P e x hx n u hn hu σ i c y hy ξ
  set j := pick (P.A.φ σ).isLB y
  have hj : y ∈ ptsIn p σ (P.A.B.U j) := mem_pick (P.A.φ σ).isLB y
  set O := ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j) with hOdef
  have hO : IsOpen O := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hen : (0 : ℝ) < (e : ℝ) * n := mul_pos he hn'

  have key : ∀ z ∈ O, 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) ∧
      (P.L.φ σ).φ i z + u.u σ z =
        ((e : ℝ) * n)⁻¹ * Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n)) := by
    intro z hz
    have hnu : ∀ l, P.nu e 0 σ z (x l) ^ (2 * n) =
        Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) * Real.exp (-((e : ℝ) * n) * (P.L.φ σ).φ i z) := by
      intro l
      rw [GlobalTheory.VolBr.nu_eq k X p P e 0 (x l) (hx.mem l) σ z i j hz.1 hz.2, Complex.normSq_eq_norm_sq, norm_pow,
        mul_pow, ← pow_mul, ← Real.exp_nat_mul]
      congr 2
      · ring_nf
      · push_cast; ring
    have hsum : ∑ l, P.nu e 0 σ z (x l) ^ (2 * n) =
        (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n)) * Real.exp (-((e : ℝ) * n) * (P.L.φ σ).φ i z) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => hnu l
    have hpos : 0 < ∑ l, P.nu e 0 σ z (x l) ^ (2 * n) := by
      obtain ⟨l, hl⟩ := hx.cover (under z)
      have h1 := ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ z hl).2
      exact Finset.sum_pos' (fun l' _ => pow_nonneg (by unfold Pair.nu; positivity) _)
        ⟨l, Finset.mem_univ _, pow_pos h1 _⟩
    have hS : 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) := by
      rw [hsum] at hpos
      exact pos_of_mul_pos_left hpos (Real.exp_pos _).le
    refine ⟨hS, ?_⟩
    rw [hu σ z, hsum, Real.log_mul hS.ne' (Real.exp_pos _).ne', Real.log_exp]
    field_simp
    ring
  have hyO : y ∈ O := ⟨hy.2, hj⟩
  have hW : IsOpen (c.e.target ∩ c.e.symm ⁻¹' O) := GlobalTheory.ChartGlue.isOpen_over c.e hO
  have hyW : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' O := GlobalTheory.ChartGlue.mem_over c.e hy.1 hyO
  have hG : ∀ l, ContDiffAt ℂ 2 (fun v => ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n) (c.e y) := fun l =>
    contDiffAt_two_of_holo hW (((GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P e 0 σ (x l) (hx.mem l) i j).2 D c).pow n) hyW
  have hS : 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm (c.e y)) ^ n) :=
    (key _ hyW.2).1
  have hf : ContDiffAt ℝ 2 (fun v => Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n)))
      (c.e y) :=
    (ContDiffAt.sum fun l _ => contDiffAt_normSq_comp (hG l)).log hS.ne'
  have heq : (fun v => ((((P.L.φ σ).addFn (u.u σ)).φ i (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => ((((e : ℝ) * n)⁻¹ *
        Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n)) + 0 : ℝ) : ℂ) :=
    eventually_of_mem (hW.mem_nhds hyW) fun v hv => by
      dsimp only
      rw [add_zero, ← (key _ hv.2).2]
      rfl
  change 0 ≤ (leviV D (fun v => ((((P.L.φ σ).addFn (u.u σ)).φ i (c.e.symm v) : ℝ) : ℂ)) (c.e y) ξ).re
  rw [leviV_congr heq, leviV_const_mul hf _ 0, Complex.re_ofReal_mul]
  exact mul_nonneg (inv_nonneg.2 hen.le) (leviV_log_sum_nonneg (fun l => contDiffAt_normSq_comp (hG l))
    (fun l => logPshAt_normSq (hG l)) hS ξ)

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantTorsionValuesUltrametricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_equivariant_torsion_values_ultrametric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → (∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p))) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧ ∀ j : ℕ, ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x' := by
  first | exact @GlobalTheory.Mum.Recog.recognition_core | exact GlobalTheory.Mum.Recog.recognition_core | (intros; apply GlobalTheory.Mum.Recog.recognition_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreProjEmbeddingFixedGroupConnectedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricFibre_projEmbedding_fixedGroup_connected : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G'), (∀ (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback π (spMap (κ.comp (residue R))) : Scheme.{0})) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ PSpace R E.N), (∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range ν) → ConnectedSpace (pullback E.f ν : Scheme.{0}) := by
  first | exact @GlobalTheory.Mum.FibConn.fib_conn | exact GlobalTheory.Mum.FibConn.fib_conn | (intros; apply GlobalTheory.Mum.FibConn.fib_conn <;> assumption)
end

