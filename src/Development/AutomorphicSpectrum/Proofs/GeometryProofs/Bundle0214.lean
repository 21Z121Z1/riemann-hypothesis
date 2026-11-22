import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0024
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0209
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0211
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0015
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0036
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionFieldExtensionExists
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0208
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointOverNumberFieldValue
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LiesOver

open GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer

section Values

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

theorem valAt_add {a b : Ω} {r s : ℂ} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) :
    ValAt ξ z (a + b) (r + s) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  obtain ⟨_, t', rfl, rfl⟩ := h'
  exact ⟨hz, t + t', map_add _ _ _, map_add _ _ _⟩

theorem valAt_int (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : ℂ) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ _, map_intCast _ _⟩

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {w : (Σ k, J k) → ℂ}

theorem evC_xpow (w : (Σ k, J k) → ℂ) (c : ∀ k, J k) (e : K → ℕ) :
    evC w (ArakelovGeometry.xpow c e) = ∏ k, w ⟨k, c k⟩ ^ e k := by
  simp [evC, ArakelovGeometry.xpow, map_prod]

theorem exists_form_valAt (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (G : MRing J), IsMultiHomog G δ ∧ aeval y G = x * ∏ k, y ⟨k, c k⟩ ^ δ k ∧
      ValAt ξ z x (evC w G / ∏ k, w ⟨k, c k⟩ ^ δ k) := by
  classical
  have hc0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hW : ∀ δ : K → ℕ, (∏ k, w ⟨k, c k⟩ ^ δ k) ≠ 0 := fun δ =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc0 k)
  have hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hpowC : ∀ δ₁ δ₂ : K → ℕ, ∏ k, w ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, w ⟨k, c k⟩ ^ δ₁ k) * ∏ k, w ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hx
    refine ⟨Pi.single k 1, MvPolynomial.X ⟨k, i⟩, ArakelovGeometry.isMultiHomog_X' k i, ?_, ?_⟩
    · rw [aeval_X, Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]
      simp [div_mul_cancel₀ _ (hy k)]
    · obtain ⟨r, hr, e⟩ := (hw.2 k (c k) (hc k)).2 i
      have e1 : (∏ k', w ⟨k', c k'⟩ ^ (Pi.single k 1 : K → ℕ) k') = w ⟨k, c k⟩ := by
        rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)]
        simp
      have e2 : evC w (MvPolynomial.X ⟨k, i⟩ : MRing J) = w ⟨k, i⟩ := by simp [evC]
      rw [e1, e2, e, mul_div_cancel_right₀ _ (hc0 k)]
      exact hr
  | algebraMap r =>
    refine ⟨0, C r, isMultiHomog_C r, by simp, ?_⟩
    have e : evC w (C r : MRing J) = (r : ℂ) := by simp [evC]
    simp only [e, Pi.zero_apply, pow_zero, Finset.prod_const_one, div_one]
    simpa using valAt_int hz r
  | add a b _ _ ha hb =>
    obtain ⟨δ₁, e₁, h₁, v₁, u₁⟩ := ha
    obtain ⟨δ₂, e₂, h₂, v₂, u₂⟩ := hb
    refine ⟨δ₁ + δ₂, e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁,
      isMultiHomog_add (ArakelovGeometry.isMultiHomog_mul h₁ (ArakelovGeometry.isMultiHomog_xpow c δ₂)) ?_, ?_, ?_⟩
    · rw [add_comm δ₁]
      exact ArakelovGeometry.isMultiHomog_mul h₂ (ArakelovGeometry.isMultiHomog_xpow c δ₁)
    · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_xpow, aeval_xpow, hpow]
      ring
    · convert valAt_add u₁ u₂ using 1
      have e : evC w (e₁ * ArakelovGeometry.xpow c δ₂ + e₂ * ArakelovGeometry.xpow c δ₁) =
          evC w e₁ * evC w (ArakelovGeometry.xpow c δ₂) + evC w e₂ * evC w (ArakelovGeometry.xpow c δ₁) := by
        simp only [evC, map_add, map_mul]
      rw [e, evC_xpow, evC_xpow, hpowC]
      have := hW δ₁
      have := hW δ₂
      field_simp
  | mul a b _ _ ha hb =>
    obtain ⟨δ₁, e₁, h₁, v₁, u₁⟩ := ha
    obtain ⟨δ₂, e₂, h₂, v₂, u₂⟩ := hb
    refine ⟨δ₁ + δ₂, e₁ * e₂, ArakelovGeometry.isMultiHomog_mul h₁ h₂, ?_, ?_⟩
    · rw [map_mul, v₁, v₂, hpow]
      ring
    · convert CoordModel.valAt_mul u₁ u₂ using 1
      have e : evC w (e₁ * e₂) = evC w e₁ * evC w e₂ := by simp only [evC, map_mul]
      rw [e, hpowC]
      have := hW δ₁
      have := hW δ₂
      field_simp

end Values

theorem valAt_cst : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (σ : F' →+* ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), NormalCpt ξ → (CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w → PtOver y ψ σ w → genPt ξ ⤳ centre z → ∀ a : F', ValAt ξ z (ψ a) (σ a) := by
  intro X Ω _ ξ K _ J _ y F' _ _ ψ σ z w hN ht hw hp hz a
  classical
  choose c hc using hw.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hO : OverInt y ψ := overInt_of_normalCpt ht hN ψ
  have hint : ∀ b : 𝓞 F', ValAt ξ z (ψ (b : F')) (σ (b : F')) := by
    intro b
    obtain ⟨δ, G, hG, hv, hu⟩ := exists_form_valAt hz hw c hy hc (hO.2 c hy b)
    have h1 := hp.2 (b : F') δ G (ArakelovGeometry.xpow c δ) hG (ArakelovGeometry.isMultiHomog_xpow c δ) (by
      rw [hv, GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.aeval_xpow])
    rw [evC_xpow] at h1
    have hW : (∏ k, w ⟨k, c k⟩ ^ δ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero
    rwa [h1, mul_div_cancel_right₀ _ hW] at hu
  have halg : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ F').2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨n, hn, hi⟩ := halg.exists_integral_multiple
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h1 := hint (⟨n • a, hi⟩ : 𝓞 F')
  have h2 : ValAt ξ z (n : Ω) ((Units.mk0 (n : ℂ) hnC : ℂˣ) : ℂ) := valAt_int hz n
  obtain ⟨hn0, h3⟩ := CoordModel.valAt_inv h2
  have h4 := CoordModel.valAt_mul h3 h1
  convert h4 using 1
  · show ψ a = (n : Ω)⁻¹ * ψ (n • a)
    rw [zsmul_eq_mul, map_mul, map_intCast, inv_mul_cancel_left₀ hn0]
  · show σ a = ((Units.mk0 (n : ℂ) hnC)⁻¹ : ℂˣ) * σ (n • a)
    rw [zsmul_eq_mul, map_mul, map_intCast, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel_left₀ hnC]

end GlobalTheory.CompanionTheory.Ar.Flat.LiesOver
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointValuesInValueSetStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_values_in_value_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (y : (Ref.pjSys Xo c).Pt la), (fun f => (Ref.pjSys Xo c).val y f) ∈ valSet Xo c (algCls Xo c) la := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.val_mem_valSet_of_uniformised | exact GlobalTheory.CompanionTheory.Ar.Rec.val_mem_valSet_of_uniformised | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.val_mem_valSet_of_uniformised <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModuleModNBasis
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.ModFree

open NumberField Module
open scoped nonZeroDivisors TensorProduct

theorem exists_map_of_basis {O B M Mb : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B]
    (S : Submonoid O) (hS : S ≤ O⁰) [IsLocalization S B] [AddCommGroup M] [Module O M]
    [AddCommGroup Mb] [Module O Mb] [Module B Mb] [IsScalarTower O B Mb] (f : M →ₗ[O] Mb)
    [IsLocalizedModule S f] {n : ℕ} (b : Basis (Fin n) B Mb) :
    ∃ φ : (Fin n → O) →ₗ[O] M, Function.Injective φ ∧
      ∀ m, ∃ s : S, ∃ y, (s : O) • m = φ y := by
  choose p hp using fun i => IsLocalizedModule.surj S f (b i)
  have hinj : Function.Injective (algebraMap O B) := IsLocalization.injective B hS
  refine ⟨Fintype.linearCombination O (fun i => (p i).1), ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [Fintype.linearCombination_apply] at hy
    have h1 : ∑ i, algebraMap O B (y i * (p i).2) • b i = 0 := by
      have h := congrArg f hy
      rw [map_sum, map_zero] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hp i, Submonoid.smul_def, algebraMap_smul, mul_smul]
    have h2 := Fintype.linearIndependent_iff.mp b.linearIndependent _ h1
    funext i
    have h3 : y i * (p i).2 = 0 := hinj (by rw [h2 i, map_zero])
    exact (mul_eq_zero.mp h3).resolve_right (nonZeroDivisors.ne_zero (hS (p i).2.2))
  · intro x
    have hx := b.sum_repr (f x)
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples S Finset.univ
      (fun i => b.repr (f x) i * ((IsLocalization.map_units B (p i).2).unit⁻¹ : Bˣ))
    choose a ha using fun i => RingHom.mem_rangeS.mp (ht i (Finset.mem_univ i))
    have hc : ∀ i, algebraMap O B (a i) * algebraMap O B (p i).2 =
        algebraMap O B t * b.repr (f x) i := by
      intro i
      rw [ha i, Algebra.smul_def, mul_assoc, mul_assoc, IsUnit.val_inv_mul, mul_one]
    have key : f ((t : O) • x) = f (Fintype.linearCombination O (fun i => (p i).1) a) := by
      rw [map_smul, Fintype.linearCombination_apply, map_sum, ← hx, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hp i, Submonoid.smul_def, ← algebraMap_smul B (a i),
        ← algebraMap_smul B ((p i).2 : O), smul_smul, hc i, mul_smul, algebraMap_smul]
    obtain ⟨c, hc'⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) key
    refine ⟨c * t, (c : O) • a, ?_⟩
    rw [map_smul, Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, hc', Submonoid.smul_def]

theorem exists_free_map_mod (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (𝓞 E) M] : Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M →
    ∀ (n N : ℕ), Module.finrank (𝓞 E) M = n → 0 < N →
    ∃ φ : (Fin n → 𝓞 E) →ₗ[𝓞 E] M, (∀ m, ∃ x b, m = φ x + N • b) ∧
      ∀ x b, φ x = N • b → ∃ x', x = N • x' := by
  intro hfin hproj n N hn hN
  set S := GlobalTheory.PlaceInt.LocBasis.primeTo (𝓞 E) N with hSdef
  have hS : S ≤ (𝓞 E)⁰ := by
    rintro s ⟨k, hk0, -, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hk0)
  have : IsDomain (Localization S) := IsLocalization.isDomain_localization hS
  have : IsPrincipalIdealRing (Localization S) :=
    GlobalTheory.PlaceInt.LocBasis.isPrincipalIdealRing_loc E N hN hS (Localization S)
  have hrank : Module.finrank (Localization S) (LocalizedModule S M) = n := by
    rw [IsLocalization.finrank_eq (Localization S) S hS,
      IsLocalizedModule.finrank_eq S (LocalizedModule.mkLinearMap S M) hS, hn]
  let b := Module.finBasisOfFinrankEq (Localization S) (LocalizedModule S M) hrank
  obtain ⟨φ, hφ, hsurj⟩ := exists_map_of_basis S hS (LocalizedModule.mkLinearMap S M) b
  have hunit : ∀ s : S, ∃ k : ℕ, (s : 𝓞 E) = k ∧ ∃ u v : ℤ, u * k + v * N = 1 := by
    rintro ⟨_, k, -, hkc, rfl⟩
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hkc
    exact ⟨k, rfl, u, v, huv⟩
  refine ⟨φ, fun m => ?_, fun x c hxc => ?_⟩
  · obtain ⟨s, y, hs⟩ := hsurj m
    obtain ⟨k, hk, u, v, huv⟩ := hunit s
    rw [hk, Nat.cast_smul_eq_nsmul] at hs
    refine ⟨u • y, v • m, ?_⟩
    calc m = ((u * k + v * N : ℤ)) • m := by rw [huv, one_smul]
      _ = u • ((k : ℤ) • m) + (N : ℤ) • (v • m) := by
        rw [add_smul, mul_smul, mul_comm v, mul_smul]
      _ = φ (u • y) + N • (v • m) := by
        rw [map_zsmul, ← hs, natCast_zsmul, natCast_zsmul]
  · obtain ⟨s, y, hs⟩ := hsurj c
    obtain ⟨k, hk, u, v, huv⟩ := hunit s
    rw [hk, Nat.cast_smul_eq_nsmul] at hs
    have hNy : N • y = k • x := by
      apply hφ
      rw [map_nsmul, map_nsmul, ← hs, hxc, smul_comm]
    refine ⟨u • y + v • x, ?_⟩
    calc x = ((u * k + v * N : ℤ)) • x := by rw [huv, one_smul]
      _ = u • ((k : ℤ) • x) + v • ((N : ℤ) • x) := by
        rw [add_smul, mul_smul, mul_smul]
      _ = N • (u • y + v • x) := by
        rw [natCast_zsmul, natCast_zsmul, ← hNy, smul_add, smul_comm u N y, smul_comm v N x]

end GlobalTheory.CompanionTheory.ModFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameHeight
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good

open AlgebraicGeometry CategoryTheory

theorem exists_const_set {K Ω : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K] [Field Ω] (f : K →+* Ω) :
    ∃ S : Set Ω, S.Finite ∧ ∀ A : Subring Ω, S ⊆ A → (∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ A) → ∀ a, f a ∈ A := by
  let bs := Module.finBasis ℚ K
  refine ⟨Set.range fun i => f (bs i), Set.finite_range _, fun A hS hn a => ?_⟩
  have hq : ∀ q : ℚ, f (algebraMap ℚ K q) ∈ A := fun q => by
    rw [eq_ratCast, Rat.cast_def, map_div₀, map_intCast, map_natCast, div_eq_mul_inv]
    exact A.mul_mem (intCast_mem A _) (hn _ q.den_nz)
  rw [← bs.sum_repr a, map_sum]
  refine A.sum_mem fun i _ => ?_
  rw [Algebra.smul_def, map_mul]
  exact A.mul_mem (hq _) (hS ⟨i, rfl⟩)

theorem test_mem {K Ω : Type} [Field K] [CommRing Ω] [Algebra K Ω] (t : TRing K) (φ : t.R →ₐ[K] Ω) (A : Subring Ω)
    (hc : ∀ a, algebraMap K Ω a ∈ A) (hX : ∀ i, φ (Ideal.Quotient.mk t.I (MvPolynomial.X i)) ∈ A) (r : t.R) :
    φ r ∈ A := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk t.I (MvPolynomial.C a) = algebraMap K t.R a := rfl
    rw [h, φ.commutes]
    exact hc a
  | add p p' hp hp' =>
    rw [map_add, map_add]
    exact A.add_mem hp hp'
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    exact A.mul_mem hp (hX i)

section Flag

variable {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ}

theorem exists_coeff_of_mem {b₀ : Fin r → E} {n : ℕ} {x : E} (hx : x ∈ flagStep Ω b₀ n) :
    ∃ t : Fin r → Ω, x = ∑ j, t j • b₀ j ∧ ∀ j : Fin r, n ≤ j → t j = 0 := by
  classical
  unfold flagStep at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, hk, rfl⟩ := h
    refine ⟨Pi.single k 1, by simp [Pi.single_apply], fun j hj => ?_⟩
    have hk' : (k : ℕ) < n := hk
    have : j ≠ k := fun e => by subst e; omega
    simp [Pi.single_apply, this]
  | zero => exact ⟨0, by simp, fun _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨t, rfl, ht⟩ := hx
    obtain ⟨t', rfl, ht'⟩ := hy
    exact ⟨t + t', by simp [add_smul, Finset.sum_add_distrib], fun j hj => by simp [ht j hj, ht' j hj]⟩
  | smul a x _ hx =>
    obtain ⟨t, rfl, ht⟩ := hx
    exact ⟨a • t, by simp [Finset.smul_sum, smul_smul], fun j hj => by simp [ht j hj]⟩

theorem sum_mem_flagStep (b₀ : Fin r → E) {n : ℕ} (t : Fin r → Ω) (ht : ∀ j : Fin r, n ≤ j → t j = 0) :
    ∑ j, t j • b₀ j ∈ flagStep Ω b₀ n := by
  refine Submodule.sum_mem _ fun j _ => ?_
  by_cases h : n ≤ j
  · rw [ht j h, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, not_le.1 h, rfl⟩)

theorem exists_tri {b b₀ : Fin r → E} (hf : ∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i)
    (hb : LinearIndependent Ω b) :
    ∃ T : Matrix (Fin r) (Fin r) Ω, (∀ i, b i = ∑ j, T i j • b₀ j) ∧ ∀ i, T i i ≠ 0 := by
  have hstep : ∀ i : Fin r, ∃ t : Fin r → Ω, b i = ∑ j, t j • b₀ j ∧ ∀ j : Fin r, (i : ℕ) + 1 ≤ j → t j = 0 := by
    intro i
    refine exists_coeff_of_mem (n := (i : ℕ) + 1) ?_
    rw [← hf]
    exact Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩
  choose T hT hz using hstep
  refine ⟨Matrix.of T, hT, fun i h0 => ?_⟩
  have hm : b i ∈ flagStep Ω b₀ i := by
    rw [hT i]
    refine sum_mem_flagStep b₀ (T i) fun j hj => ?_
    rcases Nat.eq_or_lt_of_le hj with e | e
    · rw [show j = i from Fin.ext e.symm]
      exact h0
    · exact hz i j e
  rw [← hf] at hm
  exact hb.notMem_span_image (s := {k | (k : ℕ) < i}) (x := i) (fun h => lt_irrefl (i : ℕ) h) hm

end Flag

section Frames

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem compactSpace_of_tie (all : ∀ q : X, genPt ξ ⤳ q) {κ : Type} [Finite κ] {x : κ → Ω} {o : Type} [CommRing o]
    [Algebra o Ω] (tie : CoordTie o ξ x) : CompactSpace X := by
  have hW : ∀ c, ∃ W : Set X, IsCompact W ∧ ∀ (q : X) (h : genPt ξ ⤳ q), InChart ξ x c ⟨q, h⟩ → q ∈ W := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨∅, isCompact_empty, fun q h hi => absurd hc hi.1⟩
    · obtain ⟨U, hU, hq⟩ := tie.affine c hc
      exact ⟨U, hU.isCompact, fun q h hi => (hq q).2 ⟨h, hi⟩⟩
  choose W hW hq using hW
  refine ⟨?_⟩
  have hu : (Set.univ : Set X) = ⋃ c, W c := by
    refine (Set.eq_univ_of_forall fun q => ?_).symm
    obtain ⟨c, hc⟩ := tie.cover ⟨q, all q⟩
    exact Set.mem_iUnion.2 ⟨c, hq c q _ hc⟩
  rw [hu]
  exact isCompact_iUnion hW

theorem exists_frame_set [CompactSpace X] (all : ∀ q : X, genPt ξ ⤳ q) {E : Type} [AddCommGroup E] [Module Ω E]
    (L : Lat ξ E) {r : ℕ} (b₀ : Fin r → E) (h : L.IsFlagVBOn Set.univ b₀) :
    ∃ S : Set Ω, S.Finite ∧ ∀ A : Subring Ω, S ⊆ A → ∀ q : Cpt ξ,
      ∃ (b : Fin r → E) (T : Matrix (Fin r) (Fin r) Ω), (∀ i, flagStep Ω b i = flagStep Ω b₀ i) ∧
        L.IsFrameAt b q ∧ (∀ i, b i = ∑ j, T i j • b₀ j) ∧ (∀ i j, T i j ∈ A) ∧
        ∀ i, T i i ≠ 0 ∧ (T i i)⁻¹ ∈ A := by
  have h' : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ (b : Fin r → E) (T : Matrix (Fin r) (Fin r) Ω),
      (∀ i, flagStep Ω b i = flagStep Ω b₀ i) ∧ (∀ q : Cpt ξ, q.1 ∈ U → L.IsFrameAt b q) ∧
      (∀ i, b i = ∑ j, T i j • b₀ j) ∧ ∀ i, T i i ≠ 0 := by
    intro x
    obtain ⟨U, hx, b, hf, hq⟩ := h ⟨x, all x⟩ trivial
    obtain ⟨T, hT, hd⟩ := exists_tri hf (hq ⟨x, all x⟩ trivial hx).1
    exact ⟨U, hx, b, T, hf, fun q hqU => hq q trivial hqU, hT, hd⟩
  choose U hx b T hf hq hT hd using h'
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => (U x : Set X))
    (fun x _ => (U x).isOpen.mem_nhds (hx x))
  refine ⟨⋃ x ∈ t, (Set.range (fun ij : Fin r × Fin r => T x ij.1 ij.2) ∪ Set.range fun i => (T x i i)⁻¹),
    t.finite_toSet.biUnion fun x _ => (Set.finite_range _).union (Set.finite_range _), fun A hS q => ?_⟩
  obtain ⟨x, hxt, hqx⟩ : ∃ x ∈ t, q.1 ∈ U x := by
    simpa using ht.2 (Set.mem_univ q.1)
  have hsub : Set.range (fun ij : Fin r × Fin r => T x ij.1 ij.2) ∪ (Set.range fun i => (T x i i)⁻¹) ⊆ A :=
    fun a ha => hS (Set.mem_biUnion hxt ha)
  exact ⟨b x, T x, hf x, hq x q hqx, hT x, fun i j => hsub (Or.inl ⟨(i, j), rfl⟩),
    fun i => ⟨hd x i, hsub (Or.inr ⟨i, rfl⟩)⟩⟩

end Frames

theorem exists_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), ∃ B : Finset RM.Ω, ∀ A : Subring RM.Ω, (↑B : Set RM.Ω) ⊆ A → (∀ n : ℕ, n ≠ 0 → ((n : RM.Ω))⁻¹ ∈ A) → FinRd.GoodRing Fr A := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Og Fr
  classical
  obtain ⟨S₁, hS₁f, hS₁⟩ := exists_const_set Og.𝔐.cst
  haveI : CompactSpace Og.𝔐.X := compactSpace_of_tie Og.𝔐.all Og.𝔐.tie
  have hfr := fun s => exists_frame_set Og.𝔐.all (Og.𝔐.V s) (Og.Fl.b s) (Og.Fl.sub s)
  choose S₄ hS₄f hS₄ using hfr
  letI := Small.cstAlg Og
  obtain ⟨t, φ, yq, hφ, -⟩ := Fr.exists_spread
  let M : RootIx Dw × ((k : RM.K) → RM.ι k) → RM.Ω :=
    fun p => (∏ k, RM.y ⟨k, p.2 k⟩ ^ RM.xdeg p.1 k) * Og.e p.1
  let S₂ : Set RM.Ω := Set.range fun i => φ (Ideal.Quotient.mk t.I (MvPolynomial.X i))
  have hSf : (S₁ ∪ S₂ ∪ Set.range M ∪ (Set.range fun p => (M p)⁻¹) ∪ ⋃ s, S₄ s).Finite :=
    (((hS₁f.union (Set.finite_range _)).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_iUnion hS₄f)
  refine ⟨hSf.toFinset, fun A hB hn => ?_⟩
  rw [Set.Finite.coe_toFinset] at hB
  have hc : ∀ a : c.F, Og.𝔐.cst a ∈ A :=
    hS₁ A (fun a ha => hB (Or.inl (Or.inl (Or.inl (Or.inl ha))))) hn
  refine ⟨hc, ⟨t, φ, yq, hφ, test_mem t φ A hc fun i => hB (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))⟩,
    fun ρ s _ => ⟨hB (Or.inl (Or.inl (Or.inr ⟨(ρ, s), rfl⟩))), hB (Or.inl (Or.inr ⟨(ρ, s), rfl⟩))⟩,
    fun s q => hS₄ s A (fun a ha => hB (Or.inr (Set.mem_iUnion.2 ⟨s, ha⟩))) q⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionFieldExtensionExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_field_extension_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (m : ℕ) (K : Type) [Field K] [NumberField K] [Algebra L K] (x : Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G), 1 ≤ m → x ^ m = 1 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (_ : Algebra L K') (_ : IsScalarTower L K K'), ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower L K' L'] (D' : PPData H L') (e : D.Ext D'), ∃ (s : Out.H0 D'.t.PP.L (m ^ 2)) (d : 𝓞 L'), d ≠ 0 ∧ ∀ (F : Type) [Field F] (f : L' →+* F) (y : Over.mk (spMap (f.comp (algebraMap (𝓞 L') L'))) ⟶ D'.t.G) (b : Sp F ⟶ Sp (𝓞 L)) (xF yF : Over.mk b ⟶ D.t.G) (N : ℕ) (T T' : F), xF.left = spMap ((f.comp (algebraMap K' L')).comp (algebraMap K K')) ≫ x.left → yF.left = y.left ≫ e.φ → TorsVal D'.t.PP s y N T → TorsVal D.t.PP th (xF * yF ^ m) (N * m) T' → ∃ r : ℕ, 1 ≤ r ∧ (T ^ (m ^ 2)) ^ r = (f (d : L') ^ ((N * m) ^ 2) * T') ^ r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.transl_main | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.transl_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.transl_main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointLineBundleUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_point_line_bundle_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (O C : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field C] [Algebra O C] [FaithfulSMul O C] (ρ : 𝓞 L →+* O) (y : Over.mk (spMap ρ) ⟶ D.t.G) (N : ℕ), 1 ≤ N → y ^ N = 1 → ∀ (i : D.t.PP.L.ι) (h : ⊤ ≤ (show Sp O ⟶ D.t.G.left from y.left) ⁻¹ᵁ (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => (n : ℤ))).U (fun _ => i)) (b : Sp C ⟶ Sp (𝓞 L)), b = spMap (algebraMap O C) ≫ spMap ρ → ∀ (yC : Over.mk b ⟶ D.t.G), yC.left = spMap (algebraMap O C) ≫ y.left → ∀ T : C, TorsVal D.t.PP s yC N T → ∃ ε : Oˣ, T = algebraMap O C (valR (show Sp O ⟶ D.t.G.left from y.left) _ h (s.f fun _ => i) ^ (N ^ 2) * ε) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Reg.torsVal_eq_unit_mul | exact GlobalTheory.CompanionTheory.Ar.Sl.Reg.torsVal_eq_unit_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Reg.torsVal_eq_unit_mul <;> assumption)
end

