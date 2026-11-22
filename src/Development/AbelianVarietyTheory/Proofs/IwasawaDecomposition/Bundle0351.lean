import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0336
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0346
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0339
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRankOneIsAvg
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem eq_zero_of_sum_coef {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} {d : ℝ} (hd : IsFdeg (muG ε) σ d) {m : ℕ} {a y : Fin m → H} (ha : Orthonormal ℂ a)
    (h0 : ∀ g ∈ UJset ε, ∑ j, ⟪y j, σ g (a j)⟫_ℂ = 0) (k : Fin m) : y k = 0 := by
  have h1 : ∫ g, ∑ j, coefOn σ (a j) (y j) g * star (coefOn σ (a k) (y k) g) ∂(muG ε) = 0 := by
    have : ∀ g : UJ ε, ∑ j, coefOn σ (a j) (y j) g * star (coefOn σ (a k) (y k) g) = 0 := fun g => by
      rw [← Finset.sum_mul]
      have := h0 (umat g) g.2
      simp only [coefOn]
      rw [this, zero_mul]
    simp only [this, integral_zero]
  rw [integral_finset_sum _ fun j _ => (hd.2 _ _ _ _).1] at h1
  simp only [fun j => (hd.2 (a j) (y j) (a k) (y k)).2, orthonormal_iff_ite.1 ha, ite_mul, ite_div, one_mul, zero_mul,
    zero_div, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  exact inner_self_eq_zero.1 ((div_eq_zero_iff.1 h1).resolve_right hd')

theorem exists_rank_one_isAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ a c : H, a ≠ 0 ∧ c ≠ 0 ∧ IsKFin ε σ a ∧ IsKFin ε σ c ∧ IsAvg ε σ (fun w => ⟪c, w⟫_ℂ • a) := by
  intro n ε H _ _ _ σ h
  obtain ⟨hσ, -, -, ⟨d, hd⟩, b, hb, hb0⟩ := id h
  obtain ⟨A1, A2, A3, A4, A5⟩ := isAvg_closure n ε H σ hσ
  obtain ⟨B1, B2, -, -⟩ := kCoef_kAvg n ε H σ hσ
  have he := B1 b hb
  obtain ⟨m, a, c, ha, haK, hcK, hQ⟩ := GlobalTheory.T.compactAverage_kFinite_finiteRank n ε H σ h _ he
  have hQavg := A4 _ (by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1)
  have hc : ∃ k, c k ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply B2 b hb0
    rw [hQ]; simp [hc]
  obtain ⟨k, hk⟩ := hc
  let V : Submodule ℂ (Fin m × Fin m → ℂ) :=
    Submodule.span ℂ ((fun g (p : Fin m × Fin m) => ⟪c p.1, σ g (a p.2)⟫_ℂ) '' UJset ε)
  have hV : ∀ M ∈ V, IsAvg ε σ (fun w => ∑ i, ∑ j, (M (i, j) * ⟪c j, w⟫_ℂ) • a i) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, hg, rfl⟩ := hM
      have := (A2 _ _ hQavg (A2 _ _ (A1 g hg) hQavg).2).2
      simp only [hQ, map_sum, map_smul, inner_sum, inner_smul_right, Finset.sum_smul] at this
      simpa only [mul_comm] using this
    | zero => simpa using A5
    | add M N _ _ hM hN =>
      simpa only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib] using (A2 _ _ hM hN).1
    | smul t M _ hM =>
      simpa only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, mul_assoc] using A3 t _ hM
  have hN : (fun p : Fin m × Fin m => if p.2 = k then ⟪c p.1, c k⟫_ℂ else 0) ∈ V := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have e : ∀ z : Fin m → H, φ (fun p => ⟪c p.1, z p.2⟫_ℂ) =
        ∑ j, ⟪∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i, z j⟫_ℂ := fun z => by
      rw [LinearMap.pi_apply_eq_sum_univ, Fintype.sum_prod_type, Finset.sum_comm]
      simp [sum_inner, inner_smul_left, mul_comm]
    have hy := eq_zero_of_sum_coef hd ha (y := fun j => ∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i)
      (fun g hg => by rw [← e fun j => σ g (a j)]; exact hφ _ (Submodule.subset_span ⟨g, hg, rfl⟩))
    have := e fun j => if j = k then c k else 0
    simp only [hy, inner_zero_left, Finset.sum_const_zero] at this
    refine Eq.trans (congrArg φ ?_) this
    funext p
    by_cases hp : p.2 = k <;> simp [hp]
  refine ⟨∑ i, ⟪c i, c k⟫_ℂ • a i, c k, fun h0 => hk ?_, hk,
    (kfin ε σ).sum_mem fun i _ => (kfin ε σ).smul_mem _ (haK i), hcK k, ?_⟩
  · have := ha.inner_right_fintype (fun i => ⟪c i, c k⟫_ℂ) k
    rw [h0, inner_zero_right] at this
    exact inner_self_eq_zero.1 this.symm
  · have := hV _ hN
    simp only [ite_mul, zero_mul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simpa only [Finset.smul_sum, smul_smul, mul_comm] using this

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmallOfSmallSec
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.Cartier.CartierDiv

set_option autoImplicit false

namespace GlobalTheory.SmallInduced

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    TrueGeo.valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [TrueGeo.valAt, dif_pos h]
  congr 1
  exact IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec

theorem valAt_mul {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    TrueGeo.valAt y (f * g) = TrueGeo.valAt y f * TrueGeo.valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem valAt_ne_zero {f : Z.functionField} (hf : UnitAt (below y) f) : TrueGeo.valAt y f ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hf
  rw [valAt_algebraMap]
  exact (ha.map _).ne_zero

omit [IsIntegral Z] in

theorem top_le_of_below {U : Z.Opens} (hy : below y ∈ U) : ⊤ ≤ y ⁻¹ᵁ U := fun x _ => by
  have : x = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [this]
  exact hy

theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    TrueGeo.valAt y (fnOf U h a) = valR y U a := by
  rw [← algebraMap_germ hy, valAt_algebraMap, valR, dif_pos (top_le_of_below y hy)]
  have := congrArg (fun φ => φ.hom a) (Scheme.germ_stalkClosedPointTo y U hy)
  exact this

end Val

theorem valR_spMap_comp {R K : Type} [CommRing R] [CommRing K] (φ : R →+* K) {X : Scheme.{0}}
    (x : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valR (spMap φ ≫ x) U a = φ (valR x U a) := by
  rw [← valR_appLE (spMap φ) x h le_top, valR, dif_pos (show ⊤ ≤ spMap φ ⁻¹ᵁ ⊤ from le_top), valR, dif_pos h]
  have := congrArg (fun ψ => ψ.hom ((x.appLE U ⊤ h).hom a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  refine Eq.trans ?_ this
  exact congrArg (fun ψ => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (ψ.hom ((x.appLE U ⊤ h).hom a)))
    (Scheme.Hom.appLE_eq_app (spMap φ) (U := ⊤))

theorem exists_small_of_smallSec : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p), A.n = 1 → A.ci = 0 → A.Induced M L 1 0 → ∀ s ∈ L.smallSec, ∃ f ∈ A.small 1, ∀ x : Y.X, A.D.GeneratesAt x f ↔ M.j x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s := by
  intro F _ _ C Y A M L hn hc ⟨_, r, h, hinf, hfin⟩ s hs
  have hD : (((1 : ℕ+) : ℕ) • A.D) = A.D := one_nsmul _
  have hval {K : Type} [Field K] (y : Sp K ⟶ Y.X) (i : (L.B.pull M.j).ι) (hi : ⊤ ≤ y ⁻¹ᵁ (L.B.pull M.j).U i) :
      valR y _ ((Cartier.secPull s M.j).f i) = valR (y ≫ M.j) _ (s.f (i PUnit.unit)) :=
    valR_appLE y M.j (LB.pull_U M.j i).le hi _
  refine ⟨h.rat (Cartier.secPull s M.j), ⟨?_, fun σ y => ?_, fun v e y => ?_⟩, fun x => ?_⟩
  · change h.rat (Cartier.secPull s M.j) ^ (A.n : ℕ) ∈ Y.H0 (1 • A.D)
    rw [show (A.n : ℕ) = 1 from congrArg _ hn, pow_one]
    exact Var.mem_riemannRochSpace_iff_regularAt_everywhere.2 (mem_sections.1 (h.rat_mem _))
  · obtain ⟨i, hi⟩ := exists_chart h.isLB (under y)
    have hy' : (y.1 ≫ M.j) ≫ M.p = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
      rw [Category.assoc, M.pb.w, ← Category.assoc, y.2, ← Spec.map_comp]
      rfl
    have h1 := hinf σ y ⟨_, hy'⟩ i _ rfl hi (mem_sections.1 (h.rat_mem (Cartier.secPull s M.j)) _)
    have hi' : (⟨_, hy'⟩ : CxPts M.p _) ∈ ptsIn M.p _ (L.B.U (i PUnit.unit)) :=
      mem_ptsIn.2 ((LB.pull_U M.j i).le hi)
    have h2 := hs _ ⟨_, hy'⟩
    rw [(L.φ _).nsq_eq (secVal_mem s) hi'] at h2
    rw [h.rat_mul _ i (gen_mem hi), ratVal_fnOf (mem_ptsIn.2 hi), ev, hval y.1 i (mem_ptsIn.2 hi), hc] at h1
    replace h2 := h1.trans_le h2
    have h3 : (0 : ℝ) ≤ _ := h1.ge.trans' (by positivity)
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul] at h2 h3
    unfold Adl.nrmInf
    rw [hc, hn]
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul, PNat.one_coe, pow_one]
    exact Real.rpow_le_one h3 h2 (by positivity)
  · obtain ⟨yt, hyt, hU⟩ := GlobalTheory.T.valuative_extension_point F Y M v e y
    obtain ⟨j, hj⟩ := exists_chart L.isLB (yt (IsLocalRing.closedPoint e.O))
    obtain ⟨hU1, hU2⟩ := hU _ hj
    let i : (L.B.pull M.j).ι := fun _ => j
    have hi : below y.1 ∈ (L.B.pull M.j).U i := (LB.pull_U M.j i).ge hU2
    have h1 := hfin v e y yt i hyt hU1
    have he : A.D.IsEqn (below y.1) (eqn A.D (below y.1)) := (A.D.exists_isEqn _).choose_spec
    have hr : A.D.IsEqn (below y.1) (r i) := hD ▸ h.isEqn i _ hi
    have hu := he.iff_unitAt.1 hr
    have hreg : RegAt (below y.1) (h.rat (Cartier.secPull s M.j) * (eqn A.D (below y.1) : Y.Fn)) :=
      he.regularAt_iff.1 ((congrArg (fun D => CartierDiv.RegularAt D _ _) hD).mp
        (mem_sections.1 (h.rat_mem (Cartier.secPull s M.j)) _))
    simp only [PNat.one_coe, pow_one, Nat.cast_one, one_mul, Pi.zero_apply, mul_zero, sub_zero,
      Units.val_mul, Units.val_inv_eq_inv_val] at h1
    rw [← div_eq_inv_mul] at h1
    unfold Adl.nrmFin
    rw [hn, h1]
    simp only [PNat.one_coe, pow_one, Nat.cast_one, one_mul, div_one, Real.rpow_one]
    rw [Real.exp_log (e.w.pos (valAt_ne_zero _ hu)), ← map_mul]
    refine (congrArg e.w (valAt_mul _ hreg hu.regAt)).ge.trans ?_
    rw [← mul_eqn_eq, h.rat_mul _ i (gen_mem hi), valAt_fnOf _ hi, hval _ i (top_le_of_below _ hi),
      ← hyt, valR_spMap_comp _ _ hU1]
    exact (e.mem_O _).1 (Subtype.prop _)
  · refine (congrArg (fun D => CartierDiv.GeneratesAt D _ _) hD).symm.to_iff.trans ?_
    rw [h.generatesAt_rat_iff, Cartier.nonzeroLocus_secPull]
    rfl

end GlobalTheory.SmallInduced
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistIndexOfCoefficientFieldPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting.FormsStep.CoverPl

section SlopeTestRemainingChoices

variable {K : Type} [Field K]

def vRing (v : AddValuation K (WithTop ℤ)) : ValuationSubring K where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    show 0 ≤ v (a * b)
    rw [v.map_mul]
    exact add_nonneg ha hb
  one_mem' := by
    show 0 ≤ v 1
    rw [v.map_one]
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (v.map_add a b)
  zero_mem' := by
    show 0 ≤ v 0
    rw [v.map_zero]
    exact le_top
  neg_mem' {a} ha := by
    show 0 ≤ v (-a)
    rw [v.map_neg]
    exact ha
  mem_or_inv_mem' x := by
    by_cases hx : 0 ≤ v x
    · exact Or.inl hx
    · right
      show 0 ≤ v x⁻¹
      by_contra hy
      push_neg at hx hy
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [v.map_zero] at hx
        exact absurd hx (not_lt.mpr le_top)
      have h1 : v x + v x⁻¹ = 0 := by
        rw [← v.map_mul, mul_inv_cancel₀ hx0, v.map_one]
      have h2 : v x + v x⁻¹ ≤ v x + 0 := add_le_add le_rfl hy.le
      rw [add_zero, h1] at h2
      exact absurd hx (not_lt.mpr h2)

theorem v_nonneg_int [NumberField K] (v : AddValuation K (WithTop ℤ)) (a : 𝓞 K) : 0 ≤ v (a : K) := by
  have h1 : IsIntegral ℤ (a : K) := NumberField.RingOfIntegers.isIntegral_coe a
  have h2 : IsIntegral (vRing v) (a : K) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  have h3 : algebraMap (vRing v) K y ∈ vRing v := y.2
  rw [hy] at h3
  exact h3

theorem emb_int_mem [NumberField K] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (e : K →+* FractionRing O) (a : 𝓞 K) : ∃ y : O, algebraMap O (FractionRing O) y = e a := by
  obtain ⟨p, hp, hev⟩ := NumberField.RingOfIntegers.isIntegral_coe a
  have h1 : IsIntegral O (e (a : K)) := by
    refine ⟨p.map (algebraMap ℤ O), hp.map _, ?_⟩
    have hc : (algebraMap O (FractionRing O)).comp (algebraMap ℤ O) = e.comp (algebraMap ℤ K) := RingHom.ext_int _ _
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hev, map_zero]
  exact IsIntegrallyClosed.isIntegral_iff.mp h1

theorem exists_frac_compl {A : Type} [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
    (q : Ideal A) [q.IsPrime] (hq : q ≠ ⊥) (z : K) :
    ∃ a s : A, s ∉ q ∧ (z * algebraMap A K s = algebraMap A K a ∨ z * algebraMap A K a = algebraMap A K s) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective A z
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq (Localization.AtPrime q)
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
    IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
  have hy0 : algebraMap A K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap A (Localization.AtPrime q) x)
    (algebraMap A (Localization.AtPrime q) y)
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl c
  have hs := IsLocalization.mk'_spec (Localization.AtPrime q) a s
  rcases hc with hc | hc
  · have h : x * a = y * s := hinj (by
      rw [map_mul, map_mul, ← hs, ← hc]
      ring)
    refine ⟨a, s, s.2, Or.inr ?_⟩
    rw [div_mul_eq_mul_div, div_eq_iff hy0, ← map_mul, ← map_mul, h, mul_comm]
  · have h : y * a = x * s := hinj (by
      rw [map_mul, map_mul, ← hs, ← hc]
      ring)
    refine ⟨a, s, s.2, Or.inl ?_⟩
    rw [div_mul_eq_mul_div, div_eq_iff hy0, ← map_mul, ← map_mul, ← h, mul_comm]

end SlopeTestRemainingChoices

section Cen

variable {K : Type} [Field K] [NumberField K]

def cen (v : AddValuation K (WithTop ℤ)) : Ideal (𝓞 K) where
  carrier := {a | 0 < v (a : K)}
  add_mem' {a b} ha hb := by
    show 0 < v ((a : K) + (b : K))
    exact lt_of_lt_of_le (lt_min ha hb) (v.map_add _ _)
  zero_mem' := by
    show 0 < v (0 : K)
    rw [v.map_zero]
    exact WithTop.coe_lt_top 0
  smul_mem' c a ha := by
    show 0 < v ((c : K) * (a : K))
    rw [v.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (v_nonneg_int v c))

theorem mem_cen {v : AddValuation K (WithTop ℤ)} {a : 𝓞 K} : a ∈ cen v ↔ 0 < v (a : K) := Iff.rfl

theorem cen_isPrime (v : AddValuation K (WithTop ℤ)) : (cen v).IsPrime where
  ne_top' h := by
    have h1 : (1 : 𝓞 K) ∈ cen v := h ▸ Submodule.mem_top
    change 0 < v (1 : K) at h1
    rw [v.map_one] at h1
    exact lt_irrefl _ h1
  mem_or_mem' {a b} hab := by
    by_contra hn
    push_neg at hn
    have ha : v (a : K) = 0 := le_antisymm (not_lt.mp (fun h => hn.1 h)) (v_nonneg_int v a)
    have hb : v (b : K) = 0 := le_antisymm (not_lt.mp (fun h => hn.2 h)) (v_nonneg_int v b)
    have h := (mem_cen (v := v)).mp hab
    change 0 < v ((a : K) * (b : K)) at h
    rw [v.map_mul, ha, hb, add_zero] at h
    exact lt_irrefl _ h

theorem v_nonneg_iff (v : AddValuation K (WithTop ℤ)) (q : Ideal (𝓞 K)) [q.IsPrime] (hq0 : q ≠ ⊥)
    (hq : ∀ a : 𝓞 K, a ∈ q ↔ 0 < v (a : K)) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (e : K →+* FractionRing O)
    (he : ∀ a : 𝓞 K, a ∈ q ↔ ∃ y ∈ IsLocalRing.maximalIdeal O, algebraMap O (FractionRing O) y = e (a : K)) (x : K) :
    0 ≤ v x ↔ e x ∈ (algebraMap O (FractionRing O)).range := by
  have hφ : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O (FractionRing O)
  have hout : ∀ a : 𝓞 K, a ∉ q → v (a : K) = 0 ∧ ∃ u : O, IsUnit u ∧ algebraMap O (FractionRing O) u = e (a : K) := by
    intro a ha
    refine ⟨le_antisymm (not_lt.mp (fun h => ha ((hq a).mpr h))) (v_nonneg_int v a), ?_⟩
    obtain ⟨u, hu⟩ := emb_int_mem e a
    exact ⟨u, IsLocalRing.notMem_maximalIdeal.mp (fun hm => ha ((he a).mpr ⟨u, hm, hu⟩)), hu⟩
  obtain ⟨a, s, hs, h⟩ := exists_frac_compl q hq0 x
  obtain ⟨hvs, us, hus, hes⟩ := hout s hs
  rcases h with h | h
  · obtain ⟨ua, hua⟩ := emb_int_mem e a
    have h1 : 0 ≤ v x := by
      have h' := congrArg v h
      rw [v.map_mul] at h'
      change v x + v (s : K) = v (a : K) at h'
      rw [hvs, add_zero] at h'
      rw [h']
      exact v_nonneg_int v a
    have h2 : e x ∈ (algebraMap O (FractionRing O)).range := by
      refine ⟨ua * ↑hus.unit⁻¹, ?_⟩
      have h' := congrArg e h
      rw [map_mul] at h'
      change e x * e (s : K) = e (a : K) at h'
      rw [← hes, ← hua] at h'
      rw [map_mul, ← h', mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
    exact ⟨fun _ => h2, fun _ => h1⟩
  · by_cases ha : a ∈ q
    · have hva := (hq a).mp ha
      obtain ⟨ua, hum, hua⟩ := (he a).mp ha
      have h1 : ¬ 0 ≤ v x := by
        intro hx
        have h' := congrArg v h
        rw [v.map_mul] at h'
        change v x + v (a : K) = v (s : K) at h'
        rw [hvs] at h'
        have h3 : 0 < v x + v (a : K) := lt_of_lt_of_le hva (le_add_of_nonneg_left hx)
        rw [h'] at h3
        exact lt_irrefl _ h3
      have h2 : e x ∉ (algebraMap O (FractionRing O)).range := by
        rintro ⟨y, hy⟩
        have h' := congrArg e h
        rw [map_mul] at h'
        change e x * e (a : K) = e (s : K) at h'
        rw [← hy, ← hua, ← hes, ← map_mul] at h'
        have h4 := hφ h'
        apply IsLocalRing.notMem_maximalIdeal.mpr hus
        rw [← h4]
        exact Ideal.mul_mem_left _ y hum
      exact ⟨fun hx => absurd hx h1, fun hx => absurd hx h2⟩
    · obtain ⟨hva, ua, hua', hua⟩ := hout a ha
      have h1 : 0 ≤ v x := by
        have h' := congrArg v h
        rw [v.map_mul] at h'
        change v x + v (a : K) = v (s : K) at h'
        rw [hvs, hva, add_zero] at h'
        rw [h']
      have h2 : e x ∈ (algebraMap O (FractionRing O)).range := by
        refine ⟨us * ↑hua'.unit⁻¹, ?_⟩
        have h' := congrArg e h
        rw [map_mul] at h'
        change e x * e (a : K) = e (s : K) at h'
        rw [← hes, ← hua] at h'
        rw [map_mul, ← h', mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
      exact ⟨fun _ => h2, fun _ => h1⟩

end Cen

section Main

theorem exists_setting_of_place : ∀ (D : D7) (cf : CharFrame D) (b0 b1 : Big D) (Sx : Finset (PlE D.host))
    (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (w : D.what₂.places.Pl), ∃ i, T.l i = D.what₂.places.resChar w ∧
      ∀ x : D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔
        T.emb0 i x ∈ (algebraMap (T.O0 i) (FractionRing (T.O0 i))).range := by
  intro D cf b0 b1 Sx T Sp w
  let v : AddValuation D.LL0 (WithTop ℤ) := (D.what₂.places.val w).comap (algebraMap D.LL0 D.what₂.LL)
  have hv : ∀ x : D.LL0, v x = D.what₂.places.val w (x : D.what₂.LL) := fun x => rfl
  haveI := cen_isPrime v
  have hp := D.what₂.places.resChar_prime w
  have hpc : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.LL0) ∈ cen v := by
    rw [mem_cen, hv]
    have h1 : ((((D.what₂.places.resChar w : ℕ) : 𝓞 D.LL0) : D.LL0) : D.what₂.LL) =
        ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by simp
    rw [h1, D.what₂.places.val_resChar w]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hne : cen v ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpc
    exact hp.ne_zero (by exact_mod_cast hpc)
  let q : HeightOneSpectrum (𝓞 D.LL0) := ⟨cen v, cen_isPrime v, hne⟩
  refine ⟨Sp.eTw.symm q, ?_, ?_⟩
  · obtain ⟨hl, -⟩ := Sp.pl_emb (Sp.eTw.symm q)
    rw [Equiv.apply_symm_apply] at hl
    change _ ∈ cen v at hl
    by_contra hne'
    have hcop : Nat.Coprime (T.l (Sp.eTw.symm q)) (D.what₂.places.resChar w) :=
      (Nat.coprime_primes Fact.out hp).mpr hne'
    obtain ⟨u, u', huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have h1 : (1 : 𝓞 D.LL0) ∈ cen v := by
      have h2 := congrArg (Int.cast : ℤ → 𝓞 D.LL0) huv
      push_cast at h2
      rw [← h2]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hpc)
    exact (cen_isPrime v).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · intro x
    obtain ⟨-, hq⟩ := Sp.pl_emb (Sp.eTw.symm q)
    rw [Equiv.apply_symm_apply] at hq
    exact v_nonneg_iff v (cen v) hne (fun a => mem_cen) (T.emb0 (Sp.eTw.symm q)) hq x

end Main

end GlobalTheory.HeightCounting.FormsStep.CoverPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FifteenNotMemAndDeltaInertiaOrderDividesFifteenP
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.Member.DeltaTame

theorem delta_tame_and_15 : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (P : PlE D.host), P ∈ T.pD i →
    ((15 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P → ∀ σ ∈ Ine (F := D.host.E) A,
      ∃ N : ℕ, T.delta i σ ^ (15 ^ N) = 1 := by
  intro D T i P hP
  refine ⟨?_, ?_⟩
  · intro h15
    have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := Ideal.absNorm_mem _
    have hmod := T.delta_tame i P hP
    have hdecomp : Ideal.absNorm P.asIdeal = 15 * (Ideal.absNorm P.asIdeal / 15) + 1 := by
      have := Nat.div_add_mod (Ideal.absNorm P.asIdeal) 15
      omega
    rw [hdecomp] at hmem
    push_cast at hmem h15
    have h1 : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
      have hm2 : (15 : 𝓞 D.host.E) * ((Ideal.absNorm P.asIdeal / 15 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal :=
        P.asIdeal.mul_mem_right _ h15
      have := P.asIdeal.sub_mem hmem hm2
      simpa using this
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · intro A hA σ hσ
    have h15 := T.delta_15 i P hP A hA
    have hfin : Finite ((Ine (F := D.host.E) A).map (T.delta i)) :=
      Nat.finite_of_card_ne_zero (by rw [h15]; norm_num)
    have hpow := pow_card_eq_one' (G := (Ine (F := D.host.E) A).map (T.delta i))
      (x := ⟨T.delta i σ, Subgroup.mem_map_of_mem _ hσ⟩)
    rw [h15] at hpow
    refine ⟨1, ?_⟩
    have := congrArg Subtype.val hpow
    simpa using this

end GlobalTheory.Member.DeltaTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteExceptionalPlacesOverPrimeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_exceptional_places_over_prime : ∀ (D : D7) (l : ℕ), l.Prime → ∃ F : Finset (PlE D.host), ∀ v, v ∉ F → v ∉ placesOver D.host.E l ∧ v ∉ placesS D l := by
  first | exact @GlobalTheory.PlacesExc.finite_exceptional | exact GlobalTheory.PlacesExc.finite_exceptional | (intros; apply GlobalTheory.PlacesExc.finite_exceptional <;> assumption)
end

