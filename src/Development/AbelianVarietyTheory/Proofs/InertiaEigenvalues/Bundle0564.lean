import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0555
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0551
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0539
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0529
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerInversePowerSeriesEvalOneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerInverse_powerSeries_eval_one : ∀ {ι : Type} [Fintype ι] (c : ℕ → ℂ), (Summable fun d => ‖c d‖) → ∀ (Q : ι → ℂ),
    PowerSeries.mk c * ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) = 1 →
    (∏ p, (1 - Q p)) ≠ 0 ∧ HasSum c (∏ p, (1 - Q p))⁻¹ := by
  first | exact @GlobalTheory.JSW.eulerInverse_eval_one | exact GlobalTheory.JSW.eulerInverse_eval_one | (intros; apply GlobalTheory.JSW.eulerInverse_eval_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EvaluationPowerSeriesShift
section
namespace GlobalTheory.DiscEval

open PowerSeries Finset

variable {p : ℕ} {A K C B : Type*} [CommRing A] [CommRing K] [CommRing C] [CommRing B]
  {i : C →+* B} {κ : K →+* B} {a : A →+* K}

theorem OnDisc.shiftSeries {L : PowerSeries K} (hL : OnDisc p a L) :
    OnDisc p a (PowerSeries.mk fun k => coeff (k + 1) L) := fun M hM => by
  obtain ⟨D, hD⟩ := hL M hM
  refine ⟨D + 1, fun k => ?_⟩
  obtain ⟨b, hb⟩ := hD (k + 1)
  have h1 : D + (k + 1) / M ≤ D + 1 + k / M := by
    rw [Nat.succ_div]
    split_ifs <;> omega
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le h1
  refine ⟨(p : A) ^ e * b, ?_⟩
  rw [coeff_mk, he, pow_add, map_mul, map_pow, map_natCast, ← hb]
  ring

theorem Tends.shiftIndex {s : ℕ → B} {y : B} (h : Tends p i s y) : Tends p i (fun n => s (n + 1)) y :=
  fun r => (h r).imp fun N hN n hn => hN (n + 1) (by omega)

theorem psum_succ_shift (L : PowerSeries K) (x : B) (n : ℕ) :
    psum κ L x (n + 1) = κ (coeff 0 L) + x * psum κ (PowerSeries.mk fun k => coeff (k + 1) L) x n := by
  have e : ∀ k ∈ range n, κ (coeff (k + 1) L) * x ^ (k + 1) =
      x * (κ (coeff k (PowerSeries.mk fun k => coeff (k + 1) L)) * x ^ k) := fun k _ => by
    rw [coeff_mk, pow_succ]
    ring
  rw [psum, psum, sum_range_succ', sum_congr rfl e, ← Finset.mul_sum, pow_zero, mul_one, add_comm]

theorem IsEval.shift [IsHausdorff (Ideal.span {(p : C)}) C] (hi : Function.Injective i) (hp : IsUnit (p : B))
    {L : PowerSeries K} {x : C} {y u : B} (h : IsEval p i κ L (i x) y)
    (hu : IsEval p i κ (PowerSeries.mk fun k => coeff (k + 1) L) (i x) u) :
    y = κ (coeff 0 L) + i x * u := by
  have h1 : Tends p i (fun n => psum κ L (i x) (n + 1)) (κ (coeff 0 L) + i x * u) := by
    have := Tends.add (Tends.const (p := p) (i := i) (κ (coeff 0 L)))
      (Tends.mul_left hp ⟨0, x, by rw [pow_zero, one_mul]⟩ hu)
    simpa only [psum_succ_shift] using this
  exact Tends.unique hi (Tends.shiftIndex h) h1

end GlobalTheory.DiscEval

namespace GlobalTheory.AcrisK

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

theorem ev_shift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (L : PowerSeries ↥K.1), OnDisc l (oK K) L →
    ∀ (x : AK K), thetaK K x = 0 → ∀ y : GlobalTheory.AcrisK.BK K, Ev L x y →
    ∃ (L' : PowerSeries ↥K.1) (u : GlobalTheory.AcrisK.BK K), OnDisc l (oK K) L' ∧
      (∀ k, PowerSeries.coeff k L' = PowerSeries.coeff (k + 1) L) ∧ Ev L' x u ∧
      y = inK K (PowerSeries.coeff 0 L) + toB K (ofA K x) * u := by
  intro l _ K L hL x hx y hy
  have hL' := OnDisc.shiftSeries hL
  obtain ⟨u, hu, -⟩ := existsUnique_ev hL' hx
  exact ⟨_, u, hL', fun k => PowerSeries.coeff_mk _ _, hu,
    IsEval.shift (toB_injective K) (isUnit_l K) hy hu⟩

end GlobalTheory.AcrisK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAbelianizedGaloisHomOfClosureIso
section
open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeGal

def conjGal {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']
    (φ : Ω ≃+* Ω') (j : E →+* E') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) :
    (Ω' ≃ₐ[E'] Ω') →* (Ω ≃ₐ[E] Ω) where
  toFun τ :=
    { toRingEquiv := (φ.trans τ.toRingEquiv).trans φ.symm
      commutes' := fun x => by
        show φ.symm (τ (φ (algebraMap E Ω x))) = algebraMap E Ω x
        rw [hφ, AlgEquiv.commutes, ← hφ, RingEquiv.symm_apply_apply] }
  map_one' := by
    ext z
    show φ.symm (φ z) = z
    exact φ.symm_apply_apply z
  map_mul' τ τ' := by
    ext z
    show φ.symm ((τ * τ') (φ z)) = φ.symm (τ (φ (φ.symm (τ' (φ z)))))
    rw [RingEquiv.apply_symm_apply]
    rfl

theorem conjGal_apply {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']
    (φ : Ω ≃+* Ω') (j : E →+* E') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x))
    (τ : Ω' ≃ₐ[E'] Ω') (z : Ω) : conjGal φ j hφ τ z = φ.symm (τ (φ z)) := rfl

theorem exists_abHom_of_ringEquiv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    (φ : Ω ≃+* Ω') (j : E →+* E'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) →
    ∃ ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω, Continuous ρ ∧
      ∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) →
        ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  intro E Ω _ _ _ _ _ E' Ω' _ _ _ _ _ φ j hφ
  haveI : Algebra.IsIntegral E' Ω' := (IsAlgClosure.isAlgebraic (R := E') (K := Ω')).isIntegral
  haveI : IsClosed ((commutator (Formalism.ConjugateSelfDual.G E Ω)).topologicalClosure : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  let c := conjGal φ j hφ
  have hc : Continuous c :=
    continuous_galHom_of_fix c fun y => ⟨φ y, fun τ hτ => by
      rw [conjGal_apply, hτ, RingEquiv.symm_apply_apply]⟩
  let r : Formalism.ConjugateSelfDual.G E' Ω' →* Gab E Ω := (toAb E Ω).comp c
  have hr : Continuous r := QuotientGroup.continuous_mk.comp hc
  refine ⟨liftAb r hr, continuous_liftAb r hr, fun τ σ h => ?_⟩
  rw [liftAb_toAb]
  show toAb E Ω (c τ) = toAb E Ω σ
  congr 1
  ext z
  rw [conjGal_apply, ← h, RingEquiv.symm_apply_apply]

end GlobalTheory.HeckeGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompatiblePowerSeriesValue
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.FrobChainSeries

open Finset

section General

variable {A R : Type*} [CommRing A] [CommRing R]

theorem dvd_of_limit (w L : A) (b : ℕ → A) (hL : ∀ n, L - ∑ i ∈ range n, w ^ i * b i ∈ Ideal.span {w ^ n})
    (M : ℕ) : w ^ M ∣ L - ∑ j ∈ range M, b j * w ^ j := by
  have h := Ideal.mem_span_singleton.1 (hL M)
  rwa [Finset.sum_congr rfl (fun i _ => mul_comm (w ^ i) (b i))] at h

theorem chain_dvd (φ : A →+* A) (hφ : Function.Bijective φ) (ι : R →+* A) (hι : ∀ c, φ (ι c) = ι c)
    (ω y : ℕ → A) (c : ℕ → R) (hω : ∀ n, φ (ω (n + 1)) = ω n) (hy : ∀ n, φ (y (n + 1)) = y n)
    (h0 : ∀ M, ω 0 ^ M ∣ y 0 - ∑ j ∈ range M, ι (c j) * ω 0 ^ j) :
    ∀ n M, ω n ^ M ∣ y n - ∑ j ∈ range M, ι (c j) * ω n ^ j := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    intro M
    obtain ⟨z, hz⟩ := ih M
    obtain ⟨z', rfl⟩ := hφ.2 z
    refine ⟨z', hφ.1 ?_⟩
    simp only [map_sub, map_sum, map_mul, map_pow, hι, hω, hy]
    exact hz

end General

section OC

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.LTTilt

variable {l : ℕ} [Fact l.Prime]

theorem one_le_norm_of_isUnit {c : OC l} (h : IsUnit c) : 1 ≤ ‖(c : ℂ_[l])‖ := by
  obtain ⟨d, hd⟩ := h.exists_right_inv
  have e : ‖(c : ℂ_[l])‖ * ‖(d : ℂ_[l])‖ = 1 := by
    rw [← norm_mul]
    have : (c : ℂ_[l]) * (d : ℂ_[l]) = 1 := congrArg Subtype.val hd
    rw [this, norm_one]
  have hd1 := norm_OC_le_one d
  nlinarith [norm_nonneg (c : ℂ_[l]), norm_nonneg (d : ℂ_[l])]

theorem eq_of_norm_le {x u : ℂ_[l]} {a : ℝ} (ha : a < 1)
    (h : ∀ M : ℕ, ‖x - u‖ ≤ 2 * a ^ M) : x = u := by
  have ha0 : 0 ≤ a := by
    have h1 := h 1
    rw [pow_one] at h1
    linarith [norm_nonneg (x - u)]
  have hlim : Filter.Tendsto (fun M : ℕ => 2 * a ^ M) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha).const_mul 2
  have := ge_of_tendsto' hlim h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem eval_eq {A R : Type*} [CommRing A] [CommRing R] (θ : A →+* OC l) (ι : R →+* A) (a : R →+* OC l)
    (hθι : ∀ c, θ (ι c) = a c) (w y : A) (c : ℕ → R) (u : OC l) (hw : ‖(θ w : ℂ_[l])‖ < 1)
    (hS : HasSum (fun i => ((a (c i) * θ w ^ i : OC l) : ℂ_[l])) (u : ℂ_[l]))
    (hd : ∀ M, w ^ M ∣ y - ∑ j ∈ range M, ι (c j) * w ^ j) : θ y = u := by
  refine Subtype.ext (eq_of_norm_le hw fun M => ?_)
  obtain ⟨z, hz⟩ := hd M
  have h1 : θ y - ∑ j ∈ range M, a (c j) * θ w ^ j = θ w ^ M * θ z := by
    have := congrArg θ hz
    simpa only [map_sub, map_sum, map_mul, map_pow, hθι] using this
  have h2 : ‖(θ y : ℂ_[l]) - ((∑ j ∈ range M, a (c j) * θ w ^ j : OC l) : ℂ_[l])‖ ≤ ‖(θ w : ℂ_[l])‖ ^ M := by
    have e : (θ y : ℂ_[l]) - ((∑ j ∈ range M, a (c j) * θ w ^ j : OC l) : ℂ_[l]) =
        (((θ w ^ M * θ z : OC l)) : ℂ_[l]) := by rw [← h1]; push_cast; rfl
    rw [e]
    push_cast
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (norm_OC_le_one _)
  have h3 := norm_tail_le (fun i => a (c i)) (θ w) (u : ℂ_[l]) hS M
  have h4 := norm_sub_le_norm_sub_add_norm_sub (θ y : ℂ_[l])
    ((∑ j ∈ range M, a (c j) * θ w ^ j : OC l) : ℂ_[l]) (u : ℂ_[l])
  rw [norm_sub_rev (((∑ j ∈ range M, a (c j) * θ w ^ j : OC l) : ℂ_[l]))] at h4
  linarith

end OC

end GlobalTheory.FrobChainSeries

open GlobalTheory.FrobChainSeries in

theorem GlobalTheory.FrobChainSeries.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ω : ℕ → AK K) (G : PowerSeries ↥(OL K)) (u : ℕ → OC l),
    (∀ n, frobq K (ω (n + 1)) = ω n) → (∀ n, ‖((thetaK K (ω n) : OC l) : ℂ_[l])‖ < 1) →
    (∀ n, HasSum (fun i => ((intToOC K (PowerSeries.coeff i G) * thetaK K (ω n) ^ i : OC l) : ℂ_[l])) (u n : ℂ_[l])) →
    ∃ y : ℕ → AK K, (∀ n, frobq K (y (n + 1)) = y n) ∧ (∀ n, thetaK K (y n) = u n) ∧
      ∀ M : ℕ, ω 0 ^ M ∣ y 0 - ∑ j ∈ Finset.range M, inO K (PowerSeries.coeff j G) * ω 0 ^ j := by
  intro l _ K ω G u hω hθ hS
  have hnu : ¬ IsUnit (red K (ω 0)) := fun h =>
    absurd (hθ 0) (not_lt.2 (one_le_norm_of_isUnit (((isUnit_iff_red _).2 h).map (thetaK K))))
  haveI := complete_single hnu
  obtain ⟨L, hL⟩ := GlobalTheory.Per.AinfComplete.summ_of_precomplete (ω 0) (fun i => inO K (PowerSeries.coeff i G))
  let r := Function.surjInv (frobq_bijective K).2
  have hy : ∀ n, frobq K (r^[n + 1] L) = r^[n] L := fun n => by
    rw [Function.iterate_succ_apply']
    exact Function.surjInv_eq (frobq_bijective K).2 _
  have hd := chain_dvd (frobq K).toRingHom (frobq_bijective K) (inO K) (frobq_inO K) ω (fun n => r^[n] L)
    (fun j => PowerSeries.coeff j G) hω hy (dvd_of_limit (ω 0) L _ hL)
  exact ⟨fun n => r^[n] L, hy, fun n => eval_eq (thetaK K) (inO K) (intToOC K) (thetaK_inO (K := K)) (ω n) _ _ (u n)
    (hθ n) (hS n) (hd n), hd 0⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalCharacterOfRegularCharacterGLnStatement
section
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspidalCharacter_of_regularCharacter_GLn : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K], Module.finrank (ZMod g) K = d → ∃ τ : (Kˣ →* ℂˣ) → Gn g d → ℂ, (∀ θ, IsRegularChar g d θ → IsCusp (τ θ) ∧ τ θ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ∧ ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g d).charpoly = 0 → τ θ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)) ∧ (∀ θ θ', IsRegularChar g d θ → IsRegularChar g d θ' → (τ θ = τ θ' ↔ ∃ i < d, θ' = θ ^ g ^ i)) := by
  first | exact @GlobalTheory.GreenRegular.exists_cusp_of_regular | exact GlobalTheory.GreenRegular.exists_cusp_of_regular | (intros; apply GlobalTheory.GreenRegular.exists_cusp_of_regular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicPeriodLocalPrimeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomic_period_local_prime : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (n : ℕ), 0 < n → ∃ x : P.R.B, IsUnit x ∧ (⇑P.φB)^[n] x = (l : P.R.B) * x ∧ P.ιB x ∈ (P.PD K).Fil 1 ∧ P.ιB x ∉ (P.PD K).Fil 2 ∧ ∀ j : ℕ, 0 < j → j < n → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1 := by
  first | exact @GlobalTheory.LTPeriod.main | exact GlobalTheory.LTPeriod.main | (intros; apply GlobalTheory.LTPeriod.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusLiftLubinTate
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ColmezLift

variable {A : Type} [CommRing A]

theorem pow_q_dvd {l : ℕ} [Fact l.Prime] {p : A} (hl : (l : A) ∈ Ideal.span {p}) {f : ℕ} (hf : 1 ≤ f)
    {a b : A} {n : ℕ} (h : p ^ (n + 1) ∣ a - b) : p ^ (n + 1 + 1) ∣ a ^ l ^ f - b ^ l ^ f := by
  have h1 : a ^ l - b ^ l ∈ Ideal.span {p} ^ (n + 1 + 1) :=
    GlobalTheory.LTTilt.pow_l_sub_mem _ hl (by omega) (by rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]; exact h)
  have h2 := GlobalTheory.LTTilt.pow_sub_mem _ h1 (l ^ (f - 1))
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← pow_mul, ← pow_mul, ← pow_succ'] at h2
  rwa [show f - 1 + 1 = f by omega] at h2

def phi (p : A) (ψ : A ≃+* A) (q : ℕ) (y : A) : A := ψ.symm (p * y + y ^ q)

theorem exists_fix (p : A) [IsAdicComplete (Ideal.span {p}) A] (l : ℕ) [Fact l.Prime]
    (hl : (l : A) ∈ Ideal.span {p}) (f : ℕ) (hf : 1 ≤ f) (ψ : A ≃+* A) (hψp : ψ p = p)
    (hψ : ∀ a, p ∣ ψ a - a ^ l ^ f) (y0 : A) : ∃ ω, p ∣ ω - y0 ∧ ψ ω = p * ω + ω ^ l ^ f := by
  have hsp : ψ.symm p = p := (ψ.symm_apply_eq).2 hψp.symm
  have hsd : ∀ {n : ℕ} {a : A}, p ^ n ∣ a → p ^ n ∣ ψ.symm a := fun {n a} ⟨c, hc⟩ =>
    ⟨ψ.symm c, by rw [hc, map_mul, map_pow, hsp]⟩
  have hΦ : ∀ (n : ℕ) (a b : A), p ^ (n + 1) ∣ a - b →
      p ^ (n + 1 + 1) ∣ phi p ψ (l ^ f) a - phi p ψ (l ^ f) b := by
    intro n a b h
    have e : phi p ψ (l ^ f) a - phi p ψ (l ^ f) b =
        ψ.symm (p * (a - b) + (a ^ l ^ f - b ^ l ^ f)) := by
      rw [phi, phi, ← map_sub]; congr 1; ring
    rw [e]
    exact hsd (dvd_add (by rw [pow_succ']; exact mul_dvd_mul_left p h) (pow_q_dvd hl hf h))
  have hΦ' : ∀ (n : ℕ) (a b : A), p ^ n ∣ a - b → p ^ n ∣ phi p ψ (l ^ f) a - phi p ψ (l ^ f) b := by
    intro n a b h
    cases n with
    | zero => rw [pow_zero]; exact one_dvd _
    | succ k => exact (pow_dvd_pow p (by omega)).trans (hΦ k a b h)
  have h1 : ∀ y, p ∣ phi p ψ (l ^ f) y - y := by
    intro y
    obtain ⟨c, hc⟩ := hψ y
    have e : phi p ψ (l ^ f) y - y = ψ.symm (p * (y - c)) := by
      rw [phi, ← (ψ.symm_apply_apply y), ← map_sub, ψ.symm_apply_apply]
      congr 1
      linear_combination -hc
    rw [e]
    rw [map_mul, hsp]
    exact dvd_mul_right p _
  let y : ℕ → A := fun n => (phi p ψ (l ^ f))^[n] y0
  have hy : ∀ n, y (n + 1) = phi p ψ (l ^ f) (y n) := fun n => Function.iterate_succ_apply' _ n y0
  have hstep : ∀ n, p ^ (n + 1) ∣ y (n + 1) - y n := by
    intro n
    induction n with
    | zero => rw [zero_add, pow_one, hy]; exact h1 _
    | succ n ih => have h := hΦ n _ _ ih; rwa [← hy, ← hy] at h
  have hcauchy : ∀ m k, p ^ m ∣ y m - y (m + k) := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : y m - y (m + (k + 1)) = (y m - y (m + k)) - (y (m + k + 1) - y (m + k)) := by
        rw [← add_assoc]; ring
      rw [e]
      exact dvd_sub ih ((pow_dvd_pow p (by omega)).trans (hstep (m + k)))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {p}) y fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact hcauchy m k
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hL
  have hfix : phi p ψ (l ^ f) L = L := by
    refine sub_eq_zero.1 (GlobalTheory.Per.AinfComplete.eq_zero_of_haus p _ fun n => Ideal.mem_span_singleton.2 ?_)
    have e : phi p ψ (l ^ f) L - L = (y (n + 1) - L) - (phi p ψ (l ^ f) (y n) - phi p ψ (l ^ f) L) := by
      rw [hy]; ring
    rw [e]
    exact dvd_sub ((pow_dvd_pow p n.le_succ).trans (hL (n + 1))) (hΦ' n _ _ (hL n))
  refine ⟨L, ?_, ?_⟩
  · have e : L - y0 = (y 1 - y 0) - (y 1 - L) := by simp [y]
    rw [e]
    exact dvd_sub (by simpa using hstep 0) (by simpa using hL 1)
  · exact ((ψ.symm_apply_eq).1 hfix).symm

open GlobalTheory.AinfK in

theorem exists_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ x : OCb l,
    ∃ ω : AK K, red K ω = x ∧ frobq K ω = inO K π * ω + ω ^ l ^ fK K := by
  intro l _ K π hπ x
  haveI := complete_pi hπ
  obtain ⟨ω, h1, h2⟩ := exists_fix (inO K π) l (Ideal.mem_span_singleton.2 (dvd_l hπ)) (fK K)
    (NeZero.pos (fK K)) (RingEquiv.ofBijective (frobq K) (frobq_bijective K)) (frobq_inO K π)
    (dvd_frobq_sub hπ) (inA K (WittVector.teichmuller l x))
  exact ⟨ω, ((red_eq_iff hπ _ _).2 h1).trans (red_teich x), h2⟩

end GlobalTheory.ColmezLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisAtEmbedding
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.HodgeAt

set_option maxHeartbeats 1000000 in

theorem exists_hodge_at_embedding : ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → Formalism.MainNotions.N.IsDR (P.PD K) R → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (σ : GQ l), (∀ x : ↥K.1, σ ((τ x : ↥L.1) : Om l) = (x : Om l)) → ∃ (K' : FinExt l) (H : Hodge C ξ (fun g => (r g).val.map fun x => σ (x : Om l)) K'), K.1 ≤ K'.1 ∧ ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = multV (P.PD K) R τ n := by
  intro l _ K L P AI T C hC ξ hξ a r R hR hDR τ σ hσ
  haveI := K.2
  haveI := L.2
  haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI T K L (Fin a → ↥L.1) R).1
  obtain ⟨m, d, k, hA⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (GlobalTheory.DRFil.isField_dR T) R
    (GlobalTheory.DRFil.filSpans T K L R hDR) τ
  obtain ⟨K', hKK', hK'⟩ := exists_ext_fixing l K L σ
  obtain ⟨e, he1, he0⟩ := GlobalTheory.T.exists_bdR_element_normalized_killing_phi_kernel l P σ L a
  have hid := phiS_idem l P K L τ σ hσ
  set w : Fin m → Fin a → P.R.BdR := fun i => PhiS P σ L a (d i) with hw
  have hfil : ∀ i j, w i j ∈ (P.PD K).Fil (k i) := fun i j =>
    phiS_mem_Fil l P AI T K L σ (k i) _ (GlobalTheory.DRFil.ext_mem_FilV (P.PD K) _ (hA.mem i).2)
  have hind : ∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0 := by
    intro β hβ
    have h0 : ∑ i, GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) (e * ((1 : ↥L.1) ⊗ₜ β i)) (d i) = 0 := by
      simp only [GlobalTheory.DRFil.sm_mul, GlobalTheory.DRFil.sm_one_tmul, ← map_sum]
      apply he0
      rw [PhiS_sum]
      simp only [PhiS_mulR]
      rw [← hβ]
      funext j
      simp [hw]
    funext i
    have := congrArg (phiS P σ L) (hA.indep _ h0 i)
    simpa [map_mul, hid, he1, phiS_tmul] using this
  have hspan : ∀ j, ∃ u : Fin m → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1 := by
    intro j
    obtain ⟨rr, hrr, hy⟩ := hA.span 0 (Pi.single j 1 ⊗ₜ (1 : P.R.BdR))
      (GlobalTheory.DRFil.tmul_mem_FilV (P.PD K) _ (P.PD K).one_mem)
    refine ⟨fun i => phiS P σ L (rr i), fun i => by simpa using phiS_mem_Fil l P AI T K L σ _ _ (hrr i), ?_⟩
    have h2 := congrArg (PhiS P σ L a) hy
    rw [PhiS_sm] at h2
    simp only [hid, one_mul, PhiS_sum, PhiS_sm] at h2
    have h3 : ∑ i, (fun i => phiS P σ L (rr i)) i • w i = ∑ x, fun i => phiS P σ L (rr x) * PhiS P σ L a (d x) i := rfl
    rw [h3, ← h2, PhiS_tmul]
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_eq_of_ne hij]
  have hinv : ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i,
      ((fun g => (r g).val.map fun x => σ (x : Om l)) g).map (algebraMap (Om l) P.R.BdR) *ᵥ
        (fun j => P.actQdR (g : GQ l) (w i j)) = w i := by
    intro g hg i
    have h1 := GlobalTheory.T.tensorDeRhamCoordMul_galois_action l P K L σ a r R hR g (fun y => hK' g hg y) (d i)
    rw [(GlobalTheory.DRFil.mem_DdR (P.PD K) R _).1 (hA.mem i).1.1 g] at h1
    rw [Matrix.map_map]
    exact h1.symm
  have hma := GlobalTheory.T.card_eq_of_linIndep_spanning_deRham l P AI T a m w hind (fun j => (hspan j).imp fun u hu => hu.2)
  subst hma
  obtain ⟨H, hH⟩ := GlobalTheory.T.hodge_basis_of_adapted_invariant_family l P AI T C hC ξ hξ K K' m _ w k hfil hspan hinv
  exact ⟨K', H, hKK', fun n => by rw [hH n, hA.multV_eq]⟩

end GlobalTheory.HodgeAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwOfFonOfCmpOfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hwOf_fonOf_cmpOf' : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) → (∀ (l : ℕ) [Fact l.Prime], WachEx (A l)) → ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) := by
  first | exact @GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf | exact GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf | (intros; apply GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableDiscCocycleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semistable_disc_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsUnit Z → IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA → ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (Per.σA (g : GQ l)) G → ∃ e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * e) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) ∧ bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (Y.map bk.iA * e) = bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA * (Y.map (Per.σA (g : GQ l))).map bk.iA) := by
  first | (exact @GlobalTheory.BKLim.WSeed.exists_disc_cocycle) | (exact GlobalTheory.BKLim.WSeed.exists_disc_cocycle) | (intros; apply GlobalTheory.BKLim.WSeed.exists_disc_cocycle  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltZerosUntiltFrobeniusDoubleSeriesStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tilt_zeros_untiltFrobeniusDoubleSeries : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 2 ≤ h → μ ≠ 0 → ∃ y : Fin h → ℕ → Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧ ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0 := by
  first | exact @GlobalTheory.PSerExist.exists_zeros | exact GlobalTheory.PSerExist.exists_zeros | (intros; apply GlobalTheory.PSerExist.exists_zeros <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsXPowSmulMemWachModuleOfFrobeniusStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_X_pow_smul_mem_wachModule_of_frobenius : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → ∃ a : ℕ, W.X ^ a • m ∈ W.N T := by
  first | exact @GlobalTheory.NL.DenomStep.main | exact GlobalTheory.NL.DenomStep.main | (intros; apply GlobalTheory.NL.DenomStep.main <;> assumption)
end

