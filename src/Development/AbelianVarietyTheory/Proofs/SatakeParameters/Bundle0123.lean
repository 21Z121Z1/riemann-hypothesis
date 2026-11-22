import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0115
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0116
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0005
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.Bundle0002
import Formalism.GaussJetBounds.GaussJetProofs.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualLocalBasesPairDualModRootMinusD
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem pair_value_eq {D : D7} {p : ℕ} [Fact p.Prime] {ι : ℂ ≃+* ℂ_[p]} {th : ℂ_[p]} (hth : th ≠ 0)
    {z₁ z₂ : Bool × HH D} {s₁ s₂ : D.host.E} (h₁ : ‖rho D ι z₁ s₁‖ = 1) (h₂ : ‖rho D ι z₂ s₂‖ = 1)
    (hc : ‖rho D ι z₁ (D.host.conj s₂) - rho D ι z₂ s₂‖ ≤ ‖th‖) {N : ℕ} {a b : Fin N} {X : D.host.E}
    (hX : X = s₁ * D.host.conj s₂ * (if a = b then 1 else 0)) :
    ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ (rho D ι z₁ s₁)⁻¹ * rho D ι z₁ X * (rho D ι z₂ s₂)⁻¹ =
      (if a = b then 1 else 0) + th * e := by
  have n₁ : rho D ι z₁ s₁ ≠ 0 := fun h => by simp [h] at h₁
  have n₂ : rho D ι z₂ s₂ ≠ 0 := fun h => by simp [h] at h₂
  by_cases hab : a = b
  · refine ⟨(rho D ι z₁ (D.host.conj s₂) - rho D ι z₂ s₂) / (rho D ι z₂ s₂ * th), ?_, ?_⟩
    · rw [norm_div, norm_mul, h₂, one_mul]
      exact div_le_one_of_le₀ hc (norm_nonneg _)
    · subst hX
      simp only [hab, if_true, mul_one, map_mul]
      field_simp
      ring
  · refine ⟨0, by simp, ?_⟩
    subst hX
    simp [hab]

theorem sum_pc_pc {D : D7} {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N : ℕ}
    (σ : Bool × HH D → 𝓞 D.host.E) (z₁ z₂ : Bool × HH D) (a₁ a₂ : Fin N)
    (F : (Bool × HH D) × Fin N → (Bool × HH D) × Fin N → ℂ_[p]) :
    ∑ l, ∑ l₂, pc D ι σ z₁ l a₁ * F l l₂ * pc D ι σ z₂ l₂ a₂ =
      (rho D ι z₁ (σ z₁ : D.host.E))⁻¹ * F (z₁, a₁) (z₂, a₂) * (rho D ι z₂ (σ z₂ : D.host.E))⁻¹ := by
  rw [Finset.sum_eq_single (z₁, a₁), Finset.sum_eq_single (z₂, a₂)]
  · simp [pc]
  · intro b _ hb; simp [pc, hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [pc, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem dual_local_bases_pair : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (th : ℂ_[p]), th ≠ 0 → (∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖th‖) → ∀ {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (σ : Bool × HH D → 𝓞 D.host.E), (∀ z, ‖GlobalTheory.DFrame.rho D ι z (σ z : D.host.E)‖ = 1) → (∀ t, ((P (tauPl D (true, t))).map D.host.conj).transpose * P (tauPl D (false, t)) = 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) ∧ (∀ (t : HH D) (b₁ b₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P σ r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P σ r₂ i)) * GlobalTheory.DFrame.pc D ι σ (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) := by
  intro D p _ ι th hth h2 N P σ hσ hP
  have key : ∀ t : HH D, (P (tauPl D (false, t)))⁻¹ = ((P (tauPl D (true, t))).map D.host.conj).transpose ∧
      (P (tauPl D (true, t)))⁻¹ * P (tauPl D (true, t)) = 1 := by
    intro t
    have h := hP t
    refine ⟨Matrix.inv_eq_left_inv h, ?_⟩
    apply Matrix.nonsing_inv_mul
    have hd := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
    have hd' : (P (tauPl D (true, t))).det ≠ 0 := by
      intro h0
      have : ((P (tauPl D (true, t))).map D.host.conj).det = D.host.conj (P (tauPl D (true, t))).det := by
        simpa using (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) (P (tauPl D (true, t)))).symm
      rw [this, h0] at hd
      simp at hd
    exact isUnit_iff_ne_zero.mpr hd'
  refine ⟨fun t a₁ a₂ => ?_, fun t b₁ b₂ => ?_⟩
  · rw [sum_pc_pc ι σ (false, t) (true, t) a₁ a₂
      (fun l l₂ => rho D ι (false, t) (∑ j, rowL D P σ l j * D.host.conj (rowL D P σ l₂ j)))]
    refine pair_value_eq hth (hσ _) (hσ _) (h2 t (σ (true, t))) ?_
    obtain ⟨k₁, k₂⟩ := key t
    have e := congrFun (congrFun k₂ a₂) a₁
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    have e' := congrArg D.host.conj e
    simp only [rowL, k₁, map_mul, map_sum, Matrix.transpose_apply, Matrix.map_apply] at e' ⊢
    have e'' : D.host.conj (if a₂ = a₁ then 1 else 0) = if a₁ = a₂ then 1 else 0 := by
      by_cases h : a₁ = a₂
      · simp [h]
      · simp [h, Ne.symm h]
    rw [← e'', ← e', Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  · rw [sum_pc_pc ι σ (false, t) (true, t) b₁ b₂
      (fun l l₂ => rho D ι (false, t) (∑ i, colR D P σ l i * D.host.conj (colR D P σ l₂ i)))]
    refine pair_value_eq hth (hσ _) (hσ _) (h2 t (σ (true, t))) ?_
    have e := congrFun (congrFun (hP t) b₂) b₁
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    simp only [Matrix.transpose_apply, Matrix.map_apply] at e
    simp only [colR, map_mul]
    have e'' : (if b₂ = b₁ then (1 : D.host.E) else 0) = if b₁ = b₂ then 1 else 0 := by
      by_cases h : b₁ = b₂
      · simp [h]
      · simp [h, Ne.symm h]
    rw [← e'', ← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.DFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletedLatticeBasisAtPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatLocBasis

noncomputable abbrev locRing {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Subalgebra (𝓞 E) E :=
  Localization.subalgebra.ofField E P.asIdeal.primeCompl P.asIdeal.primeCompl_le_nonZeroDivisors

theorem exists_gens {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ b : Fin n → Fin n → E, (∀ i, b i ∈ Submodule.span (locRing P) (L : Set (Fin n → E))) ∧
      ∀ x ∈ L, ∃ c : Fin n → locRing P, ∀ a, x a = ∑ i, (c i : E) * b i a := by
  have : IsLocalization.AtPrime (locRing P) P.asIdeal :=
    Localization.subalgebra.isLocalization_ofField E _ _
  have : IsDiscreteValuationRing (locRing P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) P.ne_bot _
  have : IsFractionRing (locRing P) E := Localization.subalgebra.isFractionRing_ofField E _ _
  let M := Submodule.span (locRing P) (L : Set (Fin n → E))
  have hM : Submodule.IsLattice E M := by
    refine ⟨?_, ?_⟩
    · obtain ⟨s, rfl⟩ := hfg
      exact ⟨s, (Submodule.span_span_of_tower (𝓞 E) (locRing P) _).symm⟩
    · rw [Submodule.span_span_of_tower, hsp]
  have : Module.Free (locRing P) M := Submodule.IsLattice.free E M
  have hr : Module.finrank (locRing P) M = n := by
    simpa using Submodule.IsLattice.finrank_of_pi E M
  let b := Module.finBasisOfFinrankEq (locRing P) M hr
  refine ⟨fun i => b i, fun i => (b i).2, fun x hx => ?_⟩
  refine ⟨b.repr ⟨x, Submodule.subset_span hx⟩, fun a => ?_⟩
  have h := congrArg (fun v : M => (v : Fin n → E) a) (b.sum_repr ⟨x, Submodule.subset_span hx⟩)
  simp only [Submodule.coe_sum, Finset.sum_apply] at h
  exact h.symm

theorem mul_mem_int (D : D7) {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem idem_mul_loc_mem {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : IsIdemAt e P) {t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F} (ht : t ∈ intAf D.host.F) (c : locRing P) :
    finPart D e * (t ⊗ₜ[D.host.F] (c : D.host.E)) ∈ intAE D := by
  obtain ⟨a, s, hs, hc⟩ := c.2
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ P.asIdeal.zero_mem)
  have h1 : finPart D (e * incA D ((s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hn
    exact hs ((h.2 s hs0).2 hn)
  have h2 : (t ⊗ₜ[D.host.F] (a : D.host.E)) ∈ intAE D := AddSubgroup.subset_closure ⟨t, ht, a, rfl⟩
  have h3 := mul_mem_int D h1 h2
  have h4 : finPart D (incA D ((s : D.host.E)⁻¹)) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((s : D.host.E)⁻¹) := rfl
  rw [RingHom.map_mul, h4, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm _ (a : D.host.E)] at h3
  rw [hc]
  exact h3

theorem one_mem_intAf (F : Type) [Field F] [NumberField F] : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ intAf F :=
  fun v => by rw [map_one]; exact one_mem _

theorem idem_mul_span_mem {D : D7} (V : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : IsIdemAt e P) {x : Fin V.rank → D.host.E}
    (hx : x ∈ Submodule.span (locRing P) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) :
    (fun a => finPart D e * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x a)) ∈ LamHat V := by
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, h.1.1]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have h1 : finPart D e ∈ intAE D := by
      have := idem_mul_loc_mem h (one_mem_intAf _) 1
      rwa [OneMemClass.coe_one, ← Algebra.TensorProduct.one_def, mul_one] at this
    refine GlobalTheory.LatDual.smul_mem_lamHat V _ h1 _ ?_
    rw [GlobalTheory.LatDual.lamHat_eq_hat]
    exact AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩
  | zero =>
    simp only [Pi.zero_apply, TensorProduct.tmul_zero, mul_zero]
    exact zero_mem _
  | add u w _ _ hu hw =>
    simp only [Pi.add_apply, TensorProduct.tmul_add, mul_add]
    exact add_mem hu hw
  | smul c u _ hu =>
    have := GlobalTheory.LatDual.smul_mem_lamHat V _ (idem_mul_loc_mem h (one_mem_intAf _) c) _ hu
    convert this using 2 with a
    rw [mul_mul_mul_comm, hee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl

set_option maxHeartbeats 1000000 in

theorem exists_loc_basis : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D), IsIdemAt e P → ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), (∀ z, IntVec z → (fun a => finPart D e * B.mulVec z a) ∈ LamHat V) ∧ ∀ y ∈ LamHat V, ∃ z, IntVec z ∧ (fun a => finPart D e * y a) = fun a => finPart D e * B.mulVec z a := by
  intro D V P e h
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, h.1.1]
  obtain ⟨-, -, hfg, hspan, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨b, hb, hc⟩ := exists_gens P (GlobalTheory.Member.latC V) hfg hspan
  have h1 : finPart D e ∈ intAE D := by
    have := idem_mul_loc_mem h (one_mem_intAf _) 1
    rwa [OneMemClass.coe_one, ← Algebra.TensorProduct.one_def, mul_one] at this
  refine ⟨Matrix.of fun a i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] b i a, fun z hz => ?_, fun y hy => ?_⟩
  · have := sum_mem (S := LamHat V) (t := Finset.univ) fun i _ =>
      GlobalTheory.LatDual.smul_mem_lamHat V _ (hz i) _ (idem_mul_span_mem V h (hb i))
    convert this using 1
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [GlobalTheory.LatDual.lamHat_eq_hat] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hy
      obtain ⟨c, hc⟩ := hc x hx
      refine ⟨fun i => finPart D e * (t ⊗ₜ[D.host.F] (c i : D.host.E)), fun i => idem_mul_loc_mem h ht _, ?_⟩
      funext a
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
      rw [hc a, TensorProduct.tmul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm _ (finPart D e), ← mul_assoc, hee, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_comm (b i a)]
    | zero => exact ⟨0, fun _ => zero_mem _, by rw [Matrix.mulVec_zero]⟩
    | add u w _ _ hu hw =>
      obtain ⟨z, hz, hu⟩ := hu
      obtain ⟨z', hz', hw⟩ := hw
      refine ⟨z + z', fun i => add_mem (hz i) (hz' i), funext fun a => ?_⟩
      rw [Matrix.mulVec_add, Pi.add_apply, Pi.add_apply, mul_add, mul_add, congrFun hu a, congrFun hw a]
    | neg u _ hu =>
      obtain ⟨z, hz, hu⟩ := hu
      refine ⟨-z, fun i => neg_mem (hz i), funext fun a => ?_⟩
      rw [Matrix.mulVec_neg, Pi.neg_apply, Pi.neg_apply, mul_neg, mul_neg, congrFun hu a]

end GlobalTheory.LatLocBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsKummerFracCoboundaryFullGalois
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.NoLog

theorem exists_full_frac : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
    (∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB)) →
    ∃ x y : P.R.B, x ≠ 0 ∧ ∀ g : GQ l, x * P.actQ g y - P.actQ g x * y = x * P.actQ g x * ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P _ K b b' hb h
  haveI := K.2
  haveI : Finite (GQ l ⧸ GK K) := Subgroup.quotient_finite_of_isOpen _ K.1.fixingSubgroup_isOpen
  haveI := Fintype.ofFinite (GQ l ⧸ GK K)
  let ι : P.R.B →+* FractionRing P.R.B := algebraMap P.R.B (FractionRing P.R.B)
  have hι : Function.Injective ι := IsFractionRing.injective P.R.B (FractionRing P.R.B)
  let e : GQ l → FractionRing P.R.B ≃+* FractionRing P.R.B := fun g =>
    IsFractionRing.ringEquivOfRingEquiv (A := P.R.B) (B := P.R.B) (P.actQ g).toRingEquiv
  have he : ∀ g z, e g (ι z) = ι (P.actQ g z) := fun g z =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
  have hmul : ∀ s g z, e s (e g z) = e (s * g) z := by
    intro s g
    have : (e s).toRingHom.comp (e g).toRingHom = (e (s * g)).toRingHom := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors P.R.B)
      ext z
      show e s (e g (ι z)) = e (s * g) (ι z)
      rw [he, he, he, map_mul, AlgEquiv.mul_apply]
    intro z
    exact RingHom.congr_fun this z
  have hne : ∀ g (z : P.R.B), z ≠ 0 → ι (P.actQ g z) ≠ 0 := fun g z hz =>
    (map_ne_zero_iff ι hι).2 ((map_ne_zero_iff _ (P.actQ g).injective).2 hz)
  let T : GQ l → FractionRing P.R.B := fun g => ι ((kummer P g : ℚ_[l]) • P.tB)
  have hT : ∀ s g, e s (T g) = T (s * g) - T s := by
    intro s g
    simp only [T, he, map_smul, localPrime_galoisAction_periodT, kummer_mul, smul_smul, add_smul, map_add]
    rw [mul_comm]; abel
  let f : FractionRing P.R.B := ι b' / ι b
  have hb0 : ι b ≠ 0 := (map_ne_zero_iff ι hι).2 hb
  have hf : ∀ g ∈ GK K, e g f - f = T g := by
    intro g hg
    have h1 := congrArg ι (h g hg)
    simp only [map_sub, map_mul] at h1
    have h2 := hne g b hb
    simp only [f, map_div₀, he]
    field_simp
    linear_combination h1
  let Fn : GQ l → FractionRing P.R.B := fun g => e g f - T g
  have h1 : ∀ s g, e s (Fn g) = Fn (s * g) + T s := by
    intro s g
    simp only [Fn, map_sub, hmul, hT]
    abel
  have h2 : ∀ g (k : ↥(GK K)), Fn (g * k) = Fn g := by
    intro g k
    have e1 : Fn k = f := by simp only [Fn, ← hf k k.2]; abel
    have := h1 g k
    rw [e1] at this
    simp only [Fn] at this ⊢
    linear_combination -this
  have h3 : ∀ g, Fn (QuotientGroup.mk g : GQ l ⧸ GK K).out = Fn g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (GK K) g
    rw [hk, h2]
  have hnB : ((Fintype.card (GQ l ⧸ GK K) : ℕ) : P.R.B) ≠ 0 := by
    haveI := nontrivial_B P
    rw [← map_natCast (algebraMap ℚ_[l] P.R.B)]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℚ_[l] P.R.B)).2
      (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hn : ((Fintype.card (GQ l ⧸ GK K) : ℕ) : FractionRing P.R.B) ≠ 0 := by
    rw [← map_natCast ι]; exact (map_ne_zero_iff ι hι).2 hnB
  let fa : FractionRing P.R.B := ((Fintype.card (GQ l ⧸ GK K) : ℕ) : FractionRing P.R.B)⁻¹ * ∑ q : GQ l ⧸ GK K, Fn q.out
  have hfa : ∀ s, e s fa - fa = T s := by
    intro s
    have h4 : ∑ q : GQ l ⧸ GK K, Fn (s * q.out) = ∑ q : GQ l ⧸ GK K, Fn q.out :=
      Fintype.sum_equiv (MulAction.toPerm s) _ _ fun q => by
        rw [MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, h3, smul_eq_mul]
    simp only [fa, map_mul, map_inv₀, map_natCast, map_sum, h1]
    rw [Finset.sum_add_distrib, h4, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  obtain ⟨y, x, hx, hxy⟩ := IsFractionRing.div_surjective (A := P.R.B) fa
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
  refine ⟨x, y, hx0, fun g => ?_⟩
  have hxy' : ι y / ι x = fa := hxy
  have k := hfa g
  rw [← hxy', map_div₀, he, he] at k
  have k1 := hne g x hx0
  have k2 : ι x ≠ 0 := (map_ne_zero_iff ι hι).2 hx0
  apply hι
  simp only [map_sub, map_mul]
  field_simp at k
  linear_combination k

end GlobalTheory.Pst.NoLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FilPEqSpanBetaDPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem filtration_eq_span_pow : ∀ (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  ∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n} := by
  intro l _ Co ϖ hb n
  have he := core_isEps l Co
  obtain ⟨hfil, -, -, -⟩ := filtration_eq_xi_pow l Co.ε he
  obtain ⟨-, -, -, -, hdom, -, hk⟩ := thetaP_facts l
  haveI := hdom
  have hass : Associated (algebraMap (Per.Ainf l) (Per.AinfP l) (xi Co.ε)) (beta ϖ) :=
    Ideal.span_singleton_eq_span_singleton.1 ((hk Co.ε he).symm.trans hb)
  have hD : Associated (aDp l (xi Co.ε) ^ n) (betaD ϖ ^ n) :=
    (hass.map (algebraMap (Per.AinfP l) (Per.BdRp l))).pow_pow
  ext y
  rw [hfil, Ideal.mem_span_singleton]
  exact hD.dvd_iff_dvd_left

end GlobalTheory.Pst.StLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisLogTeichmullerRatioEqAddKummer
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

variable {l : ℕ} [Fact l.Prime]

theorem map_linv (f : Per.AinfP l →+* Per.AinfP l) : f (linv l) = linv l := by
  have h := congrArg f (mul_linv (l := l))
  rw [map_mul, map_natCast, map_one] at h
  have h2 := mul_linv (l := l)
  linear_combination (linv l) * h - f (linv l) * h2

theorem beta_mem_kerP (ϖ : Per.Fl l) (hu : ϖ.untilt = ((l : ℕ) : Per.OC l)) : beta ϖ ∈ Per.kerP l := by
  rw [← ThetaD.fontaineTheta_eq_zero]
  have h := congrArg (Per.θP l) (l_mul_beta ϖ)
  rw [map_mul, map_sub, map_natCast, ThetaD.fontaineTheta_algebraMap₂, WittVector.fontaineTheta_teichmuller, hu] at h
  have hl : ((l : ℕ) : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine (mul_eq_zero.1 (h.trans ?_)).resolve_left hl
  simp

theorem gal_beta (g : GQ l) (ϖ e : Per.Fl l) (h : Per.σF g ϖ = ϖ * e) :
    Per.extP (Per.σA g) (beta ϖ) = beta ϖ + algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e) +
      beta ϖ * algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e) := by
  have e1 : Per.σA g (Per.tm ϖ) = Per.tm ϖ * Per.tm e := by
    have h1 := gal_quot g ϖ e h 1
    simp only [map_one, mul_one, map_sub] at h1
    exact sub_left_injective h1
  rw [beta, map_sub, map_mul, map_one, map_linv, GlobalTheory.RingBasics.awayMap_algebraMap₂, e1, map_mul]
  simp only [GlobalTheory.MemLoc.mu, map_sub, map_one]
  ring

theorem isLogP_map {e : Per.Fl l} (he : e.untilt = 1) {t : Per.Acris l} (ht : IsLogA e t)
    {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) :
    IsLogP (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e)) (j t) := by
  intro n
  have hu : ∀ k : ℕ, ∃ u : Per.AinfP l, ((k + 1 : ℕ) : Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e)) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n t (algebraMap (Per.AinfP l) (Per.BdRp l) c) (by
    intro r
    obtain ⟨N, hN⟩ := ht r
    obtain ⟨s, hs, z, hz⟩ := hN (max N n) (le_max_left _ _)
    refine ⟨s, z, 0, by rw [← hz]; ring, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, LogFun.ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      LogFun.partial_eq u hu _ _ _ (hf _) hs, LogFun.partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (LogFun.partial_sub_mem _ u _ (LogFun.mu_mem he) (le_max_right _ _)))
  rw [key, LogFun.ev_alg, ← map_natCast (Ideal.Quotient.mk (Per.kerP l ^ n)), ← map_mul, hc]

theorem gal_log : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (Co : Core l), Co.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
  (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ϖ.untilt = ((l : ℕ) : Per.OC l) →
  ∀ u : Per.BdRp l, IsLogP (beta ϖ) u → ∀ g : GQ l,
    Per.σDp g u = u + Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t) := by
  intro l _ P Co hζ ϖ hr hu u hlog g
  have hd : ∀ m, g (lRoot l m) = Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val * lRoot l m := fun m => by
    rw [hζ]; exact isKummer_kummer P g m
  have hd' : ∀ m, g (lRoot l m) / lRoot l m = Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val := fun m => by
    rw [hd, mul_div_cancel_right₀ _ (lRoot_ne_zero l m)]
  obtain ⟨e, he⟩ := exists_tilt (fun m => Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val)
    (fun m => by rw [← hd', ← hd', div_pow, ← map_pow, lRoot_succ]) 1 (by simp [Co.ζ_zero])
  have he1 : e.untilt = 1 := Subtype.ext (by
    have := he 0
    rw [Co.ζ_zero, one_pow, map_one] at this
    exact this)
  have hxe : Per.σF g ϖ = ϖ * e := gal_eq_mul g ϖ e fun m => by
    rw [hr, he, ← map_mul, mul_comm, ← hd]
    exact GlobalTheory.RingBasics.σC_coe g _
  obtain ⟨y, -, hy, -⟩ := exists_isLogA l e he1
  rw [← log_eq Co e (kummer P g) y he hy]
  refine IsLogP.add (beta_mem_kerP ϖ hu) (LogFun.mu_mem he1) hlog (isLogP_map he1 hy Co.j_cris) ?_
  have h := IsLogP.gal hlog g
  rwa [gal_beta g ϖ e hxe] at h

end GlobalTheory.Pst.StLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicPairAdditiveCoordsLinearFormsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitPlaces_thetaSeries_subst_orbMap_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {M N N' r : ℕ} (eA : Fin M ≃ R × Fin N)
    (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p) (Θ : MvPowerSeries (Fin r) ℂ_[p]), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (Formalism.L2.Th1.D.thetaInZ (d := nP D p) p (MaximalUnramifiedExtension p).subtype σ om oms
        (subst (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p]))
          (Formalism.L2.Th1.Top.inHyp p f f'
            (subst (fun i : Fin r => (Formalism.InvariantFactorPaths.G7.at1 i (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) Θ)))) =
      subst (hypZ D p σ om oms R f f') Θ := by
  first | exact @GlobalTheory.KerStd.HypOrbit.hypZ_of_inHyp | exact GlobalTheory.KerStd.HypOrbit.hypZ_of_inHyp | (intros; apply GlobalTheory.KerStd.HypOrbit.hypZ_of_inHyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.TameIwahori

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsIwVec {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (θ : Fin n → kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin n) k) V) (v : V) : Prop :=
  (∀ h ∈ KO k (Fin n), (∀ i j, j < i → valuation k (h.val i j) < 1) →
    (∀ i, valuation k (h.val i i - 1) < 1) → π h v = v) ∧
  ∀ t ∈ torusO k (Fin n), π (diagT k (Fin n) t) v = (torusChar θ t : ℂ) • v

end GlobalTheory.TameIwahori
end
end

