import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0237
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Principal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCompEqCocycleMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0266

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExists
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GalExist

theorem exists_sum_of_mem_La (D : D7) (T : Tor D) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (y : VC D N N') (hy : y ∈ La D T L L') :
    ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (w : Fin r → ℂ),
      (∀ j, b j ∈ YYl D L L') ∧ (∀ j, w j ∈ T.abelian₂) ∧ y = ∑ j, w j • embV D T (b j) := by
  first
  | exact @_root_.GlobalTheory.LatticeSumMembership.La_mem_sum
  | exact _root_.GlobalTheory.LatticeSumMembership.La_mem_sum
  | (apply _root_.GlobalTheory.LatticeSumMembership.La_mem_sum <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeSumMembership.La_mem_sum <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeSumMembership.La_mem_sum <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeSumMembership.La_mem_sum ..)

theorem galEx_of_galStar (D : D7) (hS : galStar D) : galEx D := by
  intro cc δ hc M ρ hK hD hM N N' L L' _ _ x n hx hn
  obtain ⟨m, hm, hmx⟩ := hx
  obtain ⟨r, b, w, hb, hw, hsum⟩ := exists_sum_of_mem_La D _ L L' _ hmx
  obtain ⟨h1, -, -, -, -, h6, -⟩ := hS cc δ hc M ρ hK hD.2.1 hD.2.2
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hw' : ∀ j, w j ∈ lamOf D cc δ := hw
  have hmul : ∀ j, ((m * n : ℕ) : ℂ) * (w j / m / n) ∈ lamOf D cc δ := by
    intro j
    have : ((m * n : ℕ) : ℂ) * (w j / m / n) = w j := by push_cast; field_simp
    rw [this]; exact hw' j
  have hex : ∀ j, ∃ t', StarPt M ρ (lamOf D cc δ) (w j / m / n) t' := by
    intro j
    have hq : InRationalLattice (lamOf D cc δ) (w j / m / n) := ⟨m * n, Nat.mul_pos hm hn, hmul j⟩
    refine h1 _ hq ?_
    by_cases h : w j / m / n ∈ lamOf D cc δ
    · exact Or.inl h
    · exact Or.inr (hM _ hq h)
  choose t' ht' using hex
  refine ⟨∑ j, ((n : ℂ) * t' j) • embV D (torConj D (tor0 D cc δ) M ρ) (b j),
    ⟨r, b, fun j => w j / m, fun j => (n : ℂ) * t' j, hb, ?_, ?_, rfl, ?_⟩, m, hm, ?_⟩
  · intro j
    refine ⟨m, hm, ?_⟩
    have : (m : ℂ) * (w j / m) = w j := by field_simp
    rw [this]; exact hw j
  · have hx : x = (m : ℂ)⁻¹ • (m • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm0, one_smul]
    rw [hx, hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← div_eq_inv_mul]
  · intro j
    have : (n : ℂ) * t' j / n = t' j := by field_simp
    show StarPt M ρ (lamOf D cc δ) (w j / m / n) ((n : ℂ) * t' j / n)
    rw [this]; exact ht' j
  · rw [Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun j _ => ?_
    refine AddSubgroup.subset_closure ⟨((m * n : ℕ) : ℂ) * t' j, (h6 _ _ _ (ht' j)).1 (hmul j), b j, hb j, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    push_cast; ring

theorem galEx_all : ∀ D : D7, galEx D := fun D => galEx_of_galStar D (GlobalTheory.T.galStar_complexMultiplication_points D)

end GlobalTheory.GalExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.QuadSubfield

variable (D : D7)

theorem emb_conj (f : D.host.E →+* ℂ) (y : D.host.E) :
    f (D.host.conj y) = starRingEnd ℂ (f y) := D.host.conjE_apply f y

theorem conj_conj (y : D.host.E) : D.host.conj (D.host.conj y) = y := by
  apply D.host.φ₀.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

theorem exists_coords {x : D.host.E} (hx : x ∈ D.host.K) :
    ∃ a b : ℚ, x = (a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD := by
  have halg : IsAlgebraic ℚ D.host.sqrtMinusD := Algebra.IsAlgebraic.isAlgebraic _
  have hx' : x ∈ Algebra.adjoin ℚ {D.host.sqrtMinusD} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hx
  clear hx
  have hs := D.host.sqrtMinusD_sq
  induction hx' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    refine ⟨a * a' - D.host.d * b * b', a * b' + a' * b, ?_⟩
    push_cast
    linear_combination (b : D.host.E) * (b' : D.host.E) * hs

theorem conj_coords (a b : ℚ) :
    D.host.conj ((a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD) =
      (a : D.host.E) - (b : D.host.E) * D.host.sqrtMinusD := by
  rw [map_add, map_mul, map_ratCast, map_ratCast, D.host.conj_sqrtMinusD]
  ring

theorem conj_mem {x : D.host.E} (hx : x ∈ D.host.K) : D.host.conj x ∈ D.host.K := by
  obtain ⟨a, b, rfl⟩ := exists_coords D hx
  rw [conj_coords]
  exact sub_mem (SubfieldClass.ratCast_mem _ a)
    (mul_mem (SubfieldClass.ratCast_mem _ b) (Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D))

def conjK : D.host.K →+* D.host.K :=
  RingHom.codRestrict ((D.host.conj : D.host.E →+* D.host.E).comp D.host.K.val.toRingHom)
    D.host.K (fun x => conj_mem D x.2)

theorem coe_conjK (x : D.host.K) : ((conjK D x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E) := rfl

theorem isGalois_over : IsGalois D.host.K D.host.E := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  exact IsGalois.tower_top_of_isGalois ℚ _ _

theorem coe_trace (y : D.host.E) :
    ((Algebra.trace D.host.K D.host.E y : D.host.K) : D.host.E) =
      ∑ τ : D.host.E ≃ₐ[D.host.K] D.host.E, τ y := by
  have := isGalois_over D
  exact trace_eq_sum_automorphisms (K := D.host.K) y

theorem conj_comm (τ : D.host.E ≃ₐ[D.host.K] D.host.E) (y : D.host.E) :
    D.host.conj (τ y) = τ (D.host.conj y) := by
  have h : D.host.conj * τ.restrictScalars ℚ = τ.restrictScalars ℚ * D.host.conj :=
    D.host.gal.injective (by rw [map_mul, map_mul, mul_comm])
  exact AlgEquiv.congr_fun h y

theorem trace_conj (y : D.host.E) :
    Algebra.trace D.host.K D.host.E (D.host.conj y) =
      conjK D (Algebra.trace D.host.K D.host.E y) := by
  apply Subtype.ext
  rw [coe_conjK, coe_trace, coe_trace, map_sum]
  exact Finset.sum_congr rfl fun τ _ => (conj_comm D τ y).symm

theorem trace_pos (y : D.host.E) (hy : y ≠ 0) :
    ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := by
  obtain ⟨a, b, hab⟩ := exists_coords D (Algebra.trace D.host.K D.host.E (y * D.host.conj y)).2
  have hfix : D.host.conj ((Algebra.trace D.host.K D.host.E (y * D.host.conj y) : D.host.K) : D.host.E)
      = ((Algebra.trace D.host.K D.host.E (y * D.host.conj y) : D.host.K) : D.host.E) := by
    rw [← coe_conjK, ← trace_conj, map_mul, conj_conj, mul_comm]
  rw [hab, conj_coords] at hfix
  have hb : (b : D.host.E) * D.host.sqrtMinusD = 0 := by linear_combination (-1 / 2 : D.host.E) * hfix
  rw [hb, add_zero] at hab
  refine ⟨a, ?_, Subtype.ext (by rw [hab]; simp)⟩
  have h1 := congrArg D.host.φ₀ hab
  rw [coe_trace, map_sum, map_ratCast] at h1
  have h2 : ∀ τ : D.host.E ≃ₐ[D.host.K] D.host.E,
      D.host.φ₀ (τ (y * D.host.conj y)) = ((Complex.normSq (D.host.φ₀ (τ y)) : ℝ) : ℂ) := by
    intro τ
    rw [map_mul, ← conj_comm, map_mul, emb_conj, Complex.mul_conj]
  simp only [h2] at h1
  have h3 : ∑ τ : D.host.E ≃ₐ[D.host.K] D.host.E, Complex.normSq (D.host.φ₀ (τ y)) = (a : ℝ) := by
    exact_mod_cast h1
  have h4 : (0 : ℝ) < a := by
    rw [← h3]
    refine Finset.sum_pos (fun τ _ => Complex.normSq_pos.2 ?_) Finset.univ_nonempty
    simpa using hy
  exact_mod_cast h4

theorem finrank_over : Module.finrank D.host.K D.host.E = fF D := by
  have h := Module.finrank_mul_finrank ℚ D.host.K D.host.E
  rw [Formalism.L2.Pj.LPb.finrank_K, D.host.finrank_cmField] at h
  show _ = 2 * D.R.ord
  omega

theorem quadratic_subfield : ∀ D : D7, Module.finrank D.host.K D.host.E = fF D ∧ ∃ (σ : D.host.K →+* D.host.K) (θ : D.host.K), (∀ x : D.host.K, ((σ x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E)) ∧ θ ^ 2 = -(D.host.d : D.host.K) ∧ σ θ = -θ ∧ (∀ x : D.host.K, ∃ a b : ℚ, x = (a : D.host.K) + (b : D.host.K) * θ) ∧ IsIntegral ℤ ((1 + θ) / 2) ∧ (∀ y : D.host.E, D.host.conj (D.host.conj y) = y) ∧ (∀ y : D.host.E, Algebra.trace D.host.K D.host.E (D.host.conj y) = σ (Algebra.trace D.host.K D.host.E y)) ∧ ∀ y : D.host.E, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := by
  intro D
  refine ⟨finrank_over D, conjK D, ⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩,
    coe_conjK D, ?_, ?_, ?_, ?_, conj_conj D, trace_conj D, trace_pos D⟩
  · apply Subtype.ext
    simpa using D.host.sqrtMinusD_sq
  · apply Subtype.ext
    rw [coe_conjK]
    exact D.host.conj_sqrtMinusD
  · intro x
    obtain ⟨a, b, h⟩ := exists_coords D x.2
    exact ⟨a, b, Subtype.ext (by simpa using h)⟩
  · have h := (Formalism.L2.Pj.LPb.w0K D).2
    convert h using 1
    first | rfl | (apply Subtype.ext; simp [Formalism.L2.Pj.LPb.w0K])

end GlobalTheory.QuadSubfield
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergReproducingKernelSumSpec
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.KerSum

theorem exists_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u v, ‖H u v‖ ≤ M * ‖u‖ * ‖v‖ := by
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun u v => H u v)
    (fun a b c => by simp)
    (fun c a b => by
      rw [← Complex.coe_smul, map_smul, LinearMap.smul_apply, Complex.coe_smul])
    (fun a b c => by simp)
    (fun c a b => by
      rw [← Complex.coe_smul, LinearMap.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul])
  let B' : V →L[ℝ] V →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ B)
  exact ⟨‖B'‖, norm_nonneg _, fun u v => B'.le_opNorm₂ u v⟩

theorem norm_kerTerm_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H : Sesq V) {M R : ℝ} (hM : 0 ≤ M) (hB : ∀ u v, ‖H u v‖ ≤ M * ‖u‖ * ‖v‖) (x w z : V)
    (hw : ‖w‖ ≤ R) :
    ‖kerTerm H x w z‖ ≤ Real.exp (π * (M * R * ‖z‖)) *
      Real.exp (-(π / 2) * (H x x).re + (π * (M * ‖z‖ + M * R)) * ‖x‖) := by
  rw [kerTerm, Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
  have h1 : (H w z).re ≤ M * R * ‖z‖ :=
    ((Complex.re_le_norm _).trans (hB w z)).trans (by gcongr)
  have h2 : (H x z).re ≤ M * ‖x‖ * ‖z‖ := (Complex.re_le_norm _).trans (hB x z)
  have h3 : -(H w x).re ≤ M * R * ‖x‖ :=
    (((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans (hB w x)).trans (by gcongr)
  have e : ((π : ℂ) * H (w + x) z - (π : ℂ) * H w x - (π : ℂ) * H x x / 2).re
      = π * ((H w z).re + (H x z).re + -(H w x).re) - π / 2 * (H x x).re := by
    simp; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) Real.pi_pos.le
  linarith

theorem differentiable_kerTerm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (H : Sesq V) (x z : V) :
    Differentiable ℂ (fun w => kerTerm H x w z) := by
  have h : ∀ v, Differentiable ℂ (fun w => H w v) := fun v =>
    (LinearMap.toContinuousLinearMap (H.flip v)).differentiable
  have e : (fun w => kerTerm H x w z) = fun w =>
      cexp ((π : ℂ) * (H w z + H x z) - (π : ℂ) * H w x - (π : ℂ) * H x x / 2) := by
    funext w; simp [kerTerm]
  rw [e]
  exact (((((h z).add_const _).const_mul _).sub ((h x).const_mul _)).sub_const _).cexp

theorem kerTerm_shift {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
    (hH : ∀ z w, H z w = conj (H w z)) (x y w z : V) :
    kerTerm H x (w + y) z * cexp (-(π : ℂ) * H w y - (π : ℂ) * H y y / 2)
      = cexp (-((π : ℂ) * I) * ((H y x).im : ℂ)) * kerTerm H (y + x) w z := by
  have h : I * ((H y x).im : ℂ) = (H y x - H x y) / 2 := by
    rw [hH x y, Complex.sub_conj]; push_cast; ring
  rw [kerTerm, kerTerm, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_add, LinearMap.add_apply]
  linear_combination (π : ℂ) * h

theorem kerSum_spec : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (α : V → ℂ), IsSemichar H Λ α → (∀ w z, Summable (fun x : Λ => α x * kerTerm H x w z)) ∧ (∀ z, Differentiable ℂ (kerSum H Λ α z)) ∧ ∀ z, ∀ y ∈ Λ, ∀ w, α y * Heisenberg₂ H y (kerSum H Λ α z) w = kerSum H Λ α z w := by
  intro V _ _ _ H hH Λ _ α hα
  obtain ⟨M, hM, hB⟩ := exists_bound H
  have hn : ∀ x : Λ, ‖α x‖ = 1 := fun x => by
    rcases hα.1 x x.2 with h | h <;> simp [h]
  have key : ∀ (z : V) (R : ℝ), ∃ u : Λ → ℝ, Summable u ∧
      ∀ (x : Λ) (w : V), ‖w‖ ≤ R → ‖α x * kerTerm H x w z‖ ≤ u x := fun z R =>
    ⟨_, (GlobalTheory.T.summable_exp_neg_herm_add_norm V H hH Λ (π * (M * ‖z‖ + M * R))).mul_left (Real.exp (π * (M * R * ‖z‖))),
      fun x w hw => by
        rw [norm_mul, hn, one_mul]
        exact norm_kerTerm_le H hM hB x w z hw⟩
  refine ⟨fun w z => ?_, fun z => ?_, fun z y hy w => ?_⟩
  · obtain ⟨u, hu, h⟩ := key z ‖w‖
    exact Summable.of_norm_bounded hu fun x => h x w le_rfl
  · refine differentiableOn_univ.1 (GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal isOpen_univ
      (F := fun (x : Λ) w => α x * kerTerm H x w z)
      (fun x => ((differentiable_kerTerm H x z).const_mul _).differentiableOn) fun w _ => ?_)
    obtain ⟨u, hu, h⟩ := key z (‖w‖ + 1)
    refine ⟨Metric.ball w 1, Metric.ball_mem_nhds w one_pos, u, hu, fun x v hv => h x v ?_⟩
    have := norm_le_norm_add_norm_sub' v w
    rw [mem_ball_iff_norm] at hv
    linarith
  · simp only [Heisenberg₂, kerSum]
    rw [← tsum_mul_right, ← tsum_mul_left,
      ← (Equiv.addLeft (⟨y, hy⟩ : Λ)).tsum_eq (fun x : Λ => α x * kerTerm H x w z)]
    refine tsum_congr fun x => ?_
    simp only [Equiv.coe_addLeft, AddSubgroup.coe_add]
    rw [hα.2.2 y hy x x.2, mul_assoc (α x), kerTerm_shift H hH.1]
    ring

end GlobalTheory.UnitaryTheta.KerSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntSerOfIsWq
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.DatumBasic

variable {p : ℕ} [Fact p.Prime]

theorem wModel_Δ (lam : Qbar →+* ℂ_[p]) {Λ : AddSubgroup ℂ} (h2 : g2 Λ ∈ Qbar) (h3 : g3 Λ ∈ Qbar)
    (hd : TaylorLogMetric.discr Λ = 1) : (wModel lam Λ).Δ = 1 := by
  set a : Qbar := ⟨g2 Λ, h2⟩ with ha
  set b : Qbar := ⟨g3 Λ, h3⟩ with hb
  have hc : ∀ x : Qbar, lamC lam (-(x : ℂ) / 4) = -(lam x) / 4 := by
    intro x
    have e : -(x : ℂ) / 4 = ((-x / 4 : Qbar) : ℂ) := by
      push_cast
      rfl
    rw [e, lamC, dif_pos (-x / 4).2]
    change lam (-x / 4) = _
    rw [map_div₀, map_neg, map_ofNat]
  have e : a ^ 3 - 27 * b ^ 2 = 1 := by
    apply Subtype.ext
    push_cast
    exact hd
  have e2 := congrArg lam e
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one] at e2
  have ea := hc a
  have eb := hc b
  simp only [ha, hb] at ea eb
  simp only [wModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, ea, eb]
  linear_combination e2

theorem intSer_of_isWq {W : WeierstrassCurve ℂ_[p]} (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1)
    (h3 : ‖W.a₃‖ ≤ 1) (h4 : ‖W.a₄‖ ≤ 1) (h6 : ‖W.a₆‖ ≤ 1) {w : PowerSeries ℂ_[p]}
    (h : IsWq W w) : IntSer w := by
  obtain ⟨hr, -, hC, hX, -⟩ := SerRing.series_ring_laws p
  have hadd : ∀ {f g : PowerSeries ℂ_[p]}, IntSer f → IntSer g → IntSer (f + g) :=
    fun hf hg => (hr _ _ hf hg).1
  have hterm : ∀ (c : ℂ_[p]) (i j : ℕ) (t : PowerSeries ℂ_[p]), ‖c‖ ≤ 1 → IntSer t →
      IntSer (PowerSeries.C c * PowerSeries.X ^ i * t ^ j) := fun c i j t hc ht =>
    SerRing.intSer_mul (SerRing.intSer_mul ((hC c).2 hc) (SerRing.intSer_pow hX i))
      (SerRing.intSer_pow ht j)
  have hone : IntSer (1 : PowerSeries ℂ_[p]) := by simpa using SerRing.intSer_pow hX 0
  have key : ∀ n : ℕ, ∃ t : PowerSeries ℂ_[p], IntSer t ∧ PowerSeries.X ^ n ∣ w - t := by
    intro n
    induction n with
    | zero => exact ⟨1, hone, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht, z, hz⟩ := ih
      refine ⟨_, hadd (hadd (hadd (hadd (hadd hone (hterm _ 1 1 t h1 ht)) (hterm _ 2 1 t h2 ht))
        (hterm _ 3 2 t h3 ht)) (hterm _ 4 2 t h4 ht)) (hterm _ 6 3 t h6 ht),
        z * (PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X +
          (PowerSeries.C W.a₃ * PowerSeries.X ^ 2 + PowerSeries.C W.a₄ * PowerSeries.X ^ 3) * (w + t) +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 5 * (w ^ 2 + w * t + t ^ 2)), ?_⟩
      have h' : w = 1 + PowerSeries.C W.a₁ * PowerSeries.X * w +
          PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * w + PowerSeries.C W.a₃ * PowerSeries.X ^ 3 * w ^ 2 +
          PowerSeries.C W.a₄ * PowerSeries.X ^ 4 * w ^ 2 +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 6 * w ^ 3 := h
      linear_combination h' + (PowerSeries.X * (PowerSeries.C W.a₁ + PowerSeries.C W.a₂ * PowerSeries.X +
          (PowerSeries.C W.a₃ * PowerSeries.X ^ 2 + PowerSeries.C W.a₄ * PowerSeries.X ^ 3) * (w + t) +
          PowerSeries.C W.a₆ * PowerSeries.X ^ 5 * (w ^ 2 + w * t + t ^ 2))) * hz
  intro n
  obtain ⟨t, ht, hd⟩ := key (n + 1)
  have e := PowerSeries.X_pow_dvd_iff.1 hd n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at e
  rw [e]
  exact ht n

theorem datum_basic : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → ‖((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 ∧ IntSer g.wq⁻¹ ∧ PowerSeries.constantCoeff g.wq⁻¹ = 1 ∧ PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq := by
  intro p _ g ⟨⟨h1, h2, h3, h4, h6, hΔ⟩, hw, _⟩ hL a2 a3 hd
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have := congrArg PowerSeries.constantCoeff hw
    simpa using this
  refine ⟨?_, SerRing.intSer_inv (intSer_of_isWq h1 h2 h3 h4 h6 hw) (by rw [hw0, norm_one]),
    by rw [PowerSeries.constantCoeff_inv, hw0, inv_one],
    GlobalTheory.ThetaParam.constantCoeff_ePhi1 g hw (GlobalTheory.OddTheta.sgStar_laws _ hL).1.2.1,
    GlobalTheory.ThetaParam.atU_sg g ((hL.sg_eq_zero 0).2 (zero_mem _))⟩
  rw [WeierstrassCurve.variableChange_Δ, wModel_Δ g.lam a2 a3 hd, mul_one, norm_pow] at hΔ
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hΔ

end GlobalTheory.EvenTheta.DatumBasic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaussianUnitary
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem sesq_eq_sum_repr {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (he : ∀ i j, H (e i) (e j) = if i = j then 1 else 0) (z w : V) :
    H z w = ∑ i, e.repr z i * conj (e.repr w i) := by
  conv_lhs => rw [← e.sum_repr z, ← e.sum_repr w]
  simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, he,
    smul_eq_mul, RingHom.id_apply, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem repr_apply_of_eigen {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (b : V →ₗ[ℂ] V) (l : Fin n → ℂ) (hl : ∀ i, b (e i) = l i • e i) (z : V)
    (i : Fin n) : e.repr (b z) i = l i * e.repr z i := by
  conv_lhs => rw [← e.sum_repr z]
  simp only [map_sum, map_smul, hl]
  simp [Finsupp.single_apply, mul_comm]

theorem det_of_eigen {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (b : V →ₗ[ℂ] V) (l : Fin n → ℂ) (hl : ∀ i, b (e i) = l i • e i) :
    LinearMap.det b = ∏ i, l i := by
  rw [← LinearMap.det_toMatrix e, ← Matrix.det_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, hl]
  simp [Matrix.diagonal_apply, Finsupp.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all

theorem integral_gaussian_unitary : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∃ κ : ℝ, κ ≠ 0 ∧ ∀ y v : V, Integrable (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) μ ∧ ∫ z, cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * cexp (π * H y v) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet
  obtain ⟨n, e, l, he, hl⟩ := GlobalTheory.UnitaryTheta.unitary_exists_orthonormal_eigenbasis V H hH a ha
  have hb : ∀ i, (1 - (a : V →ₗ[ℂ] V)) (e i) = (1 - l i) • e i := fun i => by
    simp [(hl i).2, sub_smul]
  have hd := det_of_eigen e _ _ hb
  have hr : ∀ z i, e.repr (z - a z) i = (1 - l i) * e.repr z i := fun z i => by
    simpa using repr_apply_of_eigen e _ _ hb z i
  have hne : ∀ i, 1 - l i ≠ 0 := fun i => by
    rw [hd] at hdet
    exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
  have hre : ∀ i, 0 < (1 - l i).re := fun i => by
    have h1 : (l i).re ≤ 1 := (hl i).1 ▸ re_le_norm (l i)
    have h2 : (l i).re ≠ 1 := by
      intro h
      apply hne i
      have h3 : (l i).re * (l i).re + (l i).im * (l i).im = 1 := by
        rw [← normSq_apply, normSq_eq_norm_sq, (hl i).1]; norm_num
      have h4 : (l i).im = 0 := by
        rw [h] at h3
        exact mul_self_eq_zero.1 (by linarith)
      apply Complex.ext <;> simp [h, h4]
    simp only [sub_re, one_re]
    exact sub_pos.2 (lt_of_le_of_ne h1 h2)
  let T : V ≃L[ℂ] (Fin n → ℂ) := e.equivFun.toContinuousLinearEquiv
  let Tm : V ≃ᵐ (Fin n → ℂ) := T.toHomeomorph.toMeasurableEquiv
  have hT : ∀ z i, Tm z i = e.repr z i := fun z i => rfl
  haveI : (μ.map Tm).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hν := Measure.isAddLeftInvariant_eq_smul (μ.map Tm) (volume : Measure (Fin n → ℂ))
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map Tm) (volume : Measure (Fin n → ℂ))
  set c := Measure.addHaarScalarFactor (μ.map Tm) (volume : Measure (Fin n → ℂ)) with hc
  refine ⟨(c : ℝ), by exact_mod_cast hpos.ne', fun y v => ?_⟩
  let g : Fin n → ℂ → ℂ := fun i z => cexp (-(π : ℂ) * (1 - l i) * (z * conj z) +
    π * (((1 - l i) * e.repr y i) * conj z) + π * (z * conj (e.repr v i)))
  have hg := fun i => GlobalTheory.T.integral_cexp_complex_gaussian_linear (1 - l i) ((1 - l i) * e.repr y i) (e.repr v i) (hre i)
  have hF : (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) =
      (fun x : Fin n → ℂ => ∏ i, g i (x i)) ∘ Tm := by
    funext z
    simp only [Function.comp, g, hT, ← Complex.exp_sum, sesq_eq_sum_repr H e he, hr, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hint : Integrable (fun x : Fin n → ℂ => ∏ i, g i (x i)) volume :=
    Integrable.fintype_prod (f := g) fun i => (hg i).1
  rw [hF]
  refine ⟨?_, ?_⟩
  · rw [← integrable_map_equiv, hν]
    exact hint.smul_measure_nnreal
  · have h1 := integral_map_equiv (μ := μ) Tm (fun x : Fin n → ℂ => ∏ i, g i (x i))
    simp only [Function.comp_def]
    rw [← h1, hν, integral_smul_nnreal_measure, integral_fintype_prod_volume_eq_prod, hd,
      sesq_eq_sum_repr H e he, Finset.mul_sum, Complex.exp_sum]
    have h2 : ∀ i, ∫ z, g i z = (1 - l i)⁻¹ * cexp (π * (e.repr y i * conj (e.repr v i))) := fun i => by
      rw [show ∫ z, g i z = _ from (hg i).2]
      congr 2
      field_simp [hne i]
    simp only [h2, Finset.prod_mul_distrib, Finset.prod_inv_distrib, NNReal.smul_def, real_smul]
    ring

end GlobalTheory.UnitaryTheta
end

