import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfect

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SgnLatSpanBasis
section
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma.SgnBasis

theorem eta_mul_isUnit (K : UQ) (a : K.E) (u : K.O) (hu : IsUnit u) :
    K.eta (a * algebraMap K.O K.E u) = K.eta a := by
  have hv : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E u) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    intro h
    exact (IsDiscreteValuationRing.maximalIdeal K.O).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h hu)
  simp only [UQ.eta, val, map_mul, hv, mul_one]

private theorem eta_det_trace_matrix_eq_of_span_eq (K : UQ) (B : InvAlg K)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A)
    (m : Fin (Module.finrank K.E B.A) → B.A)
    (hm : Submodule.span K.O (Set.range m) = Submodule.span K.O (Set.range e)) :
    K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)).det =
      K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det := by
  classical
  have hP0 : ∀ l, ∃ c : Fin (Module.finrank K.E B.A) → K.O, ∑ j, c j • e j = m l := by
    intro l
    refine (Submodule.mem_span_range_iff_exists_fun K.O).mp ?_
    rw [← hm]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hQ0 : ∀ l, ∃ c : Fin (Module.finrank K.E B.A) → K.O, ∑ j, c j • m j = e l := by
    intro l
    refine (Submodule.mem_span_range_iff_exists_fun K.O).mp ?_
    rw [hm]
    exact Submodule.subset_span ⟨l, rfl⟩
  choose P hP using hP0
  choose Q hQ using hQ0

  have hli : LinearIndependent K.O e :=
    e.linearIndependent.restrict_scalars fun a b h =>
      IsFractionRing.injective K.O K.E (by simpa [Algebra.smul_def] using h)

  have hsum : ∀ l, ∑ i, (∑ j, Q l j * P j i) • e i = e l := by
    intro l
    calc ∑ i, (∑ j, Q l j * P j i) • e i = ∑ j, Q l j • ∑ i, P j i • e i := by
          simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = e l := by simp only [hP, hQ]
  have hQP : Matrix.of Q * Matrix.of P = 1 := by
    ext l i
    have key : ∑ i, ((Matrix.of Q * Matrix.of P) l i - (1 : Matrix _ _ K.O) l i) • e i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Matrix.of_apply,
        Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, hsum, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ key i)
  have hunit : IsUnit (Matrix.of P).det := Matrix.isUnit_det_of_left_inverse hQP

  have hmat : (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)) =
      (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)) *
        (Matrix.of P).transpose.map (algebraMap K.O K.E) := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
    rw [← hP l]
    simp only [Finset.mul_sum, mul_smul_comm, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul K.E (P l j), map_smul, smul_eq_mul, mul_comm]
  have hdet : ((Matrix.of P).transpose.map (algebraMap K.O K.E)).det =
      algebraMap K.O K.E (Matrix.of P).det := by
    rw [RingHom.map_det, ← Matrix.det_transpose]
    rfl
  rw [hmat, Matrix.det_mul, hdet]
  exact eta_mul_isUnit K _ _ hunit

theorem sgnLat_span_basis (K : UQ) (B : InvAlg K) (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    B.sgnLat (Submodule.span K.O (Set.range e)) =
      K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det := by
  dsimp only [InvAlg.sgnLat]
  exact eta_det_trace_matrix_eq_of_span_eq K B e _
    (Classical.epsilon_spec (p := fun m : Fin (Module.finrank K.E B.A) → B.A =>
      Submodule.span K.O (Set.range m) = Submodule.span K.O (Set.range e)) ⟨e, rfl⟩)

end GlobalTheory.UnitLemma.SgnBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Sl2GeneratedWeylUnipotent
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SLGen

theorem exists_unif (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    ∃ ϖ : F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧ ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hK : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball 0 1)
      Metric.ball_subset_closedBall
  obtain ⟨ϖ, hϖ, hmax⟩ := hK.exists_isMaxOn ⟨0, by simp⟩ continuous_norm.continuousOn
  have hϖ1 : ‖ϖ‖ < 1 := by simpa using hϖ
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one F
  refine ⟨ϖ, ?_, hϖ1, hle⟩
  intro h
  have := hle x hx1
  rw [h, norm_zero] at this
  linarith

variable {F : Type} [Field F]

theorem nS_coe (z : F) : ((nS z : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, z; 0, 1] := rfl

theorem wS_coe : ((wS F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

theorem wS_inv_coe :
    (((wS F)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, wS_coe, Matrix.adjugate_fin_two]; simp

theorem diag_coe {ϖ : F} (hϖ : ϖ ≠ 0) :
    ((nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![ϖ, 0; 0, ϖ⁻¹] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hϖ] <;> field_simp <;> ring

theorem conj_step {ϖ : F} (hϖ : ϖ ≠ 0) (t : F) :
    (nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹)⁻¹ * nS t *
      (nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹) = nS (ϖ⁻¹ ^ 2 * t) := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, diag_coe hϖ, nS_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem decomp (g : SpecialLinearGroup (Fin 2) F) (hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    g = nS (((g : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) F) 1 0) *
      ((wS F)⁻¹ * nS (-(g : Matrix (Fin 2) (Fin 2) F) 1 0) * wS F) *
      nS (((g : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination -hdet | linear_combination -2 * hdet | linear_combination hdet |
      linear_combination 2 * hdet

theorem eq_top_of (H : Subgroup (SpecialLinearGroup (Fin 2) F)) (hw : wS F ∈ H) (hn : ∀ t, nS t ∈ H) :
    H = ⊤ := by
  have hl : ∀ c : F, (wS F)⁻¹ * nS (-c) * wS F ∈ H := fun c =>
    H.mul_mem (H.mul_mem (H.inv_mem hw) (hn _)) hw
  have key : ∀ g : SpecialLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → g ∈ H := by
    intro g hc
    rw [decomp g hc]
    exact H.mul_mem (H.mul_mem (hn _) (hl _)) (hn _)
  rw [eq_top_iff]
  intro g _
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have hdet := g.2
    rw [Matrix.det_fin_two, hc] at hdet
    have ha : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h; rw [h] at hdet; simp at hdet
    set L1 : SpecialLinearGroup (Fin 2) F := (wS F)⁻¹ * nS (-(1 : F)) * wS F
    have h1 : L1 * g ∈ H := by
      apply key
      simp only [L1, Matrix.SpecialLinearGroup.coe_mul, nS_coe, wS_coe, wS_inv_coe]
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc, ha]
    have : g = L1⁻¹ * (L1 * g) := by group
    rw [this]
    exact H.mul_mem (H.inv_mem (hl 1)) h1
  · exact key g hc

end GlobalTheory.JR.SLGen

open GlobalTheory.JR.SLGen in

theorem GlobalTheory.JR.sl2_closure_weyl_unipotent_eq_top :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      [Unram F E], Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t}) = ⊤ := by
  intro F E _ _ _ _ hU
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  set H := Subgroup.closure ({wS F} ∪ {g | ∃ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) ∧ g = nS t})
  obtain ⟨ϖ, hϖ0, hϖ1, hmax⟩ := exists_unif F
  have hw : wS F ∈ H := Subgroup.subset_closure (Or.inl rfl)
  have hS : ∀ t : F, (∀ y : F, ‖y‖ < 1 → ‖t * y‖ ≤ 1) → nS t ∈ H := fun t ht =>
    Subgroup.subset_closure (Or.inr ⟨t, ht, rfl⟩)
  have hball : ∀ t : F, ‖t‖ ≤ 1 → nS t ∈ H := fun t ht => hS t fun y hy => by
    rw [norm_mul]; nlinarith [norm_nonneg t, norm_nonneg y]
  have hinv : nS ϖ⁻¹ ∈ H := hS _ fun y hy => by
    have hp : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hp, mul_one]
    exact hmax y hy
  have hD : nS ϖ * ((wS F)⁻¹ * nS ϖ⁻¹ * wS F) * nS ϖ * (wS F)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (hball _ hϖ1.le)
      (H.mul_mem (H.mul_mem (H.inv_mem hw) hinv) hw)) (hball _ hϖ1.le)) (H.inv_mem hw)
  have hstep : ∀ t, nS t ∈ H → nS (ϖ⁻¹ ^ 2 * t) ∈ H := fun t ht => by
    rw [← conj_step hϖ0 t]
    exact H.mul_mem (H.mul_mem (H.inv_mem hD) ht) hD
  have hpow : ∀ k : ℕ, ∀ t, nS t ∈ H → nS ((ϖ⁻¹ ^ 2) ^ k * t) ∈ H := by
    intro k
    induction k with
    | zero => intro t ht; simpa using ht
    | succ k ih => intro t ht; rw [pow_succ', mul_assoc]; exact hstep _ (ih t ht)
  have hall : ∀ x : F, nS x ∈ H := by
    intro x
    have hq : ‖ϖ ^ 2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg ϖ]
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖x‖ + 1) by positivity) hq
    have h1 : ‖(ϖ ^ 2) ^ k * x‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      rw [lt_div_iff₀ (by positivity)] at hk
      nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg (ϖ ^ 2)) k]
    have e : x = (ϖ⁻¹ ^ 2) ^ k * ((ϖ ^ 2) ^ k * x) := by
      rw [← mul_assoc, ← mul_pow, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hϖ0), one_pow, one_mul]
    rw [e]
    exact hpow k _ (hball _ h1)
  exact eq_top_of H hw hall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanSelfDual
section
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma.OrthoSelfDual

noncomputable def hermLeft {K : UQ} (B : InvAlg K) (x z : B.A) : B.A →ₗ[K.E] K.E where
  toFun y := B.herm x y z
  map_add' a b := by
    unfold InvAlg.herm
    rw [mul_add, add_mul, map_add]
  map_smul' e y := by
    unfold InvAlg.herm
    rw [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply]

theorem herm_basis {K : UQ} (B : InvAlg K) (x : B.A) (n : ℕ) (e : Module.Basis (Fin n) K.E B.A)
    (h : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (y : B.A) (j : Fin n) :
    B.herm x y (e j) = e.repr y j := by

  have hlin : hermLeft B x (e j) = e.coord j := by
    refine e.ext fun i => ?_
    rw [Module.Basis.coord_apply, e.repr_self, Finsupp.single_apply]
    exact h i j
  have := LinearMap.congr_fun hlin y
  rw [Module.Basis.coord_apply] at this
  exact this

private lemma coord_lemma {K : UQ} (B : InvAlg K) (n : ℕ) (e : Module.Basis (Fin n) K.E B.A) (y : B.A) :
    y ∈ Submodule.span K.O (Set.range e) ↔ ∀ j, e.repr y j ∈ (algebraMap K.O K.E).range := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      intro j
      rw [e.repr_self, Finsupp.single_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    | zero =>
      intro j
      rw [map_zero, Finsupp.zero_apply]
      exact zero_mem _
    | add a b _ _ ha hb =>
      intro j
      rw [map_add, Finsupp.add_apply]
      exact add_mem (ha j) (hb j)
    | smul o a _ ha =>
      intro j
      rw [← algebraMap_smul K.E o a, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_mem ⟨o, rfl⟩ (ha j)
  · intro h
    rw [← e.sum_repr y]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨o, ho⟩ := h j
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨j, rfl⟩)

theorem span_selfDual (K : UQ) (B : InvAlg K) (x : B.A) (n : ℕ) (e : Module.Basis (Fin n) K.E B.A)
    (h : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (y : B.A) :
    y ∈ Submodule.span K.O (Set.range e) ↔
      ∀ z ∈ Submodule.span K.O (Set.range e), B.herm x y z ∈ (algebraMap K.O K.E).range := by
  rw [coord_lemma B n e y]
  constructor
  · intro hy z hz

    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨j, rfl⟩ := hw
      rw [herm_basis B x n e h y j]
      exact hy j
    | zero => simp [InvAlg.herm]
    | add a b _ _ ha hb =>
      have hadd : B.herm x y (a + b) = B.herm x y a + B.herm x y b := by
        unfold InvAlg.herm
        rw [map_add, mul_add, map_add]
      rw [hadd]
      exact add_mem ha hb
    | smul o a _ ha =>
      obtain ⟨o', ho'⟩ := K.c_int o
      have hsmul : B.herm x y (o • a) = algebraMap K.O K.E o' * B.herm x y a := by
        unfold InvAlg.herm
        rw [← algebraMap_smul K.E o a, Algebra.smul_def, map_mul B.σ, B.σ_alg, ho', mul_left_comm,
          ← Algebra.smul_def, map_smul, smul_eq_mul]
      rw [hsmul]
      exact mul_mem ⟨o', rfl⟩ ha
  · intro hy j
    rw [← herm_basis B x n e h y j]
    exact hy (e j) (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.UnitLemma.OrthoSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubIdBijOfContracting
section
noncomputable section
namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem sub_id_bij_of_contracting {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (I : Ideal A)
    [IsPrecomplete I M] [IsHausdorff I M] (T : M →+ M)
    (hT : ∀ (j : ℕ) (m : M), m ∈ (I ^ j • ⊤ : Submodule A M) → T m ∈ (I ^ (j + 1) • ⊤ : Submodule A M)) :
    (∀ b : M, ∃ m, T m - m = b) ∧ ∀ m : M, T m = m → m = 0 := by
  have hmem0 : ∀ m : M, m ∈ (I ^ 0 • ⊤ : Submodule A M) := by intro m; simp

  have hTpow : ∀ (j k : ℕ) (m : M), m ∈ (I ^ j • ⊤ : Submodule A M) →
      T^[k] m ∈ (I ^ (j + k) • ⊤ : Submodule A M) := by
    intro j k
    induction k with
    | zero => intro m hm; simpa using hm
    | succ k ih =>
      intro m hm
      rw [Function.iterate_succ_apply', ← add_assoc]
      exact hT _ _ (ih m hm)
  have hhaus : ∀ m : M, (∀ j, m ∈ (I ^ j • ⊤ : Submodule A M)) → m = 0 := fun m hm =>
    IsHausdorff.haus ‹IsHausdorff I M› m fun j => by rw [SModEq.zero]; exact hm j
  have hle : ∀ {j k : ℕ}, j ≤ k → (I ^ k • ⊤ : Submodule A M) ≤ I ^ j • ⊤ :=
    fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  refine ⟨fun b => ?_, fun m hm => hhaus m fun j => ?_⟩
  · have hiter : ∀ k, T^[k] b ∈ (I ^ k • ⊤ : Submodule A M) := fun k => by
      simpa using hTpow 0 k b (hmem0 b)

    have hcauchy : ∀ {m n : ℕ}, m ≤ n →
        (fun n => -(∑ k ∈ Finset.range n, T^[k] b)) m ≡
          (fun n => -(∑ k ∈ Finset.range n, T^[k] b)) n [SMOD (I ^ m • ⊤ : Submodule A M)] := by
      intro m n hmn
      rw [SModEq.sub_mem]
      have hd : -(∑ k ∈ Finset.range m, T^[k] b) - -(∑ k ∈ Finset.range n, T^[k] b) =
          ∑ k ∈ Finset.Ico m n, T^[k] b := by
        rw [Finset.sum_Ico_eq_sub _ hmn]
        abel
      simp only
      rw [hd]
      exact Submodule.sum_mem _ fun k hk => hle (Finset.mem_Ico.mp hk).1 (hiter k)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹IsPrecomplete I M› hcauchy
    refine ⟨L, sub_eq_zero.mp (hhaus _ fun j => ?_)⟩
    have h1 : L - -(∑ k ∈ Finset.range j, T^[k] b) ∈ (I ^ j • ⊤ : Submodule A M) := by
      have h := SModEq.sub_mem.mp (hL j)
      rw [← neg_sub]
      exact Submodule.neg_mem _ h
    have htel := Finset.sum_range_sub' (fun k => T^[k] b) j
    rw [Finset.sum_sub_distrib] at htel
    simp only [Function.iterate_zero_apply] at htel
    have hsucc : ∀ k, T (T^[k] b) = T^[k + 1] b := fun k => (Function.iterate_succ_apply' T k b).symm
    have h2 : T (-(∑ k ∈ Finset.range j, T^[k] b)) - -(∑ k ∈ Finset.range j, T^[k] b) - b =
        -(T^[j] b) := by
      rw [map_neg, map_sum]
      simp only [hsucc]
      have e : -(∑ k ∈ Finset.range j, T^[k + 1] b) - -(∑ k ∈ Finset.range j, T^[k] b) - b =
          ((∑ k ∈ Finset.range j, T^[k] b) - ∑ k ∈ Finset.range j, T^[k + 1] b) - b := by abel
      rw [e, htel]
      abel
    have h3 : T (L - -(∑ k ∈ Finset.range j, T^[k] b)) ∈ (I ^ j • ⊤ : Submodule A M) :=
      hle (Nat.le_succ j) (hT j _ h1)
    have hsplit : T L - L - b = (T (L - -(∑ k ∈ Finset.range j, T^[k] b)) -
        (L - -(∑ k ∈ Finset.range j, T^[k] b))) +
        (T (-(∑ k ∈ Finset.range j, T^[k] b)) - -(∑ k ∈ Finset.range j, T^[k] b) - b) := by
      rw [map_sub]
      abel
    rw [hsplit, h2]
    exact Submodule.add_mem _ (Submodule.sub_mem _ h3 h1) (Submodule.neg_mem _ (hiter j))
  · induction j with
    | zero => exact hmem0 m
    | succ j ih =>
      have h := hT j m ih
      rwa [hm] at h

theorem mem_span_pow_smul_top {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (x : A) (j : ℕ) (m : M) :
    m ∈ (Ideal.span {x} ^ j • ⊤ : Submodule A M) ↔ ∃ y, x ^ j • y = m := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

theorem contracting_of_semi {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (x c : A) (T : M →+ M)
    (h1 : ∀ m, T (x • m) = (c * x) • T m) (h2 : ∀ m, ∃ y, x • y = T m) (j : ℕ) (m : M)
    (hm : m ∈ (Ideal.span {x} ^ j • ⊤ : Submodule A M)) :
    T m ∈ (Ideal.span {x} ^ (j + 1) • ⊤ : Submodule A M) := by
  rw [mem_span_pow_smul_top] at hm ⊢
  obtain ⟨y, rfl⟩ := hm
  obtain ⟨z, hz⟩ := h2 y
  have hpow : ∀ (i : ℕ) (m : M), T (x ^ i • m) = (c * x) ^ i • T m := by
    intro i
    induction i with
    | zero => intro m; simp
    | succ i ih => intro m; rw [pow_succ, mul_smul, ih, h1, smul_smul, ← pow_succ]
  refine ⟨c ^ j • z, ?_⟩
  rw [hpow, ← hz, smul_smul, smul_smul]
  congr 1
  ring

theorem one_sub_frob_bij : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (P : ZMod n → Submodule k⟦X⟧ V), (∀ i, IsLat (P i)) → (∀ i, ∀ x ∈ P (i - 1), D.φ i x ∈ sh 1 (P i)) → (∀ b : ZMod n → V, (∀ i, b i ∈ P i) → ∃ m : ZMod n → V, (∀ i, m i ∈ P i) ∧ ∀ i, D.φ i (m (i - 1)) - m i = b i) ∧ ∀ m : ZMod n → V, (∀ i, m i ∈ P i) → (∀ i, D.φ i (m (i - 1)) = m i) → m = 0 := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D P hP hφ

  have hcoe : ∀ (a : k⟦X⟧) (y : V), a • y = ((a : k⟦X⟧) : k⸨X⸩) • y := by
    intro a y
    rw [← algebraMap_smul k⸨X⸩ a y]
    rfl
  have hφP : ∀ i, ∀ x ∈ P (i - 1), ∃ y ∈ P i, (PowerSeries.X : k⟦X⟧) • y = D.φ i x := by
    intro i x hx
    obtain ⟨y, hy, hyx⟩ := mem_sh_iff_exists.mp (hφ i x hx)
    exact ⟨y, hy, by rw [hcoe, ← vv_eq_coe_X, ← hyx, zpow_one]⟩
  have hφmem : ∀ i, ∀ x ∈ P (i - 1), D.φ i x ∈ P i := by
    intro i x hx
    obtain ⟨y, hy, hyx⟩ := hφP i x hx
    rw [← hyx]
    exact (P i).smul_mem _ hy

  let T : ((i : ZMod n) → P i) →+ ((i : ZMod n) → P i) :=
    { toFun := fun m i => ⟨D.φ i (m (i - 1)), hφmem i _ (m (i - 1)).2⟩
      map_zero' := by
        funext i
        apply Subtype.ext
        simp
      map_add' := by
        intro a b
        funext i
        apply Subtype.ext
        simp [map_add] }
  have : ∀ i, Module.Finite k⟦X⟧ (P i) := fun i => Module.Finite.iff_fg.mpr (hP i).1
  have hXtop : Ideal.span {(PowerSeries.X : k⟦X⟧)} ≠ ⊤ := by
    intro h
    have h1 := (Ideal.span_singleton_eq_top.mp h).map (PowerSeries.constantCoeff (R := k))
    simp at h1
  have : IsHausdorff (Ideal.span {(PowerSeries.X : k⟦X⟧)}) ((i : ZMod n) → P i) :=
    IsHausdorff.of_isLocalRing _ _ hXtop
  have : IsPrecomplete (Ideal.span {(PowerSeries.X : k⟦X⟧)}) ((i : ZMod n) → P i) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module _ _

  obtain ⟨u, hu⟩ := R.φ_v
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have h1 : ∀ m : ((i : ZMod n) → P i), T ((PowerSeries.X : k⟦X⟧) • m) =
      (((u : k⟦X⟧) * PowerSeries.X ^ (l - 1)) * PowerSeries.X) • T m := by
    intro m
    funext i
    apply Subtype.ext
    simp only [T, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, Submodule.coe_smul]
    rw [hcoe, hcoe, ← vv_eq_coe_X, D.φ_semi, hu, PowerSeries.coe_mul, PowerSeries.coe_mul,
      PowerSeries.coe_pow, ← vv_eq_coe_X, mul_assoc, pow_sub_one_mul hl]
  have h2 : ∀ m : ((i : ZMod n) → P i), ∃ y : ((i : ZMod n) → P i),
      (PowerSeries.X : k⟦X⟧) • y = T m := by
    intro m
    choose y hy hyx using fun i => hφP i _ (m (i - 1)).2
    exact ⟨fun i => ⟨y i, hy i⟩, funext fun i => Subtype.ext (hyx i)⟩
  obtain ⟨hsurj, hinj⟩ := sub_id_bij_of_contracting (Ideal.span {(PowerSeries.X : k⟦X⟧)}) T
    (fun j m hm => contracting_of_semi _ _ T h1 h2 j m hm)
  refine ⟨fun b hb => ?_, fun m hm hfix => ?_⟩
  · obtain ⟨m, hm⟩ := hsurj (fun i => ⟨b i, hb i⟩)
    refine ⟨fun i => (m i : V), fun i => (m i).2, fun i => ?_⟩
    have h := congrArg (fun z => ((z i : P i) : V)) hm
    simpa [T] using h
  · have h := hinj (fun i => ⟨m i, hm i⟩) (funext fun i => Subtype.ext (hfix i))
    funext i
    have hi := congrArg (fun z => ((z i : P i) : V)) h
    simpa using hi

end GlobalTheory.PhiGam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitiveStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_action_hermitian_invariants_transitive : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ X : Hn r F E, ∃ a : Inv r F, HasInv X a) ∧ (∀ (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (a : Inv r F), HasInv X a → HasInv (actU g X) a) ∧ (∀ (X₁ X₂ : Hn r F E) (a : Inv r F), Delta a ≠ 0 → HasInv X₁ a → HasInv X₂ a → ∃! g : Matrix.unitaryGroup (Fin r) E, actU g X₁ = X₂) ∧ ∀ a : Inv r F, Delta a ≠ 0 → ((∃ X : Hn r F E, HasInv X a) ↔ ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map (algebraMap F E)) := by
  first | exact @GlobalTheory.JR.HermInv.herm_invariants | exact GlobalTheory.JR.HermInv.herm_invariants | (intros; apply GlobalTheory.JR.HermInv.herm_invariants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfectStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) ∧ (∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1) ∧ ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ‖Algebra.trace F E (e * y)‖ < 1) → ‖y‖ < 1 := by
  first | exact @GlobalTheory.NTr.traceForm_perfect | exact GlobalTheory.NTr.traceForm_perfect | (intros; apply GlobalTheory.NTr.traceForm_perfect <;> assumption)
end

