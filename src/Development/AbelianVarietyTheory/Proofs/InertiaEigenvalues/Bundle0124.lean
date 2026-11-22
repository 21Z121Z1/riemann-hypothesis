import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0112
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0056
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0058
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0099
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0102
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0109

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSatMOfSmul
section
namespace GlobalTheory.NL.Coker

open Formalism.BasicNotions

variable {O : Type} [CommRing O] {n : ℕ} {M : Type} [AddCommGroup M] [Module (LetA O n) M]

def satM (p : ℕ) (P N : Submodule (LetA O n) M) : Submodule (LetA O n) M where
  carrier := {x | x ∈ N ∧ ∃ k : ℕ, ((p : LetA O n)) ^ k • x ∈ P ∧ (letπ : LetA O n) ^ k • x ∈ P}
  add_mem' := by
    rintro x y ⟨hx, k, hk1, hk2⟩ ⟨hy, j, hj1, hj2⟩
    refine ⟨N.add_mem hx hy, k + j, ?_, ?_⟩
    · rw [smul_add, pow_add]
      refine P.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact P.smul_mem _ hk1
      · rw [mul_smul]; exact P.smul_mem _ hj1
    · rw [smul_add, pow_add]
      refine P.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact P.smul_mem _ hk2
      · rw [mul_smul]; exact P.smul_mem _ hj2
  zero_mem' := ⟨N.zero_mem, 0, by simp, by simp⟩
  smul_mem' := by
    rintro a x ⟨hx, k, hk1, hk2⟩
    refine ⟨N.smul_mem a hx, k, ?_, ?_⟩
    · rw [smul_comm]; exact P.smul_mem a hk1
    · rw [smul_comm]; exact P.smul_mem a hk2

theorem satM_le (p : ℕ) (P N : Submodule (LetA O n) M) : satM p P N ≤ N := fun _ hx => hx.1

theorem le_satM (p : ℕ) {P N : Submodule (LetA O n) M} (h : P ≤ N) : P ≤ satM p P N :=
  fun x hx => ⟨h hx, 0, by simpa using hx, by simpa using hx⟩

theorem mem_satM_of_smul {p : ℕ} {P N : Submodule (LetA O n) M} {x : M} (hx : x ∈ N)
    (h1 : ((p : LetA O n)) • x ∈ satM p P N) (h2 : (letπ : LetA O n) • x ∈ satM p P N) :
    x ∈ satM p P N := by
  obtain ⟨-, k, hk1, -⟩ := h1
  obtain ⟨-, j, -, hj2⟩ := h2
  refine ⟨hx, k + j + 1, ?_, ?_⟩
  · have : ((p : LetA O n)) ^ (k + j + 1) • x = ((p : LetA O n)) ^ j • (((p : LetA O n)) ^ k • ((p : LetA O n)) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]; exact P.smul_mem _ hk1
  · have : (letπ : LetA O n) ^ (k + j + 1) • x = (letπ : LetA O n) ^ k • ((letπ : LetA O n) ^ j • (letπ : LetA O n) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]; exact P.smul_mem _ hj2

theorem uniform {p : ℕ} {P N : Submodule (LetA O n) M} (hN : N.FG) (h : N ≤ satM p P N) :
    ∃ c : ℕ, ∀ z ∈ N, ((p : LetA O n)) ^ c • z ∈ P ∧ (letπ : LetA O n) ^ c • z ∈ P := by
  classical
  obtain ⟨G, rfl⟩ := hN
  have hk : ∀ x ∈ G, ∃ k : ℕ, ((p : LetA O n)) ^ k • x ∈ P ∧ (letπ : LetA O n) ^ k • x ∈ P :=
    fun x hx => (h (Submodule.subset_span hx)).2
  choose! k hk using hk
  refine ⟨G.sup k, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem x hx =>
    have hle : k x ≤ G.sup k := Finset.le_sup hx
    obtain ⟨h1, h2⟩ := hk x hx
    constructor
    · rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]; exact P.smul_mem _ h1
    · rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]; exact P.smul_mem _ h2
  | zero => simp
  | add x y _ _ hx hy =>
    exact ⟨by rw [smul_add]; exact P.add_mem hx.1 hy.1, by rw [smul_add]; exact P.add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    exact ⟨by rw [smul_comm]; exact P.smul_mem a hx.1, by rw [smul_comm]; exact P.smul_mem a hx.2⟩

end GlobalTheory.NL.Coker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCharacterOnIdempotentPartProdInlStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normCharacterOnIdempotentPart_prod_inl : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) (e₁ : ι₁ → B₁.A) (e₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (x : B₁.A × B₂.A), chi (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (S₁.map Function.Embedding.inl) x = chi B₁ e₁ S₁ x.1 := by
  first | exact @GlobalTheory.UnitLemma.Desc.chi_prod_inl | exact GlobalTheory.UnitLemma.Desc.chi_prod_inl | (intros; apply GlobalTheory.UnitLemma.Desc.chi_prod_inl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowSubOneOfNotDvd
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Cyc

theorem geom_sum_one_add_expand {R : Type*} [CommRing R] (y : R) (n : ℕ) :
    ∃ z : R, (1 + y) ^ n - 1 = y * ((n : R) + (n.choose 2 : ℕ) * y + y ^ 2 * z) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨z + (n.choose 2 : ℕ) + y * z, ?_⟩
    have h : (1 + y) ^ n = 1 + y * ((n : R) + (n.choose 2 : ℕ) * y + y ^ 2 * z) := by
      rw [← hz]; ring
    have hc : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    rw [pow_succ, h, hc]
    push_cast
    ring

variable {l : ℕ} [hl : Fact l.Prime]

theorem padicInt_norm_add_eq_of_lt {a b : ℤ_[l]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [PadicInt.norm_add_eq_max_of_ne h.ne', max_eq_left h.le]

theorem norm_pow_sub_one_of_not_dvd (x : ℤ_[l]) (hx : ‖x - 1‖ < 1) (n : ℕ) (hn : ¬ l ∣ n) :
    ‖x ^ n - 1‖ = ‖x - 1‖ := by
  obtain ⟨z, hz⟩ := geom_sum_one_add_expand (x - 1) n
  rw [add_sub_cancel] at hz
  have hn1 : ‖(n : ℤ_[l])‖ = 1 := by
    apply le_antisymm (PadicInt.norm_le_one _)
    by_contra h
    push_neg at h
    have h' : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
    exact hn (Int.natCast_dvd_natCast.mp h')
  have e : (n : ℤ_[l]) + (n.choose 2 : ℕ) * (x - 1) + (x - 1) ^ 2 * z
      = n + (x - 1) * ((n.choose 2 : ℕ) + (x - 1) * z) := by ring
  rw [hz, norm_mul, e, padicInt_norm_add_eq_of_lt, hn1, mul_one]
  rw [hn1, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)) hx

theorem norm_pow_prime_sub_one (x : ℤ_[l]) (hx : ‖x - 1‖ ≤ (l : ℝ)⁻¹)
    (h2 : l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) :
    ‖x ^ l - 1‖ = ‖x - 1‖ * ‖(l : ℤ_[l])‖ := by
  obtain ⟨z, hz⟩ := geom_sum_one_add_expand (x - 1) l
  rw [add_sub_cancel] at hz
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hi0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hsq : (l : ℝ)⁻¹ * (l : ℝ)⁻¹ < (l : ℝ)⁻¹ := mul_lt_of_lt_one_right hi0 hi1
  have hA : ‖((l.choose 2 : ℕ) : ℤ_[l]) * (x - 1)‖ < (l : ℝ)⁻¹ := by
    rw [norm_mul]
    by_cases h : l = 2
    · exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)) (h2 h)
    · have hlt : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h)
      obtain ⟨c, hc⟩ := hl.out.dvd_choose_self (k := 2) (by norm_num) hlt
      have : ‖((l.choose 2 : ℕ) : ℤ_[l])‖ ≤ (l : ℝ)⁻¹ := by
        rw [hc, Nat.cast_mul, norm_mul, PadicInt.norm_p]
        exact mul_le_of_le_one_right hi0.le (PadicInt.norm_le_one _)
      exact lt_of_le_of_lt (mul_le_mul this hx (norm_nonneg _) hi0.le) hsq
  have hB : ‖(x - 1) ^ 2 * z‖ < (l : ℝ)⁻¹ := by
    rw [norm_mul, sq, norm_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)) ?_
    exact lt_of_le_of_lt (mul_le_mul hx hx (norm_nonneg _) hi0.le) hsq
  rw [hz, norm_mul, add_assoc, padicInt_norm_add_eq_of_lt]
  rw [PadicInt.norm_p]
  exact lt_of_le_of_lt (PadicInt.nonarchimedean _ _) (max_lt hA hB)

theorem norm_pow_nat_sub_one (n : ℕ) (hn : n ≠ 0) : ∀ (x : ℤ_[l]), ‖x - 1‖ ≤ (l : ℝ)⁻¹ →
    (l = 2 → ‖x - 1‖ < (l : ℝ)⁻¹) → ‖x ^ n - 1‖ = ‖x - 1‖ * ‖(n : ℤ_[l])‖ := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx h2
    by_cases hd : l ∣ n
    · obtain ⟨m, rfl⟩ := hd
      have hm : m ≠ 0 := by rintro rfl; simp at hn
      have hlt : m < l * m := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm) hl.out.one_lt
      have key := norm_pow_prime_sub_one x hx h2
      have hle : ‖x ^ l - 1‖ ≤ ‖x - 1‖ := by
        rw [key]; exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
      rw [pow_mul, ih m hlt hm (x ^ l) (hle.trans hx) (fun h => hle.trans_lt (h2 h)), key,
        Nat.cast_mul, norm_mul, mul_assoc]
    · have hn1 : ‖(n : ℤ_[l])‖ = 1 := by
        apply le_antisymm (PadicInt.norm_le_one _)
        by_contra h
        push_neg at h
        have h' : ‖((n : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
        rw [PadicInt.norm_int_lt_one_iff_dvd] at h'
        exact hd (Int.natCast_dvd_natCast.mp h')
      rw [norm_pow_sub_one_of_not_dvd x (hx.trans_lt hi1) n hd, hn1, mul_one]

theorem norm_unit_zpow_sub_one :
    ∀ (l : ℕ) [Fact l.Prime], ∀ (s : ℕ) (u : ℤ_[l]ˣ), 1 ≤ s → (l = 2 → 2 ≤ s) →
      ‖(u : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) → ∀ n : ℤ, n ≠ 0 →
      ‖((u ^ n : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) * ‖(n : ℤ_[l])‖ := by
  intro l hl s u hs h2 hu n hn
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hx : ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ)⁻¹ := by
    rw [hu, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1.le (by omega)
  have hx2 : l = 2 → ‖(u : ℤ_[l]) - 1‖ < (l : ℝ)⁻¹ := fun h => by
    have := h2 h
    rw [hu, ← zpow_neg_one]
    exact zpow_lt_zpow_right₀ hl1 (by omega)
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · have hm : m ≠ 0 := by rintro rfl; simp at hn
    rw [zpow_natCast, Units.val_pow_eq_pow_val, norm_pow_nat_sub_one m hm _ hx hx2, hu,
      Int.cast_natCast]
  · have hm : m ≠ 0 := by rintro rfl; simp at hn
    have e : (((u ^ m)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) - 1
        = -((((u ^ m)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (((u ^ m : ℤ_[l]ˣ) : ℤ_[l]) - 1)) := by
      rw [mul_sub, Units.inv_mul]; ring
    rw [zpow_neg, zpow_natCast, e, norm_neg, norm_mul, PadicInt.norm_units, one_mul,
      Units.val_pow_eq_pow_val, norm_pow_nat_sub_one m hm _ hx hx2, hu, Int.cast_neg, norm_neg,
      Int.cast_natCast]

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitalIntegralDescendedEqUnitary
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.DescOrb

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem mulMat_comm (A : Et F E) {r : ℕ} (τ : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (Ax : Matrix (Fin r) (Fin r) E)
    (hA : ∀ z, j (algebraMap A.K A.L τ * z) = Ax *ᵥ j z) (t : A.L) :
    Ax * A.mulMat j t = A.mulMat j t * Ax := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨z, rfl⟩ := j.surjective v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Et.mulMat_mulVec_apply, ← hA]
  congr 1; ring

theorem actU_actU {r : ℕ} (g h : unitaryGroup (Fin r) E) (X : Hn r F E) :
    actU g (actU h X) = actU (g * h) X := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show g.1 * (h.1 * X.1.1 * star h.1) * star g.1 = (g.1 * h.1) * X.1.1 * star (g.1 * h.1)
    rw [star_mul]; simp only [Matrix.mul_assoc]
  · show g.1 *ᵥ (h.1 *ᵥ X.2.1) = (g.1 * h.1) *ᵥ X.2.1
    rw [Matrix.mulVec_mulVec]

end GlobalTheory.JR.DescOrb

namespace GlobalTheory.JR.DescOrb

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_mulMat [hU : Unram F E] (A : Et F E) {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) :
    Continuous fun t : A.L => A.mulMat j t := by
  haveI := hU.lcF
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hj : Continuous (j : A.L → Fin r → E) :=
    IsModuleTopology.continuous_of_linearMap ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  refine continuous_matrix fun i k => ?_
  simp only [Et.mulMat, LinearMap.toMatrix'_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    LinearEquiv.coe_coe]
  exact (continuous_apply i).comp (hj.comp (continuous_id.mul continuous_const))

theorem orbL_descFn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (τ : A.K) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (lam : F) (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → (∀ g, 0 ≤ α g) → ∀ Z : Set (Matrix (Fin r) (Fin r) E), (∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1) → ∀ f₀ : Hn r F E → ℂ, Continuous f₀ → (∀ X, f₀ X ≠ 0 → X.1.1 ∈ Z) → ∀ y : A.L, (letI := M.mU; Integrable (fun g => f₀ (actU g (Ax, j y, lam))) M.μU) → A.orbL ν (A.descFn M Ax j lam α f₀) y = orbU M f₀ (Ax, j y, lam) := by
  intro F E _ _ _ _ hU A r M τ x j hx Ax hA lam ν hν α hα hα0 Z hZ f₀ hf₀ hf₀Z y hint
  letI := M.mU
  haveI := M.bU
  haveI := M.haarU
  haveI := hU.ultraE; haveI := hU.lcE; haveI := hU.ultraF; haveI := hU.lcF
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun y => (hU.norm_star y).le⟩
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) E) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).locallyCompactSpace
  haveI : SecondCountableTopology (unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  haveI : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  haveI : LocallyCompactSpace (unitary A.L) := (isClosed_unitary (R := A.L)).locallyCompactSpace
  haveI : SecondCountableTopology (unitary A.L) :=
    (isClosed_unitary (R := A.L)).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite M.μU := inferInstance
  haveI : M.μU.IsMulRightInvariant := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M
  have huc : Continuous (A.uHom hx) := continuous_induced_rng.2 ((continuous_mulMat A j).comp continuous_subtype_val)
  have hinvc : Continuous fun g : unitaryGroup (Fin r) E => g⁻¹ := continuous_inv

  set X : Hn r F E := (Ax, j y, lam) with hXdef
  have hcomm : ∀ t : unitary A.L, ((A.uHom hx t : Matrix (Fin r) (Fin r) E)) * Ax.1 = Ax.1 * A.uHom hx t := fun t =>
    (mulMat_comm A τ j Ax.1 hA t).symm
  have hshift : ∀ t : unitary A.L, ((Ax, j (t.1 * y), lam) : Hn r F E) = actU (A.uHom hx t) X := by
    intro t
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
    · show Ax.1 = (A.uHom hx t : Matrix (Fin r) (Fin r) E) * Ax.1 * star (A.uHom hx t : Matrix (Fin r) (Fin r) E)
      rw [hcomm, Matrix.mul_assoc, Unitary.mul_star_self_of_mem (A.uHom hx t).2, Matrix.mul_one]
    · show j (t.1 * y) = (A.uHom hx t : Matrix (Fin r) (Fin r) E) *ᵥ j y
      rw [Et.uHom_apply, Et.mulMat_mulVec_apply]
  have step1 : ∀ t : unitary A.L, A.descFn M Ax j lam α f₀ (t.1 * y) =
      ∫ g, f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ) ∂M.μU := by
    intro t
    have h := integral_mul_right_eq_self (μ := M.μU)
      (fun g => f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) (A.uHom hx t)
    simp only [mul_inv_cancel_right] at h
    rw [← h]
    show (∫ g, f₀ (actU g ((Ax, j (t.1 * y), lam) : Hn r F E)) * (α g : ℂ) ∂M.μU) = _
    simp only [hshift t, actU_actU]
  have hact : Continuous fun g : unitaryGroup (Fin r) E => actU g X := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ continuous_const)
    · exact (((continuous_subtype_val.matrix_mul continuous_const).matrix_mul
        (continuous_subtype_val.star))).subtype_mk _
    · exact continuous_subtype_val.matrix_mulVec continuous_const
  have hcont : Continuous (Function.uncurry fun (t : unitary A.L) (g : unitaryGroup (Fin r) E) =>
      f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) :=
    (hf₀.comp (hact.comp continuous_snd)).mul (Complex.continuous_ofReal.comp
      (hα.continuous.comp (continuous_snd.mul (hinvc.comp (huc.comp continuous_fst)))))
  have hαint : ∀ g : unitaryGroup (Fin r) E, f₀ (actU g X) ≠ 0 →
      Integrable (fun t => α (g * (A.uHom hx t)⁻¹)) ν := by
    intro g hg
    by_contra hn
    have h1 := integral_undef hn
    rw [hZ g (hf₀Z _ hg)] at h1
    exact one_ne_zero h1
  have hInt : Integrable (Function.uncurry fun (t : unitary A.L) (g : unitaryGroup (Fin r) E) =>
      f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) (ν.prod M.μU) := by
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => ?_, ?_⟩
    · by_cases hg : f₀ (actU g X) = 0
      · simp [Function.uncurry, hg]
      · exact ((hαint g hg).ofReal).const_mul (f₀ (actU g X))
    · refine hint.norm.congr (Eventually.of_forall fun g => ?_)
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [integral_const_mul]
      by_cases hg : f₀ (actU g X) = 0
      · simp [hg]
      · rw [integral_congr_ae (Eventually.of_forall fun t => abs_of_nonneg (hα0 _)), hZ g (hf₀Z _ hg), mul_one]
  show ∫ t : unitary A.L, A.descFn M Ax j lam α f₀ (t.1 * y) ∂ν = ∫ g, f₀ (actU g X) ∂M.μU
  simp_rw [step1]
  rw [integral_integral_swap hInt]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [integral_const_mul, integral_complex_ofReal]
  by_cases hg : f₀ (actU g X) = 0
  · simp [hg]
  · rw [hZ g (hf₀Z _ hg)]; simp

end GlobalTheory.JR.DescOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSchwartzVanishOffTranslates
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem parahoric_schwartz_vanish_off_translates : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ) (N : ℕ), (∀ x, Φ x ≠ 0 → ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K)) → (∀ h : GL (Fin r ⊕ Fin t) O, (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O).map (algebraMap O K) * x) = Φ x) → (∀ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 → ∀ (lift : GL (Fin r) (IsLocalRing.ResidueField O) → Matrix (Fin r) (Fin r) O), (∀ g, (lift g).map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O))) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, ∑ᶠ g ∈ {g : GL (Fin r) (IsLocalRing.ResidueField O) | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v}, Φ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * x) = 0) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ x ≠ 0 → ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ Φ N hsupp h2 h3 x hx
  classical
  by_contra hnot
  obtain ⟨z, hz⟩ := hsupp x hx
  have hc0 : algebraMap O K (ϖ ^ N) ≠ 0 := by
    rw [Ne, (IsFractionRing.injective O K).eq_iff' (map_zero _)]
    exact pow_ne_zero _ hϖ.ne_zero
  have hzn : ¬ ∃ (g : GL (Fin r) K) (w : Matrix (Fin r ⊕ Fin t) (Fin r) O), z.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w).map (algebraMap O K) := by
    rintro ⟨g, w, hw⟩
    apply hnot
    refine ⟨Units.mk0 _ hc0 • g, w, ?_⟩
    rw [← hw, ← hz]
    simp [Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨a, ha, hcore⟩ := GlobalTheory.T.exists_hyperplane_residue_outside_translates O K r t ϖ hϖ z hzn
  have hsurj : ∀ g : GL (Fin r) (IsLocalRing.ResidueField O), ∃ L : Matrix (Fin r) (Fin r) O, L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) := by
    intro g
    have hs' : ∀ i j, ∃ o : O, IsLocalRing.residue O o = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) i j :=
      fun i j => IsLocalRing.residue_surjective _
    choose L hL using hs'
    exact ⟨Matrix.of L, by ext i j; exact hL i j⟩
  choose lift hlift using hsurj
  have hs := h3 a ha lift hlift x
  set G := {g : GL (Fin r) (IsLocalRing.ResidueField O) | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v} with hG
  have hfix : ∀ g ∈ G, Φ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * x) = Φ x := by
    intro g hg
    obtain ⟨h, hh1, hh2, hh3⟩ := hcore g hg (lift g) (hlift g)
    rw [← h2 h hh1 hh2]
    congr 1
    have e1 := congrArg (fun m : Matrix (Fin r ⊕ Fin t) (Fin r) O => m.map (algebraMap O K)) hh3
    simp only [Matrix.map_mul] at e1
    rw [← hz] at e1
    rw [Matrix.mul_smul, Matrix.mul_smul] at e1
    exact smul_right_injective _ hc0 e1
  rw [finsum_mem_congr rfl hfix] at hs
  have hGfin : G.Finite := Set.toFinite G
  rw [finsum_mem_eq_finite_toFinset_sum _ hGfin, Finset.sum_const] at hs
  have h1 : (1 : GL (Fin r) (IsLocalRing.ResidueField O)) ∈ hGfin.toFinset := by
    rw [Set.Finite.mem_toFinset]; intro v _; simp
  have hcard : hGfin.toFinset.card ≠ 0 := Finset.card_ne_zero.2 ⟨_, h1⟩
  rw [nsmul_eq_mul] at hs
  exact hx ((mul_eq_zero.1 hs).resolve_left (by exact_mod_cast hcard))

theorem parahoric_schwartz_mem_span_translates : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ Φ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ, (∃ N : ℕ, (∀ x (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), Φ (x + (ϖ ^ N • z).map (algebraMap O K)) = Φ x) ∧ ∀ x, Φ x ≠ 0 → ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K)) → (∀ h : GL (Fin r ⊕ Fin t) O, (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O).map (algebraMap O K) * x) = Φ x) → (∀ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 → ∀ (lift : GL (Fin r) (IsLocalRing.ResidueField O) → Matrix (Fin r) (Fin r) O), (∀ g, (lift g).map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O))) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, ∑ᶠ g ∈ {g : GL (Fin r) (IsLocalRing.ResidueField O) | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v}, Φ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin t) (Fin t) O)).map (algebraMap O K) * x) = 0) → Φ ∈ Submodule.span ℂ {Ψ | ∃ g : GL (Fin r) K, Ψ = Set.indicator {x : Matrix (Fin r ⊕ Fin t) (Fin r) K | ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, x * (g : Matrix (Fin r) (Fin r) K) = (Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O) + ϖ • z).map (algebraMap O K)} (fun _ => (1 : ℂ))} := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ Φ ⟨N, hinv, hsupp⟩ h2 h3
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.T.finite_classes_mod_uniformizer_pow_matrices O K r t ϖ hϖ N
  have hΩ := GlobalTheory.parahoric_schwartz_vanish_off_translates O K r t ϖ hϖ Φ N hsupp h2 h3
  set S : GL (Fin r) K → Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) := fun g =>
    {x | ∃ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)} with hS
  have hconst : ∀ g x x', x ∈ S g → x' ∈ S g → Φ x = Φ x' := by
    rintro g x x' ⟨z, hz⟩ ⟨z', hz'⟩
    rw [GlobalTheory.T.congruenceInvariant_const_on_frame_translate O K r t ϖ hϖ Φ h2 x g z hz, GlobalTheory.T.congruenceInvariant_const_on_frame_translate O K r t ϖ hϖ Φ h2 x' g z' hz']
  have huniq : ∀ g g' x, x ∈ S g → x ∈ S g' → S g = S g' := by
    rintro g g' x ⟨z, hz⟩ ⟨z', hz'⟩
    ext y; constructor
    · rintro ⟨w, hw⟩; exact GlobalTheory.T.frame_translate_lattice_coset_subset O K r t ϖ hϖ x g g' z z' hz hz' y w hw
    · rintro ⟨w, hw⟩; exact GlobalTheory.T.frame_translate_lattice_coset_subset O K r t ϖ hϖ x g' g z' z hz' hz y w hw
  let gs : Matrix (Fin r ⊕ Fin t) (Fin r) K → GL (Fin r) K := fun y =>
    if h : Φ y ≠ 0 then (hΩ y h).choose else 1
  have hgs : ∀ y, Φ y ≠ 0 → y ∈ S (gs y) := by
    intro y hy
    simp only [gs, dif_pos hy]
    exact (hΩ y hy).choose_spec
  let F : Finset (Set (Matrix (Fin r ⊕ Fin t) (Fin r) K)) :=
    (T.filter (fun y => Φ y ≠ 0)).image (fun y => S (gs y))
  have hcover : ∀ x, Φ x ≠ 0 → ∃ A ∈ F, x ∈ A := by
    intro x hx
    obtain ⟨z, hz⟩ := hsupp x hx
    obtain ⟨y, hyT, z', rfl⟩ := hT x z hz
    have hy : Φ y ≠ 0 := by rwa [hinv] at hx
    refine ⟨S (gs y), Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨hyT, hy⟩, rfl⟩, ?_⟩
    obtain ⟨z₀, hz₀⟩ := hgs y hy
    exact GlobalTheory.T.lattice_coset_translate_mem_of_cover O K r t ϖ hϖ N y (gs y) z₀ hz₀ (fun z => hΩ _ (by rwa [hinv])) z'
  have hF : ∀ A ∈ F, ∃ g, A = S g := by
    intro A hA
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hA
    exact ⟨_, rfl⟩
  let c : Set (Matrix (Fin r ⊕ Fin t) (Fin r) K) → ℂ := fun A => if h : A.Nonempty then Φ h.some else 0
  have hc : ∀ A ∈ F, ∀ x ∈ A, c A = Φ x := by
    intro A hA x hx
    obtain ⟨g, rfl⟩ := hF A hA
    have hne : (S g).Nonempty := ⟨x, hx⟩
    simp only [c, dif_pos hne]
    exact hconst g _ _ hne.some_mem hx
  have heq : Φ = ∑ A ∈ F, c A • A.indicator (fun _ => (1 : ℂ)) := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Set.indicator_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hx : Φ x = 0
    · rw [hx]; symm
      apply Finset.sum_eq_zero
      intro A hA
      split_ifs with h
      · rw [hc A hA x h, hx]
      · rfl
    · obtain ⟨A, hA, hxA⟩ := hcover x hx
      rw [Finset.sum_eq_single A]
      · rw [if_pos hxA, hc A hA x hxA]
      · intro B hB hBA
        rw [if_neg]
        intro hxB
        obtain ⟨g, rfl⟩ := hF A hA
        obtain ⟨g', rfl⟩ := hF B hB
        exact hBA (huniq g' g x hxB hxA)
      · intro h; exact absurd hA h
  rw [heq]
  refine Submodule.sum_mem _ fun A hA => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  obtain ⟨g, rfl⟩ := hF A hA
  exact ⟨g, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPreservesTestFixesUnit
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem fourier_test_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ f', IsTest f' → IsTest (fourG M ψ f')) ∧ (∀ f, IsTest f → IsTest (fourU M ψ f)) ∧ IsTest (unitG r F) ∧ IsTest (unitU r F E) ∧ fourG M ψ (unitG r F) = unitG r F ∧ fourU M ψ (unitU r F E) = unitU r F E := by
  intro F E _ _ _ _ hU r M ψ hψ
  haveI := hU.ultraF; haveI := hU.ultraE; haveI := hU.lcF; haveI := hU.lcE
  have htr := GlobalTheory.T.unramifiedQuadratic_trace_eq_add_star F E
  refine ⟨fun f' hf => ⟨GlobalTheory.T.isLocallyConstant_partialFourierGLBlock F E r M ψ hψ f' hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f' hf), GlobalTheory.T.hasCompactSupport_partialFourierGLBlock F E r M ψ hψ f' hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f' hf)⟩,
    fun f hf => ⟨GlobalTheory.T.partialFourierHermitianBlock_isLocallyConstant F E r M ψ hψ htr f hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f hf), GlobalTheory.T.partialFourierHermitianBlock_hasCompactSupport F E r M ψ hψ htr f hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f hf)⟩,
    GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport F r, GlobalTheory.T.isTest_unitIndicatorHermitianBlock F E r hU.norm_star, GlobalTheory.T.partialFourierGLBlock_unitIndicator F E r M ψ hψ, GlobalTheory.T.partialFourierHermitianBlock_unitIndicator F E r M ψ hψ htr (GlobalTheory.T.exists_integral_trace_unit_unramifiedQuadratic F E htr)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiKMulNLEqOneOnIntegralLatticeStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiK_mul_NL_eq_one_on_integral_lattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y : A.L, (∀ i, ‖j y i‖ ≤ 1) → A.psiK ψ (x * A.NL y) = 1 := by
  first | exact @GlobalTheory.JR.NormInt.main | exact GlobalTheory.JR.NormInt.main | (intros; apply GlobalTheory.JR.NormInt.main <;> assumption)
end

