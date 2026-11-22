import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0014
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0130
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MultisetEq
section
open Finset Matrix

noncomputable section

namespace GlobalTheory.Dec.GelfSepProof

open PowerSeries Matrix in

theorem _root_.GlobalTheory.Dec.GelfSepProof.gen {n : ℕ} (l : Fin n → ℂ) :
    ((1 : PowerSeries ℂ) -
        PowerSeries.X * PowerSeries.mk fun (k : ℕ) ↦ ∑ a : Fin n, ∑ b : Fin n, (_root_.Formalism.REAL.Amat l ^ k) a b) *
      ∏ a : Fin n, ((1 : PowerSeries ℂ) - (PowerSeries.C : ℂ → PowerSeries ℂ) (l a) * PowerSeries.X) =
    ∏ a : Fin n,
      ((1 : PowerSeries ℂ) -
        ((PowerSeries.C : ℂ → PowerSeries ℂ) (l a) + (1 : PowerSeries ℂ)) * PowerSeries.X) := by
  have hA : ∀ a b, _root_.Formalism.REAL.Amat l a b = if a = b then l a else if a < b then -1 else 0 := by
    intro a b
    unfold _root_.Formalism.REAL.Amat
    rfl
  set A := _root_.Formalism.REAL.Amat l with hAdef
  let Y : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := A.map (PowerSeries.C : ℂ → PowerSeries ℂ)
  let B : Matrix (Fin n) (Fin n) (PowerSeries ℂ) :=
    Matrix.of fun a b => PowerSeries.mk fun k => (A ^ k) a b
  have hB : (1 - (X : PowerSeries ℂ) • Y) * B = 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc]
    ext a b k
    rcases k with _ | k
    · simp [B, Matrix.one_apply]
    · simp [B, Y, Matrix.mul_apply, Matrix.one_apply, pow_succ', PowerSeries.coeff_succ_X_mul,
        map_sum]
      split_ifs <;> simp
  let c : Matrix (Fin n) (Fin 1) (PowerSeries ℂ) := replicateCol (Fin 1) 1
  let R : Matrix (Fin 1) (Fin n) (PowerSeries ℂ) := replicateRow (Fin 1) 1
  let J : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := Matrix.of fun _ _ => 1
  let U : Matrix (Fin n) (Fin 1) (PowerSeries ℂ) := -((X : PowerSeries ℂ) • (B * c))
  have hcR : c * R = J := by
    ext a b
    simp [c, R, J, Matrix.mul_apply]
  have hBc : (1 - (X : PowerSeries ℂ) • Y) * (B * c) = c := by
    rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
  have hfactor : (1 - (X : PowerSeries ℂ) • Y) * (1 + U * R) =
      1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J := by
    have hU : (1 - (X : PowerSeries ℂ) • Y) * U = -((X : PowerSeries ℂ) • c) := by
      show (1 - (X : PowerSeries ℂ) • Y) * -((X : PowerSeries ℂ) • (B * c)) = _
      rw [Matrix.mul_neg, Matrix.mul_smul, hBc]
    rw [mul_add, mul_one, ← Matrix.mul_assoc, hU, Matrix.neg_mul, Matrix.smul_mul, hcR]
    abel
  have hdet1 : (1 - (X : PowerSeries ℂ) • Y).det = ∏ a : Fin n, (1 - C (l a) * X) := by
    rw [Matrix.det_of_isUpperTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [Y, hA, mul_comm]
    · intro a b hab
      have hba : b < a := hab
      simp [Y, hA, hba.ne', not_lt_of_gt hba, Matrix.one_apply_ne hba.ne']
  have hdet2 : (1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J).det =
      ∏ a : Fin n, (1 - (C (l a) + 1) * X) := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [Y, J, hA]
      ring
    · intro a b hab
      have hab' : a < b := hab
      simp [Y, J, hA, hab'.ne, hab', Matrix.one_apply_ne hab'.ne]
  have hdet3 : (1 + U * R).det =
      1 - X * PowerSeries.mk fun k => ∑ a : Fin n, ∑ b : Fin n, (A ^ k) a b := by
    rw [Matrix.det_one_add_mul_comm, Matrix.det_unique]
    simp [U, R, B, c, Matrix.mul_apply, Finset.mul_sum, sub_eq_add_neg]
    simp only [← Finset.mul_sum]
    congr 1
    ext k
    simp [PowerSeries.coeff_mk, map_sum]
  rw [← hdet2, ← hfactor, Matrix.det_mul, hdet1, hdet3, mul_comm]

theorem shift_inj (s t : Multiset ℂ) (h : s.map (· + 1) + t = t.map (· + 1) + s) : s = t := by
  classical
  have hinj : Function.Injective (fun x : ℂ => x + 1) := add_left_injective 1
  have hc : ∀ x : ℂ, s.count x + t.count (x + 1) = t.count x + s.count (x + 1) := by
    intro x
    have := congrArg (Multiset.count (x + 1)) h
    rw [Multiset.count_add, Multiset.count_add] at this
    have e1 := Multiset.count_map_eq_count' (fun x : ℂ => x + 1) s hinj x
    have e2 := Multiset.count_map_eq_count' (fun x : ℂ => x + 1) t hinj x
    omega
  ext x
  have hk : ∀ k : ℕ, s.count x + t.count (x + k) = t.count x + s.count (x + k) := by
    intro k
    induction k with
    | zero => simp [add_comm]
    | succ k ih =>
      have := hc (x + k)
      rw [Nat.cast_succ, ← add_assoc]
      omega
  have hi : Function.Injective (fun k : ℕ => x + (k : ℂ)) := fun a b hab => by
    simpa using hab
  obtain ⟨_, ⟨k, rfl⟩, hk'⟩ := (Set.infinite_range_of_injective hi).exists_notMem_finset (s + t).toFinset
  simp only [Multiset.mem_toFinset, Multiset.mem_add, not_or] at hk'
  have := hk k
  rw [Multiset.count_eq_zero_of_notMem hk'.1, Multiset.count_eq_zero_of_notMem hk'.2] at this
  omega

theorem exists_perm {n : ℕ} (f g : Fin n → ℂ) (h : univ.val.map f = univ.val.map g) :
    ∃ s : Equiv.Perm (Fin n), g = f ∘ s := by
  classical
  have hc : ∀ c, Fintype.card {a // g a = c} = Fintype.card {a // f a = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [eq_comm (b := c)]
    exact this.symm
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩
  funext a
  exact (Equiv.ofFiberEquiv_map _ a).symm

open Polynomial in

theorem multiset_eq {n : ℕ} (f g f' g' : Fin n → ℂ)
    (h : (∏ a, (1 - C (f a) * X)) * ∏ a, (1 - C (g a) * X) =
      (∏ a, (1 - C (f' a) * X)) * ∏ a, (1 - C (g' a) * (X : ℂ[X]))) :
    univ.val.map f + univ.val.map g = univ.val.map f' + univ.val.map g' := by
  have key : ∀ (p : Fin n → ℂ) (u : ℂ), u ≠ 0 →
      ∏ a, (u - p a) = u ^ n * ∏ a, (1 - p a * u⁻¹) := by
    intro p u hu
    have : u ^ n = ∏ _a : Fin n, u := by simp
    rw [this, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    field_simp
  have hP : (∏ a, (X - C (f a))) * ∏ a, (X - C (g a)) =
      (∏ a, (X - C (f' a))) * ∏ a, ((X : ℂ[X]) - C (g' a)) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := {0}ᶜ) ?_ (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro u hu
    have hu : u ≠ 0 := hu
    have h2 := congrArg (Polynomial.eval u⁻¹) h
    simp only [eval_mul, eval_prod, eval_sub, eval_one, eval_C, eval_X] at h2
    simp only [Set.mem_setOf_eq, eval_mul, eval_prod, eval_sub, eval_C, eval_X]
    rw [key f u hu, key g u hu, key f' u hu, key g' u hu]
    linear_combination (u ^ n * u ^ n) * h2
  have hr : ∀ p q : Fin n → ℂ, ((∏ a, (X - C (p a))) * ∏ a, ((X : ℂ[X]) - C (q a))).roots =
      univ.val.map p + univ.val.map q := by
    intro p q
    rw [← Polynomial.roots_multiset_prod_X_sub_C (univ.val.map p + univ.val.map q), Multiset.map_add,
      Multiset.prod_add, Multiset.map_map, Multiset.map_map]
    rfl
  rw [← hr, ← hr, hP]

open PowerSeries in

theorem sep {n : ℕ} (l l' : Fin n → ℂ) :
    (∀ k, ∑ a, ∑ b, (Formalism.REAL.Amat l ^ k) a b = ∑ a, ∑ b, (Formalism.REAL.Amat l' ^ k) a b) ↔
      ∃ s : Equiv.Perm (Fin n), l' = l ∘ s := by
  have g1 := gen l
  have g2 := gen l'
  constructor
  · intro h
    rw [← funext h] at g2
    apply exists_perm
    apply shift_inj
    rw [Multiset.map_map, Multiset.map_map]
    apply multiset_eq
    apply Polynomial.coe_injective
    have hcoe : ∀ p : Fin n → ℂ, ((∏ a, (1 - Polynomial.C (p a) * Polynomial.X) : Polynomial ℂ) : ℂ⟦X⟧) =
        ∏ a, (1 - C (p a) * X) := by
      intro p
      rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
      simp
    simp only [Polynomial.coe_mul, hcoe]
    simp only [Function.comp, map_add, map_one]
    rw [← g1, ← g2]
    ring
  · rintro ⟨s, rfl⟩
    have e1 : ∏ a, (1 - C ((l ∘ s) a) * (X : ℂ⟦X⟧)) = ∏ a, (1 - C (l a) * X) :=
      Equiv.prod_comp s (fun a => 1 - C (l a) * (X : ℂ⟦X⟧))
    have e2 : ∏ a, (1 - (C ((l ∘ s) a) + 1) * (X : ℂ⟦X⟧)) = ∏ a, (1 - (C (l a) + 1) * X) :=
      Equiv.prod_comp s (fun a => 1 - (C (l a) + 1) * (X : ℂ⟦X⟧))
    rw [e1, e2, ← g1] at g2
    have hne : ∏ a, (1 - C (l a) * (X : ℂ⟦X⟧)) ≠ 0 := by
      intro h0
      have := congrArg (constantCoeff (R := ℂ)) h0
      simp [map_prod] at this
    have h3 := mul_left_cancel₀ X_ne_zero (sub_right_injective (mul_right_cancel₀ hne g2))
    intro k
    have := congrArg (coeff k) h3
    simpa using this.symm

end GlobalTheory.Dec.GelfSepProof

namespace GlobalTheory.Dec

end GlobalTheory.Dec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeDedekindZetaRealValueAndLeZetaPow
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DedekindZetaBound

theorem term_eq_ofReal (a : ℕ → ℕ) {l : ℕ} (hl : 2 ≤ l) (n : ℕ) :
    LSeries.term (fun n => (a n : ℂ)) (l : ℂ) n = (((a n : ℝ) * ((n : ℝ) ^ l)⁻¹ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : l ≠ 0 := by omega
    simp [this]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_natCast, div_eq_mul_inv]
    push_cast
    rfl

theorem lseriesHasSum_zeta_pow {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    LSeriesHasSum (fun n => (((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n : ℕ) : ℂ)) s
      (riemannZeta s ^ k) := by
  induction k with
  | zero =>
    have := hasSum_single (f := LSeries.term
      (fun n => (((ArithmeticFunction.zeta ^ 0 : ArithmeticFunction ℕ) n : ℕ) : ℂ)) s) 1
      (fun b hb => by
        rcases eq_or_ne b 0 with rfl | h0
        · simp
        · simp [LSeries.term_of_ne_zero h0, ArithmeticFunction.one_apply_ne hb])
    simpa [LSeriesHasSum] using this
  | succ k ih =>
    have := ArithmeticFunction.LSeriesHasSum_mul
      (f := ((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℂ))
      (g := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ))
      ih (ArithmeticFunction.LSeriesHasSum_zeta hs)
    rw [← ArithmeticFunction.natCoe_mul] at this
    rw [pow_succ, pow_succ]
    exact this

theorem hasSum_zeta_pow {l : ℕ} (hl : 2 ≤ l) (k : ℕ) :
    HasSum (fun n : ℕ => (((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ) *
      ((n : ℝ) ^ l)⁻¹) ((∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ^ k) := by
  have hs : 1 < ((l : ℂ)).re := by
    rw [Complex.natCast_re]; exact_mod_cast hl
  have h := lseriesHasSum_zeta_pow hs k
  have e : riemannZeta (l : ℂ) = ((∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, Complex.ofReal_tsum]
    refine tsum_congr fun m => ?_
    rw [Complex.cpow_natCast]
    push_cast
    rfl
  rw [e, ← Complex.ofReal_pow, LSeriesHasSum, funext (term_eq_ofReal _ hl)] at h
  exact Complex.hasSum_ofReal.1 h

theorem one_le_zetaE_and_le : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), 2 ≤ l →
    1 ≤ zetaE E l ∧ zetaE E l ≤ (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ^ Module.finrank ℚ E := by
  intro E _ _ l hl
  have h := hasSum_zeta_pow hl (Module.finrank ℚ E)
  set a : ℕ → ℝ := fun n =>
    (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ l)⁻¹ with ha
  have h0 : ∀ n, 0 ≤ a n := fun n => by positivity
  have hle : ∀ n : ℕ, a n ≤
      (((ArithmeticFunction.zeta ^ Module.finrank ℚ E : ArithmeticFunction ℕ) n : ℕ) : ℝ) *
        ((n : ℝ) ^ l)⁻¹ := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · have : l ≠ 0 := by omega
      simp [ha, this]
    · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast GlobalTheory.ncard_ideal_absNorm_eq_le E hn
  have hsum : Summable a := Summable.of_nonneg_of_le h0 hle h.summable
  have e : zetaE E l = ∑' n, a n := by
    unfold zetaE dedekindZeta LSeries
    rw [funext (term_eq_ofReal _ hl), ← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [e]
  refine ⟨le_trans ?_ (hsum.le_tsum 1 fun n _ => h0 n), hasSum_le hle hsum.hasSum h⟩
  simp [ha, Ideal.absNorm_eq_one_iff]

end GlobalTheory.DedekindZetaBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PointConjMemCongruenceSubgroupOfCongrLattice
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PointLattice

theorem conj_mulVec_eq_smul (I : AutInst) (x : I.GA) (c : ℕ) (M : Matrix (Fin I.n) (Fin I.n) I.E)
    (hM : ∀ y ∈ lamX I x, ∃ z ∈ lamX I x, M *ᵥ y = (c : I.E) • z)
    (w : Fin I.n → I.E ⊗[I.F] Af I.F) (hw : w ∈ I.Lf) :
    ∃ z ∈ I.Lf, (I.fmat x.2⁻¹ * M.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x.2) *ᵥ w =
      (c : I.E ⊗[I.F] Af I.F) • z := by
  have e1 : Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L = I.Lf := by
    unfold Formalism.UG.latS AutInst.Lf lamAf
    rw [Set.image_eq_range]
    rfl
  have hfin := Module.Finite.iff_fg.2 I.L_fg
  have hu := Formalism.UG.P.csSpan_back Formalism.UG.P.csGlob_intAdApprox I.L hfin I.L_span
    (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (I.fmat x.2 *ᵥ w)
    (by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]; exact e1.symm ▸ hw)
  rw [← lamX_eq_globLat] at hu
  rw [← mulVec_mulVec]
  generalize I.fmat x.2 *ᵥ w = u at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    obtain ⟨z, hz, e⟩ := hM y hy
    refine ⟨_, (GlobalTheory.Count.Test.mem_lamX I x z).1 hz, ?_⟩
    rw [← mulVec_mulVec, ← mulVec_smul]
    congr 1
    funext i
    have h := (RingHom.map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F) : I.E →+* _) M y i).symm
    rw [e] at h
    refine h.trans ?_
    simp
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨z, hz, e⟩ := hu
    obtain ⟨z', hz', e'⟩ := hv
    exact ⟨z + z', add_mem hz hz', by rw [mulVec_add, e, e', smul_add]⟩
  | smul s u _ hu =>
    obtain ⟨z, hz, e⟩ := hu
    refine ⟨s • z, Submodule.smul_mem _ s hz, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, mulVec_smul, e, smul_comm]

theorem conj_mem_Kg_of_congr : ∀ (I : AutInst) (x a : I.GA) (g : ℕ) (γ : GL (Fin I.n) I.E), I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → (∀ y ∈ lamX I x, ∃ z ∈ lamX I x, ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) *ᵥ y = (g : I.E) • z) → (∀ y ∈ lamX I x, ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I x) → (x⁻¹ * a * x).2 ∈ I.Kg g := by
  intro I x a g γ ha h1 h2
  have hk : I.fmat (x⁻¹ * a * x).2 = I.fmat x.2⁻¹ * I.fmat a.2 * I.fmat x.2 := rfl
  have hx1 : I.fmat x.2⁻¹ * I.fmat x.2 = 1 := Units.inv_mul _
  have hx2 : I.fmat x.2 * I.fmat x.2⁻¹ = 1 := Units.mul_inv _
  have hc : ∀ y ∈ I.Lf, ∃ z ∈ I.Lf,
      (I.fmat (x⁻¹ * a * x).2 - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := by
    intro y hy
    obtain ⟨z, hz, e⟩ := conj_mulVec_eq_smul I x g _ h1 y hy
    refine ⟨z, hz, ?_⟩
    rw [← e, hk, ha, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
      mul_sub, sub_mul, mul_one, hx1]
  refine ⟨fun y => ?_, hc⟩
  symm
  show I.fmat (x⁻¹ * a * x).2 *ᵥ y ∈ I.Lf ↔ y ∈ I.Lf
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨z, hz, e⟩ := conj_mulVec_eq_smul I x 1 _
      (fun y hy => ⟨_, h2 y hy, by rw [Nat.cast_one, one_smul]⟩) _ hy
    rw [Nat.cast_one, one_smul, mulVec_mulVec, hk, ha] at e
    have hγ : ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map
        (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) = 1 := by
      rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have h3 : ∀ A B C D : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F), A * B = 1 → B * A = 1 →
        C * D = 1 → A * C * B * (A * D * B) = 1 := by
      intro A B C D p q r
      calc A * C * B * (A * D * B) = A * (C * (B * A) * D) * B := by simp only [mul_assoc]
        _ = 1 := by rw [q, mul_one, r, mul_one, p]
    rw [h3 _ _ _ _ hx1 hx2 hγ, one_mulVec] at e
    exact e ▸ hz
  · obtain ⟨z, hz, e⟩ := hc y hy
    rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add, Nat.cast_smul_eq_nsmul] at e
    rw [e]
    exact add_mem (nsmul_mem hz g) hy

end GlobalTheory.PointLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFiveFactorsHermitianVolume
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FiveFactors

theorem volU_eq (k : ℕ) : GlobalTheory.FlagMeas.volU k = sphV k * (2 : ℝ) ^ (((k : ℝ) ^ 2 - k) / 2) := by
  unfold GlobalTheory.FlagMeas.volU
  congr 1
  rw [← Real.rpow_natCast, ← Nat.choose_two_right, Nat.cast_choose_two]
  congr 1
  ring

theorem sum_Ioc_half (m n : ℕ) (h : m ≤ n) :
    ∑ M ∈ Finset.Ioc m n, ((M : ℝ) - 1 / 2) = ((n : ℝ) ^ 2 - (m : ℝ) ^ 2) / 2 := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n h ih =>
    rw [Finset.sum_Ioc_succ_top h, ih]
    push_cast
    ring

theorem vInv_pos (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
  positivity

theorem prod_rankFac (E : Type) [Field E] [NumberField E] [StarRing E] (m n : ℕ) (h : m ≤ n) :
    ∏ M ∈ Finset.Ioc m n, rankFac E M =
      (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (((n : ℝ) ^ 2 - (m : ℝ) ^ 2) / 2)) *
        ∏ M ∈ Finset.Ioc m n, Formalism.HermitianLatticesTheory.lValEta E M := by
  have hv := vInv_pos E
  unfold rankFac
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (by positivity), ← Finset.mul_sum,
    sum_Ioc_half m n h]

theorem dimN_eq (n a : ℕ) (j : Fin a → ℕ) (h : 2 * ∑ i, j i ≤ n) :
    (dimN n j : ℝ) = 2 * ((∑ i, j i : ℕ) : ℝ) ^ 2 - ∑ i, (j i : ℝ) ^ 2
      + 2 * ((∑ i, j i : ℕ) : ℝ) * (n - 2 * ((∑ i, j i : ℕ) : ℝ)) := by
  have h1 := (GlobalTheory.dim_unipotent_radical_identities a (fun i => (j i : ℤ)) n).1
  have h2 : (dimN n j : ℤ) = 2 * ((∑ i, j i : ℕ) : ℤ) ^ 2 - ∑ i, (j i : ℤ) ^ 2
      + 2 * ((∑ i, j i : ℕ) : ℤ) * (n - 2 * ((∑ i, j i : ℕ) : ℤ)) := by
    unfold dimN
    push_cast [Nat.cast_sub h, Finset.sum_filter]
    exact h1
  exact_mod_cast h2

theorem cIw_eq (p q a : ℕ) (j : Fin a → ℕ) (hp : ∑ i, j i ≤ p) (hq : ∑ i, j i ≤ q) :
    cIw p q j = (2 : ℝ) ^ (-((dimN (p + q) j : ℝ) / 2) + (((p : ℝ) + q) * ((∑ i, j i : ℕ) : ℝ)
        - ((∑ i, j i : ℕ) : ℝ) ^ 2 - ((∑ i, j i : ℕ) : ℝ) / 2 - ∑ i, (j i : ℝ) ^ 2)) *
      (sphV p * sphV q / (sphV (p - ∑ i, j i) * sphV (q - ∑ i, j i) * ∏ i, sphV (j i))) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hP : (∏ i, GlobalTheory.FlagMeas.volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) =
      (∏ i, sphV (j i)) * (2 : ℝ) ^ (∑ i, (j i : ℝ) ^ 2 - ((∑ i, j i : ℕ) : ℝ) / 2) := by
    simp only [volU_eq, mul_assoc, ← Real.rpow_add h2]
    rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos h2]
    congr 2
    push_cast
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold cIw
  rw [hP]
  simp only [volU_eq]
  rw [Nat.cast_sub hp, Nat.cast_sub hq]
  generalize ((∑ i, j i : ℕ) : ℝ) = J
  generalize ∑ i, (j i : ℝ) ^ 2 = S
  generalize (dimN (p + q) j : ℝ) = D
  have key : (2 : ℝ) ^ (-(D / 2) + (((p : ℝ) + q) * J - J ^ 2 - J / 2 - S)) =
      (2 : ℝ) ^ (-(D / 2)) * (2 : ℝ) ^ (((p : ℝ) ^ 2 - p) / 2) * (2 : ℝ) ^ (((q : ℝ) ^ 2 - q) / 2) /
      ((2 : ℝ) ^ (S - J / 2) * (2 : ℝ) ^ ((((p : ℝ) - J) ^ 2 - (p - J)) / 2) *
        (2 : ℝ) ^ ((((q : ℝ) - J) ^ 2 - (q - J)) / 2)) := by
    simp only [← Real.rpow_add h2, ← Real.rpow_sub h2]
    congr 1
    ring
  rw [key, div_mul_div_comm]
  congr 1 <;> ring

theorem prod_five_factors : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (p q a : ℕ) (j : Fin a → ℕ), ∑ i, j i ≤ q → 2 * q + 2 ≤ p + q → cIw p q j ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * dimN (p + q) j / 2) * (∏ i, 2 ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * ∏ l ∈ Finset.Icc 2 (j i), zetaE E l)) / ∏ M ∈ Finset.Ioc (p + q - 2 * ∑ i, j i) (p + q), rankFac E M = kapBd E p q j := by
  intro E _ _ _ _ p q a j hq hpq
  have hp : ∑ i, j i ≤ p := by omega
  have hn : 2 * ∑ i, j i ≤ p + q := by omega
  have hv := vInv_pos E
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hD := dimN_eq (p + q) a j hn
  have hmid : (∏ i, (2 : ℝ) ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * (dedekindZeta_residue E *
      Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * ∏ l ∈ Finset.Icc 2 (j i), zetaE E l)) =
      (2 : ℝ) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ i, (j i : ℝ) ^ 2) * (dedekindZeta_residue E ^ a *
      Formalism.HermitianLatticesTheory.vInv E ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ i, (j i : ℝ) ^ 2) *
        ∏ i, ∏ l ∈ Finset.Icc 2 (j i), zetaE E l) := by
    have hc : (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ i, (j i : ℝ) ^ 2 =
        ((∑ i, Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
    rw [hc, Real.rpow_natCast, Real.rpow_natCast]
    simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [hmid, prod_rankFac E _ _ (Nat.sub_le _ _), cIw_eq p q a j hp hq, mul_pow,
    ← Real.rpow_mul_natCast h2.le, Nat.cast_sub hn]
  unfold kapBd
  rw [hD]
  push_cast [-Nat.cast_sum]
  generalize ((∑ i, j i : ℕ) : ℝ) = J
  generalize ∑ i, (j i : ℝ) ^ 2 = S
  generalize (sphV p * sphV q / (sphV (p - ∑ i, j i) * sphV (q - ∑ i, j i) * ∏ i, sphV (j i))) ^
    Formalism.HermitianLatticesTheory.fDeg E = R
  generalize (Formalism.HermitianLatticesTheory.fDeg E : ℝ) = f
  generalize Formalism.HermitianLatticesTheory.vInv E = v at hv ⊢
  generalize ((p : ℝ) + q) = n
  rw [Real.mul_rpow h2.le hv.le, Real.mul_rpow h2.le hv.le, ← div_div]
  congr 1
  have k2 : (2 : ℝ) ^ (-(f * (n * J - J ^ 2 + J / 2))) =
      (2 : ℝ) ^ ((-((2 * J ^ 2 - S + 2 * J * (n - 2 * J)) / 2) + (n * J - J ^ 2 - J / 2 - S)) * f) *
      (2 : ℝ) ^ (f * (2 * J ^ 2 - S + 2 * J * (n - 2 * J)) / 2) * (2 : ℝ) ^ (f * S) /
      (2 : ℝ) ^ (f * ((n ^ 2 - (n - 2 * J) ^ 2) / 2)) := by
    simp only [← Real.rpow_add h2, ← Real.rpow_sub h2]
    congr 1
    ring
  have kv : v ^ (-(f * (2 * J ^ 2 - S + 2 * J * (n - 2 * J)) / 2)) =
      v ^ (f * (2 * J ^ 2 - S + 2 * J * (n - 2 * J)) / 2) * v ^ (f * S) /
      v ^ (f * ((n ^ 2 - (n - 2 * J) ^ 2) / 2)) := by
    simp only [← Real.rpow_add hv, ← Real.rpow_sub hv]
    congr 1
    ring
  rw [k2, kv]
  field_simp

end GlobalTheory.FiveFactors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportFrameAlongUnitaryAdelicStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_frame_along_unitary_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (g k : ℕ) (h : UPts σ J (Ad F)), (∀ x, (h⁻¹).1.1 *ᵥ x ∈ Λ' ↔ x ∈ Λ) → ∀ Fr : AdFrame σ J Λ g k, ∃ Fr' : AdFrame σ J Λ' g k, ∀ y : UPts σ J (Ad F), (Fr.InK y.1 ↔ Fr'.InK (h⁻¹ * y * h : UPts σ J (Ad F)).1) ∧ Fr.chi y.1 = Fr'.chi (h⁻¹ * y * h : UPts σ J (Ad F)).1 := by
  first | exact @GlobalTheory.St.G.FrMap.transport | exact GlobalTheory.St.G.FrMap.transport | (intros; apply GlobalTheory.St.G.FrMap.transport <;> assumption)
end

