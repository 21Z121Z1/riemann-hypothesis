import Formalism.PieriBlockIdeals.Bundle0006
import Formalism.PieriBlockIdeals.PieriColumnMinors.Bundle0007
import Formalism.PieriBlockIdeals.PieriColumnMinors.Bundle0006
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0014
import Formalism.PieriBlockIdeals.PieriColumnMinors.Bundle0005
import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightSuccessive
import Formalism.PieriBlockIdeals.PieriColumnMinors.LpcDpartCommEps
import Formalism.PieriBlockIdeals.PieriColumnMinors.BinaryFormsExample

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.LemmaDSkeletonFour
section
namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem antitone_increment : AntiStep := AntiStep_of no_bad_tuple

theorem columns_from_pieri : ColumnsFromPieri :=
  ColumnsFromPieri_of swap_path_exists same_column measure_swap_invariant monotone_run weight_iff_condition good_swap_exists
    antitone_increment antitone_shapes

theorem lemma_d_skeleton_four : LemmaDSkeleton4 := LemmaDSkeleton4_of columns_from_pieri

end Formalism.CohomologicalDescent.LC
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.LrcFockZeroRight
section
open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility

def Zl (l : ℕ) : Subring ℚ where
  carrier := {x | x.den.Coprime l}
  mul_mem' := by
    intro a b ha hb
    exact Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd a b) (Nat.Coprime.mul_left ha hb)
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd a b) (Nat.Coprime.mul_left ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

theorem mem_Zl (l : ℕ) (x : ℚ) : x ∈ Zl l ↔ x.den.Coprime l := Iff.rfl

theorem lrc_int_mem (l : ℕ) (z : ℤ) : (z : ℚ) ∈ Zl l := by
  rw [mem_Zl]; simp

theorem lrc_coprime_iff {l : ℕ} (hl : l.Prime) (m : ℕ) : m.Coprime l ↔ ¬ (l : ℤ) ∣ (m : ℤ) := by
  rw [Int.natCast_dvd_natCast, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]

theorem lrc_inv_mem {l : ℕ} (hl : l.Prime) (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) : ((m : ℚ)⁻¹) ∈ Zl l := by
  rw [mem_Zl]
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero _)
  have h : ((m : ℚ)⁻¹).den = m.natAbs := by
    rw [Rat.inv_intCast_den, if_neg hm0]
  rw [h, lrc_coprime_iff hl, Int.dvd_natAbs]
  exact hm

theorem zl_mem_iff {l : ℕ} (hl : l.Prime) (x : ℚ) :
    x ∈ Zl l ↔ ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ ∃ z : ℤ, (m : ℚ) * x = z := by
  constructor
  · intro hx
    refine ⟨(x.den : ℤ), (lrc_coprime_iff hl _).1 hx, x.num, ?_⟩
    have := Rat.den_mul_eq_num x
    exact_mod_cast this
  · rintro ⟨m, hm, z, hz⟩
    have hm0 : (m : ℚ) ≠ 0 := by
      intro h
      have : m = 0 := by exact_mod_cast h
      subst this
      exact hm (dvd_zero _)
    have : x = (m : ℚ)⁻¹ * (z : ℚ) := by
      rw [← hz, ← mul_assoc, inv_mul_cancel₀ hm0, one_mul]
    rw [this]
    exact (Zl l).mul_mem (lrc_inv_mem hl m hm) (lrc_int_mem l z)

theorem zl_unit {l : ℕ} (hl : l.Prime) (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) : IsUnit (m : Zl l) := by
  have hm0 : (m : ℚ) ≠ 0 := by
    intro h
    have : m = 0 := by exact_mod_cast h
    subst this
    exact hm (dvd_zero _)
  refine IsUnit.of_mul_eq_one (⟨(m : ℚ)⁻¹, lrc_inv_mem hl m hm⟩ : Zl l) ?_
  apply Subtype.ext
  simp [hm0]

theorem mem_one_iff (l : ℕ) (x : ℚ) : x ∈ (1 : Submodule (Zl l) ℚ) ↔ x ∈ Zl l := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

example (l : ℕ) (V : Type) [AddCommGroup V] [Module ℚ V] : IsScalarTower (Zl l) ℚ V := inferInstance
example (l : ℕ) : Algebra (Zl l) ℚ := inferInstance

theorem lrc_smul_def (l : ℕ) {V : Type*} [AddCommGroup V] [Module ℚ V] (c : Zl l) (v : V) :
    c • v = (c : ℚ) • v := rfl

def locSpan (l : ℕ) (hl : l.Prime) {V : Type*} [AddCommGroup V] [Module ℚ V] (M : AddSubgroup V) :
    Submodule (Zl l) V where
  carrier := {v | ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ m • v ∈ M}
  add_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨m', hm', hb⟩
    refine ⟨m * m', fun h => ?_, ?_⟩
    · rcases (Nat.prime_iff_prime_int.1 hl).dvd_or_dvd h with h | h
      · exact hm h
      · exact hm' h
    · rw [smul_add]
      refine M.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]
        exact M.zsmul_mem ha _
      · rw [mul_smul]
        exact M.zsmul_mem hb _
  zero_mem' := ⟨1, fun h => by
    have := Int.natCast_dvd_natCast.1 (by simpa using h : ((l : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ))
    exact hl.one_lt.ne' (Nat.dvd_one.1 this), by simp⟩
  smul_mem' := by
    rintro c v ⟨m, hm, hv⟩
    obtain ⟨m', hm', z, hz⟩ := (zl_mem_iff hl (c : ℚ)).1 c.2
    refine ⟨m' * m, fun h => ?_, ?_⟩
    · rcases (Nat.prime_iff_prime_int.1 hl).dvd_or_dvd h with h | h
      · exact hm' h
      · exact hm h
    · have : (m' * m) • (c • v) = z • (m • v) := by
        rw [lrc_smul_def, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ z, ← Int.cast_smul_eq_zsmul ℚ m,
          smul_smul, smul_smul, ← hz]
        congr 1
        push_cast
        ring
      rw [this]
      exact M.zsmul_mem hv _

theorem mem_locSpan (l : ℕ) (hl : l.Prime) {V : Type*} [AddCommGroup V] [Module ℚ V] (M : AddSubgroup V) (v : V) :
    v ∈ locSpan l hl M ↔ ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ m • v ∈ M := Iff.rfl

theorem le_locSpan (l : ℕ) (hl : l.Prime) {V : Type*} [AddCommGroup V] [Module ℚ V] (M : AddSubgroup V) {v : V}
    (hv : v ∈ M) : v ∈ locSpan l hl M :=
  ⟨1, fun h => by
    have := Int.natCast_dvd_natCast.1 (by simpa using h : ((l : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ))
    exact hl.one_lt.ne' (Nat.dvd_one.1 this), by simpa using hv⟩

theorem lrc_intQ_apply (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = map (Int.castRingHom ℚ) P := rfl

theorem lrc_eval_map (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    eval (idFrame ℚ r n) (map (Int.castRingHom ℚ) P) = ((eval (idFrame ℤ r n) P : ℤ) : ℚ) := by
  have h : (eval (idFrame ℚ r n)).comp (map (Int.castRingHom ℚ)) =
      (Int.castRingHom ℚ).comp (eval (idFrame ℤ r n)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp only [RingHom.comp_apply, map_X, eval_X, idFrame]
      split_ifs <;> simp
  exact congrArg (fun F => F P) h

theorem lrc_applyWord_mem (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) : applyWord R w f ∈ dualWeyl R r n ν := by
  induction w with
  | nil => exact hf
  | cons x w ih =>
    rw [applyWord_cons]
    exact rowDivStable R r n ν _ _ _ _ ih

theorem lrc_fock_add_right {σ : Type} (f g g' : MvPolynomial σ ℚ) : fockQ f (g + g') = fockQ f g + fockQ f g' := by
  rw [(fockQPos σ f (g + g')).1, (fockQBilin σ g g' f 1).1, (fockQPos σ g f).1, (fockQPos σ g' f).1]

theorem lrc_fock_smul_right {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ f (c • g) = c * fockQ f g := by
  rw [(fockQPos σ f (c • g)).1, (fockQBilin σ g 0 f c).2, (fockQPos σ g f).1]

theorem lrc_fock_zero_right {σ : Type} (f : MvPolynomial σ ℚ) : fockQ f 0 = 0 := by
  have := lrc_fock_smul_right (0 : ℚ) f 0
  simpa using this

theorem fock_word (r : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (F : MvPolynomial (Fin r × Fin r) ℚ)
    (hF : F ∈ dualWeyl ℚ r r ν) (w : List (Fin r × Fin r × ℕ)) :
    fockQ F (applyWord ℚ w (hw ℚ le_rfl ν)) =
      eval (idFrame ℚ r r) (applyWord ℚ (transposeWord w) F) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by
  rw [(fockQPos _ F _).1, fock_space_word_adjoint,
    fock_space_highest_weight r r le_rfl ν hν _ (lrc_applyWord_mem ℚ r r ν _ F hF)]

theorem fock_int (r : ℕ) (ν : Fin r → ℕ) (hν : Antitone ν) (x : MvPolynomial (Fin r × Fin r) ℤ)
    (hx : x ∈ dualWeyl ℤ r r ν) (y : MvPolynomial (Fin r × Fin r) ℤ) (hy : y ∈ weyl ℤ r r le_rfl ν) :
    ∃ z : ℤ, fockQ (intQ r r x) (intQ r r y) = z * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by
  unfold weyl at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    refine ⟨eval (idFrame ℤ r r) (applyWord ℤ (transposeWord w) x), ?_⟩
    simp only [lrc_intQ_apply]
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map,
      fock_word r ν hν _ (dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r r ν x hx) w, lclosedeq_applyWord_map, lrc_eval_map]
  | zero =>
    refine ⟨0, ?_⟩
    rw [map_zero, lrc_fock_zero_right]
    simp
  | add y y' _ _ ih ih' =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨z', hz'⟩ := ih'
    refine ⟨z + z', ?_⟩
    rw [map_add, lrc_fock_add_right, hz, hz']
    push_cast
    ring
  | smul c y _ ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨c * z, ?_⟩
    rw [map_smul, ← Int.cast_smul_eq_zsmul ℚ, lrc_fock_smul_right, hz]
    push_cast
    ring

theorem lrc_den_dvd_mul (x : ℚ) (m : ℕ) (h : x.den ∣ m) : ∃ z : ℤ, (m : ℚ) * x = z := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨(k : ℤ) * x.num, ?_⟩
  have := Rat.den_mul_eq_num x
  push_cast
  rw [← this]
  ring

theorem dual_int_loc (hC : CoeffWord) (hL : LowerTriIntegral) (l : ℕ) (hl : l.Prime) (r : ℕ) (ν : Fin r → ℕ)
    (g : MvPolynomial (Fin r × Fin r) ℚ) (hg : g ∈ dualWeyl ℚ r r ν)
    (h : ∀ ω : List (Fin r × Fin r × ℕ), eval (idFrame ℚ r r) (applyWord ℚ ω g) ∈ Zl l) :
    ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ ∃ g' ∈ dualWeyl ℤ r r ν, (m : ℚ) • g = intQ r r g' := by
  classical
  have hhom : IsWeightedHomogeneous (colW r r) g ν := hg.1
  have h1 : ∀ e : Fin r × Fin r →₀ ℕ, LowerTri e → coeff e g ∈ Zl l := by
    intro e he
    by_cases hs : ∀ s : Fin r, ∑ a : Fin r, e (a, s) = ν s
    · rw [hC ℚ r r ν g e hhom he hs]
      exact h _
    · have : coeff e g = 0 := by
        by_contra hne
        apply hs
        intro s
        rw [← lccomp_weight_colW_apply, hhom hne]
      rw [this]
      exact (Zl l).zero_mem
  set M : ℕ := ∏ e ∈ g.support.filter (fun e => LowerTri e), (coeff e g).den with hM
  have hMc : M.Coprime l := by
    rw [hM]
    refine Nat.Coprime.prod_left fun e he => ?_
    exact h1 e (Finset.mem_filter.1 he).2
  have h2 : ∀ e : Fin r × Fin r →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e ((M : ℚ) • g) = z := by
    intro e he
    rw [coeff_smul, smul_eq_mul]
    by_cases hes : e ∈ g.support
    · exact lrc_den_dvd_mul _ _ (Finset.dvd_prod_of_mem (fun e => (coeff e g).den) (Finset.mem_filter.2 ⟨hes, he⟩))
    · rw [notMem_support_iff.1 hes]
      exact ⟨0, by simp⟩
  have hMg : (M : ℚ) • g ∈ dualWeyl ℚ r r ν := (dualWeyl ℚ r r ν).smul_mem _ hg
  obtain ⟨Q', hQ'⟩ := hL r r ν _ hMg h2
  refine ⟨(M : ℤ), (lrc_coprime_iff hl M).1 hMc, Q', ?_, ?_⟩
  · rw [dualWeylIntRat r r ν Q', ← lrc_intQ_apply, ← hQ']
    exact hMg
  · rw [← hQ']
    push_cast
    rfl

end Formalism.CohomologicalDescent.LR
end
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.PieriGenerated
section
namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem tower_pieri : TowerPieri := TowerPieri_of completeReducibility_holds highestWeightDominant_holds

theorem pieri_rule : Pieri := by
  intro K P M q _ _ _ _ _ _ _ _ EM B lam2 hF h0 n
  have hT := tensor_tower K P M q EM B n hF
  have hb := tensor_base_case K P M q EM n (fun b => (lam2 b : K)) h0
  have hTP := tower_pieri K (Tens (Fin q) P M n) q n (fun j => Dpart K EM j) (epsY K n)
    (tensForm n B) lam2 hT hb
  apply eq_top_iff.mpr
  rw [← hTP, Submodule.span_le]
  rintro z ⟨tau, κ, ρ, hp, hcas⟩
  exact Submodule.mem_iSup_of_mem tau (Submodule.subset_span ⟨κ, ρ, hp, fun j hj => hcas j hj⟩)

theorem pieri_generated : PieriGenerated := by
  intro K P M q _ _ _ _ _ _ _ _ EM B lam2 hF hgen n
  exact pieri_rule K P M q EM B lam2 hF (generatedHighestWeight_holds K M q EM B hF _ hgen) n

end Formalism.CohomologicalDescent.LP
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.RowGenDerivative
section
open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility

def der (r n : ℕ) (a b : Fin r) :
    Derivation ℚ (MvPolynomial (Fin r × Fin n) ℚ) (MvPolynomial (Fin r × Fin n) ℚ) :=
  mkDerivation ℚ fun v => if v.1 = b then X (a, v.2) else 0

theorem der_X {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    der r n a b (X v) = if v.1 = b then X (a, v.2) else 0 := by
  rw [der, mkDerivation_X]

theorem der_comm {r n : ℕ} (a b c d : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    der r n a b (der r n c d f) - der r n c d (der r n a b f) =
      (if b = c then der r n a d f else 0) - (if d = a then der r n c b f else 0) := by
  have h : ⁅der r n a b, der r n c d⁆ =
      (if b = c then der r n a d else 0) - (if d = a then der r n c b else 0) := by
    apply MvPolynomial.derivation_ext
    rintro ⟨x, s⟩
    rw [Derivation.commutator_apply, Derivation.sub_apply]
    have e3 : ∀ (P : Prop) [Decidable P]
        (D : Derivation ℚ (MvPolynomial (Fin r × Fin n) ℚ) (MvPolynomial (Fin r × Fin n) ℚ))
        (g : MvPolynomial (Fin r × Fin n) ℚ), (if P then D else 0) g = if P then D g else 0 := by
      intro P _ D g
      split_ifs <;> simp
    simp only [e3, der_X]
    by_cases h1 : x = d
    · subst h1
      by_cases h2 : x = b
      · subst h2
        by_cases h3 : x = c
        · subst h3
          by_cases h4 : x = a
          · subst h4; simp [der_X]
          · have h4' : ¬ a = x := fun h => h4 h.symm
            simp [der_X, h4, h4']
        · have h3' : ¬ c = x := fun h => h3 h.symm
          by_cases h4 : x = a
          · subst h4; simp [der_X, h3, h3']
          · have h4' : ¬ a = x := fun h => h4 h.symm
            simp [der_X, h3, h4, h3', h4']
      · by_cases h3 : b = c
        · subst h3; simp [der_X, h2]
        · have h3' : ¬ c = b := fun h => h3 h.symm
          simp [der_X, h2, h3, h3']
    · by_cases h2 : x = b
      · subst h2
        by_cases h4 : d = a
        · subst h4; simp [der_X, h1]
        · have h4' : ¬ a = d := fun h => h4 h.symm
          simp [der_X, h1, h4, h4']
      · simp [der_X, h1, h2]
  have h' := congrArg (fun D => D f) h
  simp only [Derivation.commutator_apply, Derivation.sub_apply] at h'
  rw [h']
  split_ifs <;> simp

theorem rowGen_X' {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    rowGen ℚ a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  rw [rowGen, aeval_X]

theorem rowGen_C' {r n : ℕ} (a b : Fin r) (c : ℚ) :
    rowGen ℚ a b (C c : MvPolynomial (Fin r × Fin n) ℚ) = Polynomial.C (C c) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem rowGen_derivative {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    (1 + if a = b then Polynomial.X else 0) * Polynomial.derivative (rowGen ℚ a b f) =
      rowGen ℚ a b (der r n a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [rowGen_C', ← MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, mul_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
      ← hp, der_X, rowGen_X']
    by_cases h1 : v.1 = b
    · by_cases h2 : a = b
      · subst h2
        have e : ((a, v.2) : Fin r × Fin n) = v := by rw [← h1]
        simp only [h1, if_true, rowGen_X', e]
        simp
        ring
      · have h3 : ¬ ((a, v.2) : Fin r × Fin n).1 = b := h2
        simp only [h1, h2, if_true, if_false, rowGen_X', h3]
        simp
        ring
    · simp only [h1, if_false, map_zero]
      simp
      ring

theorem rowDiv_zero' {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) : rowDiv ℚ a b 0 f = f := by
  unfold rowDiv
  induction f using MvPolynomial.induction_on with
  | C c => simp [rowGen_C']
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp, rowGen_X']
    split_ifs <;> simp

theorem rowDiv_succ {r n : ℕ} (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    ((k + 1 : ℕ) : ℚ) • rowDiv ℚ a b (k + 1) f =
      rowDiv ℚ a b k (der r n a b f) - (if a = b then (k : ℚ) • rowDiv ℚ a b k f else 0) := by
  have h := congrArg (fun P => Polynomial.coeff P k) (rowGen_derivative a b f)
  beta_reduce at h
  unfold rowDiv
  rw [← h, add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_derivative]
  by_cases hab : a = b
  · simp only [hab, if_true]
    cases k with
    | zero => simp [MvPolynomial.smul_eq_C_mul, mul_comm]
    | succ k =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      simp only [MvPolynomial.smul_eq_C_mul]
      push_cast
      simp only [map_add, map_natCast, map_one]
      ring
  · simp only [hab, if_false, zero_mul, Polynomial.coeff_zero, add_zero, sub_zero, MvPolynomial.smul_eq_C_mul]
    push_cast
    simp only [map_add, map_natCast, map_one]
    ring

theorem rowDiv_one {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    rowDiv ℚ a b 1 f = der r n a b f := by
  have h := rowDiv_succ a b 0 f
  simpa [rowDiv_zero'] using h

theorem closed_of_der {r n : ℕ} (a b : Fin r) (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ))
    (hM : ∀ f ∈ M, der r n a b f ∈ M) (k : ℕ) : ∀ f ∈ M, rowDiv ℚ a b k f ∈ M := by
  induction k with
  | zero => intro f hf; rwa [rowDiv_zero']
  | succ k ih =>
    intro f hf
    have h := rowDiv_succ a b k f
    have h2 : rowDiv ℚ a b k (der r n a b f) - (if a = b then (k : ℚ) • rowDiv ℚ a b k f else 0) ∈ M := by
      refine M.sub_mem (ih _ (hM f hf)) ?_
      split_ifs
      · exact M.smul_mem _ (ih f hf)
      · exact M.zero_mem
    rw [← h] at h2
    have h3 := M.smul_mem (((k + 1 : ℕ) : ℚ)⁻¹) h2
    rwa [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at h3

theorem der_pow {r n : ℕ} (a b : Fin r) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    rowDiv ℚ a b k f = ((k.factorial : ℚ)⁻¹) • ((der r n a b : Module.End ℚ _) ^ k) f := by
  induction k generalizing f with
  | zero => simp [rowDiv_zero']
  | succ k ih =>
    have h := rowDiv_succ a b k f
    simp only [hab, if_false, sub_zero] at h
    rw [ih] at h
    have h3 := congrArg (fun x => (((k + 1 : ℕ) : ℚ)⁻¹) • x) h
    beta_reduce at h3
    rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul] at h3
    rw [h3, smul_smul, pow_succ, Module.End.mul_apply, Nat.factorial_succ]
    congr 1
    push_cast
    rw [mul_inv]

theorem der_mem {r n : ℕ} (ν : Fin n → ℕ) (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ)
    (hf : f ∈ dualWeyl ℚ r n ν) : (der r n a b : Module.End ℚ _) f ∈ dualWeyl ℚ r n ν := by
  have h := rowDivStable ℚ r n ν a b 1 f hf
  rwa [rowDiv_one] at h

theorem fock_add_left {σ : Type} (f f' g : MvPolynomial σ ℚ) : fockQ (f + f') g = fockQ f g + fockQ f' g :=
  (fockQBilin σ f f' g 0).1

theorem fock_smul_left {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ (c • f) g = c * fockQ f g :=
  (fockQBilin σ f 0 g c).2

theorem fock_symm {σ : Type} (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := (fockQPos σ f g).1

theorem fock_add_right {σ : Type} (f g g' : MvPolynomial σ ℚ) : fockQ f (g + g') = fockQ f g + fockQ f g' := by
  rw [fock_symm, fock_add_left, fock_symm g, fock_symm g']

theorem fock_smul_right {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ f (c • g) = c * fockQ f g := by
  rw [fock_symm, fock_smul_left, fock_symm g]

theorem fock_der {r n : ℕ} (a b : Fin r) (f g : MvPolynomial (Fin r × Fin n) ℚ) :
    fockQ (der r n a b f) g = fockQ f (der r n b a g) := by
  rw [← rowDiv_one, ← rowDiv_one]
  exact fockQRowDivAdj r n a b 1 f g

end Formalism.CohomologicalDescent.LR
end
end

