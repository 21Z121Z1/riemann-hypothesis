import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0023
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SplitUnramifiedPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0009
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
import Formalism.HermitianCurvature.StatementM
import Formalism.HermitianCurvature.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AevalNegEqZeroOfResolventIdentityStatement
section
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_neg_eq_zero_of_resolvent_identity : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (p : Polynomial ℂ), (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = p.eval u • w) → Polynomial.aeval (-Ω) p = 0 ∧ ∀ (α : ℂ) (w : N), Ω w = α • w → ∀ (q : Polynomial ℂ), p = (Polynomial.X + Polynomial.C α) * q → ∀ u : ℂ, X u w = q.eval u • w := by
  first | exact @GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity | exact GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity | (intros; apply GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlgTensWtNearStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wtNear_pr_and_io_of_algTens : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (Λ : Fin n → ℝ) (t : ℝ), AlgTens ε E N F io pr → (∀ w, w ∈ WtNear E Λ t → ∀ s c, pr s (Pi.single c w) ∈ WtNear (F s) Λ (t + 1)) ∧ ∀ s (y : N s), y ∈ WtNear (F s) Λ t → ∀ d, io s y d ∈ WtNear E Λ (t + 1) := by
  first | exact @GlobalTheory.algTens_wtNear | exact GlobalTheory.algTens_wtNear | (intros; apply GlobalTheory.algTens_wtNear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliLeftComatrix
section
open Formalism.REAL Finset

namespace GlobalTheory

theorem capelli_left_comatrix :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E →
      ∀ (u : ℂ) (j l : Fin (m + 1)),
        ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
            (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) =
          if l = j then qdet E u else 0 := by
  intro A _ _ m E hE u j l
  set b : Fin (m + 1) → Fin (m + 1) := Fin.cons l (Fin.succAbove j) with hb
  have hexp := PI.QmColExpWork.expFirst E id b u
  have hbc : b ∘ Fin.succ = Fin.succAbove j := by
    funext k; simp [hb]
  have hb0 : b 0 = l := by simp [hb]
  rw [hbc, hb0] at hexp
  have hcast : ∀ (k : ℕ) (x : A), (((-1 : ℤ) ^ k : ℤ) : A) * x = ((-1 : ℂ) ^ k) • x := by
    intro k x
    rw [Algebra.smul_def]
    push_cast
    simp
  have hL : ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
      (Tm E u a l * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) =
      ((-1 : ℂ) ^ (j : ℕ)) • qminor E id b u := by
    rw [hexp, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcast, smul_smul, ← pow_add, add_comm (j : ℕ) (a : ℕ)]
    rfl
  rw [hL]
  by_cases hlj : l = j
  · subst hlj
    have hbcyc : b = id ∘ PI.QmColExpWork.cyc0 m l := by
      funext k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp [hb, PI.QmColExpWork.cycle_perm_zero]
      · simp [hb, PI.QmColExpWork.cycle_perm_succ]
    rw [if_pos rfl, hbcyc, qSkewCol A (m + 1) (m + 1) E hE id id _ u, PI.QmColExpWork.sign_cycle_perm,
      Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, hcast, smul_smul, ← mul_pow]
    simp [qdet]
  · rw [if_neg hlj]
    obtain ⟨k0, hk0⟩ := Fin.exists_succAbove_eq hlj
    have hfix : b ∘ Equiv.swap (0 : Fin (m + 1)) k0.succ = b := by
      funext k
      have h0 : b 0 = b k0.succ := by simp [hb, hk0]
      simp only [Function.comp, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, h0]
      · rw [h2, h0]
      · rfl
    have hs := qSkewCol A (m + 1) (m + 1) E hE id b (Equiv.swap 0 k0.succ) u
    rw [hfix, Equiv.Perm.sign_swap (Fin.succ_ne_zero k0).symm] at hs
    have h2 : (2 : ℂ) • qminor E id b u = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hs]
      simp
    have hz : qminor E id b u = 0 := by
      have h3 := congrArg (fun x => (2 : ℂ)⁻¹ • x) h2
      simpa [smul_smul] using h3
    rw [hz, smul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasKIsSymmetricAndFormStatement
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casK_isSymmetric_and_inner_re_eq : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E → LinearMap.IsSymmetric (CasK ε E) ∧ ∀ x, (⟪x, CasK ε E x⟫_ℂ).re = ∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.casK_isSymmetric_and_form | exact GlobalTheory.casK_isSymmetric_and_form | (intros; apply GlobalTheory.casK_isSymmetric_and_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscriminantGramUnit
section
noncomputable section
open scoped TensorProduct
open Matrix

namespace GlobalTheory.CutMultiplicationUnits

section Lin

variable {k A O : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing O] [Algebra k O]

abbrev cut (k : Type) {A : Type} [CommRing k] [CommRing A] [Algebra k A] (e : A) : Submodule k A :=
  LinearMap.range (LinearMap.mulLeft k e)

theorem mul_mem_cut {e : A} (y : A) {a : A} (ha : a ∈ cut k e) : y * a ∈ cut k e := by
  obtain ⟨c, rfl⟩ := ha
  exact ⟨y * c, by simp [mul_left_comm]⟩

theorem e_mul_of_mem {e : A} (he : e * e = e) {a : A} (ha : a ∈ cut k e) : e * a = a := by
  obtain ⟨c, rfl⟩ := ha
  simp [← mul_assoc, he]

def mulCut (e y : A) : cut k e →ₗ[k] cut k e :=
  (LinearMap.mulLeft k y).restrict (fun _ ha => mul_mem_cut y ha)

variable {n : ℕ} {e : A} (b : Module.Basis (Fin n) k (cut k e))

variable (T : Fin n → (A →ₐ[k] O))

end Lin

section Local

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

def extFun (l : R →ₗ[ℤ] ℤ) : Op p R →ₗ[ℤ_[p]] ℤ_[p] :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℤ_[p] ℤ_[p]).toLinearMap ∘ₗ l.baseChange ℤ_[p]

variable [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R]
  {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O]

end Local

section Compare

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces ReciprocityTheory.ChartRestriction.G.Pdiv

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

theorem sig_eq_bar [StarRing R] (x : Op p R) : AvDefs.sig p R x = bar p R x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z a => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def placeUEquiv : AvDefs.PlaceU p R ≃ Place p R where
  toFun w := ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  invFun w := ⟨w.e, w.idem, w.ne_zero, w.primitive⟩
  left_inv _ := rfl
  right_inv _ := rfl

def placeEquiv [StarRing R] : AvDefs.Place p R ≃ SplitPlace p R where
  toFun w := ⟨⟨w.e, w.idem, w.ne_zero, w.prim⟩, fun h =>
    w.split ((sig_eq_bar w.e).trans (congrArg Place.e h).symm)⟩
  invFun w := ⟨w.e, w.idem, w.ne_zero, w.primitive, fun h =>
    w.ne_conj (Place.ext ((sig_eq_bar w.e).symm.trans h).symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def owEquiv (w : Place p R) : cut ℤ_[p] w.e ≃ₗ[ℤ_[p]] w.Ow :=
  LinearEquiv.ofBijective
    ((Ideal.Quotient.mkₐ ℤ_[p] (Ideal.span {1 - w.e})).toLinearMap ∘ₗ (cut ℤ_[p] w.e).subtype) (by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro a ha
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 ha)
        have hc' : c * (1 - w.e) = (a : Op p R) := hc
        apply Subtype.ext
        rw [← e_mul_of_mem w.idem a.2, ← hc', mul_left_comm, mul_sub, w.idem.eq, mul_one,
          sub_self, mul_zero]
        rfl
      · intro s
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
        refine ⟨⟨w.e * a, a, rfl⟩, Ideal.Quotient.eq.2 ?_⟩
        exact Ideal.mem_span_singleton'.2 ⟨-a, by
          show -a * (1 - w.e) = w.e * a - a
          ring⟩)

def embEquiv (w : Place p R) (O : Type) [CommRing O] [Algebra ℤ_[p] O] :
    AvDefs.Emb (O := O) w.e ≃ w.Emb O := Equiv.refl _

variable [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R]
  {C : Type} [Field C] [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O]

end Compare

end GlobalTheory.CutMultiplicationUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGridFiveApartOnCut
section
open Formalism.FourierDecayAlt Finset

namespace GlobalTheory

theorem exists_grid_five_apart_on_cut :
    (∀ (u u' : ℕ → ℝ) (l M₀ : ℕ), 5 * (M₀ : ℝ) ≤ |u l - u' l| → ∃ Y : Finset ℝ, M₀ ≤ Y.card ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧
      ∀ y ∈ Y, I.OnCut u u' l y ∧ I.OnCut u u' l (y + 1)) ∧
    ∀ r : ℕ, 5 * (3 * (r + 1) * (2 * r + 1)) ≤ 30 * (r + 1) ^ 2 + 6 := by
  refine ⟨fun u u' l M₀ h => ?_, fun r => by nlinarith [Nat.zero_le r]⟩
  have hmax : min (u l) (u' l) + 5 * (M₀ : ℝ) ≤ max (u l) (u' l) := by
    have := max_sub_min_eq_abs (u l) (u' l)
    rw [abs_sub_comm] at h
    linarith
  refine ⟨(range M₀).image (fun i : ℕ => -(min (u l) (u' l) + 3 + 5 * (i : ℝ))), ?_, ?_, ?_⟩
  · rw [card_image_of_injective, card_range]
    intro i j hij
    have : (i : ℝ) = j := by
      simp only at hij
      linarith
    exact_mod_cast this
  · intro y hy y' hy' hne
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy
    obtain ⟨j, -, rfl⟩ := mem_image.1 hy'
    have hij : i ≠ j := fun e => hne (by rw [e])
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
      exact le_trans (by linarith) (le_abs_self _)
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
      exact le_trans (by linarith) (neg_le_abs _)
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hy
    have h1 : (i : ℝ) + 1 ≤ M₀ := by exact_mod_cast mem_range.1 hi
    have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    unfold I.OnCut
    rcases le_total (u l) (u' l) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at hmax
      rw [min_eq_left hle]
      exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩
    · rw [min_eq_right hle, max_eq_left hle] at hmax
      rw [min_eq_right hle]
      exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLinearEquivOfIrreducibleIsHW
section
open Formalism.REAL

namespace GlobalTheory

theorem stable_submodule_proj_bijective {U V₁ V₂ : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ U) (E₁ : Fin n → Fin n → Module.End ℂ V₁)
    (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ) (v : U)
    (p : U →ₗ[ℂ] V₁) (q : U →ₗ[ℂ] V₂)
    (hp : ∀ a b x, p (E a b x) = E₁ a b (p x)) (hq : ∀ a b x, q (E a b x) = E₂ a b (q x))
    (hpq : ∀ x, p x = 0 → q x = 0 → x = 0)
    (h₁ : ∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (h₂ : ∀ S : Submodule ℂ V₂, (∀ a b, ∀ x ∈ S, E₂ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hw : ∀ a, E₁ a a (p v) = ν a • p v) (hv₁ : p v ≠ 0) (hv₂ : q v ≠ 0)
    (S : Submodule ℂ U) (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (hvS : v ∈ S)
    (htop : ∀ x ∈ S, (∀ a, E a a x = ν a • x) → ∃ c : ℂ, x = c • v) :
    Function.Bijective (q.comp S.subtype) := by
  constructor
  · have hK := h₁ ((S ⊓ LinearMap.ker q).map p) (by
      rintro a b _ ⟨x, ⟨hxS, hxq⟩, rfl⟩
      refine ⟨E a b x, ⟨hS a b x hxS, ?_⟩, hp a b x⟩
      have hxq' : q x = 0 := hxq
      show q (E a b x) = 0
      rw [hq, hxq', map_zero])
    rcases hK with hK | hK
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have hx' : q x = 0 := hx
      have hm : p x ∈ (S ⊓ LinearMap.ker q).map p := ⟨x, ⟨x.2, hx'⟩, rfl⟩
      rw [hK, Submodule.mem_bot] at hm
      exact Subtype.ext (hpq _ hm hx')
    · exfalso
      have hm : p v ∈ (S ⊓ LinearMap.ker q).map p := by rw [hK]; trivial
      obtain ⟨x, ⟨hxS, hxq⟩, hxp⟩ := hm
      have hxq' : q x = 0 := hxq
      obtain ⟨c, hc⟩ := htop x hxS (fun a => by
        rw [← sub_eq_zero]
        apply hpq
        · rw [map_sub, hp, map_smul, hxp, hw, sub_self]
        · rw [map_sub, hq, map_smul, hxq', map_zero, smul_zero, sub_self])
      rw [hc, map_smul, smul_eq_zero] at hxq'
      rcases hxq' with h0 | h0
      · apply hv₁
        rw [← hxp, hc, h0, zero_smul, map_zero]
      · exact hv₂ h0
  · have hK := h₂ (S.map q) (by
      rintro a b _ ⟨x, hxS, rfl⟩
      exact ⟨E a b x, hS a b x hxS, hq a b x⟩)
    rcases hK with hK | hK
    · exfalso
      have hm : q v ∈ S.map q := ⟨v, hvS, rfl⟩
      rw [hK, Submodule.mem_bot] at hm
      exact hv₂ hm
    · intro y
      have hm : y ∈ S.map q := by rw [hK]; trivial
      obtain ⟨x, hxS, rfl⟩ := hm
      exact ⟨⟨x, hxS⟩, rfl⟩

theorem exists_linearEquiv_of_irreducible_isHW :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁) (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ) (v₁ : V₁) (v₂ : V₂), GlRel E₁ → GlRel E₂ → (∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ S : Submodule ℂ V₂, (∀ a b, ∀ x ∈ S, E₂ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → IsHW E₁ ν v₁ → IsHW E₂ ν v₂ → v₁ ≠ 0 → v₂ ≠ 0 → ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by
  intro V₁ _ _ V₂ _ _ n E₁ E₂ ν v₁ v₂ hE₁ hE₂ h₁ h₂ hw₁ hw₂ hv₁ hv₂
  let E : Fin n → Fin n → Module.End ℂ (V₁ × V₂) := fun a b => (E₁ a b).prodMap (E₂ a b)
  have hEap : ∀ a b (x : V₁ × V₂), E a b x = (E₁ a b x.1, E₂ a b x.2) := fun _ _ _ => rfl
  have hE : GlRel E := by
    intro a b c d
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hEap]
    rw [glRel_apply_comm hE₁ a b c d, glRel_apply_comm hE₂ a b c d]
    split_ifs <;> simp [hEap]
    all_goals (constructor <;> abel)
  have hw : IsHW E ν (v₁, v₂) := by
    refine ⟨fun a => ?_, fun a b h => ?_⟩
    · rw [hEap, hw₁.1, hw₂.1]; rfl
    · rw [hEap, hw₁.2 a b h, hw₂.2 a b h]; rfl
  obtain ⟨S, hS, hvS, htop⟩ := exists_stable_submodule_topWeight_line _ n E ν _ hE hw
  have b₂ := stable_submodule_proj_bijective E E₁ E₂ ν (v₁, v₂) (LinearMap.fst ℂ V₁ V₂)
    (LinearMap.snd ℂ V₁ V₂) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x h h' => Prod.ext h h') h₁ h₂ hw₁.1 hv₁ hv₂ S hS hvS htop
  have b₁ := stable_submodule_proj_bijective E E₂ E₁ ν (v₁, v₂) (LinearMap.snd ℂ V₁ V₂)
    (LinearMap.fst ℂ V₁ V₂) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x h h' => Prod.ext h' h) h₂ h₁ hw₂.1 hv₂ hv₁ S hS hvS htop
  refine ⟨(LinearEquiv.ofBijective _ b₁).symm.trans (LinearEquiv.ofBijective _ b₂), ?_⟩
  intro a b x
  obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective _ b₁).surjective x
  have h : E₁ a b (LinearEquiv.ofBijective _ b₁ y)
      = LinearEquiv.ofBijective _ b₁ ⟨E a b y, hS a b y y.2⟩ := rfl
  rw [h]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowOfFiniteField
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EmbFrob

open Polynomial

theorem exists_pow_of_finite_field (p : ℕ) [Fact p.Prime] {F k : Type} [Field F] [Finite F]
    [Field k] [CharP k p] (f g : F →+* k) : ∃ i : ℕ, ∀ a : F, g a = f a ^ p ^ i := by
  haveI : CharP F p := f.charP f.injective p
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : Algebra F k := f.toAlgebra
  haveI : IsScalarTower (ZMod p) F k := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let g' : F →ₐ[ZMod p] k :=
    { g with commutes' := fun z =>
        RingHom.congr_fun (Subsingleton.elim (g.comp (algebraMap (ZMod p) F)) (algebraMap _ k)) z }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2
    (g'.restrictNormal' F)
  refine ⟨n, fun a => ?_⟩
  have h1 : algebraMap F k (g'.restrictNormal' F a) = g' (algebraMap F F a) :=
    AlgHom.restrictNormal_commutes g' F a
  have h2 : g'.restrictNormal' F a = a ^ p ^ (n : ℕ) := by
    rw [← hn]
    simp [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [h2, map_pow] at h1
  exact h1.symm

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

theorem comap_eq {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] [IsDedekindDomain OE]
    [CharZero OE] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[p] R]
    (hp : ¬ IsUnit (p : R)) (w : Place p OE) {P : Ideal OE}
    (hP : ∀ Q : Ideal OE, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤) (σ : OE →+* R)
    (hσ : extend σ w.e = 1) : (IsLocalRing.maximalIdeal R).comap σ = P := by
  by_contra hne
  have hpQ : (p : OE) ∈ (IsLocalRing.maximalIdeal R).comap σ := by
    rw [Ideal.mem_comap, map_natCast]; exact hp
  have hQ : ((IsLocalRing.maximalIdeal R).comap σ).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun h => ?_
    rw [h, Ideal.mem_bot] at hpQ
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hpQ
  let φ : w.Ow →+* R := Ideal.Quotient.lift _ (extend σ).toRingHom (by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    simp [hσ])
  have hφ : ∀ a, φ (w.toOw a) = σ a := fun a => by
    show extend (p := p) σ (1 ⊗ₜ a) = σ a
    simp
  have hle : ((IsLocalRing.maximalIdeal R).comap σ).map w.toOw ≤
      (IsLocalRing.maximalIdeal R).comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, hφ]
    exact ha
  rw [hP _ hQ hne, top_le_iff] at hle
  exact Ideal.comap_ne_top φ (IsLocalRing.maximalIdeal.isMaximal R).ne_top hle

theorem exists_frobenius_pow : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [IsDedekindDomain OE] [CharZero OE] [Module.Finite ℤ OE] (C : Type) [Field C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R],
    v.Integers R → ¬ IsUnit (p : R) → ∀ (w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE)
    (σ τ : OE →+* R), σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e →
    τ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e →
    ∃ i : ℕ, ∀ a : OE, v (algebraMap R C (τ a - σ a ^ (p ^ i))) < 1 := by
  intro p _ OE _ _ _ _ C _ v R _ _ _ hv hp w σ τ hσ hτ
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  let w' : Place p OE := ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  obtain ⟨P, hPm, hpP, -, hP⟩ := GlobalTheory.OnePrime.exists_prime_under p OE w'
  have h1 := comap_eq hp w' hP σ hσ
  have h2 := comap_eq hp w' hP τ hτ
  have hP0 : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hpP
  haveI : Finite (OE ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  letI : Field (OE ⧸ P) := Ideal.Quotient.field P
  haveI : CharP (IsLocalRing.ResidueField R) p := by
    refine (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 ?_
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]
    exact hp
  obtain ⟨i, hi⟩ := exists_pow_of_finite_field p (k := IsLocalRing.ResidueField R)
    (Ideal.quotientMap (IsLocalRing.maximalIdeal R) σ h1.ge)
    (Ideal.quotientMap (IsLocalRing.maximalIdeal R) τ h2.ge)
  refine ⟨i, fun a => ?_⟩
  have h3 : IsLocalRing.residue R (τ a) = IsLocalRing.residue R (σ a) ^ p ^ i :=
    hi (Ideal.Quotient.mk P a)
  have h4 : τ a - σ a ^ p ^ i ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, h3, sub_self]
  exact lt_of_le_of_ne (hv.map_le_one _) fun h => h4 (hv.isUnit_iff_valuation_eq_one.2 h)

end GlobalTheory.EmbFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPrimitiveIdempotentMapEqOne
section
open TensorProduct

namespace GlobalTheory

theorem exists_primitive_idempotent_map_eq_one {A R : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] (φ : A →+* R) :
    ∃ e : A, e * e = e ∧ e ≠ 0 ∧ (∀ f : A, f * f = f → f * e = f → f = 0 ∨ f = e) ∧ φ e = 1 := by
  let S : Set (Ideal A) := {I | ∃ e : A, e * e = e ∧ φ e = 1 ∧ I = Ideal.span {1 - e}}
  have hS : S.Nonempty := ⟨_, 1, by simp, by simp, rfl⟩
  obtain ⟨I, ⟨e, he, hφe, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian A A)) S hS
  have key : ∀ f : A, f * f = f → f * e = f → φ f = 1 → f = e := by
    intro f hf hfe hφf
    have hle : Ideal.span {1 - e} ≤ Ideal.span {1 - f} := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton']
      exact ⟨1 - e, by linear_combination hfe⟩
    have heq : Ideal.span {1 - e} = Ideal.span {1 - f} := by
      by_contra hne
      exact hmax _ ⟨f, hf, hφf, rfl⟩ (lt_of_le_of_ne hle hne)
    have hmem : 1 - f ∈ Ideal.span {1 - e} := heq ▸ Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    linear_combination e * hc - hfe + c * he
  refine ⟨e, he, ?_, ?_, hφe⟩
  · rintro rfl
    simp at hφe
  · intro f hf hfe
    have hid : IsIdempotentElem (φ f) := by
      change φ f * φ f = φ f
      rw [← map_mul, hf]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hid with h | h
    · left
      have := key (e - f) (by linear_combination he + hf - 2 * hfe)
        (by linear_combination he - hfe) (by rw [map_sub, h, hφe, sub_zero])
      linear_combination -this
    · exact Or.inr (key f hf hfe h)

theorem exists_placeU_mem_emb (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [Algebra ℤ_[p] R] (σ : OE →+* R) :
    ∃ w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE,
      σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e := by
  haveI : IsNoetherianRing (ℤ_[p] ⊗[ℤ] OE) :=
    IsNoetherianRing.of_finite ℤ_[p] _
  obtain ⟨e, h1, h2, h3, h4⟩ := exists_primitive_idempotent_map_eq_one
    (ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (p := p) σ).toRingHom
  exact ⟨⟨e, h1, h2, h3⟩, h4⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstAssocStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesConvergentSubst_assoc : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ρ σ τ : Type) [Fintype ρ] [Fintype σ] (s : ρ → MvPowerSeries σ K) (t : σ → MvPowerSeries τ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) → (∀ i, Small (t i)) → Bdd S → (∀ j, Small (csub t (s j))) ∧ csub t (csub s S) = csub (fun j => csub t (s j)) S := by
  first | exact @GlobalTheory.ConvSer.csub_assoc | exact GlobalTheory.ConvSer.csub_assoc | (intros; apply GlobalTheory.ConvSer.csub_assoc <;> assumption)
end

