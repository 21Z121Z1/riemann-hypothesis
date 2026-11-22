import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalIntegralLiftOfOrthogon
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolProdLeTsumSlices
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem covol_prod_le_tsum_slices : ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] [MeasurableSpace G₁] [MeasurableSpace G₂] [MeasurableMul G₂] (μ₁ : Measure G₁) (μ₂ : Measure G₂) [SigmaFinite μ₁] [SigmaFinite μ₂] [μ₂.IsMulLeftInvariant] (Γ : Subgroup (G₁ × G₂)) (K : Subgroup G₂) (A : Set (G₁ × G₂)) (ι : Type) [Countable ι] (x : ι → G₂) (Γc Ac : ι → Set G₁), MeasurableSet (K : Set G₂) → (∀ c, ∀ g ∈ Γc c, ∃ γ ∈ Γ, γ.1 = g ∧ (x c)⁻¹ * γ.2 * x c ∈ K) → (∀ y ∈ A, ∃ c, ∃ γ ∈ Γ, ∃ k ∈ K, γ.2 * y.2 = x c * k ∧ γ.1 * y.1 ∈ Ac c) → μ₂ K ≠ ⊤ → covol (Γ : Set (G₁ × G₂)) (μ₁.prod μ₂) A ≤ μ₂ K * ∑' c, covol (Γc c) μ₁ (Ac c) := by
  intro G₁ G₂ _ _ _ _ _ μ₁ μ₂ _ _ _ Γ K A ι _ x Γc Ac hK hΓ hA hfin
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hb => ?_
  obtain ⟨ε', hε', hsum⟩ := ENNReal.exists_pos_sum_of_countable (ε := (ε : ENNReal))
    (by exact_mod_cast hε.ne') ι
  have key : ∀ c, ∃ D : Set G₁, MeasurableSet D ∧
      μ₂ K * μ₁ D ≤ μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c ∧
      (D = Set.univ ∨ ∀ y ∈ Ac c, ∃ g ∈ Γc c, g * y ∈ D) := by
    intro c
    by_cases h0 : μ₂ K = 0
    · exact ⟨Set.univ, MeasurableSet.univ, by simp [h0], Or.inl rfl⟩
    · have hc : μ₂ K * covol (Γc c) μ₁ (Ac c) ≠ ⊤ :=
        ne_top_of_le_ne_top hb.ne (mul_le_mul_right (ENNReal.le_tsum c) _)
      have hlt : μ₂ K * covol (Γc c) μ₁ (Ac c) < μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c :=
        ENNReal.lt_add_right hc (by exact_mod_cast (hε' c).ne')
      have h2 : μ₂ K * covol (Γc c) μ₁ (Ac c) = ⨅ (D : Set G₁) (_ : MeasurableSet D)
          (_ : ∀ y ∈ Ac c, ∃ g ∈ Γc c, g * y ∈ D), μ₂ K * μ₁ D := by
        simp only [covol, ENNReal.mul_iInf_of_ne h0 hfin]
      rw [h2] at hlt
      simp only [iInf_lt_iff] at hlt
      obtain ⟨D, hD, hcov, hlt⟩ := hlt
      rw [← h2] at hlt
      exact ⟨D, hD, hlt.le, Or.inr hcov⟩
  choose D hDm hDle hDcov using key
  have hKm : ∀ c, MeasurableSet ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂)) := fun c =>
    measurable_const_mul _ hK
  have h1 : covol (Γ : Set (G₁ × G₂)) (μ₁.prod μ₂) A ≤
      (μ₁.prod μ₂) (⋃ c, D c ×ˢ ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂))) := by
    refine iInf_le_of_le _ (iInf_le_of_le (MeasurableSet.iUnion fun c => (hDm c).prod (hKm c))
      (iInf_le_of_le ?_ le_rfl))
    intro y hy
    obtain ⟨c, γ, hγ, k, hk, h2, h1⟩ := hA y hy
    rcases hDcov c with hu | hcov
    · refine ⟨γ, hγ, Set.mem_iUnion.2 ⟨c, by simp [hu], ?_⟩⟩
      simpa [h2] using hk
    · obtain ⟨g, hg, hgD⟩ := hcov _ h1
      obtain ⟨δ, hδ, rfl, hδK⟩ := hΓ c g hg
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, Set.mem_iUnion.2 ⟨c, by simpa [mul_assoc] using hgD, ?_⟩⟩
      have := K.mul_mem hδK hk
      simpa [mul_assoc, h2] using this
  refine h1.trans ((measure_iUnion_le _).trans ?_)
  calc ∑' c, (μ₁.prod μ₂) (D c ×ˢ ((fun g => (x c)⁻¹ * g) ⁻¹' (K : Set G₂)))
      ≤ ∑' c, (μ₂ K * covol (Γc c) μ₁ (Ac c) + ε' c) := by
        refine ENNReal.tsum_le_tsum fun c => ?_
        rw [Measure.prod_prod, measure_preimage_mul, mul_comm]
        exact hDle c
    _ ≤ _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        exact add_le_add le_rfl hsum.le

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerTail
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.DerTail

theorem tri_add (a b : ℕ) : (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, Nat.triangle_succ, Nat.triangle_succ, ih]
    ring

variable {g : ℕ} [Fact g.Prime]

theorem entN_tl (m : ℕ) {n : ℕ} (M : Mt g n) {a b : ℕ} (ha : a < m) (hb : b < m) :
    entN (tl m M) a b = entN M a b := by
  rw [entN, dif_pos ⟨ha, hb⟩]; rfl

theorem entN_fin {n : ℕ} (M : Mt g n) (a b : Fin n) : entN M a b = M a b := by
  rw [entN, dif_pos ⟨a.2, b.2⟩]

theorem inR_iff (i : ℕ) {n : ℕ} (M : Mt g n) :
    InR i M ↔ ∀ a : ℕ, i ≤ a → a < n → (∀ b, b < a → entN M a b = 0) ∧ entN M a a = 1 := by
  constructor
  · rintro ⟨h1, h2⟩ a hia han
    refine ⟨fun b hb => ?_, ?_⟩
    · by_cases hbi : b < i
      · have := h1 ⟨a, han⟩ ⟨b, by omega⟩ hbi hia
        exact (entN_fin M ⟨a, han⟩ ⟨b, by omega⟩).trans this
      · have := (h2 ⟨a - i, by omega⟩ ⟨b - i, by omega⟩).1 (by simp only [Fin.mk_lt_mk]; omega)
        simp only [br] at this
        rwa [show i + (a - i) = a by omega, show i + (b - i) = b by omega] at this
    · have := (h2 ⟨a - i, by omega⟩ ⟨a - i, by omega⟩).2 rfl
      simp only [br] at this
      rwa [show i + (a - i) = a by omega] at this
  · intro h
    refine ⟨fun a b hb ha => ?_, fun a b => ⟨fun hab => ?_, fun hab => ?_⟩⟩
    · exact (entN_fin M a b).symm.trans ((h a ha a.2).1 b (by omega))
    · have := a.2
      have hab' : (b : ℕ) < a := hab
      exact (h (i + a) (by omega) (by omega)).1 (i + b) (by omega)
    · subst hab
      have := a.2
      exact (h (i + a) (by omega) (by omega)).2

theorem inR_split {i m n : ℕ} (him : i ≤ m) (hmn : m ≤ n) (M : Mt g n) :
    InR i M ↔ InR m M ∧ InR i (tl m M) := by
  simp only [inR_iff]
  constructor
  · intro h
    refine ⟨fun a ha han => h a (by omega) han, fun a ha ham => ⟨fun b hb => ?_, ?_⟩⟩
    · rw [entN_tl m M ham (by omega)]
      exact (h a ha (by omega)).1 b hb
    · rw [entN_tl m M ham ham]
      exact (h a ha (by omega)).2
  · rintro ⟨h1, h2⟩ a ha han
    by_cases ham : a < m
    · refine ⟨fun b hb => ?_, ?_⟩
      · rw [← entN_tl m M ham (by omega)]
        exact (h2 a ha ham).1 b hb
      · rw [← entN_tl m M ham ham]
        exact (h2 a ha ham).2
    · exact h1 a (by omega) han

theorem tl_tl {i m n : ℕ} (him : i ≤ m) (M : Mt g n) : tl i (tl m M) = tl i M := by
  funext a b
  have := a.2
  have := b.2
  exact entN_tl m M (by omega) (by omega)

theorem supFrom_split {i m n : ℕ} (him : i < m) (hmn : m ≤ n) (M : Mt g n) :
    supFrom i M = supFrom (m - 1) M + supFrom i (tl m M) := by
  unfold supFrom
  rw [add_comm, ← Finset.sum_Ico_consecutive _ (show i ≤ m - 1 by omega) (show m - 1 ≤ n - 1 by omega)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  exact (entN_tl m M (by omega) (by omega)).symm

theorem der_tail : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m n : ℕ) (F : Gn g n → ℂ),
    i < m → m ≤ n → der ψ i (tail ψ m F) = der ψ i F := by
  intro g _ ψ i m n F him hmn
  funext h
  rw [GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum g ψ i m _ h him.le, GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum g ψ i n _ h (by omega)]
  have he : i * (n - i) + (n - i) * (n - i - 1) / 2 =
      (i * (m - i) + (m - i) * (m - i - 1) / 2) + (m * (n - m) + (n - m) * (n - m - 1) / 2) := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le him.le
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [show i + a + b - i = a + b by omega, show i + a - i = a by omega, show i + a + b - (i + a) = b by omega,
      tri_add]
    ring
  rw [he, pow_add _ _ (m * (n - m) + (n - m) * (n - m - 1) / 2), mul_inv _ ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2)),
    mul_assoc]
  congr 1
  unfold tail
  set c : ℂ := ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2))⁻¹
  have h1 : ∀ p : Gn g m, (if InR i (p : Mt g m) ∧ tl i (p : Mt g m) = (h : Mt g i) then
      (c * ∑ x : Gn g n, if InR m (x : Mt g n) ∧ tl m (x : Mt g n) = (p : Mt g m) then
        F x * (ψ (supFrom (m - 1) (x : Mt g n)))⁻¹ else 0) * (ψ (supFrom i (p : Mt g m)))⁻¹ else 0) =
      c * ∑ x : Gn g n, if tl m (x : Mt g n) = (p : Mt g m) then
        (if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then
          F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0) else 0 := by
    intro p
    split_ifs with hp
    · rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : tl m (x : Mt g n) = (p : Mt g m)
      · rw [if_pos hx]
        rw [← hx] at hp
        rw [tl_tl him.le] at hp
        rw [inR_split him.le hmn (x : Mt g n), supFrom_split him hmn (x : Mt g n), AddChar.map_add_eq_mul, mul_inv,
          ← hx]
        by_cases hR : InR m (x : Mt g n)
        · rw [if_pos ⟨hR, rfl⟩, if_pos ⟨⟨hR, hp.1⟩, hp.2⟩, mul_assoc]
        · rw [if_neg (fun hh => hR hh.1), if_neg (fun hh => hR hh.1.1), zero_mul]
      · rw [if_neg hx, if_neg (fun hh => hx hh.2), zero_mul]
    · symm
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : tl m (x : Mt g n) = (p : Mt g m)
      · rw [if_pos hx, if_neg]
        rintro ⟨ha, hb⟩
        apply hp
        rw [← hx, tl_tl him.le]
        exact ⟨((inR_split him.le hmn _).1 ha).2, hb⟩
      · rw [if_neg hx]
  rw [Finset.sum_congr rfl fun p _ => h1 p, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i)
  · have hu : IsUnit (tl m (x : Mt g n)) :=
      ((GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g m (n - m) n (by omega)).2.2.1 x ((inR_split him.le hmn _).1 hx.1).1.1).1
    obtain ⟨p, hp⟩ := hu
    rw [Finset.sum_eq_single p]
    · rw [if_pos hp.symm]
    · intro q _ hq
      rw [if_neg]
      intro hh
      exact hq (Units.ext (hp.trans hh).symm)
    · intro hh
      exact absurd (Finset.mem_univ p) hh
  · simp [hx]

end GlobalTheory.GLm.DerTail
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetConjOnMatricesKillingIntoSubspace
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.HomConjDet

section General

variable {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

theorem det_eq_of_equiv (e : U ≃ₗ[ℂ] V) (φ : U →ₗ[ℂ] U) (ψ : V →ₗ[ℂ] V)
    (h : ∀ x, e (φ x) = ψ (e x)) : LinearMap.det φ = LinearMap.det ψ := by
  rw [← LinearMap.det_conj φ e]
  congr 1
  ext y
  simp [h]

variable [Module.Finite ℂ U] [Module.Finite ℂ V]

theorem det_comp_left (α : V →ₗ[ℂ] V) :
    LinearMap.det (LinearMap.llcomp ℂ U V V α : (U →ₗ[ℂ] V) →ₗ[ℂ] (U →ₗ[ℂ] V)) = LinearMap.det α ^ Module.finrank ℂ U := by
  let b := Module.finBasis ℂ U
  have h := LinearMap.det_pi (fun _ : Fin (Module.finrank ℂ U) => α)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  symm
  refine det_eq_of_equiv (b.constr ℂ) _ _ fun x => ?_
  refine b.ext fun i => ?_
  simp

theorem det_comp_right (β : U →ₗ[ℂ] U) :
    LinearMap.det (LinearMap.lcomp ℂ V β) = LinearMap.det β ^ Module.finrank ℂ V := by
  let b := Module.finBasis ℂ V
  have h := LinearMap.det_pi (fun _ : Fin (Module.finrank ℂ V) => β.dualMap)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, LinearMap.det_dualMap] at h
  rw [← h]
  symm
  refine det_eq_of_equiv ((LinearEquiv.linearMapPi ℂ).trans (LinearEquiv.congrRight b.equivFun.symm))
    _ _ fun x => ?_
  ext y
  simp [LinearEquiv.congrRight]

end General

variable {n : ℕ}

def homMat (P Q : Submodule ℂ (Fin n → ℂ)) :
    (((Fin n → ℂ) ⧸ P) →ₗ[ℂ] Q) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  (LinearMap.toMatrix' : ((Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ
    LinearMap.llcomp ℂ _ _ _ Q.subtype ∘ₗ LinearMap.lcomp ℂ Q P.mkQ

theorem homMat_mulVec (P Q : Submodule ℂ (Fin n → ℂ)) (T : ((Fin n → ℂ) ⧸ P) →ₗ[ℂ] Q) (y : Fin n → ℂ) :
    homMat P Q T *ᵥ y = (T (P.mkQ y) : Fin n → ℂ) := by
  simp [homMat, LinearMap.toMatrix'_mulVec]

theorem homMat_injective (P Q : Submodule ℂ (Fin n → ℂ)) : Function.Injective (homMat P Q) := by
  intro S T h
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := P.mkQ_surjective x
  apply Subtype.ext
  rw [← homMat_mulVec, ← homMat_mulVec, h]

theorem range_homMat (P Q : Submodule ℂ (Fin n → ℂ)) (H : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hH : ∀ X, X ∈ H ↔ (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q) : LinearMap.range (homMat P Q) = H := by
  ext X
  rw [hH]
  constructor
  · rintro ⟨T, rfl⟩
    refine ⟨fun y hy => ?_, fun y => ?_⟩
    · rw [homMat_mulVec, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hy]
      simp
    · rw [homMat_mulVec]
      exact Subtype.property _
  · rintro ⟨h1, h2⟩
    refine ⟨P.liftQ ((Matrix.toLin' X).codRestrict Q fun y => by simpa using h2 y) ?_, ?_⟩
    · intro y hy
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      simpa using h1 y hy
    · apply Matrix.toLin'.injective
      refine LinearMap.ext fun y => ?_
      rw [Matrix.toLin'_apply, homMat_mulVec]
      simp

theorem det_conj_hom : ∀ (n : ℕ) (f g : Matrix (Fin n) (Fin n) ℂ) (P Q : Submodule ℂ (Fin n → ℂ)) (H : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)), f * g = 1 → ‖f.det‖ = 1 → (∀ y ∈ P, f *ᵥ y ∈ P) → (∀ y ∈ Q, f *ᵥ y ∈ Q) → (∀ X, X ∈ H ↔ (∀ y ∈ P, X *ᵥ y = 0) ∧ ∀ y, X *ᵥ y ∈ Q) → Module.finrank ℂ H = (n - Module.finrank ℂ P) * Module.finrank ℂ Q ∧ ∀ φ : H →ₗ[ℂ] H, (∀ X : H, ((φ X : H) : Matrix (Fin n) (Fin n) ℂ) = f * (X : Matrix (Fin n) (Fin n) ℂ) * g) → ‖LinearMap.det φ‖ = detOn f Q ^ (n - Module.finrank ℂ P) * detOn f P ^ Module.finrank ℂ Q := by
  intro n f g P Q H hfg hdet hP hQ hH
  obtain rfl := range_homMat P Q H hH
  let e := LinearEquiv.ofInjective _ (homMat_injective P Q)
  have hq : Module.finrank ℂ ((Fin n → ℂ) ⧸ P) = n - Module.finrank ℂ P := by
    have := P.finrank_quotient_add_finrank
    rw [Module.finrank_fin_fun] at this
    omega
  refine ⟨?_, fun φ hφ => ?_⟩
  · rw [← e.finrank_eq, Module.finrank_linearMap, hq]
  have hgf : g * f = 1 := mul_eq_one_comm.1 hfg
  have hgP := GlobalTheory.FlagLeviGroup.inv_keeps hgf P hP
  have hP' : ∀ y ∈ P, Matrix.toLin' f y ∈ P := fun y hy => by simpa using hP y hy
  have hQ' : ∀ y ∈ Q, Matrix.toLin' f y ∈ Q := fun y hy => by simpa using hQ y hy
  have hgP' : P ≤ P.comap (Matrix.toLin' g) := fun y hy => by simpa using hgP y hy
  set α := (Matrix.toLin' f).restrict hQ' with hα
  set β := P.mapQ P (Matrix.toLin' g) hgP' with hβ
  have h1 : LinearMap.det (LinearMap.llcomp ℂ _ _ _ α ∘ₗ LinearMap.lcomp ℂ Q β) = LinearMap.det φ := by
    refine det_eq_of_equiv e _ _ fun T => ?_
    apply Subtype.ext
    rw [hφ]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun y => ?_
    simp only [Matrix.toLin'_apply, e, LinearEquiv.ofInjective_apply, ← Matrix.mulVec_mulVec,
      homMat_mulVec]
    simp [hα, hβ, LinearMap.restrict_apply]
  have h2 := LinearMap.det_eq_det_mul_det P (Matrix.toLin' g) hgP'
  have h3 : LinearMap.det ((Matrix.toLin' f).restrict hP') *
      LinearMap.det ((Matrix.toLin' g).restrict hgP') = 1 := by
    rw [← map_mul, ← LinearMap.det_id (A := ℂ) (M := P)]
    congr 1
    refine LinearMap.ext fun y => Subtype.ext ?_
    simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec, hfg]
  have h4 : ‖g.det‖ = 1 := by
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => ‖M.det‖) hfg
    simpa [hdet] using this
  have h5 : LinearMap.det β = LinearMap.det ((Matrix.toLin' f).restrict hP') * g.det := by
    rw [← LinearMap.det_toLin' g, h2, ← mul_assoc, h3, one_mul]
  rw [← h1, LinearMap.det_comp, det_comp_left, det_comp_right, hq, h5, detOn, detOn, dif_pos hP',
    dif_pos hQ']
  simp [h4, hα]

end GlobalTheory.HomConjDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalIntegralLiftOfOrthogonStatement
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stabilizerNilradicalIntegral_lift_of_orthogonal : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), R ≤ perpIn I x R → ∀ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ R, Φ *ᵥ y = 0) → (∀ y ∈ perpIn I x R, Φ *ᵥ y ∈ R) → ∃ Y ∈ nilInt I x R, ∀ y ∈ perpIn I x R, Y *ᵥ y = Φ *ᵥ y := by
  first | exact @GlobalTheory.NilLift.exists_nilInt_lift | exact GlobalTheory.NilLift.exists_nilInt_lift | (intros; apply GlobalTheory.NilLift.exists_nilInt_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSymmInvariantKernelHermitianFrames
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem exists_symm_invariant_kernel : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, P Λ ↔ (S.IsTerm d Λ ∧ S.InFF β (j + 1) βJ d Λ)) → ∃ m : Submodule L.O S.V → Submodule L.O S.V → ℝ, (∀ h ∈ S.St, ∀ x y, P x → P y → m (h • x) (h • y) = m x y) ∧ ∀ x, P x → {y | P y ∧ m x y ≠ 0}.Finite ∧ (∀ y, P y → 0 ≤ m x y ∧ m x y = m y x) ∧ |(∑ᶠ y : {y // P y}, m x y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ ‖∑ᶠ y : {y // P y}, (m x y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk j β βJ d P hP
  have hPe : P = fun Λ => S.IsTerm d Λ ∧ S.InFF β (j + 1) βJ d Λ :=
    funext fun Λ => propext (hP Λ)
  subst hPe
  refine ⟨fun x y => S.kern β (j + 1) βJ d x y, ?_, ?_⟩
  · intro h hh x y hx _
    exact GlobalTheory.T.frameMovesKernel_commonStabilizer_smul_eq L r k S d x hx.1 β (j + 1) βJ y h hh
  · intro x hx
    have base := GlobalTheory.T.hermDoubleCosetMoves_finite_targets_split L r k S j β βJ d x hx.1 hx.2
    refine ⟨?_, ?_, GlobalTheory.T.hermitianDoubleCoset_kernel_row_sum_near_one L r k S hk j β βJ d x hx.1 hx.2,
      GlobalTheory.T.hermitianDoubleCoset_kernel_bound_by_weight L r k S hk j β βJ d x hx.1 hx.2⟩
    · exact base.2.2.1.subset fun y hy => hy.2
    · intro y hy
      exact ⟨base.2.2.2.1 y, GlobalTheory.T.hermDoubleCosetMoveKernel_symm L r k S j β βJ d x hx.1 hx.2 y hy.1 hy.2⟩

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankAndDetOfRealBasisSkewPartStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_and_det_of_real_basis_skew_part : ∀ (n : ℕ) (ε : Fin n → Bool) (N : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ N, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ N) → LinearIndependent ℝ E → (∀ X, (X ∈ N ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → Module.finrank ℂ N = d ∧ ∀ (φ : N →ₗ[ℂ] N) (L : Matrix (Fin d) (Fin d) ℝ), (∀ (k : Fin d) (h : E k ∈ N), ((φ ⟨E k, h⟩ : N) : Matrix (Fin n) (Fin n) ℂ) = ∑ i, L i k • E i) → LinearMap.det φ = ((L.det : ℝ) : ℂ) := by
  first | exact @GlobalTheory.RealFormBasis.finrank_and_det | exact GlobalTheory.RealFormBasis.finrank_and_det | (intros; apply GlobalTheory.RealFormBasis.finrank_and_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramNumberNormalizedInvariance
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.YInv
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.YjInv

variable {k r j : ℕ}

theorem N_ej (hj : j ≤ r) {n : Mat k r} (hn : n ∈ Nset k r) (a : Fin j) :
    n *ᵥ bvec (eI k r (Fin.castLE hj a)) =
      ∑ b : Fin j, n (eI k r (Fin.castLE hj b)) (eI k r (Fin.castLE hj a)) • bvec (eI k r (Fin.castLE hj b)) := by
  rw [N_e hn]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hj) ((Fin.castLE_injective hj).injOn) (by simp) ?_ (by simp)
  intro b _ hb
  have hb' : j ≤ b.val := by
    by_contra h
    exact hb ⟨⟨b.val, by omega⟩, by simp, rfl⟩
  have ha := a.isLt
  rw [hn.2.1 (Fin.castLE hj a) _ (by simp [eI]; omega), if_neg, zero_smul]
  intro h
  have := congrArg Fin.val h
  simp [eI] at this
  omega

theorem N_detj (hj : j ≤ r) {n : Mat k r} (hn : n ∈ Nset k r) :
    (Matrix.of fun b a : Fin j => n (eI k r (Fin.castLE hj b)) (eI k r (Fin.castLE hj a))).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp only [Matrix.of_apply]
    rw [hn.2.1 (Fin.castLE hj a) _ le_rfl, if_pos rfl]
  · intro b a hab
    have hab' : a.val < b.val := hab
    simp only [Matrix.of_apply]
    rw [hn.2.1 (Fin.castLE hj a) (eI k r (Fin.castLE hj b)) hab'.le, if_neg]
    intro h
    have := congrArg Fin.val h
    simp [eI] at this
    omega

theorem Yj_N (hj : j ≤ r) {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (γ : Mat k r)
    {n₁ n₂ : Mat k r} (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (x : Mat k r) :
    Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x) := by
  have h₁' := (nSubgroup k r).2.2 _ h₁
  unfold Yj Dj
  rw [dInv k r z z' hz hz' n₁ (N_sub_S z h₁) n₂ (N_sub_S z' h₂), Ppos_N hz hz' h₁ h₂,
    ← gramProj_comb _ (fun a : Fin j => (n₂ * x)⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) _ (N_detj hj h₁')]
  congr 2
  funext a
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    N_ej hj h₁']
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.of_apply, ← Matrix.mulVec_mulVec]

theorem Yj_K (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) {κ : Mat k r} (hG : κ ∈ GG k r)
    (hκ : κ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) :
    Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x := by
  have h1 : star κ * κ = 1 := Matrix.mem_unitaryGroup_iff'.1 hκ
  have h2 : κ * star κ = 1 := Matrix.mem_unitaryGroup_iff.1 hκ
  have hG' : star κ * Hpk k r * κ = Hpk k r := hG
  have hc : (Hpk k r - 1) * κ = κ * (Hpk k r - 1) := by
    have : κ * Hpk k r = Hpk k r * κ := by
      conv_lhs => rw [← hG', ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.sub_mul, Matrix.mul_sub, this, Matrix.one_mul, Matrix.mul_one]
  unfold Yj
  rw [gramProj_unitary (Ppos k r z z' γ x) (Ppos k r z z' γ (x * κ)) _ κ hκ]
  · congr 2
    funext a
    rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ κ,
      Matrix.mul_nonsing_inv _ (det_unit hG), Matrix.one_mulVec]
  · intro p
    rw [mem_Ppos, mem_Ppos]
    simp only [Matrix.mulVec_mulVec, hc]
    refine and_congr ⟨fun h => ?_, fun h => ?_⟩ Iff.rfl
    · rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    · have := congrArg (star κ *ᵥ ·) h
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [← Matrix.mul_assoc, h1, Matrix.one_mul] at this

theorem yj_invariant : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x) ∧ (∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x)) ∧ ∀ ρ ∈ Rset k r γ, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x := by
  intro k r j hj z z' γ hz hz' hγ x _
  refine ⟨fun κ hκ => Yj_K hj z z' γ x hκ.1 hκ.2, fun n₁ h₁ n₂ h₂ => Yj_N hj hz hz' γ h₁ h₂ x, fun ρ hρ => ?_⟩
  rw [← Yj_N hj hz hz' γ ((nSubgroup k r).2.2 _ hρ.2) hρ.1 x]
  congr 1
  have hm : IsUnit (γ * ρ * γ⁻¹).det := det_unit hρ.2.1
  have e : γ * ρ = γ * ρ * γ⁻¹ * γ := by
    rw [Matrix.mul_assoc (γ * ρ), Matrix.nonsing_inv_mul _ (det_unit hγ), Matrix.mul_one]
  rw [Matrix.mul_assoc]
  conv_lhs => rw [show (γ * ρ * γ⁻¹)⁻¹ * (γ * ρ) = (γ * ρ * γ⁻¹)⁻¹ * (γ * ρ * γ⁻¹ * γ) from by rw [← e]]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hm, Matrix.one_mul]

end GlobalTheory.Amp.YjInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLayerProductMeasureMulProdLocalStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagLayerProductMeasure_mul_prod_local : ∀ (ι : Type) [Fintype ι] (n f a : ℕ) (j : Fin a → ℕ) (s s₁ : Fin a → ℝ) (loc : ι → Fin a → ℝ), (∀ i, s i ^ f = s₁ i ^ f * ∏ v, loc v i) → layerProd n f j s id = layerProd n f j s₁ id * ∏ v, layerProd n 1 j (loc v) id := by
  first | exact @GlobalTheory.FlagMeas.layerProd_mul_prod | exact GlobalTheory.FlagMeas.layerProd_mul_prod | (intros; apply GlobalTheory.FlagMeas.layerProd_mul_prod <;> assumption)
end

