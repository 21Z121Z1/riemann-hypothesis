import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import GroundTheory.GlobalFields.TateThesis.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.Exchange

section Algebra
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem rowE_mul_inl (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : n) (s) :
    ((rowE c p u).val * M) (Sum.inl r) s = M (Sum.inl r) s := by
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem rowE_mul_inr (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : Fin c) (s) :
    ((rowE c p u).val * M) (Sum.inr r) s =
      M (Sum.inr r) s + if r.val + 1 = p then ∑ t, u t * M (Sum.inl t) s else 0 := by
  by_cases h : r.val + 1 = p <;>
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h, add_comm]

theorem mul_rowE_inr (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : Fin c) :
    (M * (rowE c p u).val) r (Sum.inr s) = M r (Sum.inr s) := by
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_rowE_inl (P : Fin c) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : n) :
    (M * (rowE c (P.val + 1) u).val) r (Sum.inl s) = M r (Sum.inl s) + M r (Sum.inr P) * u s := by
  simp [rowE, lowU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Fin.val_inj]

theorem colE_mul_inr (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : Fin c) (s) :
    ((colE c p u).val * M) (Sum.inr r) s = M (Sum.inr r) s := by
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem colE_mul_inl (P : Fin c) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r : n) (s) :
    ((colE c (P.val + 1) u).val * M) (Sum.inl r) s = M (Sum.inl r) s + u r * M (Sum.inr P) s := by
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Fin.val_inj]

theorem mul_colE_inl (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : n) :
    (M * (colE c p u).val) r (Sum.inl s) = M r (Sum.inl s) := by
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_colE_inr (p : ℕ) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : Fin c) :
    (M * (colE c p u).val) r (Sum.inr s) =
      M r (Sum.inr s) + if s.val + 1 = p then ∑ t, M r (Sum.inl t) * u t else 0 := by
  by_cases h : s.val + 1 = p <;>
  simp [colE, upU, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, h, add_comm]

theorem rowE_neg_mul (p : ℕ) (u : n → k) : rowE c p (-u) * rowE c p u = 1 := by
  ext1
  simp only [rowE, lowU, Units.val_mul, fromBlocks_multiply, Units.val_one]
  rw [← fromBlocks_one]
  congr 1 <;> simp
  ext l s; by_cases h : l.val + 1 = p <;> simp [h]

theorem colE_neg_mul (p : ℕ) (u : n → k) : colE c p (-u) * colE c p u = 1 := by
  ext1
  simp only [colE, upU, Units.val_mul, fromBlocks_multiply, Units.val_one]
  rw [← fromBlocks_one]
  congr 1 <;> simp
  ext l s; by_cases h : s.val + 1 = p <;> simp [h]

theorem rowE_mul_embX (p : ℕ) (u : n → k) (g : GL n k) :
    rowE c p u * embX c g = embX c g * rowE c p (g.valᵀ.mulVec u) := by
  ext1
  simp only [rowE, lowU, embX, Units.val_mul, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk,
    fromBlocks_multiply]
  congr 1 <;> simp
  ext l s; by_cases h : l.val + 1 = p <;> simp [h, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.mulVec, mul_comm]

theorem colE_mul_embX (p : ℕ) (u : n → k) (g : GL n k) :
    colE c p u * embX c g = embX c g * colE c p ((g⁻¹).val.mulVec u) := by
  have : colE c p (g.val.mulVec ((g⁻¹).val.mulVec u)) * embX c g = embX c g * colE c p ((g⁻¹).val.mulVec u) := by
    generalize (g⁻¹).val.mulVec u = w
    ext1
    simp only [colE, upU, embX, Units.val_mul, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk,
      fromBlocks_multiply]
    congr 1 <;> simp
    ext l s; by_cases h : s.val + 1 = p <;> simp [h, Matrix.mul_apply, dotProduct, Matrix.mulVec]
  rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this

theorem rowE_mul_mem (P : Fin c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c (P.val + 1 + 1)) :
    ∃ w : n → k, ∀ u : n → k, ∃ h ∈ N k n c (P.val + 1), simpleSum h = simpleSum g ∧
      rowE c (P.val + 1) u * g = h * rowE c (P.val + 1) (u + w) := by
  rw [Model.mem_N_iff] at hg
  have h11 : ∀ r s, g.val (Sum.inl r) (Sum.inl s) = if r = s then 1 else 0 := fun r s => by
    simpa [Matrix.one_apply] using hg (Sum.inl r) (Sum.inl s) le_rfl
  have h12 : ∀ r (s : Fin c), s.val ≤ P.val + 1 → g.val (Sum.inl r) (Sum.inr s) = 0 := fun r s h => by
    simpa using hg (Sum.inl r) (Sum.inr s) (by simpa [lev] using h)
  have h21 : ∀ (r : Fin c) s, P.val < r.val → g.val (Sum.inr r) (Sum.inl s) = 0 := fun r s h => by
    simpa using hg (Sum.inr r) (Sum.inl s) (by simp [lev]; omega)
  have h22 : ∀ (r s : Fin c), s.val ≤ r.val → g.val (Sum.inr r) (Sum.inr s) = if r = s then 1 else 0 :=
    fun r s h => by simpa [Matrix.one_apply] using hg (Sum.inr r) (Sum.inr s) (by simpa [lev] using h)
  refine ⟨fun s => g.val (Sum.inr P) (Sum.inl s), fun u => ⟨rowE c (P.val + 1) u * g *
    rowE c (P.val + 1) (-(u + fun s => g.val (Sum.inr P) (Sum.inl s))), ?_, ?_, ?_⟩⟩
  · rw [Model.mem_N_iff]
    rintro (r | r) (s | s) h <;> simp only [lev, Sum.elim_inl, Sum.elim_inr] at h <;>
      simp only [Units.val_mul, mul_rowE_inl, mul_rowE_inr, rowE_mul_inl, rowE_mul_inr]
    · simp [h11, h12 r P (by omega), Matrix.one_apply]
    · simp [h12 r s (by omega)]
    · by_cases hr : r = P
      · subst hr; simp [h11, h12, h22]; ring
      · have : P.val < r.val := by have := Fin.val_ne_of_ne hr; omega
        simp [h21 r s this, h22 r P this.le, hr, this.ne']
    · by_cases hr : r = P
      · subst hr; simp [h22 r s (by omega), fun t => h12 t s (by omega), Matrix.one_apply]
      · simp [h22 r s (by omega), Fin.val_ne_of_ne hr, Matrix.one_apply]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · simp only [Units.val_mul, mul_rowE_inr, rowE_mul_inr]
      split_ifs with hi
      · simp [fun t => h12 t j (by omega)]
      · simp
    · rfl
  · rw [mul_assoc, rowE_neg_mul, mul_one]

theorem colE_mul_mem (P : Fin c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c P.val) :
    ∃ w : n → k, ∀ u : n → k, ∃ h ∈ N k n c (P.val + 1), simpleSum h = simpleSum g ∧
      colE c (P.val + 1) u * g = h * colE c (P.val + 1) (u + w) := by
  rw [Model.mem_N_iff] at hg
  have h11 : ∀ r s, g.val (Sum.inl r) (Sum.inl s) = if r = s then 1 else 0 := fun r s => by
    simpa [Matrix.one_apply] using hg (Sum.inl r) (Sum.inl s) le_rfl
  have h12 : ∀ r (s : Fin c), s.val < P.val → g.val (Sum.inl r) (Sum.inr s) = 0 := fun r s h => by
    simpa using hg (Sum.inl r) (Sum.inr s) (by simp [lev]; omega)
  have h21 : ∀ (r : Fin c) s, P.val ≤ r.val + 1 → g.val (Sum.inr r) (Sum.inl s) = 0 := fun r s h => by
    simpa using hg (Sum.inr r) (Sum.inl s) (by simpa [lev] using h)
  have h22 : ∀ (r s : Fin c), s.val ≤ r.val → g.val (Sum.inr r) (Sum.inr s) = if r = s then 1 else 0 :=
    fun r s h => by simpa [Matrix.one_apply] using hg (Sum.inr r) (Sum.inr s) (by simpa [lev] using h)
  refine ⟨fun s => g.val (Sum.inl s) (Sum.inr P), fun u => ⟨colE c (P.val + 1) u * g *
    colE c (P.val + 1) (-(u + fun s => g.val (Sum.inl s) (Sum.inr P))), ?_, ?_, ?_⟩⟩
  · rw [Model.mem_N_iff]
    rintro (r | r) (s | s) h <;> simp only [lev, Sum.elim_inl, Sum.elim_inr] at h <;>
      simp only [Units.val_mul, mul_colE_inl, mul_colE_inr, colE_mul_inl, colE_mul_inr]
    · simp [h11, h21 P s (by omega), Matrix.one_apply]
    · by_cases hr : s = P
      · subst hr; simp [h11, h21, h22]; ring
      · have : s.val < P.val := by have := Fin.val_ne_of_ne hr; omega
        simp [h12 r s this, h22 P s this.le, Ne.symm hr, this.ne]
    · simp [h21 r s (by omega)]
    · by_cases hr : s = P
      · subst hr; simp [h22 r s (by omega), fun t => h21 r t (by omega), Matrix.one_apply]
      · simp [h22 r s (by omega), Fin.val_ne_of_ne hr, Matrix.one_apply]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · simp only [Units.val_mul, mul_colE_inr, colE_mul_inr]
      split_ifs with hi
      · simp [fun t => h21 i t (by omega)]
      · simp
    · rfl
  · rw [mul_assoc, colE_neg_mul, mul_one]

end Algebra

section Analysis
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  (ν : Measure k) [ν.IsAddHaarMeasure] {A : Type} [AddCommGroup A] [Module ℂ A]

theorem integrable_of_mem_SB {f : (n → k) → ℂ} (hf : f ∈ SB (n → k)) :
    Integrable f (Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  exact hf.1.continuous.integrable_of_hasCompactSupport hf.2

def avg (T : (n → k) → A →ₗ[ℂ] A) (l : A →ₗ[ℂ] ℂ) (h : ∀ v, (fun u => l (T u v)) ∈ SB (n → k)) :
    A →ₗ[ℂ] ℂ where
  toFun v := ∫ u, l (T u v) ∂(Measure.pi fun _ => ν)
  map_add' v w := by
    simp only [map_add]
    exact integral_add (integrable_of_mem_SB ν (h v)) (integrable_of_mem_SB ν (h w))
  map_smul' a v := by
    simp only [map_smul, RingHom.id_apply]
    exact integral_smul a _

def avg₂ {P : Type} [AddCommGroup P] [Module ℂ P] (T : (n → k) → A →ₗ[ℂ] A) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ)
    (h : ∀ φ v, (fun u => b φ (T u v)) ∈ SB (n → k)) : P →ₗ[ℂ] A →ₗ[ℂ] ℂ where
  toFun φ := avg ν T (b φ) (h φ)
  map_add' φ φ' := by
    ext v
    simp only [avg, map_add, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    exact integral_add (integrable_of_mem_SB ν (h φ v)) (integrable_of_mem_SB ν (h φ' v))
  map_smul' a φ := by
    ext v
    simp only [avg, map_smul, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
    exact integral_smul a _

theorem isNEquiv_integral {ψ : AddChar k Circle} {p q : ℕ} {σ : Representation ℂ (GL (n ⊕ Fin c) k) A}
    {l : A → ℂ} (hl : IsNEquiv ψ p σ l) (E : (n → k) → GL (n ⊕ Fin c) k)
    (hE : ∀ g ∈ N k n c q, ∃ w : n → k, ∀ u : n → k, ∃ h ∈ N k n c p, simpleSum h = simpleSum g ∧
      E u * g = h * E (u + w)) :
    IsNEquiv ψ q σ fun v => ∫ u, l (σ (E u) v) ∂(Measure.pi fun _ => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  intro g hg v
  obtain ⟨w, hw⟩ := hE g hg
  have : ∀ u, l (σ (E u) (σ g v)) = (ψ (simpleSum g) : ℂ) * l (σ (E (u + w)) v) := fun u => by
    obtain ⟨h, hN, hs, he⟩ := hw u
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hl h hN, hs]
  simp only [this]
  rw [integral_const_mul, integral_add_right_eq_self (fun u => l (σ (E u) v)) w]

theorem integral_embX {P : Type} [AddCommGroup P] [Module ℂ P] {π : Representation ℂ (GL n k) P}
    {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} {b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ} (E : (n → k) → GL (n ⊕ Fin c) k)
    (g m : GL n k) (z : ℝ) (φ : P) (hb : ∀ v, b (π g φ) (σ (embX c g) v) = (z : ℂ) * b φ v)
    (hE : ∀ u, E u * embX c g = embX c g * E (m.val.mulVec u)) (v : A) :
    ∫ u, b (π g φ) (σ (E u) (σ (embX c g) v)) ∂(Measure.pi fun _ => ν) =
      ((z * (nabs k (Matrix.GeneralLinearGroup.det m))⁻¹ : ℝ) : ℂ) *
        ∫ u, b φ (σ (E u) v) ∂(Measure.pi fun _ => ν) := by
  have : ∀ u, b (π g φ) (σ (E u) (σ (embX c g) v)) = (z : ℂ) * b φ (σ (E (m.val.mulVec u)) v) := fun u => by
    rw [← Module.End.mul_apply, ← map_mul, hE, map_mul, Module.End.mul_apply, hb]
  simp only [this]
  rw [integral_const_mul, (GlobalTheory.SplitWeil.linear_change_of_variables k n n ν).1 m (fun u => b φ (σ (E u) v))]
  simp [mul_assoc]

end Analysis

theorem exchange_isPos : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ), (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ p σ l → ∃ l' : A →ₗ[ℂ] ℂ, (∀ v, l' v = exUp ν p σ l v) ∧ IsNEquiv ψ (p + 1) σ l') ∧ (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ (p + 1) σ l → ∃ l' : A →ₗ[ℂ] ℂ, (∀ v, l' v = exDown ν p σ l v) ∧ IsNEquiv ψ p σ l') ∧ ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (π : Representation ℂ (GL n k) P) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ), (IsPos ψ p π σ b → ∃ b' : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b' φ v = exUp ν p σ (b φ) v) ∧ IsPos ψ (p + 1) π σ b') ∧ (IsPos ψ (p + 1) π σ b → ∃ b' : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b' φ v = exDown ν p σ (b φ) v) ∧ IsPos ψ p π σ b') := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ψ hψ hψ1 ν _ A _ _ σ hσ
  have H := GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have up : ∀ l : A → ℂ, IsNEquiv ψ p σ l → IsNEquiv ψ (p + 1) σ (exUp ν p σ l) := fun l hl => by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    exact isNEquiv_integral ν hl _ fun g hg => rowE_mul_mem ⟨q, by omega⟩ hg
  have down : ∀ l : A → ℂ, IsNEquiv ψ (p + 1) σ l → IsNEquiv ψ p σ (exDown ν p σ l) := fun l hl =>
    isNEquiv_integral ν hl _ fun g hg => colE_mul_mem ⟨p, hpc⟩ hg
  refine ⟨fun l hl => ⟨avg ν (fun u => σ (rowE c p u)) l fun v => ((H l v).1 hl).1, fun v => rfl, up l hl⟩,
    fun l hl => ⟨avg ν (fun u => σ (colE c (p + 1) u)) l fun v => ((H l v).2 hl).1, fun v => rfl, down l hl⟩,
    fun P _ _ π b => ⟨fun hb => ⟨avg₂ ν (fun u => σ (rowE c p u)) b fun φ v => ((H (b φ) v).1 (hb.1 φ)).1,
      fun φ v => rfl, fun φ => up _ (hb.1 φ), fun g φ v => ?_⟩,
    fun hb => ⟨avg₂ ν (fun u => σ (colE c (p + 1) u)) b fun φ v => ((H (b φ) v).2 (hb.1 φ)).1,
      fun φ v => rfl, fun φ => down _ (hb.1 φ), fun g φ v => ?_⟩⟩⟩
  · let m : GL n k := ⟨g.valᵀ, (g⁻¹).valᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
      by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
    have hm : Matrix.GeneralLinearGroup.det m = Matrix.GeneralLinearGroup.det g := by
      ext; simp [m]
    refine (integral_embX ν (rowE c p) g m _ φ (hb.2 g φ) (fun u => rowE_mul_embX p u g) v).trans ?_
    rw [hm, ← Real.rpow_neg_one, ← Real.rpow_add (nabs_pos k _)]
    congr 3
    push_cast; ring
  · refine (integral_embX ν (colE c (p + 1)) g g⁻¹ _ φ (hb.2 g φ) (fun u => colE_mul_embX (p + 1) u g) v).trans ?_
    have hm : (nabs k (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ = nabs k (Matrix.GeneralLinearGroup.det g) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← nabs_mul, ← map_mul, inv_mul_cancel, map_one, nabs_one]
    rw [hm, ← Real.rpow_add_one (nabs_pos k _).ne']
    congr 3
    push_cast; ring

end GlobalTheory.RootEx.Exchange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwiningSymplecticAndGroupLaw
section
noncomputable section

open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil.Intertw

variable {l : Type} [Fintype l]

theorem sympl_smul_left (r : ℝ) (w w' : l ⊕ l → ℝ) : sympl (r • w) w' = r * sympl w w' := by
  simp only [sympl, pPart_smul, qPart_smul, real_inner_smul_left]
  ring

theorem sympl_smul_right (r : ℝ) (w w' : l ⊕ l → ℝ) : sympl w (r • w') = r * sympl w w' := by
  simp only [sympl, pPart_smul, qPart_smul, real_inner_smul_right]
  ring

theorem sympl_antisymm (w w' : l ⊕ l → ℝ) : sympl w w' = -sympl w' w := by
  simp only [sympl, real_inner_comm (pPart w) (qPart w'), real_inner_comm (qPart w) (pPart w')]
  ring

theorem sympl_sub_left (u u' z : l ⊕ l → ℝ) : sympl (u - u') z = sympl u z - sympl u' z := by
  have h1 : pPart (u - u') = pPart u - pPart u' := rfl
  have h2 : qPart (u - u') = qPart u - qPart u' := rfl
  simp only [sympl, h1, h2, inner_sub_left]
  ring

theorem eq_zero_of_exp_eq_one (D : ℝ) (h : ∀ r : ℝ, exp (((π * (r * D) : ℝ) : ℂ) * I) = 1) : D = 0 := by
  by_contra hD
  have := h D⁻¹
  rw [inv_mul_cancel₀ hD, mul_one, Complex.exp_pi_mul_I] at this
  norm_num at this

theorem rhoFun_gaussian_ne_zero (w : l ⊕ l → ℝ) :
    rhoFun w ⇑(GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)) (-pPart w) ≠ 0 := by
  simp only [rhoFun, neg_add_cancel, GroundTheory.Global.gaussianSchwartz_apply]
  refine mul_ne_zero ?_ ?_
  · intro h
    have := norm_phase w (-pPart w)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · simp

theorem coe_smul_sch (c : ℂ) (f : Sch l) : ⇑(c • f) = c • ⇑f := by
  funext x
  simp

theorem eq_of_smul_eq_smul {c c' : ℂ} {F : EuclideanSpace ℝ l → ℂ} {x : EuclideanSpace ℝ l} (hx : F x ≠ 0)
    (h : c • F = c' • F) : c = c' := by
  have := congrFun h x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx this

theorem eq_of_rhoFun_eq {u u' : l ⊕ l → ℝ} (h : ∀ g : Sch l, rhoFun u ⇑g = rhoFun u' ⇑g) : u = u' := by
  classical
  set g0 := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hg0
  have key : ∀ z : l ⊕ l → ℝ, exp (((π * (2 * sympl (u - u') z) : ℝ) : ℂ) * I) = 1 := by
    intro z
    obtain ⟨g1, hg1⟩ := exists_schwartz_rhoFun l z g0
    have h1 := h g1
    rw [hg1, rhoFun_rhoFun, rhoFun_rhoFun] at h1
    have h2 := congrArg (rhoFun z) (h g0)
    rw [rhoFun_rhoFun, rhoFun_rhoFun, add_comm z u, add_comm z u', sympl_antisymm z u, sympl_antisymm z u'] at h2
    set a := sympl u z
    set b := sympl u' z
    set F := rhoFun (u + z) ⇑g0
    set G := rhoFun (u' + z) ⇑g0
    have h3 : (exp (((π * -b : ℝ) : ℂ) * I) * exp (((π * a : ℝ) : ℂ) * I)) • F =
        (exp (((π * b : ℝ) : ℂ) * I) * exp (((π * -a : ℝ) : ℂ) * I)) • F := by
      rw [mul_smul, h1, smul_smul, mul_comm, ← smul_smul, ← h2, smul_smul, mul_smul]
    have h4 := eq_of_smul_eq_smul (rhoFun_gaussian_ne_zero (u + z)) h3
    rw [← Complex.exp_add, ← Complex.exp_add] at h4
    rw [sympl_sub_left]
    have e : ((π * (2 * (a - b)) : ℝ) : ℂ) * I =
        (((π * -b : ℝ) : ℂ) * I + ((π * a : ℝ) : ℂ) * I) - (((π * b : ℝ) : ℂ) * I + ((π * -a : ℝ) : ℂ) * I) := by
      push_cast
      ring
    rw [e, Complex.exp_sub, h4, div_self (exp_ne_zero _)]
  have hz : ∀ z, sympl (u - u') z = 0 := by
    intro z
    have := eq_zero_of_exp_eq_one (2 * sympl (u - u') z) fun r => by
      have := key (r • z)
      rwa [sympl_smul_right, show 2 * (r * sympl (u - u') z) = r * (2 * sympl (u - u') z) by ring] at this
    linarith
  have hJ : Matrix.J l ℝ *ᵥ (u - u') = 0 := by
    ext b
    have := hz (Pi.single b 1)
    rw [sympl_antisymm, sympl_single] at this
    simpa using this
  have hd : u - u' = 0 := by
    have : u - u' = -((Matrix.J l ℝ * Matrix.J l ℝ) *ᵥ (u - u')) := by
      rw [Matrix.J_squared, Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]
    rw [this, ← Matrix.mulVec_mulVec, hJ, Matrix.mulVec_zero, neg_zero]
  exact sub_eq_zero.mp hd

end GlobalTheory.RealWeil.Intertw

namespace GlobalTheory.RealWeil

open Intertw in

theorem intertwining_symplectic_and_group_law : ∀ (l : Type) [Fintype l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → Sch l →ₗ[ℂ] Sch l),
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (A t w) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) →
    (∀ t w w', sympl (A t w) (A t w') = sympl w w') ∧ (∀ s t w, A (s + t) w = A s (A t w)) ∧ ∀ w, A 0 w = w := by
  intro l _ A T hadd h0 hI _
  have hsurj : ∀ t (h : Sch l), T t (T (-t) h) = h := fun t h => by rw [← hadd, add_neg_cancel, h0]
  refine ⟨fun t w w' => ?_, fun s t w => ?_, fun w => ?_⟩
  · have hE : ∀ v v' : l ⊕ l → ℝ, exp (((π * sympl (A t v) (A t v') : ℝ) : ℂ) * I) =
        exp (((π * sympl v v' : ℝ) : ℂ) * I) := by
      intro v v'
      set g0 := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hg0
      obtain ⟨f₁, hf₁⟩ := exists_schwartz_rhoFun l v' (T (-t) g0)
      obtain ⟨f₂, hf₂⟩ := exists_schwartz_rhoFun l v f₁
      obtain ⟨f₃, hf₃⟩ := exists_schwartz_rhoFun l (v + v') (T (-t) g0)
      have e2 : f₂ = exp (((π * sympl v v' : ℝ) : ℂ) * I) • f₃ := by
        apply DFunLike.coe_injective
        rw [coe_smul_sch, hf₂, hf₁, hf₃, rhoFun_rhoFun]
      have k1 := hI t v' (T (-t) g0) f₁ hf₁
      have k2 := hI t v f₁ f₂ hf₂
      have k3 := hI t (v + v') (T (-t) g0) f₃ hf₃
      rw [hsurj] at k1 k3
      rw [k1, rhoFun_rhoFun, e2, map_smul, coe_smul_sch, k3, map_add] at k2
      exact (eq_of_smul_eq_smul (rhoFun_gaussian_ne_zero (A t v + A t v')) k2).symm
    apply sub_eq_zero.mp
    refine eq_zero_of_exp_eq_one _ fun r => ?_
    have := hE (r • w) w'
    rw [map_smul, sympl_smul_left, sympl_smul_left] at this
    rw [show ((π * (r * (sympl (A t w) (A t w') - sympl w w')) : ℝ) : ℂ) * I =
        ((π * (r * sympl (A t w) (A t w')) : ℝ) : ℂ) * I - ((π * (r * sympl w w') : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_sub, this, div_self (exp_ne_zero _)]
  · apply Intertw.eq_of_rhoFun_eq
    intro g
    obtain ⟨f₁, hf₁⟩ := exists_schwartz_rhoFun l w (T (-(s + t)) g)
    have h1 := hI (s + t) w _ f₁ hf₁
    have h2 := hI t w _ f₁ hf₁
    have h3 := hI s (A t w) _ _ h2
    rw [hsurj] at h1
    rw [← hadd, ← hadd, hsurj, h1] at h3
    exact h3
  · apply Intertw.eq_of_rhoFun_eq
    intro g
    obtain ⟨f₁, hf₁⟩ := exists_schwartz_rhoFun l w g
    have h := hI 0 w g f₁ hf₁
    rw [h0, h0] at h
    rw [← h, hf₁]

end GlobalTheory.RealWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair
section
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LatPair
open SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}

theorem ite_mem_SB {X : Type*} [TopologicalSpace X] {p : X → Prop} [DecidablePred p] (h : IsClopen {x | p x})
    (hc : IsCompact {x | p x}) : (fun x => if p x then (1 : ℂ) else 0) ∈ SB X := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro' hc h.1 fun x hx => if_neg hx⟩
  by_cases hx : p x
  · exact ⟨_, h.2, hx, fun y hy => (if_pos hy).trans (if_pos hx).symm⟩
  · exact ⟨_, h.compl.2, hx, fun y hy => (if_neg hy).trans (if_neg hx).symm⟩

variable [Fintype n] [Fintype n']

theorem isClopen_lattice (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : IsClopen (L : Set (n → k)) := by
  classical
  haveI := t2Space k
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have h : ((g • stdLat k n : Submodule 𝒪[k] (n → k)) : Set (n → k)) =
      ⋂ i, (fun x => ((g⁻¹ : GL n k).val *ᵥ x) i) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [SetLike.mem_coe, mem_smul_iff, mem_stdLat, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [h]
  refine isClopen_iInter_of_finite fun i => IsClopen.preimage ⟨(isCompact_int k).isClosed, isOpen_int k⟩ ?_
  exact (continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)

omit [Fintype n] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem maps_stdLat_iff {x : Matrix n n' k} :
    (∀ y ∈ stdLat k n', x *ᵥ y ∈ stdLat k n) ↔ ∀ i j, x i j ∈ 𝒪[k] := by
  classical
  simp only [mem_stdLat]
  refine ⟨fun h i j => ?_, fun h y hy i => sum_mem fun j _ => mul_mem (h i j) (hy j)⟩
  have := h (Pi.single j 1) (fun l => ?_) i
  · simpa using this
  · rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]

theorem isClopen_isCompact_maps (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsLattice k]
    [L.IsLattice k] : IsClopen {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} ∧
      IsCompact {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} := by
  classical
  haveI := t2Space k
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n') S
  obtain ⟨h, rfl⟩ := exists_smul_lat (stdLat k n) L
  let K : Set (Matrix n n' k) := Set.univ.pi fun _ => Set.univ.pi fun _ => (𝒪[k] : Set k)
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k
  have hKo : IsOpen K :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k
  have e : {x : Matrix n n' k | ∀ y ∈ g • stdLat k n', x *ᵥ y ∈ h • stdLat k n} = sideMul g h ⁻¹' K := by
    ext x
    have h1 : sideMul g h x ∈ K ↔ ∀ i j, ((h⁻¹ : GL n k).val * x * g.val) i j ∈ 𝒪[k] :=
      ⟨fun H i j => H i trivial j trivial, fun H i _ j _ => H i j⟩
    rw [Set.mem_preimage, h1, ← maps_stdLat_iff, Set.mem_setOf_eq]
    simp only [mem_smul_iff, ← mulVec_mulVec]
    refine ⟨fun H y hy => H (g • y) (by simpa using hy), fun H y hy => ?_⟩
    have := H _ hy
    rwa [show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this
  rw [e]
  exact ⟨IsClopen.preimage ⟨hKc.isClosed, hKo⟩ (sideMul g h).continuous, (sideMul g h).isCompact_preimage.2 hKc⟩

theorem latInd_mem_SB (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsLattice k] [L.IsLattice k] :
    latInd S L ∈ SB (Matrix n n' k) := by
  classical
  exact ite_mem_SB (isClopen_isCompact_maps S L).1 (isClopen_isCompact_maps S L).2

theorem isClopen_isCompact_mapsPair (P : Pair k n') (Q : Pair k n) :
    IsClopen {x : Matrix n n' k | Maps P Q x} ∧ IsCompact {x : Matrix n n' k | Maps P Q x} := by
  have e : {x : Matrix n n' k | Maps P Q x} = {x : Matrix n n' k | ∀ y ∈ P.ker, x *ᵥ y ∈ Q.ker} ∩
      (fun x : Matrix n n' k => x *ᵥ P.vec - Q.vec) ⁻¹' (Q.ker : Set (n → k)) := by
    ext x
    exact maps_iff_glue P.hasVal_vec Q.hasVal_vec
  have h2 := (isClopen_lattice Q.ker).preimage (f := fun x : Matrix n n' k => x *ᵥ P.vec - Q.vec)
    ((continuous_id.matrix_mulVec continuous_const).sub continuous_const)
  obtain ⟨h1, hc⟩ := isClopen_isCompact_maps P.ker Q.ker
  rw [e]
  exact ⟨h1.inter h2, hc.inter_right h2.1⟩

theorem phiOne_mem_SB (P : Pair k n') (Q : Pair k n) : phiOne P Q ∈ SB (Matrix n n' k) := by
  classical
  exact ite_mem_SB (isClopen_isCompact_mapsPair P Q).1 (isClopen_isCompact_mapsPair P Q).2

end GlobalTheory.LatPair
end
end

