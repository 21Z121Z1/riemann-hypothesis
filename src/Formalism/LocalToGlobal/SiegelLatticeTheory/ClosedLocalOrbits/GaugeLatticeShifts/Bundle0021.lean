import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0018
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObjInhab

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormSqLine
section
noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL

theorem normSq_line (γ δ : ℂ) (t : ℝ) :
    Complex.normSq (γ + (t : ℂ) * δ) = Complex.normSq γ + t ^ 2 * Complex.normSq δ + 2 * t * (γ * conj δ).re := by
  rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal, map_mul, Complex.conj_ofReal,
    show γ * ((t : ℂ) * conj δ) = (t : ℂ) * (γ * conj δ) by ring, Complex.re_ofReal_mul]
  ring

section Pos

variable {n r k : ℕ} (ε : Fin n → Bool)

def hJL (x : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun v := hJ ε x v
  map_add' v w := UnitaryIsometries.hJ_add_right ε x v w
  map_smul' a v := by simp [UnitaryIsometries.hJ_smul_right]

theorem hJ_self_pos {x : Fin n → ℂ} (hx : ∀ i, ε i = false → x i = 0) (hx0 : x ≠ 0) : 0 < (hJ ε x x).re := by
  have h : hJ ε x x = ∑ i, ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
    unfold hJ Jm
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ε i = true
    · simp only [hi, if_true, one_mul]
      rw [mul_comm]
      push_cast
      exact Complex.mul_conj' (x i)
    · have : x i = 0 := hx i (by simpa using hi)
      simp [this]
  rw [h, Complex.re_sum]
  simp only [Complex.ofReal_re]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hx0 (funext h')
  exact Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩

theorem exists_pos {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ} (hdim : n = 2 * r + 1 + k) (hk : 1 ≤ k)
    (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) (hez : ∀ a, hJ ε (e a) z = 0)
    (hzz : hJ ε z z = -(T : ℂ)) (hT : 0 < T) :
    ∃ p, (∀ a, hJ ε (e a) p = 0) ∧ hJ ε z p = 0 ∧ 0 < (hJ ε p p).re := by
  set L : (Fin n → ℂ) →ₗ[ℂ] (Fin r → ℂ) := LinearMap.pi fun a => hJL ε (e a) with hL
  set Q : (Fin n → ℂ) →ₗ[ℂ] ({i // ε i = false} → ℂ) := LinearMap.pi fun i => LinearMap.proj i.1 with hQ
  have hcard : Fintype.card {i // ε i = false} = r + 1 := by
    rw [Fintype.card_subtype]; exact hsig
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 := LinearMap.finrank_range_add_finrank_ker Q
  have h1r : Module.finrank ℂ (LinearMap.range L) ≤ r := by
    have := Submodule.finrank_le (LinearMap.range L)
    simpa using this
  have h2r : Module.finrank ℂ (LinearMap.range Q) ≤ r + 1 := by
    have := Submodule.finrank_le (LinearMap.range Q)
    simpa [hcard] using this
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker L) (LinearMap.ker Q)
  have h4 : Module.finrank ℂ ↥(LinearMap.ker L ⊔ LinearMap.ker Q) ≤ n := by
    have := Submodule.finrank_le (LinearMap.ker L ⊔ LinearMap.ker Q)
    simpa using this
  simp only [Module.finrank_fin_fun] at h1 h2
  have h5 : LinearMap.ker L ⊓ LinearMap.ker Q ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h3
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h5
  have hxL : ∀ a, hJ ε (e a) x = 0 := fun a => congrFun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).1) a
  have hxQ : ∀ i, ε i = false → x i = 0 := fun i hi =>
    congrFun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).2) ⟨i, hi⟩
  have hxx := hJ_self_pos ε hxQ hx0
  have hTne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT.ne'
  set c : ℂ := hJ ε z x / hJ ε z z with hc
  refine ⟨x - c • z, fun a => ?_, ?_, ?_⟩
  · rw [UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_smul_right, hxL a, hez a, mul_zero, sub_zero]
  · rw [UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_smul_right, hc, hzz]
    field_simp
    ring
  · have hzp : hJ ε z (x - c • z) = 0 := by
      rw [UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_smul_right, hc, hzz]
      field_simp
      ring
    rw [UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_smul_left, hzp, mul_zero, sub_zero, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_smul_right,
      UnitaryIsometries.hJ_conj ε x z, hc, hzz]
    have e1 : hJ ε z x / -(T : ℂ) * conj (hJ ε z x) = ((-(Complex.normSq (hJ ε z x) / T) : ℝ) : ℂ) := by
      rw [div_mul_eq_mul_div, Complex.mul_conj]
      push_cast
      ring
    rw [e1, Complex.sub_re, Complex.ofReal_re]
    have : 0 ≤ Complex.normSq (hJ ε z x) / T := div_nonneg (Complex.normSq_nonneg _) hT.le
    linarith

theorem exists_rho {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' : ℝ} (hdim : n = 2 * r + 1 + k)
    (hk : 1 ≤ k) (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) (hez : ∀ a, hJ ε (e a) z = 0)
    (hzz : hJ ε z z = -(T : ℂ)) (hT : 0 < T) (hT' : 0 < T') :
    ∃ ρ : Matrix (Fin n) (Fin n) ℂ, UnitaryIsometries.IsIsom ε ρ ∧ (∀ a, ρ *ᵥ e a = e a) ∧
      Complex.normSq (hJ ε z (ρ *ᵥ z')) ≠ T * T' := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  by_cases hγ : hJ ε z z' = 0
  · refine ⟨1, UnitaryIsometries.isIsom_one ε, fun a => one_mulVec _, ?_⟩
    rw [one_mulVec, hγ, map_zero]
    exact hTT.ne
  obtain ⟨p, hpe, hpz, hpp⟩ := exists_pos ε hdim hk hsig hez hzz hT
  set π := (hJ ε p p).re with hπ
  have hpR : hJ ε p p = (π : ℂ) := (Complex.conj_eq_iff_re.1 (UnitaryIsometries.hJ_self_conj ε p)).symm
  set s := Real.sqrt (T / π) with hs
  have hs2 : s * s * π = T := by
    rw [hs, Real.mul_self_sqrt (div_nonneg hT.le hpp.le)]
    field_simp
  set p1 : Fin n → ℂ := (s : ℂ) • p with hp1
  have hp1p1 : hJ ε p1 p1 = T := by
    rw [hp1, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, hpR, Complex.conj_ofReal]
    exact_mod_cast (by rw [← hs2]; ring : s * (s * π) = T)
  have hzp1 : hJ ε z p1 = 0 := by rw [hp1, UnitaryIsometries.hJ_smul_right, hpz, mul_zero]
  have hp1z : hJ ε p1 z = 0 := by rw [UnitaryIsometries.hJ_conj, hzp1, map_zero]
  have hep1 : ∀ a, hJ ε (e a) p1 = 0 := fun a => by rw [hp1, UnitaryIsometries.hJ_smul_right, hpe a, mul_zero]

  obtain ⟨u, huu, heu, hzu, huz'⟩ : ∃ u : Fin n → ℂ, hJ ε u u = 0 ∧ (∀ a, hJ ε (e a) u = 0) ∧
      hJ ε z u = -(T : ℂ) ∧ hJ ε u z' ≠ 0 := by
    have hiso : ∀ t : ℂ, t * conj t = 1 → hJ ε (z + t • p1) (z + t • p1) = 0 := by
      intro t ht
      simp only [UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, hzz, hzp1, hp1z,
        hp1p1]
      linear_combination (T : ℂ) * ht
    by_cases hplus : hJ ε (z + (1 : ℂ) • p1) z' ≠ 0
    · refine ⟨z + (1 : ℂ) • p1, hiso 1 (by simp), fun a => ?_, ?_, hplus⟩
      · rw [UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, hez a, hep1 a]; ring
      · rw [UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, hzz, hzp1]; ring
    · refine ⟨z + (-1 : ℂ) • p1, hiso (-1) (by simp), fun a => ?_, ?_, ?_⟩
      · rw [UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, hez a, hep1 a]; ring
      · rw [UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, hzz, hzp1]; ring
      · push_neg at hplus
        intro hminus
        apply hγ
        rw [UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_smul_left] at hplus hminus
        simp only [map_one, map_neg, one_mul, neg_mul] at hplus hminus
        linear_combination (hplus + hminus) / 2
  have hue : ∀ a, hJ ε u (e a) = 0 := fun a => by rw [UnitaryIsometries.hJ_conj, heu a, map_zero]
  set δ : ℂ := Complex.I * hJ ε u z' * T with hδ
  have hδ0 : δ ≠ 0 := mul_ne_zero (mul_ne_zero Complex.I_ne_zero huz') (Complex.ofReal_ne_zero.2 hT.ne')
  have hval : ∀ t : ℝ, hJ ε z (UnitaryIsometries.tv ε u (Complex.I * t) *ᵥ z') = hJ ε z z' + (t : ℂ) * δ := by
    intro t
    rw [UnitaryIsometries.tv_apply, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_smul_right, hzu, hδ]
    ring
  have hsq : ∀ t : ℝ, Complex.normSq (hJ ε z z' + (t : ℂ) * δ) =
      Complex.normSq (hJ ε z z') + t ^ 2 * Complex.normSq δ + 2 * t * (hJ ε z z' * conj δ).re :=
    fun t => normSq_line _ _ t
  have hex : ∃ t : ℝ, Complex.normSq (hJ ε z z' + (t : ℂ) * δ) ≠ T * T' := by
    by_contra hall
    push_neg at hall
    have e0 := hall 0
    have e1 := hall 1
    have e2 := hall 2
    rw [hsq] at e0 e1 e2
    have : Complex.normSq δ = 0 := by nlinarith
    exact hδ0 (Complex.normSq_eq_zero.1 this)
  obtain ⟨t, ht⟩ := hex
  refine ⟨UnitaryIsometries.tv ε u (Complex.I * t), UnitaryIsometries.tv_isIsom ε u ?_, fun a => UnitaryIsometries.tv_fix ε u _ (hue a), ?_⟩
  · rw [huu, mul_zero, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  · rw [hval]
    exact ht

end Pos

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def WittGram : Prop :=
  ∀ (n m : ℕ) (ε : Fin n → Bool) (x y : Fin m → Fin n → ℂ),
    (∀ i j, hJ ε (x i) (x j) = hJ ε (y i) (y j)) →
    (Matrix.of fun i j => hJ ε (x i) (x j)).det ≠ 0 → ∃ g : Formalism.REAL.UJ ε, ∀ i, uMat g *ᵥ x i = y i

section Pure

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_smul_l (a : ℂ) (x y : Fin n → ℂ) : hJ ε (a • x) y = conj a * hJ ε x y := by
  unfold hJ
  rw [star_smul, smul_dotProduct, smul_eq_mul]
  rfl

theorem hJ_smul_r (a : ℂ) (x y : Fin n → ℂ) : hJ ε x (a • y) = a * hJ ε x y := by
  unfold hJ
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_add_l (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  unfold hJ
  rw [star_add, add_dotProduct]

theorem hJ_add_r (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  unfold hJ
  rw [mulVec_add, dotProduct_add]

theorem hJ_cj (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) :=
  Formalism.L2.SG.PoincareInHH.Cut.hJ_conj ε x y

theorem hJ_zero_of_cj {x y : Fin n → ℂ} (h : hJ ε y x = 0) : hJ ε x y = 0 := by
  rw [hJ_cj, h, map_zero]

theorem witt_idx (W : WittGram) {ι : Type} [Fintype ι] [DecidableEq ι] (x y : ι → Fin n → ℂ)
    (hG : ∀ i j, hJ ε (x i) (x j) = hJ ε (y i) (y j))
    (hnd : (Matrix.of fun i j => hJ ε (x i) (x j)).det ≠ 0) :
    ∃ g : Formalism.REAL.UJ ε, ∀ i, uMat g *ᵥ x i = y i := by
  let e := Fintype.equivFin ι
  have hM : (Matrix.of fun i j => hJ ε ((x ∘ e.symm) i) ((x ∘ e.symm) j)) =
      Matrix.reindex e e (Matrix.of fun i j => hJ ε (x i) (x j)) := by
    ext i j; rfl
  obtain ⟨g, hg⟩ := W n (Fintype.card ι) ε (x ∘ e.symm) (y ∘ e.symm) (fun i j => hG _ _)
    (by rw [hM, Matrix.det_reindex_self]; exact hnd)
  exact ⟨g, fun i => by simpa using hg (e i)⟩

def tup {r : ℕ} (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : (Fin r ⊕ Fin r) ⊕ Unit → Fin n → ℂ
  | .inl (.inl a) => e a
  | .inl (.inr a) => f a
  | .inr _ => z

theorem normSq_last_sub_pos_of_Gv_diagonal_pos {r : ℕ} (T T' : ℝ) (c : Fin (r + 1) → ℂ) (hG : 0 < Gv T T' (Matrix.diagonal c)) :
    0 < ‖c (Fin.last r)‖ ^ 2 - T * T' := by
  have h1 := Dl_diagonal c (r + 1) le_rfl
  have h2 := Dl_diagonal c r (Nat.le_succ r)
  rw [Fin.prod_univ_castSucc] at h1
  set P := ∏ i : Fin r, c (Fin.castSucc i)
  have e1 : (∏ i : Fin r, c (Fin.castLE le_rfl (Fin.castSucc i))) = P :=
    Finset.prod_congr rfl fun i _ => by congr 1
  have e2 : (∏ i : Fin r, c (Fin.castLE (Nat.le_succ r) i)) = P :=
    Finset.prod_congr rfl fun i _ => by congr 1
  have e3 : Fin.castLE (le_refl (r + 1)) (Fin.last r) = Fin.last r := Fin.ext rfl
  rw [e1, e3] at h1
  rw [e2] at h2
  unfold Gv at hG
  rw [h1, h2, norm_mul, mul_pow] at hG
  by_contra hn
  push Not at hn
  have hP : 0 ≤ ‖P‖ ^ 2 := sq_nonneg _
  nlinarith

theorem real_loc (W : WittGram) {r : ℕ} (e f : Fin r → Fin n → ℂ) (z z' w : Fin n → ℂ) (T T' sc : ℝ)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (hez' : ∀ a, hJ ε (e a) z' = 0) (hfz' : ∀ a, hJ ε (f a) z' = 0)
    (hzz : hJ ε z z = -(T : ℂ)) (hz'z' : hJ ε z' z' = -(T' : ℂ))
    (hew : ∀ a, hJ ε (e a) w = 0) (hfw : ∀ a, hJ ε (f a) w = 0) (hzw : hJ ε z w = 0)
    (hww : hJ ε w w = 1) (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc)
    (c : Fin (r + 1) → ℂ) (hc : ∀ l, c l ≠ 0) (hG : 0 < Gv T T' (Matrix.diagonal c)) :
    ∃ g : Formalism.REAL.UJ ε, Zhat ε (famSc sc e z) (famSc sc e z') (uMat g) = Matrix.diagonal c := by
  have hsc0 : (sc : ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hT'0 : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  have hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0 := fun a b => by
    rw [hJ_cj, hef]; split_ifs with h1 h2 h2 <;> simp_all
  have hze : ∀ a, hJ ε z (e a) = 0 := fun a => hJ_zero_of_cj ε (hez a)
  have hzf : ∀ a, hJ ε z (f a) = 0 := fun a => hJ_zero_of_cj ε (hfz a)
  have hz'e : ∀ a, hJ ε z' (e a) = 0 := fun a => hJ_zero_of_cj ε (hez' a)
  have hz'f : ∀ a, hJ ε z' (f a) = 0 := fun a => hJ_zero_of_cj ε (hfz' a)
  have hwe : ∀ a, hJ ε w (e a) = 0 := fun a => hJ_zero_of_cj ε (hew a)
  have hwf : ∀ a, hJ ε w (f a) = 0 := fun a => hJ_zero_of_cj ε (hfw a)
  have hwz : hJ ε w z = 0 := hJ_zero_of_cj ε hzw
  set sf : Fin r → ℂ := fun b => ((sc : ℂ) ^ (r - b.1))⁻¹ with hsf
  have hsf0 : ∀ b, sf b ≠ 0 := fun b => inv_ne_zero (pow_ne_zero _ hsc0)
  have hsfc : ∀ b, conj (sf b) = sf b := fun b => by
    simp only [hsf, map_inv₀, map_pow, Complex.conj_ofReal]
  set lam : Fin r → ℂ := fun b => c (Fin.castSucc b) / (sf b * sf b) with hlam
  have hlam0 : ∀ b, lam b ≠ 0 := fun b => div_ne_zero (hc _) (mul_ne_zero (hsf0 b) (hsf0 b))
  have hclam0 : ∀ b, conj (lam b) ≠ 0 := fun b => (map_ne_zero _).2 (hlam0 b)
  set cl := c (Fin.last r) with hcl
  have hgap := normSq_last_sub_pos_of_Gv_diagonal_pos T T' c hG
  set q : ℝ := ‖cl‖ ^ 2 / T - T' with hq
  have hq0 : 0 ≤ q := by
    rw [hq, div_sub' hT.ne']
    exact div_nonneg (by nlinarith) hT.le
  set α : ℂ := -cl / T with hα
  set β : ℂ := ((Real.sqrt q : ℝ) : ℂ) with hβ
  have hββ : conj β * β = (q : ℂ) := by
    rw [hβ, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hq0]
  have hαα : conj α * α * (-(T : ℂ)) + (q : ℂ) = -(T' : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, hα, Complex.normSq_div, Complex.normSq_neg,
      Complex.normSq_ofReal, Complex.normSq_eq_norm_sq, hq]
    push_cast
    field_simp
    ring
  let x := tup e f z'
  let y := tup (fun b => lam b • f b) (fun b => (conj (lam b))⁻¹ • e b) (α • z + β • w)
  have hGram : ∀ i j, hJ ε (x i) (x j) = hJ ε (y i) (y j) := by
    intro i j
    rcases i with (a | a) | ⟨⟩ <;> rcases j with (b | b) | ⟨⟩ <;>
      simp only [x, y, tup, hJ_smul_l, hJ_smul_r, hJ_add_l, hJ_add_r, hee, hff, hef, hfe, hez, hfz, hez', hfz',
        hze, hzf, hz'e, hz'f, hew, hfw, hzw, hwe, hwf, hwz, hww, hzz, hz'z', mul_zero, add_zero,
        zero_add, mul_one]
    · split_ifs with h
      · subst h
        rw [mul_one, inv_mul_cancel₀ (hclam0 a)]
      · simp
    · split_ifs with h
      · subst h
        simp only [map_inv₀, Complex.conj_conj, mul_one]
        exact (mul_inv_cancel₀ (hlam0 a)).symm
      · simp
    · rw [← hαα, ← hββ]
      ring
  have hnd : (Matrix.of fun i j => hJ ε (x i) (x j)).det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hv0
    have hA : ∀ a, v (.inl (.inr a)) = 0 := fun a => by
      have h1 := congrFun hv (.inl (.inl a))
      simpa [mulVec, dotProduct, Fintype.sum_sum_type, x, tup, hee, hef, hez'] using h1
    have hB : ∀ a, v (.inl (.inl a)) = 0 := fun a => by
      have h1 := congrFun hv (.inl (.inr a))
      simpa [mulVec, dotProduct, Fintype.sum_sum_type, x, tup, hff, hfe, hfz'] using h1
    have hC : v (.inr ()) = 0 := by
      have h1 := congrFun hv (.inr ())
      simp [mulVec, dotProduct, Fintype.sum_sum_type, x, tup, hz'e, hz'f, hz'z'] at h1
      tauto
    funext i
    rcases i with (a | a) | ⟨⟩
    · exact hB a
    · exact hA a
    · exact hC
  obtain ⟨g, hg⟩ := witt_idx ε W x y hGram hnd
  have hge : ∀ b, uMat g *ᵥ e b = lam b • f b := fun b => hg (.inl (.inl b))
  have hgz : uMat g *ᵥ z' = α • z + β • w := hg (.inr ())
  refine ⟨g, ?_⟩
  have hne : ∀ b : Fin r, Fin.last r ≠ Fin.castSucc b := fun b h => Fin.castSucc_ne_last b h.symm
  ext a b
  refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
  · simp only [Zhat, famSc, fam, Fin.snoc_last, Fin.val_last, Nat.sub_self, pow_zero, inv_one, one_smul, hgz,
      hJ_add_r, hJ_smul_r, hzz, hzw, mul_zero, add_zero, Matrix.diagonal_apply_eq, hα, hcl]
    field_simp
  · simp only [Zhat, famSc, fam, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last, Nat.sub_self, pow_zero, inv_one,
      one_smul, mulVec_smul, hge, hJ_smul_r, hzf, mul_zero, Matrix.diagonal_apply_ne _ (hne b)]
  · simp only [Zhat, famSc, fam, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last, Nat.sub_self, pow_zero, inv_one,
      one_smul, hgz, hJ_smul_l, hJ_add_r, hJ_smul_r, hez, hew, mul_zero, add_zero,
      Matrix.diagonal_apply_ne _ (hne a).symm]
  · simp only [Zhat, famSc, fam, Fin.snoc_castSucc, Fin.val_castSucc, mulVec_smul, hge, hJ_smul_l, hJ_smul_r, hef,
      Matrix.diagonal_apply, Fin.castSucc_inj]
    split_ifs with h
    · subst h
      have := hsfc a
      simp only [hsf] at this
      rw [this, hlam]
      simp only [hsf]
      field_simp
    · simp

end Pure

section Glob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hJ_X (v : InfinitePlace X.B.I.F) (p q : (Formalism.MainNotions.S.VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd p)) (rv X.B.I v (X.crd q)) = embS D (X.pl v) ((Formalism.MainNotions.S.VS D).hT p q) :=
  Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v p q

theorem Tw_pos (u : D.what₂.Word) : 0 < Tw (D := D) u := by
  unfold Tw
  exact_mod_cast (D.mem u).A.T_prime.pos

theorem stepReal_of_witt (W : WittGram) : StepReal := by
  intro D X u u' sc hsc c hc
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  simp only [Good, Set.mem_ofPred_eq] at hc
  have key : ∀ v, ∃ g : Formalism.REAL.UJ (X.B.I.ε v),
      Zhat (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat g) = Matrix.diagonal (c v) := by
    intro v
    have h0 : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b =>
      (hJ_X X v _ _).trans (by rw [X.ee]; simp)
    have h1 : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0 := fun a b =>
      (hJ_X X v _ _).trans (by rw [X.ff]; simp)
    have h2 : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0 :=
      fun a b => (hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
    have h3 : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) = 0 := fun w a =>
      (hJ_X X v _ _).trans (by rw [(X.zu_orth w a).1]; simp)
    have h4 : ∀ (w : D.what₂.Word) a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR w)) = 0 := fun w a =>
      (hJ_X X v _ _).trans (by rw [(X.zu_orth w a).2]; simp)
    have h5 : ∀ (w : D.what₂.Word), hJ (X.B.I.ε v) (rv X.B.I v (X.zR w)) (rv X.B.I v (X.zR w)) = -(Tw (D := D) w : ℂ) :=
      fun w => (hJ_X X v _ _).trans (by rw [X.zu_norm w]; simp [Tw])
    have hw := X.wfr_perp u v ⟨0, hk⟩
    have hww : hJ (X.B.I.ε v) (X.wfr u v ⟨0, hk⟩) (X.wfr u v ⟨0, hk⟩) = 1 := by
      rw [X.wfr_on]; simp
    exact real_loc (X.B.I.ε v) W (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u')) (X.wfr u v ⟨0, hk⟩) (Tw u) (Tw u') sc h0 h1 h2 (h3 u) (h4 u)
      (h3 u') (h4 u') (h5 u) (h5 u') (fun a => (hw.1 a).1) (fun a => (hw.1 a).2) hw.2 hww (Tw_pos u) (Tw_pos u')
      hsc (c v) (hc v).1 (hc v).2
  choose γ hγ using key
  exact ⟨γ, fun v => hγ v⟩

end Glob

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

