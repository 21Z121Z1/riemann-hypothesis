import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0012
import Lemmata.GeneralBFactForm.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0008

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def x0F (X : Data E r) : Frame X.Ψ r := fun τ => (X.signature τ).choose

def OmF (X : Data E r) (x0 : Frame X.Ψ r) : Set (V (nd X)) := {z | cpt X x0 z ∈ X.dom}

def rhF (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) : ℝ :=
  -∑ τ, Real.log ‖dmin X.Gm (cpt X x0 z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖

def eF (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) : ℝ := rhF X x0 z + Real.log (1 + ‖z‖ ^ 2)

def densF (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) : ℝ :=
  ∏ τ, ∏ i : Fin r, ‖dmin X.Gm (cpt X x0 z) τ i.castSucc‖ ^ (-2 : ℤ)

def muF (X : Data E r) (x0 : Frame X.Ψ r) : Measure (V (nd X)) :=
  (volume.restrict (OmF X x0)).withDensity fun z => ENNReal.ofReal (densF X x0 z)

def sat (X : Data E r) (x0 : Frame X.Ψ r) (C : Set (Frame X.Ψ r)) : Set (V (nd X)) :=
  {z | z ∈ OmF X x0 ∧ ∃ x ∈ C, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = rmul x b}

def kaF (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (z : V (nd X)) : ℝ := Real.exp (-bb * rhF X x0 z)

def IsOrth (X : Data E r) (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def poin (X : Data E r) (la : Wt X.Ψ r) (F : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑' γ : X.Γ, (X.χ la γ.1)⁻¹ * F (lact γ.1 x)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

noncomputable section

section Mat

variable {n : ℕ}

lemma inv_blockTriangular {α : Type*} [LinearOrder α] {b : Fin n → α} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.BlockTriangular b) (hd : M.det ≠ 0) : (M⁻¹).BlockTriangular b := by
  haveI : Invertible M := M.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hd)
  exact Matrix.blockTriangular_inv_of_blockTriangular hM

lemma det_lowerUni {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular OrderDual.toDual)
    (h1 : ∀ a, N a a = 1) : N.det = 1 := by
  rw [Matrix.det_of_lowerTriangular N hN]
  simp [h1]

theorem lu_unique {N N' U U' : Matrix (Fin n) (Fin n) ℂ}
    (hN : N.BlockTriangular OrderDual.toDual) (hN1 : ∀ a, N a a = 1)
    (hN' : N'.BlockTriangular OrderDual.toDual) (hN'1 : ∀ a, N' a a = 1)
    (hU : U.BlockTriangular id) (hU' : U'.BlockTriangular id) (hd : U'.det ≠ 0)
    (h : N * U = N' * U') : N = N' ∧ U = U' := by
  first | exact Bl.general_b_fact_form.goal1 .. | (apply Bl.general_b_fact_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_form.goal1 <;> assumption)

lemma lminor_last' (M : Matrix (Fin n) (Fin n) ℂ) : lminor M (Fin.last n) = M.det := by
  rfl

theorem lu_exists {M : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i : Fin (n + 1), lminor M i ≠ 0) :
    ∃ N U : Matrix (Fin n) (Fin n) ℂ, N.BlockTriangular OrderDual.toDual ∧ (∀ a, N a a = 1) ∧
      U.BlockTriangular id ∧ U.det ≠ 0 ∧ N * U = M := by
  classical
  let A : ∀ r : Fin n, Matrix (Fin r) (Fin r) ℂ := fun r =>
    M.submatrix (Fin.castLE r.isLt.le) (Fin.castLE r.isLt.le)
  have hA : ∀ r : Fin n, IsUnit (A r).det := fun r => isUnit_iff_ne_zero.mpr (hM r.castSucc)
  let x : ∀ r : Fin n, Fin r → ℂ := fun r =>
    -((fun j => M r (Fin.castLE r.isLt.le j)) ᵥ* (A r)⁻¹)
  have hx : ∀ r : Fin n, ∀ j : Fin r,
      ∑ i : Fin r, x r i * M (Fin.castLE r.isLt.le i) (Fin.castLE r.isLt.le j) =
        -M r (Fin.castLE r.isLt.le j) := by
    intro r j
    have hv : x r ᵥ* A r = -(fun j => M r (Fin.castLE r.isLt.le j)) := by
      simp only [x, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hA r),
        Matrix.vecMul_one]
    have h := congrFun hv j
    simpa [Matrix.vecMul, dotProduct, A] using h

  let L : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun r c =>
    if h : c < r then x r ⟨c, h⟩ else if c = r then 1 else 0
  have hLlow : L.BlockTriangular OrderDual.toDual := by
    intro r c hrc
    have hrc' : r < c := OrderDual.toDual_lt_toDual.mp hrc
    simp [L, not_lt.mpr hrc'.le, hrc'.ne']
  have hL1 : ∀ a, L a a = 1 := fun a => by simp [L]
  have hLdet : L.det = 1 := det_lowerUni hLlow hL1
  have hLu : IsUnit L.det := by rw [hLdet]; exact isUnit_one
  have hrow : ∀ r c : Fin n, c < r → (L * M) r c = 0 := by
    intro r c hcr
    have e1 : ∀ k, L r k * M k c =
        (if h : k < r then x r ⟨k, h⟩ * M k c else 0) + (if k = r then M k c else 0) := by
      intro k
      by_cases h : k < r
      · simp [L, h, h.ne]
      · by_cases h' : k = r
        · subst h'
          simp [L]
        · simp [L, h, h']
    have hsub : ∑ k : Fin n, (if h : k < r then x r ⟨k, h⟩ * M k c else 0) =
        ∑ j : Fin r, x r j * M (Fin.castLE r.isLt.le j) c := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb r.isLt.le)))]
      · rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : (Fin.castLEEmb r.isLt.le j) < r := by
          show (j : ℕ) < r
          exact j.isLt
        rw [dif_pos hj]
        rfl
      · intro k _ hk
        have hk' : ¬ k < r := by
          intro h
          apply hk
          exact Finset.mem_map.mpr ⟨⟨k, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
        rw [dif_neg hk']
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ r (fun k => M k c), if_pos (Finset.mem_univ _), hsub]
    have h := hx r ⟨c, hcr⟩
    have hc : Fin.castLE r.isLt.le (⟨c, hcr⟩ : Fin r) = c := Fin.ext rfl
    rw [hc] at h
    rw [h]
    ring
  refine ⟨L⁻¹, L * M, inv_blockTriangular hLlow (by rw [hLdet]; exact one_ne_zero), ?_, ?_, ?_, ?_⟩
  · intro a
    have h1 : (L * L⁻¹) a a = 1 := by
      rw [Matrix.mul_nonsing_inv L hLu]
      simp
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
    · rwa [hL1, one_mul] at h1
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with h | h
      · have h0 : L⁻¹ k a = 0 := inv_blockTriangular hLlow (by rw [hLdet]; exact one_ne_zero)
          (OrderDual.toDual_lt_toDual.mpr h)
        rw [h0, mul_zero]
      · have h0 : L a k = 0 := hLlow (OrderDual.toDual_lt_toDual.mpr h)
        rw [h0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · intro r c hcr
    exact hrow r c hcr
  · rw [Matrix.det_mul, hLdet, one_mul, ← lminor_last']
    exact hM _
  · rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hLu, Matrix.one_mul]

end Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def Mt (v : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => v (τ, a, b)

def BC (ι : Type*) [Fintype ι] (r : ℕ) : Set (Ix ι r → ℂ) := {v | ∀ τ, ∀ i : Fin (r + 1), lminor (Mt v τ) i ≠ 0}

def sS (ι : Type*) (r : ℕ) : Set (Ix ι r → ℂ) := {w | ∀ τ b, w (τ, b, b) ≠ 0}

lemma Mt_lu (w : Ix ι r → ℂ) (τ : ι) : Mt (lu w) τ = (1 + sl w τ) * up w τ := by
  ext a b
  rfl

lemma one_add_sl_low (w : Ix ι r → ℂ) (τ : ι) : (1 + sl w τ).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
  simp [sl, Matrix.one_apply_ne hij'.ne, not_lt.mpr hij'.le]

lemma one_add_sl_diag (w : Ix ι r → ℂ) (τ : ι) (a : Fin r) : (1 + sl w τ) a a = 1 := by
  simp [sl]

lemma up_upper (w : Ix ι r → ℂ) (τ : ι) : (up w τ).BlockTriangular id := by
  intro i j hij
  have hij' : j < i := hij
  simp [up, hij']

lemma det_up (w : Ix ι r → ℂ) (τ : ι) : (up w τ).det = ∏ b, w (τ, b, b) := by
  rw [Matrix.det_of_upperTriangular (up_upper w τ)]
  simp [up]

lemma det_up_ne {w : Ix ι r → ℂ} (hw : w ∈ sS ι r) (τ : ι) : (up w τ).det ≠ 0 := by
  rw [det_up]
  exact Finset.prod_ne_zero_iff.mpr fun b _ => hw τ b

lemma eq_of_sl_up {w w' : Ix ι r → ℂ} (h1 : ∀ τ, sl w τ = sl w' τ) (h2 : ∀ τ, up w τ = up w' τ) : w = w' := by
  funext i
  obtain ⟨τ, a, b⟩ := i
  by_cases hba : b < a
  · have h := congrFun (congrFun (h1 τ) a) b
    simpa [sl, hba] using h
  · have h := congrFun (congrFun (h2 τ) a) b
    simpa [up, hba] using h

theorem lu_injOn : Set.InjOn (lu (ι := ι) (r := r)) (sS ι r) := by
  intro w hw w' hw' h
  have key : ∀ τ, (1 + sl w τ) = (1 + sl w' τ) ∧ up w τ = up w' τ := by
    intro τ
    have hM : (1 + sl w τ) * up w τ = (1 + sl w' τ) * up w' τ := by
      rw [← Mt_lu, ← Mt_lu, h]
    exact lu_unique (one_add_sl_low w τ) (one_add_sl_diag w τ) (one_add_sl_low w' τ)
      (one_add_sl_diag w' τ) (up_upper w τ) (up_upper w' τ) (det_up_ne hw' τ) hM
  exact eq_of_sl_up (fun τ => add_left_cancel (key τ).1) (fun τ => (key τ).2)

theorem BC_subset_image : BC ι r ⊆ lu '' sS ι r := by
  intro v hv
  choose N U hN hN1 hU hUd hNU using fun τ => lu_exists (M := Mt v τ) (hv τ)
  refine ⟨fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2 else U i.1 i.2.1 i.2.2, ?_, ?_⟩
  · intro τ b
    show (if b < b then N τ b b else U τ b b) ≠ 0
    rw [if_neg (lt_irrefl b)]
    intro h0
    have hdet : (U τ).det = ∏ b, U τ b b := Matrix.det_of_upperTriangular (hU τ)
    exact hUd τ (hdet ▸ Finset.prod_eq_zero (Finset.mem_univ b) h0)
  · have hsl : ∀ τ, 1 + sl (fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2
        else U i.1 i.2.1 i.2.2) τ = N τ := by
      intro τ
      ext a b
      rcases lt_trichotomy b a with h | h | h
      · simp [sl, h, Matrix.one_apply_ne (ne_of_gt h)]
      · subst h
        simp [sl, hN1]
      · have h0 : N τ a b = 0 := hN τ (OrderDual.toDual_lt_toDual.mpr h)
        simp [sl, not_lt.mpr h.le, Matrix.one_apply_ne (ne_of_lt h), h0]
    have hup : ∀ τ, up (fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2
        else U i.1 i.2.1 i.2.2) τ = U τ := by
      intro τ
      ext a b
      by_cases h : b < a
      · have h0 : U τ a b = 0 := hU τ h
        simp [up, h, h0]
      · simp [up, h]
    funext i
    obtain ⟨τ, a, b⟩ := i
    show ((1 + sl _ τ) * up _ τ : Matrix (Fin r) (Fin r) ℂ) a b = v (τ, a, b)
    rw [hsl, hup, hNU]
    rfl

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Matrix
open scoped Matrix ComplexOrder ENNReal

noncomputable section

theorem SumBoundStatement_holds : SumBoundStatement := by
  intro f p q s hs Γ hd hU
  obtain ⟨c, hc, hsepΓ⟩ := sumBd_sep Γ hd hU
  obtain ⟨C, hC, hbound⟩ := sumBd_sum (p := p) (q := q) (f := f) hs hc
  refine ⟨C, hC, fun v hv => ?_⟩
  choose G hG hGw using fun k => sumBd_frame (hv k)
  let x : Γ → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fun γ k =>
    ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * G k
  have hxU : ∀ a k, IsUpq (x a k) := fun a k => sumBd_isUpq_mul (hU a.1 a.2 k) (hG k)
  have hxsep : ∀ a b : Γ, a ≠ b → ∃ k i j,
      c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
    intro a b hab
    have hmem : b.1 * a.1⁻¹ ∈ Γ := Γ.mul_mem b.2 (Γ.inv_mem a.2)
    have hne : b.1 * a.1⁻¹ ≠ 1 := fun h => hab (Subtype.ext (mul_inv_eq_one.mp h).symm)
    obtain ⟨k, i, j, hk⟩ := hsepΓ _ hmem hne
    refine ⟨k, i, j, le_of_le_of_eq hk ?_⟩
    have : x b k * (x a k)⁻¹ = (((b.1 * a.1⁻¹) k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
      simp only [x, Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.coe_units_inv]
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (G k), sumBd_mul_inv (hG k), Matrix.one_mul]
    rw [this]
  calc ∑' γ : Γ, ENNReal.ofReal (∏ k, dpow (mob ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Zof v k)) s)
      = ∑' γ : Γ, ENNReal.ofReal (∏ k, (Complex.normSq (det (x γ k).toBlocks₂₂))⁻¹ ^ s) := by
        congr 1; funext γ
        rw [Finset.prod_congr rfl fun k _ => hGw k _ (hU γ.1 γ.2 k) s]
    _ ≤ C := hbound Γ x hxU hxsep

end
end ReciprocityTheory.ChartRestriction.G.AR.Up
end

