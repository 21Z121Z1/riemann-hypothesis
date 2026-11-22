import Mathlib
import Formalism.PeriodIntegrals.Bundle0031
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.Blocks
section
noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def blkDet {K : Type} [CommRing K] : List (K × ℕ) → K
  | [] => 1
  | (t, s) :: bs => (-1) ^ (s * (s - 1) / 2) * t ^ s * blkDet bs

theorem antidiag_det {K : Type} [CommRing K] (t : K) (s : ℕ) :
    (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det =
      (-1) ^ (s * (s - 1) / 2) * t ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (Fin.last s)]
    · have hm : ((Matrix.of fun a b : Fin (s + 1) => if a.val + b.val + 1 = s + 1 then t else 0).submatrix
          Fin.succ (Fin.last s).succAbove) =
          Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0 := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last, Fin.val_succ,
          Fin.coe_castSucc]
        split_ifs <;> first | rfl | omega
      rw [hm, ih]
      simp only [Matrix.of_apply, Fin.val_zero, Fin.val_last, zero_add, eq_self_iff_true, if_true]
      have hexp : (s + 1) * (s + 1 - 1) / 2 = s + s * (s - 1) / 2 := by
        rcases s with _ | k
        · rfl
        · have hk : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
            simp only [Nat.add_sub_cancel]
            ring
          rw [hk, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
          exact Nat.add_comm _ _
      rw [hexp]
      ring
    · intro j _ hj
      have hj' : (j : ℕ) ≠ s := fun h => hj (Fin.ext (by rw [Fin.val_last]; exact h))
      simp [hj']
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem ptEntry_det {K : Type} [CommRing K] (bs : List (K × ℕ)) (n : ℕ)
    (h : (bs.map Prod.snd).sum = n) :
    (Matrix.of fun a b : Fin n => ptEntry bs a.val b.val).det = blkDet bs := by
  induction bs generalizing n with
  | nil =>
    simp at h
    subst h
    simp [blkDet]
  | cons x bs ih =>
    obtain ⟨t, s⟩ := x
    simp only [List.map_cons, List.sum_cons] at h
    subst h
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv]
    have hb : (Matrix.of fun a b : Fin (s + (bs.map Prod.snd).sum) =>
        ptEntry ((t, s) :: bs) a.val b.val).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0) 0 0
          (Matrix.of fun a b : Fin (bs.map Prod.snd).sum => ptEntry bs a.val b.val) := by
      ext (a | a) (b | b)
      all_goals
        have ha := a.2
        have hb' := b.2
        simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
          Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Fin.coe_castAdd, Fin.coe_natAdd,
          Matrix.zero_apply, ptEntry]
        split_ifs <;> first | rfl | omega | simp
    rw [hb, Matrix.det_fromBlocks_zero₂₁, antidiag_det, ih _ rfl]
    simp [blkDet]

theorem ptEntryL_eq {E : Type} [CommRing E] (l : List (Eˣ × ℕ+)) (a b : ℕ) :
    Loc.ptEntryL l a b = ptEntry (l.map fun x => ((x.1 : E), (x.2 : ℕ))) a b := by
  induction l generalizing a b with
  | nil => simp [Loc.ptEntryL, ptEntry]
  | cons x l ih =>
    obtain ⟨t, s⟩ := x
    simp only [Loc.ptEntryL, List.map_cons, ptEntry, ih]

theorem ptEntry_append_lt {K : Type} [Zero K] (head tail : List (K × ℕ)) (a b : ℕ)
    (ha : a < (head.map Prod.snd).sum) (hb : b < (head.map Prod.snd).sum) :
    ptEntry (head ++ tail) a b = ptEntry head a b := by
  induction head generalizing a b with
  | nil => simp at ha
  | cons x hd ih =>
    obtain ⟨t, s⟩ := x
    simp only [List.map_cons, List.sum_cons] at ha hb
    simp only [List.cons_append, ptEntry]
    split_ifs <;> first | rfl | exact ih _ _ (by omega) (by omega)

theorem ptEntry_append_ge {K : Type} [Zero K] (head tail : List (K × ℕ)) (a b : ℕ)
    (ha : (head.map Prod.snd).sum ≤ a) :
    ptEntry (head ++ tail) a b =
      if (head.map Prod.snd).sum ≤ b then
        ptEntry tail (a - (head.map Prod.snd).sum) (b - (head.map Prod.snd).sum) else 0 := by
  induction head generalizing a b with
  | nil => simp
  | cons x hd ih =>
    obtain ⟨t, s⟩ := x
    simp only [List.map_cons, List.sum_cons] at ha ⊢
    simp only [List.cons_append, ptEntry]
    have hna : ¬ (a < s ∧ b < s) := by omega
    rw [if_neg hna]
    by_cases hb : s ≤ b
    · rw [if_pos ⟨by omega, hb⟩, ih (a - s) (b - s) (by omega)]
      by_cases hc : (hd.map Prod.snd).sum ≤ b - s
      · rw [if_pos hc, if_pos (by omega), Nat.sub_sub, Nat.sub_sub]
      · rw [if_neg hc, if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]

theorem blkDet_ne_zero {K : Type} [CommRing K] [IsDomain K] (bs : List (K × ℕ))
    (h : ∀ b ∈ bs, b.1 ≠ 0) : blkDet bs ≠ 0 := by
  induction bs with
  | nil => simp [blkDet]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    have ht : t ≠ 0 := h (t, s) (by simp)
    have hbs : blkDet bs ≠ 0 := ih (fun b hb => h b (by simp [hb]))
    simp only [blkDet]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ ht)) hbs

theorem dmin_top (D : Formalism.BasicNotions.D7) {n : ℕ} (w : Point D.host.E n) : Dmin w n = blkDet w.1 := by
  have hw := w.2
  unfold Dmin ptMat
  rw [dif_pos le_rfl, ← ptEntry_det w.1 n hw.2]
  congr 1

theorem topNe (D : Formalism.BasicNotions.D7) (w : Point D.host.E (D.R.rS + 1)) : Dmin w (D.R.rS + 1) ≠ 0 := by
  rw [dmin_top]
  exact blkDet_ne_zero _ (fun b hb => (w.2.1 b hb).1)

theorem dmin_last_one (D : Formalism.BasicNotions.D7) (w : Point D.host.E (D.R.rS + 1))
    (head : List (D.host.E × ℕ)) (t : D.host.E) (h : w.1 = head ++ [(t, 1)]) :
    Dmin w D.R.rS = blkDet head := by
  have h2 := w.2.2
  rw [h] at h2
  simp at h2
  have hsum : (head.map Prod.snd).sum = D.R.rS := by omega
  unfold Dmin ptMat
  rw [dif_pos (Nat.le_succ _), ← ptEntry_det head D.R.rS hsum]
  congr 1
  ext a b
  change ptEntry w.1 a.val b.val = ptEntry head a.val b.val
  rw [h, ptEntry_append_lt head _ _ _ (by rw [hsum]; exact a.2) (by rw [hsum]; exact b.2)]

theorem dmin_last_big (D : Formalism.BasicNotions.D7) (w : Point D.host.E (D.R.rS + 1))
    (head : List (D.host.E × ℕ)) (t : D.host.E) (s : ℕ)
    (h : w.1 = head ++ [(t, s)]) (hs : 2 ≤ s) : Dmin w D.R.rS = 0 := by
  have h2 := w.2.2
  rw [h] at h2
  simp at h2
  unfold Dmin ptMat
  rw [dif_pos (Nat.le_succ _)]
  apply Matrix.det_eq_zero_of_row_eq_zero ⟨(head.map Prod.snd).sum, by omega⟩
  intro b
  have hb2 := b.2
  change ptEntry w.1 (head.map Prod.snd).sum b.val = 0
  rw [h, ptEntry_append_ge head _ _ _ le_rfl]
  split_ifs with hb
  · simp only [ptEntry]
    split_ifs <;> first | rfl | omega
  · rfl

end PI.SupportDatumW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.Development
section
noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocStep : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D), Agree δ M p →
  ∀ (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)), kind w = kind w' →
  ∀ c : Option ((M p).Cls D.R.rS), BBtop M δ T T' p w c ≠ 0 → BBtop M δ T T' p w' c ≠ 0 →
    (M p).modK ((D.s.atP p).ιE (Dmin w (D.R.rS + 1))) =
        (M p).modK ((D.s.atP p).ιE (Dmin w' (D.R.rS + 1))) ∧
      (M p).modK ((D.s.atP p).ιE (Dmin w D.R.rS)) = (M p).modK ((D.s.atP p).ιE (Dmin w' D.R.rS))

def TopNe : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (w : Point D.host.E (D.R.rS + 1)), Dmin w (D.R.rS + 1) ≠ 0

theorem ne_zero_of_finprod_ne_zero {α : Type*} (f : α → ℂ) (hf : (Function.mulSupport f).Finite)
    (h : ∏ᶠ a, f a ≠ 0) (a : α) : f a ≠ 0 := by
  intro ha
  apply h
  rw [finprod_eq_prod f hf]
  apply Finset.prod_eq_zero (i := a)
  · rw [Set.Finite.mem_toFinset]
    simp [Function.mem_mulSupport, ha]
  · exact ha

theorem norm_conjF (D : Formalism.BasicNotions.D7) (x : D.host.E) :
    Algebra.norm ℚ (D.conjF x) = Algebra.norm ℚ x := by
  let σ : D.host.E →ₐ[ℚ] D.host.E := D.conjF.restrictScalars ℚ
  have hb : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  exact Algebra.norm_eq_of_algEquiv (AlgEquiv.ofBijective σ hb) x

theorem absNorm_eq_of_modK (D : Formalism.BasicNotions.D7)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hM : ∀ p, (M p).OK)
    (x x' : D.host.E) (hx : x ≠ 0) (hx' : x' ≠ 0)
    (h : ∀ p, (M p).modK ((D.s.atP p).ιE x) = (M p).modK ((D.s.atP p).ιE x')) :
    |Algebra.norm ℚ x| = |Algebra.norm ℚ x'| := by
  have e := local_product_formula D.host.F D.host.E D.sp.cm.deg2 D.conjF D.s.atP M hM
  have h1 := e x hx
  have h2 := e x' hx'
  simp only [h] at h1
  have h3 := h1.symm.trans h2
  have h4 := inv_injective h3
  exact_mod_cast h4

theorem supportVec_of (hL : LocStep) (hT : TopNe) (D : Formalism.BasicNotions.D7) : PI.SupportParts.SupportVec D := by
  intro δ M hA T T' w w' κ th hf hf' hB hB'
  have hk : kind w = κ := by
    by_contra hne
    exact hB (by simp [BBG, hne])
  have hk' : kind w' = κ := by
    by_contra hne
    exact hB' (by simp [BBG, hne])
  have hp : ∏ᶠ p, BBtop M δ T T' p w (th p) ≠ 0 := by
    intro h0
    exact hB (by simp [BBG, hk, h0])
  have hp' : ∏ᶠ p, BBtop M δ T T' p w' (th p) ≠ 0 := by
    intro h0
    exact hB' (by simp [BBG, hk', h0])
  have hkk : kind w = kind w' := hk.trans hk'.symm
  have hloc := fun p => hL D δ M p (hA p) T T' w w' hkk (th p)
    (ne_zero_of_finprod_ne_zero _ hf hp p) (ne_zero_of_finprod_ne_zero _ hf' hp' p)
  have hOK : ∀ p, (M p).OK := fun p => (hA p).1
  unfold PI.SupportParts.normG Gpt
  rcases hcase : kind w with _ | ζ
  · have h0 : Dmin w D.R.rS = 0 := by
      unfold kind at hcase
      by_contra hne
      simp [hne] at hcase
    have hcase' : kind w' = none := hkk ▸ hcase
    have h0' : Dmin w' D.R.rS = 0 := by
      unfold kind at hcase'
      by_contra hne
      simp [hne] at hcase'
    rw [h0, h0']
    have hn := absNorm_eq_of_modK D M hOK _ _ (hT D w) (hT D w') (fun p => (hloc p).1)
    simp only [mul_zero, map_zero, sub_zero, map_mul, abs_mul, norm_conjF, hn]
  · have hcase' : kind w' = some ζ := hkk ▸ hcase
    have hr : Dmin w D.R.rS ≠ 0 := by
      unfold kind at hcase
      by_contra hne
      simp [hne] at hcase
    have hr' : Dmin w' D.R.rS ≠ 0 := by
      unfold kind at hcase'
      by_contra hne
      simp [hne] at hcase'
    have hz : zetaOf w = ζ := by
      unfold kind at hcase
      simpa [hr] using hcase
    have hz' : zetaOf w' = ζ := by
      unfold kind at hcase'
      simpa [hr'] using hcase'
    have e1 : Dmin w (D.R.rS + 1) = ζ * Dmin w D.R.rS := by
      rw [← hz, zetaOf, div_mul_cancel₀ _ hr]
    have e1' : Dmin w' (D.R.rS + 1) = ζ * Dmin w' D.R.rS := by
      rw [← hz', zetaOf, div_mul_cancel₀ _ hr']
    have hn := absNorm_eq_of_modK D M hOK _ _ hr hr' (fun p => (hloc p).2)
    have g1 : ∀ x : D.host.E, ζ * x * D.conjF (ζ * x) - (T : D.host.E) * T' * (x * D.conjF x) =
        x * D.conjF x * (ζ * D.conjF ζ - (T : D.host.E) * T') := by
      intro x
      rw [map_mul]
      ring
    rw [e1, e1', g1, g1]
    simp only [map_mul, abs_mul, norm_conjF, hn]

theorem supportVecAll_of (hL : LocStep) (hT : TopNe) : PI.SupportParts.SupportVecAll :=
  fun D => supportVec_of hL hT D

end PI.SupportDatumW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.ModKUnitMul
section
noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def CokDetL : Prop := ∀ (R : Type) [CommRing R] (n : ℕ) (Z Z' : Matrix (Fin n) (Fin n) R),
  Z.det ∈ nonZeroDivisors R → Z'.det ∈ nonZeroDivisors R →
  Nonempty (((Fin n → R) ⧸ LinearMap.range Z.mulVecLin) ≃ₗ[R] ((Fin n → R) ⧸ LinearMap.range Z'.mulVecLin)) →
  ∃ u : Rˣ, Z'.det = u * Z.det

def DetForm : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (T T' : ℕ),
  ∃ C : Option D.host.E → (D.s.atP p).Ep, ∀ (w : Point D.host.E (D.R.rS + 1))
    (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)), modPt δ T T' p w = some a →
    a.mat.det = (D.s.atP p).ιE (Dmin w (D.R.rS + 1)) * C (kind w)

theorem uLow_det {E : Type} [CommRing E] {n : ℕ} (x : Loc.IL n → E) : (Loc.uLow x).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun i j hij => ?_)]
  · simp [Loc.uLow]
  · have hij' : i < j := hij
    simp only [Loc.uLow]
    rw [if_neg (ne_of_lt hij'), dif_neg (not_lt.2 hij'.le)]

theorem uUp_det {E : Type} [CommRing E] {n : ℕ} (w : Loc.Pt E n) (y : Loc.IN w → E) :
    (Loc.uUp w y).det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => ?_)]
  · simp [Loc.uUp]
  · have hij' : j < i := hij
    simp only [Loc.uUp]
    rw [if_neg (ne_of_gt hij'), dif_neg (fun h => absurd h.1 (not_lt.2 hij'.le))]

theorem bb_exists {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) {m : ℕ} (w : Loc.Pt E (m + 1)) (c : M.Cls m) (h : M.BB w c ≠ 0) :
    ∃ Z : M.Mat (m + 1), (Z.Z.map M.R.subtype).det = w.mat.det ∧
      Nonempty (M.Iso Z (Quotient.out c)) := by
  have hex : ∃ xy, M.bbIntegrand w c xy ≠ 0 := by
    by_contra hne
    push Not at hne
    apply h
    unfold Loc.Model.BB
    simp [hne]
  obtain ⟨⟨x, y⟩, hxy⟩ := hex
  unfold Loc.Model.bbIntegrand at hxy
  simp only at hxy
  split_ifs at hxy with hZ
  · have h1 := left_ne_zero_of_mul hxy
    have h2 := Nat.cast_ne_zero.mp h1
    unfold Loc.Model.nIso at h2
    refine ⟨_, ?_, (Nat.card_ne_zero.mp h2).1⟩
    show (Loc.uLow x * w.mat * Loc.uUp w y).det = _
    rw [Matrix.det_mul, Matrix.det_mul, uLow_det, uUp_det, one_mul, mul_one]
  · exact absurd rfl hxy

theorem bbtop_ne {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {T T' : ℕ} {p : PlF D}
    {w : Point D.host.E (D.R.rS + 1)} {c : Option ((M p).Cls D.R.rS)}
    (h : BBtop M δ T T' p w c ≠ 0) :
    ∃ a cl, modPt δ T T' p w = some a ∧ c = some cl ∧ (M p).BB a cl ≠ 0 := by
  unfold BBtop at h
  rcases hm : modPt δ T T' p w with _ | a <;> rcases c with _ | cl
  · simp [hm] at h
  · simp [hm] at h
  · simp [hm] at h
  · simp only [hm] at h
    exact ⟨a, cl, rfl, rfl, right_ne_zero_of_mul h⟩

theorem modK_unit_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) (u : (M.R)ˣ) (x : E) : M.modK ((u : M.R) * x) = M.modK x := by
  have hu : (((u : M.R) : E)) * ((((u⁻¹ : (M.R)ˣ) : M.R) : E)) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  unfold Loc.Model.modK
  congr 2
  ext z
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨((u : M.R) : E) * y, M.R.mul_mem (u : M.R).2 hy, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(((u⁻¹ : (M.R)ˣ) : M.R) : E) * y, M.R.mul_mem (↑u⁻¹ : M.R).2 hy, ?_⟩
    linear_combination (x * y) * hu

theorem nzd_of_unit {E : Type} [CommRing E] (S : Subring E) (x : S) (h : IsUnit (x : E)) :
    x ∈ nonZeroDivisors S := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have h1 : (x : E) * (y : E) = 0 := by rw [← Subring.coe_mul, hy, Subring.coe_zero]
    exact Subtype.ext (by simpa using h.mul_right_eq_zero.1 h1)
  · have h1 : (y : E) * (x : E) = 0 := by rw [← Subring.coe_mul, hy, Subring.coe_zero]
    exact Subtype.ext (by simpa using h.mul_left_eq_zero.1 h1)

theorem locStep_of (hC : CokDetL) (hD : DetForm)
    (hT : ∀ (D : Formalism.BasicNotions.D7) (w : Point D.host.E (D.R.rS + 1)), Dmin w (D.R.rS + 1) ≠ 0)
    (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)) (hk : kind w = kind w')
    (c : Option ((M p).Cls D.R.rS)) (hw : BBtop M δ T T' p w c ≠ 0) (hw' : BBtop M δ T T' p w' c ≠ 0) :
    (M p).modK ((D.s.atP p).ιE (Dmin w (D.R.rS + 1))) =
        (M p).modK ((D.s.atP p).ιE (Dmin w' (D.R.rS + 1))) ∧
      (M p).modK ((D.s.atP p).ιE (Dmin w D.R.rS)) = (M p).modK ((D.s.atP p).ιE (Dmin w' D.R.rS)) := by
  obtain ⟨a, cl, ha, hc, hb⟩ := bbtop_ne hw
  obtain ⟨a', cl', ha', hc', hb'⟩ := bbtop_ne hw'
  rw [hc] at hc'
  cases hc'
  obtain ⟨Z, hZ, ⟨φ⟩⟩ := bb_exists (M p) a cl hb
  obtain ⟨Z', hZ', ⟨φ'⟩⟩ := bb_exists (M p) a' cl hb'
  have hmap : ∀ Y : (M p).Mat (D.R.rS + 1), (Y.Z.map (M p).R.subtype).det = ((Y.Z.det : (M p).R) : _) :=
    fun Y => (RingHom.map_det (M p).R.subtype Y.Z).symm
  have hu1 : IsUnit (Z.Z.map (M p).R.subtype).det := Z.unit
  have hu2 : IsUnit (Z'.Z.map (M p).R.subtype).det := Z'.unit
  have n1 : Z.Z.det ∈ nonZeroDivisors (M p).R := nzd_of_unit _ _ (by rw [← hmap]; exact hu1)
  have n2 : Z'.Z.det ∈ nonZeroDivisors (M p).R := nzd_of_unit _ _ (by rw [← hmap]; exact hu2)
  obtain ⟨u, hu⟩ := hC (M p).R (D.R.rS + 1) Z.Z Z'.Z n1 n2 ⟨φ.1.trans φ'.1.symm⟩
  obtain ⟨C, hCf⟩ := hD D δ p T T'
  have d1 := hCf w a ha
  have d2 := hCf w' a' ha'
  rw [← hk] at d2

  have e : a'.mat.det = ((u : (M p).R) : (D.s.atP p).Ep) * a.mat.det := by
    rw [← hZ, ← hZ', hmap, hmap, hu, Subring.coe_mul]
  have hua : IsUnit a.mat.det := hZ ▸ hu1
  have hCu : IsUnit (C (kind w)) := by
    rw [d1] at hua
    exact isUnit_of_mul_isUnit_right hua
  have key : (D.s.atP p).ιE (Dmin w' (D.R.rS + 1)) =
      ((u : (M p).R) : (D.s.atP p).Ep) * (D.s.atP p).ιE (Dmin w (D.R.rS + 1)) := by
    rw [d1, d2, ← mul_assoc] at e
    exact hCu.mul_right_cancel e
  refine ⟨by rw [key, modK_unit_mul], ?_⟩
  rcases hcase : kind w with _ | ζ
  · have h0 : Dmin w D.R.rS = 0 := by
      unfold kind at hcase
      by_contra hne
      simp [hne] at hcase
    have hcase' : kind w' = none := hk ▸ hcase
    have h0' : Dmin w' D.R.rS = 0 := by
      unfold kind at hcase'
      by_contra hne
      simp [hne] at hcase'
    rw [h0, h0']
  · have hcase' : kind w' = some ζ := hk ▸ hcase
    have hr : Dmin w D.R.rS ≠ 0 := by
      unfold kind at hcase
      by_contra hne
      simp [hne] at hcase
    have hr' : Dmin w' D.R.rS ≠ 0 := by
      unfold kind at hcase'
      by_contra hne
      simp [hne] at hcase'
    have hz : zetaOf w = ζ := by
      unfold kind at hcase
      simpa [hr] using hcase
    have hz' : zetaOf w' = ζ := by
      unfold kind at hcase'
      simpa [hr'] using hcase'
    have e1 : Dmin w (D.R.rS + 1) = ζ * Dmin w D.R.rS := by
      rw [← hz, zetaOf, div_mul_cancel₀ _ hr]
    have e1' : Dmin w' (D.R.rS + 1) = ζ * Dmin w' D.R.rS := by
      rw [← hz', zetaOf, div_mul_cancel₀ _ hr']
    have hζ : ζ ≠ 0 := by
      intro h0
      apply hT D w
      rw [e1, h0, zero_mul]
    have hζu : IsUnit ((D.s.atP p).ιE ζ) := (isUnit_iff_ne_zero.mpr hζ).map (D.s.atP p).ιE
    have key' : (D.s.atP p).ιE (Dmin w' D.R.rS) =
        ((u : (M p).R) : (D.s.atP p).Ep) * (D.s.atP p).ιE (Dmin w D.R.rS) := by
      rw [e1, e1', map_mul, map_mul] at key
      apply hζu.mul_left_cancel
      rw [key]
      ring
    rw [key', modK_unit_mul]

end PI.SupportDatumW
end
end

