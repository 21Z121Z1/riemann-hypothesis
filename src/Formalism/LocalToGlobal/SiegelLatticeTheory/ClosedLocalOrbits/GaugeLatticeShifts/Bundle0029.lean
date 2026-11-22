import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0028
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0027
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsColLatRepS
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0024
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfL

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BigCellDiagIff
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem dl_diagonal {r : ℕ} (c : Fin (r + 1) → ℂ) (l : ℕ) (h : l ≤ r + 1) :
    Dl (Matrix.diagonal c) l = ∏ i : Fin l, c (Fin.castLE h i) := by
  unfold Dl
  simp only [dif_pos h, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective h), Matrix.det_diagonal,
    Function.comp_apply]

theorem continuous_dl {r : ℕ} (l : ℕ) : Continuous fun Z : MZ r => Dl (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) l := by
  unfold Dl
  by_cases h : l ≤ r + 1
  · simp only [dif_pos h]
    fun_prop
  · simp only [dif_neg h]
    exact continuous_const

theorem continuous_gv {r : ℕ} (T T' : ℝ) : Continuous fun Z : MZ r => Gv T T' (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := by
  have h1 := continuous_dl (r := r) (r + 1)
  have h2 := continuous_dl (r := r) r
  unfold Gv
  fun_prop

theorem continuous_diag (r : ℕ) : Continuous fun c : Fin (r + 1) → ℂ => (Matrix.diagonal c : MZ r) := by
  exact Continuous.matrix_diagonal continuous_id

theorem measurable_wt (r k : ℕ) (T T' : ℝ) : Measurable fun c : Fin (r + 1) → ℂ => wtLoc k T T' c := by
  have h1 : Continuous fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c : MZ r) :=
    (continuous_gv T T').comp (continuous_diag r)
  have h2 := h1.measurable
  have h3 : ∀ l, Measurable fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c : MZ r) l :=
    fun l => ((continuous_dl l).comp (continuous_diag r)).measurable
  unfold wtLoc
  unfold JacV
  unfold modC
  fun_prop

theorem dcLoc_eq (r : ℕ) : dcLoc (r := r) = (2 : ℝ≥0∞) ^ (r + 1) • (volume : Measure (Fin (r + 1) → ℂ)) := by
  haveI : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by rw [two_smul]; infer_instance
  unfold dcLoc
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, volume_pi, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FrMIsIsom
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

variable {n r k : ℕ} {ε : Fin n → Bool} {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ}

theorem hJ_syn_syn {w : Fin k → Fin n → ℂ} (F : Frm ε e p z w T) (α β : Fin r → ℂ) (γ : ℂ) (δ : Fin k → ℂ)
    (α' β' : Fin r → ℂ) (γ' : ℂ) (δ' : Fin k → ℂ) :
    hJ ε (syn e p z w T α β γ δ) (syn e p z w T α' β' γ' δ') =
      ∑ a, α' a * conj (β a) + ∑ a, β' a * conj (α a) + (-γ' / (T : ℂ)) * conj γ + ∑ j, δ' j * conj (δ j) := by
  rw [hJ_syn]
  have h1 : ∀ a, hJ ε (syn e p z w T α β γ δ) (e a) = conj (β a) := fun a => by rw [UnitaryIsometries.hJ_conj, syn_e F]
  have h2 : ∀ a, hJ ε (syn e p z w T α β γ δ) (p a) = conj (α a) := fun a => by rw [UnitaryIsometries.hJ_conj, syn_p F]
  have h3 : hJ ε (syn e p z w T α β γ δ) z = conj γ := by rw [UnitaryIsometries.hJ_conj, synthesized_vector_z_pairing F]
  have h4 : ∀ j, hJ ε (syn e p z w T α β γ δ) (w j) = conj (δ j) := fun j => by rw [UnitaryIsometries.hJ_conj, syn_w F]
  simp only [h1, h2, h3, h4]

def frL (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w y : Fin k → Fin n → ℂ) (T : ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun v := syn e p z y T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v)
  map_add' v v' := by
    simp only [syn, UnitaryIsometries.hJ_add_right, add_smul, Finset.sum_add_distrib, neg_add, add_div]
    abel
  map_smul' c v := by
    simp only [syn, UnitaryIsometries.hJ_smul_right, RingHom.id_apply, smul_add, Finset.smul_sum, smul_smul]
    rw [show -(c * hJ ε z v) / (T : ℂ) = c * (-hJ ε z v / T) by ring]

def frM (e p : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (w y : Fin k → Fin n → ℂ) (T : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix' (frL (ε := ε) e p z w y T)

theorem frM_apply (w y : Fin k → Fin n → ℂ) (v : Fin n → ℂ) :
    frM (ε := ε) e p z w y T *ᵥ v =
      syn e p z y T (fun a => hJ ε (p a) v) (fun a => hJ ε (e a) v) (hJ ε z v) (fun j => hJ ε (w j) v) := by
  rw [frM, LinearMap.toMatrix'_mulVec]
  rfl

theorem frM_isIsom {w y : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (Fy : Frm ε e p z y T)
    (hdim : n = 2 * r + 1 + k) : UnitaryIsometries.IsIsom ε (frM (ε := ε) e p z w y T) := by
  intro v v'
  rw [frM_apply, frM_apply, hJ_syn_syn Fy]
  conv_rhs => rw [recon Fw hdim v, recon Fw hdim v', hJ_syn_syn Fw]

theorem frM_fix {w y : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) {v : Fin n → ℂ}
    (hv : ∀ j, hJ ε (w j) v = 0) : frM (ε := ε) e p z w y T *ᵥ v = v := by
  rw [frM_apply]
  conv_rhs => rw [recon Fw hdim v]
  simp only [syn, hv, zero_smul, Finset.sum_const_zero]

theorem frM_w {w y : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (j : Fin k) :
    frM (ε := ε) e p z w y T *ᵥ w j = y j := by
  rw [frM_apply]
  simp only [syn, Fw.pw, Fw.ew, Fw.zw, Fw.ww, zero_smul, Finset.sum_const_zero, zero_add, neg_zero, zero_div,
    ite_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem span_perp {w : Fin k → Fin n → ℂ} (F : Frm ε e p z w T) (a : ℕ) :
    ∀ x ∈ spanLt e a, ∀ j, hJ ε x (w j) = 0 := by
  intro x hx j
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, _, rfl⟩ := hy
    exact F.ew b j
  | zero => exact UnitaryIsometries.hJ_zero_left ε _
  | add x y _ _ hx hy => rw [UnitaryIsometries.hJ_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [UnitaryIsometries.hJ_smul_left, hx, mul_zero]

theorem spanLt_le (a : ℕ) (h : a ≤ r) : spanLt e a ≤ spanLt e r := by
  unfold spanLt
  refine Submodule.span_mono ?_
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨b, b.2, rfl⟩

theorem mem_NH {w : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) {s : UJ ε}
    (hs : s ∈ UnitaryIsometries.RI.SG ε e z) : ∃ m ∈ NG ε e z, ∃ h ∈ HG ε e p z, s = m * h := by
  set M := Formalism.MainNotions.S.uMat s with hM
  have hsi : s⁻¹ ∈ UnitaryIsometries.RI.SG ε e z := (UnitaryIsometries.RI.SG ε e z).inv_mem hs
  have hiso := UnitaryIsometries.isIsom_uMat ε s
  have hback : ∀ v : Fin n → ℂ, M *ᵥ (Formalism.MainNotions.S.uMat s⁻¹ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, hM, uMat_mul_inv, one_mulVec]
  have hMe : ∀ a j, hJ ε (e a) (M *ᵥ w j) = 0 := by
    intro a j
    rw [← hback (e a), hiso]
    have hx := hsi.1 a
    have hdec : Formalism.MainNotions.S.uMat s⁻¹ *ᵥ e a = e a + (Formalism.MainNotions.S.uMat s⁻¹ - 1) *ᵥ e a := by
      rw [Matrix.sub_mulVec, one_mulVec]; abel
    rw [hdec, UnitaryIsometries.hJ_add_left, Fw.ew, span_perp Fw a.1 _ hx j, add_zero]
  have hMz : ∀ j, hJ ε z (M *ᵥ w j) = 0 := by
    intro j
    rw [← hback z, hiso]
    have hx := hsi.2
    have hdec : Formalism.MainNotions.S.uMat s⁻¹ *ᵥ z = z + (Formalism.MainNotions.S.uMat s⁻¹ - 1) *ᵥ z := by
      rw [Matrix.sub_mulVec, one_mulVec]; abel
    rw [hdec, UnitaryIsometries.hJ_add_left, Fw.zw, span_perp Fw r _ hx j, add_zero]
  set y : Fin k → Fin n → ℂ := fun j => M *ᵥ w j - ∑ a, hJ ε (p a) (M *ᵥ w j) • e a with hy
  have hpe : ∀ a b, hJ ε (p a) (e b) = if b = a then 1 else 0 := fun a b => hJ_swapδ Fw.ep b a
  have hwe : ∀ j b, hJ ε (M *ᵥ w j) (e b) = 0 := fun j b => hJ_swap0 (hMe b j)
  have Fy : Frm ε e p z y T := by
    refine ⟨Fw.ee, Fw.ep, Fw.pp, Fw.ez, Fw.pz, Fw.zz, fun a j => ?_, fun a j => ?_, fun j => ?_, fun i j => ?_,
      Fw.T_ne⟩
    · simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, Fw.ee, mul_zero, Finset.sum_const_zero, sub_zero, hMe]
    · simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, hpe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    · have hze : ∀ b, hJ ε z (e b) = 0 := fun b => hJ_swap0 (Fw.ez b)
      simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sum_right, hze, mul_zero, Finset.sum_const_zero, sub_zero, hMz]
    · simp only [hy, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_sum_right, UnitaryIsometries.hJ_sum_left, hwe, Fw.ee, hMe,
        mul_zero, Finset.sum_const_zero, sub_zero]
      rw [hM]
      exact (hiso _ _).trans (Fw.ww i j)
  have hI := frM_isIsom Fw Fy hdim
  set hU := UnitaryIsometries.toUJ ε hI with hUdef
  have hUm : Formalism.MainNotions.S.uMat hU = frM (ε := ε) e p z w y T := UnitaryIsometries.uMat_toUJ ε hI
  have hUe : ∀ a, Formalism.MainNotions.S.uMat hU *ᵥ e a = e a := fun a => by
    rw [hUm]; exact frM_fix Fw hdim fun j => hJ_swap0 (Fw.ew a j)
  have hUp : ∀ a, Formalism.MainNotions.S.uMat hU *ᵥ p a = p a := fun a => by
    rw [hUm]; exact frM_fix Fw hdim fun j => hJ_swap0 (Fw.pw a j)
  have hUz : Formalism.MainNotions.S.uMat hU *ᵥ z = z := by
    rw [hUm]; exact frM_fix Fw hdim fun j => hJ_swap0 (Fw.zw j)
  have hUH : hU ∈ HG ε e p z := ⟨hUe, hUp, hUz⟩
  have hUw : ∀ j, Formalism.MainNotions.S.uMat hU⁻¹ *ᵥ y j = w j := fun j => by
    rw [← frM_w (y := y) Fw j, ← hUm, mulVec_mulVec, uMat_inv_mul, one_mulVec]
  refine ⟨s * hU⁻¹, ?_, hU, hUH, by group⟩
  have hmv : ∀ v, (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ v = M *ᵥ (Formalism.MainNotions.S.uMat hU⁻¹ *ᵥ v) - v := fun v => by
    rw [uMat_mul, Matrix.sub_mulVec, one_mulVec, ← mulVec_mulVec]
  have hme : ∀ a, (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ e a = (M - 1) *ᵥ e a := fun a => by
    rw [hmv, inv_fix ε (hUe a), Matrix.sub_mulVec, one_mulVec]
  have hmz : (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ z = (M - 1) *ᵥ z := by
    rw [hmv, inv_fix ε hUz, Matrix.sub_mulVec, one_mulVec]
  have hmy : ∀ j, (Formalism.MainNotions.S.uMat (s * hU⁻¹) - 1) *ᵥ y j ∈ spanLt e r := fun j => by
    rw [hmv, hUw, hy, sub_sub_cancel]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, a.2, rfl⟩)
  refine ⟨⟨fun a => ?_, ?_⟩, fun v hv => ?_⟩
  · rw [hme]; exact hs.1 a
  · rw [hmz]; exact hs.2
  · rw [recon Fy hdim v]
    simp only [syn, mulVec_add, mulVec_sum, mulVec_smul, hv, zero_smul, Finset.sum_const_zero, add_zero]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ ?_)) (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmy j))
    · rw [hme]; exact spanLt_le a.1 (le_of_lt a.2) (hs.1 a)
    · rw [hmz]; exact hs.2

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.GramEqOfHyp
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool)

def frm3 (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : Fin r ⊕ (Fin r ⊕ Unit) → Fin n → ℂ :=
  Sum.elim e (Sum.elim f (fun _ => z))

structure Hyp (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (T : ℂ) : Prop where
  ee : ∀ a b, hJ ε (e a) (e b) = 0
  ef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0
  ff : ∀ a b, hJ ε (f a) (f b) = 0
  ez : ∀ a, hJ ε (e a) z = 0
  fz : ∀ a, hJ ε (f a) z = 0
  zz : hJ ε z z = -T

theorem Hyp.fe {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a b : Fin r) :
    hJ ε (f a) (e b) = if a = b then 1 else 0 := by
  rw [hJ_conj, h.ef]; by_cases hab : b = a
  · subst hab; simp
  · rw [if_neg hab, if_neg (Ne.symm hab), map_zero]

theorem Hyp.ze {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a : Fin r) :
    hJ ε z (e a) = 0 := by rw [hJ_conj, h.ez, map_zero]

theorem Hyp.zf {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (h : Hyp ε e f z T) (a : Fin r) :
    hJ ε z (f a) = 0 := by rw [hJ_conj, h.fz, map_zero]

theorem gram_eq_of_hyp {e f e' f' : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T : ℂ}
    (h : Hyp ε e f z T) (h' : Hyp ε e' f' z' T) (i j : Fin r ⊕ (Fin r ⊕ Unit)) :
    hJ ε (frm3 e f z i) (frm3 e f z j) = hJ ε (frm3 e' f' z' i) (frm3 e' f' z' j) := by
  rcases i with a | a | _ <;> rcases j with b | b | _ <;>
    simp only [frm3, Sum.elim_inl, Sum.elim_inr, h.ee, h'.ee, h.ef, h'.ef, h.ff, h'.ff, h.ez, h'.ez, h.fz, h'.fz,
      h.zz, h'.zz, h.fe, h'.fe, h.ze, h'.ze, h.zf, h'.zf]

theorem gram_nd_of_hyp {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℂ} (hT : T ≠ 0) (h : Hyp ε e f z T) :
    (Matrix.of fun i j => hJ ε (frm3 e f z i) (frm3 e f z j)).det ≠ 0 := by
  intro hdet
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hw0
  have row : ∀ i, ∑ j, hJ ε (frm3 e f z i) (frm3 e f z j) * w j = 0 := fun i => by
    have := congrFun hw i
    simpa [mulVec, dotProduct] using this
  funext i
  rcases i with a | a | u
  · have := row (Sum.inr (Sum.inl a))
    simpa [Fintype.sum_sum_type, frm3, h.fe, h.ff, h.fz] using this
  · have := row (Sum.inl a)
    simpa [Fintype.sum_sum_type, frm3, h.ee, h.ef, h.ez] using this
  · have := row (Sum.inr (Sum.inr u))
    simp [Fintype.sum_sum_type, frm3, h.ze, h.zf, h.zz] at this
    rcases this with h1 | h1
    · exact absurd h1 hT
    · simpa using h1

theorem coord_inj {k : ℕ} (hdim : n = 2 * r + 1 + k)
    (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) :
    ∃ (N : Fin (r + 1) → Fin n) (P : Fin (r + k) → Fin n), Function.Injective N ∧ Function.Injective P ∧
      (∀ y, ε (N y) = false) ∧ (∀ x, ε (P x) = true) := by
  set sN := Finset.univ.filter (fun i : Fin n => ε i = false) with hsN
  set sP := Finset.univ.filter (fun i : Fin n => ε i = true) with hsP
  have hcard : sP.card + sN.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => ε i = true)
    simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
    exact this
  have hP : sP.card = r + k := by omega
  let eN := sN.equivFinOfCardEq hsig
  let eP := sP.equivFinOfCardEq hP
  refine ⟨fun y => (eN.symm y).1, fun x => (eP.symm x).1, ?_, ?_, fun y => ?_, fun x => ?_⟩
  · exact Subtype.val_injective.comp eN.symm.injective
  · exact Subtype.val_injective.comp eP.symm.injective
  · exact (Finset.mem_filter.1 (eN.symm y).2).2
  · exact (Finset.mem_filter.1 (eP.symm x).2).2

theorem complement {k : ℕ} (hdim : n = 2 * r + 1 + k)
    (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1)
    {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ} (hT : 0 < T) (h : Hyp ε e f z (T : ℂ)) :
    ∃ w : Fin k → Fin n → ℂ, (∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0) ∧
      (∀ c a, hJ ε (e c) (w a) = 0) ∧ (∀ c a, hJ ε (f c) (w a) = 0) ∧ (∀ a, hJ ε z (w a) = 0) := by
  obtain ⟨N, P, hN, hP, hNs, hPs⟩ := coord_inj ε hdim hsig
  have hNP : ∀ y x, N y ≠ P x := fun y x h => by have := hNs y; rw [h, hPs x] at this; exact Bool.noConfusion this
  set sq : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) with hsq
  have hsqc : conj sq = sq := Complex.conj_ofReal _
  have hsq2 : sq * sq = 1 / 2 := by
    rw [hsq, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast; ring
  let p : Fin r → Fin n := fun c => P (Fin.castAdd k c)
  let q : Fin r → Fin n := fun c => N (Fin.castSucc c)
  let qz : Fin n := N (Fin.last r)
  let wi : Fin k → Fin n := fun j => P (Fin.natAdd r j)
  let e0 : Fin r → Fin n → ℂ := fun c => sq • (dl (p c) + dl (q c))
  let f0 : Fin r → Fin n → ℂ := fun c => sq • (dl (p c) - dl (q c))
  let z0 : Fin n → ℂ := ((Real.sqrt T : ℝ) : ℂ) • dl qz
  let w0 : Fin k → Fin n → ℂ := fun j => dl (wi j)
  have hp : Function.Injective p := hP.comp (Fin.castAdd_injective r k)
  have hq : Function.Injective q := hN.comp (Fin.castSucc_injective r)
  have hqz : ∀ c, q c ≠ qz := fun c h => Fin.castSucc_ne_last c (hN h)
  have hwi : Function.Injective wi := hP.comp (Fin.natAdd_injective k r)
  have hpw : ∀ c j, p c ≠ wi j := fun c j h => by
    have h1 := congrArg Fin.val (hP h)
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h1
    omega
  have hd : ∀ i j, hJ ε (dl i) (dl j) = if i = j then (if ε i then 1 else -1) else 0 := hJ_dl ε
  have pp : ∀ a b, hJ ε (dl (p a)) (dl (p b)) = if a = b then 1 else 0 := fun a b => by
    rw [hd]; by_cases hab : a = b
    · subst hab; simp [p, hPs]
    · rw [if_neg (hp.ne hab), if_neg hab]
  have qq : ∀ a b, hJ ε (dl (q a)) (dl (q b)) = if a = b then -1 else 0 := fun a b => by
    rw [hd]; by_cases hab : a = b
    · subst hab; simp [q, hNs]
    · rw [if_neg (hq.ne hab), if_neg hab]
  have pq : ∀ a b, hJ ε (dl (p a)) (dl (q b)) = 0 := fun a b => by rw [hd, if_neg (hNP _ _).symm]
  have qp : ∀ a b, hJ ε (dl (q a)) (dl (p b)) = 0 := fun a b => by rw [hd, if_neg (hNP _ _)]
  have h0 : Hyp ε e0 f0 z0 (T : ℂ) := by
    refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun a => ?_, ?_⟩
    · simp only [e0, hJ_smul_left, hJ_smul_right, hJ_add_left, hJ_add_right, pp, qq, pq, qp, hsqc]
      split_ifs <;> ring
    · simp only [e0, f0, hJ_smul_left, hJ_smul_right, hJ_add_left, hJ_sub_right, pp, qq, pq, qp, hsqc]
      split_ifs
      · linear_combination 2 * hsq2
      · ring
    · simp only [f0, hJ_smul_left, hJ_smul_right, hJ_sub_left, hJ_sub_right, pp, qq, pq, qp, hsqc]
      split_ifs <;> ring
    · have h1 : p a ≠ qz := (hNP _ _).symm
      simp only [e0, z0, hJ_smul_left, hJ_smul_right, hJ_add_left, hd, if_neg h1, if_neg (hqz a)]
      ring
    · have h1 : p a ≠ qz := (hNP _ _).symm
      simp only [f0, z0, hJ_smul_left, hJ_smul_right, hJ_sub_left, hd, if_neg h1, if_neg (hqz a)]
      ring
    · have hs : ((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = (T : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]
      have hq0 : ε qz = false := hNs _
      simp only [z0, hJ_smul_left, hJ_smul_right, hd, if_true, Complex.conj_ofReal, hq0, Bool.false_eq_true,
        if_false]
      linear_combination (-1 : ℂ) * hs
  obtain ⟨g, hg⟩ := witt_of_gram' ε (frm3 e0 f0 z0) (frm3 e f z) (gram_eq_of_hyp ε h0 h)
    (gram_nd_of_hyp ε (by exact_mod_cast hT.ne') h0)
  have hiso := isIsom_uMat ε g
  have he : ∀ c, Formalism.MainNotions.S.uMat g *ᵥ e0 c = e c := fun c => hg (Sum.inl c)
  have hf : ∀ c, Formalism.MainNotions.S.uMat g *ᵥ f0 c = f c := fun c => hg (Sum.inr (Sum.inl c))
  have hz : Formalism.MainNotions.S.uMat g *ᵥ z0 = z := hg (Sum.inr (Sum.inr ()))
  have ww : ∀ a b, hJ ε (w0 a) (w0 b) = if a = b then 1 else 0 := fun a b => by
    simp only [w0]; rw [hd]; by_cases hab : a = b
    · subst hab; simp [wi, hPs]
    · rw [if_neg (hwi.ne hab), if_neg hab]
  have pw : ∀ c j, hJ ε (dl (p c)) (w0 j) = 0 := fun c j => by simp only [w0]; rw [hd, if_neg (hpw c j)]
  have qw : ∀ c j, hJ ε (dl (q c)) (w0 j) = 0 := fun c j => by simp only [w0]; rw [hd, if_neg (hNP _ _)]
  have zw : ∀ j, hJ ε (dl qz) (w0 j) = 0 := fun j => by simp only [w0]; rw [hd, if_neg (hNP _ _)]
  refine ⟨fun j => Formalism.MainNotions.S.uMat g *ᵥ w0 j, fun a b => by rw [hiso, ww], fun c a => ?_, fun c a => ?_, fun a => ?_⟩
  · rw [← he, hiso]; simp only [e0, hJ_smul_left, hJ_add_left, pw, qw]; ring
  · rw [← hf, hiso]; simp only [f0, hJ_smul_left, hJ_sub_left, pw, qw]; ring
  · rw [← hz, hiso]; simp only [z0, hJ_smul_left, zw]; ring

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormClosed
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.NormCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NormExpSatC' : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') →
    NormExpSat (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')

def SatGramC' : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    SatGram (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (Y.tO u u').genSet
        (Aset Y.TR (Y.cs u)) (Aset Y.TR (Y.cs u')) ∧
      SatGram (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (Y.tO u u').ngSet
        (Aset Y.TR (Y.cs u)) (Aset Y.TR (Y.cs u'))

def ChiNBiC : Prop := ∀ (D : D7) (X : HidaSetting D), ChiNBi X

def NeatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK

def LeviOntoC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.Pf.NormSteps.LeviOntoS Y.TR (Y.cs u)

theorem colLatRepC (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) :
    Formalism.L2.SG.Pf.NormSteps.ColLatRepS (Y.cs u) Y.hK :=
  Formalism.L2.SG.Pf.NormSteps.column_lattice_representatives (Y.cs u) Y.hK (Y.rowsOK u)

def MassAC : Prop := ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), MassA Y.TR (X.Fu u) (Y.cs u)

theorem chiNIndepC_holds : ChiNIndepC := fun _ X Y u u' =>
  chiNIndep_of_frameTie (cs := Y.cs u) (cs' := Y.cs u') (hTF := Full.frameTie (X := X) u u')

theorem normExpSatC'_of (hCL : NeatC) (hO : LeviOntoC) (hM : MassAC) (hS : SatGramC') : NormExpSatC' := by
  intro D X Y u u' _ _ _ hAbs
  obtain ⟨hSg, hSn⟩ := hS D X Y u u' ‹_› ‹_› ‹_›
  have hTF := Full.frameTie (X := X) u u'
  have hF := colFree_steps (TR := Y.TR) (F0 := X.Fu u) (cs := Y.cs u) (hK := Y.hK) (hR := Y.colReps u)
    (hCL := hCL D X Y u) (hO := hO D X Y u) (hRep := colLatRepC D X Y u) (hMass := hM D X Y u)
  have hF' := colFree_steps (TR := Y.TR) (F0 := X.Fu u') (cs := Y.cs u') (hK := Y.hK) (hR := Y.colReps u')
    (hCL := hCL D X Y u') (hO := hO D X Y u') (hRep := colLatRepC D X Y u') (hMass := hM D X Y u')
  exact normExpSat_of (TR := Y.TR) (cs := Y.cs u) (cs' := Y.cs u') (FdN := Y.FN u) (FdN' := Y.FN u')
    (hHS := hilbert_schmidt_blocks) (hGam := Formalism.L2.SG.NormCut.gamma_product_sum_holds)
    (hPsi := Formalism.L2.SG.NormCut.psi_natural_equiv_holds) (hAbs := hAbs)
    (hChi := chiNIndep_of_frameTie (cs := Y.cs u) (cs' := Y.cs u') (hTF := hTF))
    (sc := scOf Y.TR (Y.cs u)) (sc' := scOf Y.TR (Y.cs u'))
    (hPh := colPhase_holds (TR := Y.TR) (cs := Y.cs u) (cs' := Y.cs u') (hTF := hTF))
    (A := Aset Y.TR (Y.cs u)) (A' := Aset Y.TR (Y.cs u')) (hF := hF) (hF' := hF') (hSg := hSg) (hSn := hSn)

end Formalism.L2.SG.NormCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePf
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ScalarFrameCT : Prop :=
  ∀ (D : D7) (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' F'' : LFlag (VS D) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (Tn T'n : ℕ),
    FixedHyp D Λ F → IsLift Λ F' → IsLift Λ F'' → IsFixedConv Λ (gS D) F' → IsFixedConv Λ (gS D) F'' →
    IsAdmissible Λ (gS D) F F' → IsAdmissible Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → IsGeneric Λ (gS D) F F' → IsGeneric Λ (gS D) F F'' →
    Lat.s0 Λ F F' F'' β D.R.k = 1 → IsScalar Λ F F' F'' β → Gval F F' ≠ 0 → Gval F F'' ≠ 0 →
    T ≠ 0 → T' ≠ 0 →
    ∀ p : PlF D, (locH Z p).IsScalarPair (locTerm Z p Λ F F' Tn T'n) (locTerm Z p Λ F F'' Tn T'n)

def IotaStep : Prop :=
  ∀ (D : D7) (Z : LocDat D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' F'' : LFlag (VS D) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    FixedHyp D Λ F → IsLift Λ F' → IsLift Λ F'' → IsFixedConv Λ (gS D) F' → IsFixedConv Λ (gS D) F'' →
    IsAdmissible Λ (gS D) F F' → IsAdmissible Λ (gS D) F F'' →
    IsPair Λ F F' F'' β (gS D) → IsGeneric Λ (gS D) F F' → IsGeneric Λ (gS D) F F'' →
    Lat.s0 Λ F F' F'' β D.R.k = 1 → IsScalar Λ F F' F'' β → Gval F F' ≠ 0 → Gval F F'' ≠ 0 →
    T ≠ 0 → T' ≠ 0 →
    ∀ p : PlF D, IotaEl Z p Λ (frame F) (frameAct (frame F') (admXi D Λ F F')⁻¹)
      (frameAct (frame F'') (admXi D Λ F F'')⁻¹) β

end Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.ScalarFramePf

theorem scalarFrameCT_of (hI : IotaStep) : ScalarFrameCT := by
  intro D Z Λ T T' F F' F'' β Tn T'n hF hl' hl'' hc' hc'' ha' ha'' hP hg' hg'' hs hsc hG' hG'' hT hT' p
  exact isScalarPair_lt Z p Λ (frame F) (frameAct (frame F') (admXi D Λ F F')⁻¹)
    (frameAct (frame F'') (admXi D Λ F F'')⁻¹) β Tn T'n
    (gfacts_of Λ F F' F'' β hF hl' hl'' hc' hc'' hP hs hsc hG' hG'' hT hT')
    (hI D Z Λ F F' F'' β hF hl' hl'' hc' hc'' ha' ha'' hP hg' hg'' hs hsc hG' hG'' hT hT' p)

end Formalism.L2.SG.Pf
end
end

