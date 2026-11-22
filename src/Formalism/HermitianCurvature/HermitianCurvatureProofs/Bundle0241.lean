import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0235
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0163
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPContPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HermBvecEI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.AdjugateLastEntrySum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.FixOfPos
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0239
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0222

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomInvSqrt
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ContDiff Topology

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def phiS (c t : ℝ) : ℝ := sc c t * (Real.sqrt t)⁻¹

def PhiS (c : ℝ) (w : ℂ) : ℂ := ((phiS c w.re : ℝ) : ℂ)

lemma phiS_cd {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (phiS c) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : c / 8 < t
  · have h1 : ContDiff ℝ ∞ (sc c) := by
      unfold sc
      exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    have hpos : 0 < t := by linarith
    have h2 : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.sqrt y)⁻¹) t :=
      (Real.contDiffAt_sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'
    exact h1.contDiffAt.mul h2
  · have hev : phiS c =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds (show t < c / 4 by linarith)] with y hy
      have hy' : y < c / 4 := hy
      have h0 : (y - c / 4) / (c / 4) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      simp [phiS, sc, Real.smoothTransition.zero_of_nonpos h0]
    exact contDiffAt_const.congr_of_eventuallyEq hev

lemma phiS_ev {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : c / 2 < t) :
    phiS c =ᶠ[𝓝 t] fun y => y ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds ht] with y hy
  have hy' : c / 2 < y := hy
  have hc4 : 0 < c / 4 := by positivity
  have h1 : 1 ≤ (y - c / 4) / (c / 4) := by
    rw [le_div_iff₀ hc4]
    linarith
  have hy0 : 0 ≤ y := by linarith
  simp only [phiS, sc, Real.smoothTransition.one_of_one_le h1, one_mul]
  rw [Real.rpow_neg hy0, Real.sqrt_eq_rpow]

lemma phiS_bound {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ∃ A : ℝ, ∀ t : ℝ, c ≤ t → ‖iteratedFDeriv ℝ j (phiS c) t‖ ≤ A := by
  refine ⟨|(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * c ^ (-(1 / 2 : ℝ) - j), fun t ht => ?_⟩
  have hct : c / 2 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hev := phiS_ev hc hct
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_eq_iterate]
  simp only [Real.iter_deriv_rpow_const]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hq : -(1 / 2 : ℝ) - (j : ℝ) ≤ 0 := by linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc ht hq) (abs_nonneg _)

lemma PhiS_eq : ∀ c : ℝ, PhiS c = (Complex.ofRealCLM) ∘ (phiS c ∘ Complex.reCLM) := by
  intro c
  funext w
  simp [PhiS]

lemma PhiS_cd {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (PhiS c) := by
  rw [PhiS_eq]
  exact Complex.ofRealCLM.contDiff.comp ((phiS_cd hc).comp Complex.reCLM.contDiff)

lemma PhiS_bound {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ∃ B : ℝ, ∀ w ∈ {w : ℂ | c ≤ w.re}, ‖iteratedFDeriv ℝ j (PhiS c) w‖ ≤ B := by
  obtain ⟨A, hA⟩ := phiS_bound hc j
  refine ⟨‖Complex.ofRealCLM‖ * (A * ∏ _i : Fin j, ‖Complex.reCLM‖), fun w hw => ?_⟩
  have hw' : c ≤ w.re := hw
  have hj : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  rw [PhiS_eq]
  calc ‖iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ (phiS c ∘ Complex.reCLM)) w‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ j (phiS c ∘ Complex.reCLM) w‖ :=
        Complex.ofRealCLM.norm_iteratedFDeriv_comp_left ((phiS_cd hc).comp Complex.reCLM.contDiff).contDiffAt hj
    _ ≤ ‖Complex.ofRealCLM‖ * (A * ∏ _i : Fin j, ‖Complex.reCLM‖) := by
        gcongr
        rw [Complex.reCLM.iteratedFDeriv_comp_right (phiS_cd hc) w hj]
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        gcongr
        exact hA _ (by simpa using hw')

theorem unipotent_inverse_sqrt_bound : UBLInvSqrt := by
  intro k r d P hP S hSG c hc hSc n
  obtain ⟨hPcd, -⟩ := poly_adm (n := n) hP
  obtain ⟨M, hM⟩ := poly_H hP n
  have hU : UBL (fun g => PhiS c (P g)) S n 0 d :=
    ubl_fdb P hPcd S hSG {w : ℂ | c ≤ w.re} hSc d n M hM (PhiS c) (PhiS_cd hc) (PhiS_bound hc)
  refine ubl_congr (V := P ⁻¹' {w : ℂ | c / 2 < w.re}) ?_ ?_ hSG ?_ hU
  · exact (isOpen_lt continuous_const Complex.continuous_re).preimage hPcd.continuous
  · intro g hg
    have h := hSc g hg
    show c / 2 < (P g).re
    linarith
  · intro g _ hg
    have hg' : c / 2 < (P g).re := hg
    have hc4 : 0 < c / 4 := by positivity
    have h1 : 1 ≤ ((P g).re - c / 4) / (c / 4) := by
      rw [le_div_iff₀ hc4]
      linarith
    show (((Real.sqrt (P g).re)⁻¹ : ℝ) : ℂ) = PhiS c (P g)
    rw [PhiS, phiS, sc, Real.smoothTransition.one_of_one_le h1, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMContPf
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

namespace ContPfM

section ring

variable {R : Type*} [Ring R] (a c d : ℕ → R)

def Mi (i : ℕ) : Matrix (Fin 2) (Fin 2) R := !![a i, d i; -c i, 0]

def prodM (lo n : ℕ) : Matrix (Fin 2) (Fin 2) R := ((List.range n).map fun j => Mi a c d (lo + j)).prod

def bus : ℕ → R × R
  | 0 => (1, 0)
  | i + 1 => ((bus i).1 * a i - (bus i).2 * c i, (bus i).1 * d i)

def tds (r : ℕ) : ℕ → Fin 2 → R
  | 0, b => if b = 0 then 1 else 0
  | 1, b => if 1 ≤ r then (if b = 0 then a (r - 1) else d (r - 1)) else 0
  | m + 2, b => if m + 2 ≤ r then a (r - (m + 2)) * tds r (m + 1) b - c (r - (m + 1)) * d (r - (m + 2)) * tds r m b else 0

variable {a c d}

theorem prodM_succ_left (lo n : ℕ) : prodM a c d lo (n + 1) = Mi a c d lo * prodM a c d (lo + 1) n := by
  unfold prodM
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  congr 2
  exact List.map_congr_left (fun j _ => by
    show Mi a c d (lo + (j + 1)) = Mi a c d (lo + 1 + j)
    congr 1
    omega)

theorem prodM_succ_right (lo n : ℕ) : prodM a c d lo (n + 1) = prodM a c d lo n * Mi a c d (lo + n) := by
  unfold prodM
  rw [List.range_succ, List.map_append, List.prod_append]
  simp

theorem bus_eq : ∀ i, (bus a c d i).1 = prodM a c d 0 i 0 0 ∧ (bus a c d i).2 = prodM a c d 0 i 0 1
  | 0 => by simp [bus, prodM]
  | i + 1 => by
    obtain ⟨h1, h2⟩ := bus_eq i
    rw [prodM_succ_right]
    simp only [bus, h1, h2, Matrix.mul_apply, Fin.sum_univ_two, Mi, zero_add]
    simp [sub_eq_add_neg]

theorem tds_eq (hcd : ∀ i, Commute (c (i + 1)) (d i)) (r : ℕ) :
    ∀ m, m ≤ r → ∀ b, tds a c d r m b = prodM a c d (r - m) m 0 b
  | 0, _, b => by fin_cases b <;> simp [tds, prodM]
  | 1, hm, b => by
    rw [prodM_succ_left]
    fin_cases b <;> simp [tds, hm, prodM, Mi]
  | m + 2, hm, b => by
    have ih1 := tds_eq hcd r (m + 1) (by omega) b
    have ih0 := tds_eq hcd r m (by omega) b
    have e1 : r - (m + 2) + 1 = r - (m + 1) := by omega
    have e2 : r - (m + 1) + 1 = r - m := by omega
    show (if m + 2 ≤ r then a (r - (m + 2)) * tds a c d r (m + 1) b -
        c (r - (m + 1)) * d (r - (m + 2)) * tds a c d r m b else 0) = _
    have hL : prodM a c d (r - (m + 1)) (m + 1) = Mi a c d (r - (m + 1)) * prodM a c d (r - m) m := by
      rw [prodM_succ_left, e2]
    have hR : prodM a c d (r - (m + 2)) (m + 2) =
        Mi a c d (r - (m + 2)) * (Mi a c d (r - (m + 1)) * prodM a c d (r - m) m) := by
      rw [prodM_succ_left, e1, hL]
    rw [if_pos hm, ih1, ih0, hL, hR]
    have hc := (hcd (r - (m + 2))).eq
    rw [e1] at hc
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Mi]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, zero_mul, add_zero, neg_mul]
    simp only [hc, mul_neg, mul_assoc, sub_eq_add_neg]

theorem tds_bus (hcd : ∀ i, Commute (c (i + 1)) (d i)) (r : ℕ) :
    tds a c d r r 0 = (bus a c d r).1 ∧ tds a c d r r 1 = (bus a c d r).2 := by
  rw [tds_eq hcd r r le_rfl, tds_eq hcd r r le_rfl, (bus_eq r).1, (bus_eq r).2, Nat.sub_self]
  exact ⟨rfl, rfl⟩

end ring

section ops

open ContPf

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

variable (X) in

def aSv (Y : ℂ) (i : ℕ) : Module.End ℂ (WSm r X) := algebraMap ℂ _ Y - eS X i 3

theorem cp_vABs (Y : ℂ) : ∀ i, i ≤ r → ∀ f : WSm r X,
    (Q.vABs r Y i).1 (f : (Fin r → ℂ) → X) = (((bus (aSv X Y) (eS X · 4) (eS X · 5) i).1 f : WSm r X) : (Fin r → ℂ) → X) ∧
      (Q.vABs r Y i).2 (f : (Fin r → ℂ) → X) = (((bus (aSv X Y) (eS X · 4) (eS X · 5) i).2 f : WSm r X) : (Fin r → ℂ) → X)
  | 0, _, f => ⟨rfl, rfl⟩
  | i + 1, hi, f => by
    have hir : i < r := by omega
    have ih := cp_vABs Y i (by omega)
    simp only [Q.vABs, dif_pos hir, bus]
    refine ⟨?_, ?_⟩
    · have e1 : Y • (f : (Fin r → ℂ) → X) - pbOp ⟨i, hir⟩ (f : (Fin r → ℂ) → X) =
          ((aSv X Y i f : WSm r X) : (Fin r → ℂ) → X) := by
        simp only [aSv, eS, dif_pos hir]
        rfl
      have e2 : cbOp ⟨i, hir⟩ (f : (Fin r → ℂ) → X) = ((eS X i 4 f : WSm r X) : (Fin r → ℂ) → X) := by
        simp only [eS, dif_pos hir]
        rfl
      rw [e1, e2, (ih _).1, (ih _).2]
      rfl
    · have e3 : cbiOp ⟨i, hir⟩ (f : (Fin r → ℂ) → X) = ((eS X i 5 f : WSm r X) : (Fin r → ℂ) → X) := by
        simp only [eS, dif_pos hir]
        rfl
      rw [e3, (ih _).1]
      rfl

theorem cp_tdUv (Y : ℂ) (b : Fin 2) : ∀ m, ∀ f : WSm r X,
    tdUv r Y m b (f : (Fin r → ℂ) → X) = ((tds (aSv X Y) (eS X · 4) (eS X · 5) r m b f : WSm r X) : (Fin r → ℂ) → X)
  | 0, f => by
    fin_cases b <;> simp [tdUv, tds]
  | 1, f => by
    by_cases h1 : 1 ≤ r
    · have hr : r - 1 < r := by omega
      fin_cases b
      · simp only [tdUv, tds, dif_pos h1, if_pos h1, Fin.zero_eta, if_true, aSv, eS, dif_pos hr]
        rfl
      · simp only [tdUv, tds, dif_pos h1, if_pos h1, Fin.mk_one, one_ne_zero, if_false, eS, dif_pos hr]
        rfl
    · simp only [tdUv, tds, dif_neg h1, if_neg h1]
      rfl
  | m + 2, f => by
    by_cases h2 : m + 2 ≤ r
    · have ih1 := cp_tdUv Y b (m + 1) f
      have ih0 := cp_tdUv Y b m f
      have hr2 : r - (m + 2) < r := by omega
      have hr1 : r - (m + 1) < r := by omega
      simp only [tdUv, tds, dif_pos h2, if_pos h2]
      rw [ih1, ih0]
      simp only [aSv, eS, dif_pos hr2, dif_pos hr1]
      rfl
    · simp only [tdUv, tds, dif_neg h2, if_neg h2]
      rfl

end ops

section loc

open ContPf

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem loc_pbOp (l : Fin r) : Loc (X := X) (pbOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h.eventuallyEq_nhds] with y hy
  simp only [pbOp, wirtBar, hy.fderiv_eq]

theorem loc_cbOp (l : Fin r) : Loc (X := X) (cbOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h] with y hy
  simp only [cbOp, hy]

theorem loc_cbiOp (l : Fin r) : Loc (X := X) (cbiOp l) := by
  intro f₁ f₂ x h
  filter_upwards [h] with y hy
  simp only [cbiOp, hy]

theorem loc_tdUv (Y : ℂ) (b : Fin 2) : ∀ m, Loc (tdUv (X := X) r Y m b)
  | 0 => by
    unfold tdUv
    split_ifs
    · exact loc_id
    · exact loc_zero
  | 1 => by
    unfold tdUv
    split_ifs
    · exact loc_sub (loc_smul Y loc_id) (loc_pbOp _)
    · exact loc_cbiOp _
    · exact loc_zero
  | m + 2 => by
    have ih1 := loc_tdUv Y b (m + 1)
    have ih0 := loc_tdUv Y b m
    unfold tdUv
    split_ifs
    · exact loc_sub (loc_sub (loc_smul Y ih1) (loc_comp (loc_pbOp _) ih1))
        (loc_comp (loc_cbOp _) (loc_comp (loc_cbiOp _) ih0))
    · exact loc_zero

theorem loc_vABs (Y : ℂ) : ∀ i, Loc (X := X) (Q.vABs r Y i).1 ∧ Loc (X := X) (Q.vABs r Y i).2
  | 0 => ⟨loc_id, loc_zero⟩
  | i + 1 => by
    obtain ⟨h1, h2⟩ := loc_vABs Y i
    by_cases hi : i < r
    · simp only [Q.vABs, dif_pos hi]
      exact ⟨loc_sub (loc_comp h1 (loc_sub (loc_smul Y loc_id) (loc_pbOp _))) (loc_comp h2 (loc_cbOp _)),
        loc_comp h1 (loc_cbiOp _)⟩
    · simp only [Q.vABs, dif_neg hi]
      exact ⟨h1, h2⟩

end loc

end ContPfM

open ContPf ContPfM in
theorem mirror_residue_continuity : JDRvCont := by
  intro X _ _ r Y O hO hOm f hf c hc b
  obtain ⟨f', hf'm, hf'e⟩ := cp_cutoff O hO hOm f hf c hc
  have e1 : tdUv r Y r b f c = tdUv r Y r b f' c := ((loc_tdUv Y b r) f f' c hf'e.symm).eq_of_nhds
  have ev := loc_vABs (X := X) (r := r) Y r
  have h3 := cp_tdUv Y b r ⟨f', hf'm⟩
  have h4 := cp_vABs Y r le_rfl ⟨f', hf'm⟩
  have h5 := tds_bus (a := aSv (r := r) X Y) (c := (eS X · 4)) (d := (eS X · 5))
    (fun i => eS_comm (i + 1) i (by omega) 4 5) r
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · have e2 : (Q.vABs r Y r).1 f c = (Q.vABs r Y r).1 f' c := (ev.1 f f' c hf'e.symm).eq_of_nhds
    simp only [Q.cmp, if_true]
    rw [e1, e2]
    change tdUv r Y r 0 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c =
      (Q.vABs r Y r).1 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c
    rw [h3, h4.1, h5.1]
  · have e2 : (Q.vABs r Y r).2 f c = (Q.vABs r Y r).2 f' c := (ev.2 f f' c hf'e.symm).eq_of_nhds
    simp only [Q.cmp, show ¬ ((1 : Fin 2) = 0) by decide, if_false]
    rw [e1, e2]
    change tdUv r Y r 1 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c =
      (Q.vABs r Y r).2 ((⟨f', hf'm⟩ : WSm r X) : (Fin r → ℂ) → X) c
    rw [h3, h4.2, h5.2]

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GeometryEquivarianceFirstVector
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.GsFr
open scoped Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S2

variable {k r : ℕ}

private theorem herm_hpk_mulVec_of_mem_uh {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v w := by
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show star (h *ᵥ w) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (h *ᵥ v)) = star w ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']

lemma unitH_UH {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v : Fin (2 * r + k + 1) → ℂ) :
    unitH k r (h *ᵥ v) = h *ᵥ unitH k r v := by
  show ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ v)).re)⁻¹ : ℝ) : ℂ) • (h *ᵥ v)) =
    h *ᵥ ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ : ℝ) : ℂ) • v)
  rw [herm_hpk_mulVec_of_mem_uh hh, Matrix.mulVec_smul]

lemma omW_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (g : B.Mat k r) :
    omW k r z z' (n * g * n') = omW k r z z' g := by
  show prW k r z (xcof k r z z' (n * g * n')) = prW k r z (xcof k r z z' g)
  rw [xcof_N hz hz' hn hn' g]
  exact prW_N hn (fun a => xcof_esI z z' g a)

lemma omW'_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    omW' k r z z' (n * g * n') = omW' k r z z' g := by
  have hh : nᴴ * Hpk k r * n = Hpk k r := hn.1
  have hleft : (Hpk k r * nᴴ * Hpk k r) * n = 1 := by
    calc (Hpk k r * nᴴ * Hpk k r) * n = Hpk k r * (nᴴ * Hpk k r * n) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh, WeylGroupFacts.hpk_sq]
  have hnn : n⁻¹ * n = 1 := by
    rw [Matrix.inv_eq_left_inv hleft]
    exact hleft
  show prW k r z' ((n * g * n')⁻¹ *ᵥ xcofL k r z z' (n * g * n')) = prW k r z' (g⁻¹ *ᵥ xcofL k r z z' g)
  rw [xcofL_N hz hz' hn hn' g, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.mul_assoc, hnn, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  exact prW_N (WeylGroupFacts.mem_n_inv hn') (fun a => ginv_xcofL_esI z z' hg a)

end S2

open S2 in
theorem geometry_equivariance_first_vector : GeomEqvNu := by
  intro k r z z' _ hz hz' h hh n hn h' hh' n' hn' g hg
  have hy : h⁻¹ * n⁻¹ * g * n' * h' = h⁻¹ * (n⁻¹ * g * n') * h' := by simp only [Matrix.mul_assoc]
  have hhi := WeylGroupFacts.uw_inv hh
  have hhi' := WeylGroupFacts.uw_inv hh'
  have hni := WeylGroupFacts.mem_n_inv hn
  have hu : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h (RankOneEmbeddings.In.uw_unit hh)
  have hu' : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv h' (RankOneEmbeddings.In.uw_unit hh')
  constructor
  · show unitH k r (omW k r z z' g) = h *ᵥ unitH k r (omW k r z z' (h⁻¹ * n⁻¹ * g * n' * h'))
    rw [hy, omW_UW hz hhi hh', omW_N hz hz' hni hn', unitH_UH hhi.1, Matrix.mulVec_mulVec, hu,
      Matrix.one_mulVec]
  · show unitH k r (omW' k r z z' g) = h' *ᵥ unitH k r (omW' k r z z' (h⁻¹ * n⁻¹ * g * n' * h'))
    rw [hy, omW'_UW hz hz' hhi hh', omW'_N hz hz' hni hn' hg.1, unitH_UH hhi'.1, Matrix.mulVec_mulVec,
      hu', Matrix.one_mulVec]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDefectPlusWordLe
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section wts

variable {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty P) (Pv : ℝ → ℝ) (C : ℝ)

def RHyp : List ℝ → Prop
  | [] => True
  | y :: ys => (0 < (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re ∧
      (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).im = 0 ∧
      |Pv y| ≤ C * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) ∧ RHyp ys

theorem prodR_props (hC : 0 ≤ C) : ∀ ys : List ℝ, RHyp l0 a e ρ Pv C ys →
    (topRprod l0 a e ρ ys).im = 0 ∧ 0 < (topRprod l0 a e ρ ys).re ∧
      (ys.map fun y => |Pv y|).prod ≤ C ^ ys.length * (topRprod l0 a e ρ ys).re
  | [], _ => by simp [topRprod]
  | y :: ys, ⟨⟨h1, h2, h3⟩, hr⟩ => by
    obtain ⟨i1, i2, i3⟩ := prodR_props hC ys hr
    simp only [topRprod, Complex.mul_im, Complex.mul_re, List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨by rw [i1, h2]; ring, by rw [i1, h2]; simp only [mul_zero, zero_mul, sub_zero]; positivity, ?_⟩
    rw [i1, h2]
    simp only [mul_zero, sub_zero]
    have hp : 0 ≤ (ys.map fun y => |Pv y|).prod := List.prod_nonneg fun x hx => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
    calc |Pv y| * (ys.map fun y => |Pv y|).prod ≤ (C * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) *
          (C ^ ys.length * (topRprod l0 a e ρ ys).re) := mul_le_mul h3 i3 hp (by positivity)
      _ = C ^ (ys.length + 1) * ((topRprod l0 a e ρ ys).re * (topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y).re) := by
          ring

end wts

section wts2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem second_defect_plus_word_le (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (a : List C.Letter) (e : Wd.Ix (Fin a.length)) (ρ : M.Ty (D.parOf S v)) (C : ℝ) (hC : 0 ≤ C) (ys : List ℝ)
    (hR : RHyp (p v).l0 a e ρ (S.P v) C ys) :
    del2 S p v a e ρ * (ys.map fun y => |S.P v y|).prod ≤
      C ^ ys.length * del2 S p v (KB.plusW ys a) (KB.firstSt ys e) ρ := by
  obtain ⟨i1, i2, i3⟩ := prodR_props (p v).l0 a e ρ (S.P v) C hC ys hR
  have hd : del2 S p v (KB.plusW ys a) (KB.firstSt ys e) ρ = del2 S p v a e ρ * (topRprod (p v).l0 a e ρ ys).re := by
    unfold del2
    rw [cW_plusW, Complex.mul_re, i1, mul_zero, sub_zero, Real.sqrt_mul' _ i2.le]
    rw [show √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(topRprod (p v).l0 a e ρ ys).re *
        (√(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(topRprod (p v).l0 a e ρ ys).re) =
        √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re * √(Top.cW (D.parOf S v) (p v).l0 a e ρ).re *
          (√(topRprod (p v).l0 a e ρ ys).re * √(topRprod (p v).l0 a e ρ ys).re) by ring,
      Real.mul_self_sqrt i2.le]
  rw [hd]
  have h0 := second_defect_nonneg S p v a e ρ
  calc del2 S p v a e ρ * (ys.map fun y => |S.P v y|).prod ≤
        del2 S p v a e ρ * (C ^ ys.length * (topRprod (p v).l0 a e ρ ys).re) := mul_le_mul_of_nonneg_left i3 h0
    _ = _ := by ring

end wts2

end

end Formalism.FourierDecayAlt.P.PBL
end

