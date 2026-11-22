import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0285
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0243
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0284
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0276

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
section
noncomputable section
open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.L2.SG.KappaOffDiagonal

namespace GlobalTheory.TypeAsm.GramPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D}

theorem pl_vOf (τ : D.what₂.Tau) : X.pl (vOf X τ) = τ := X.pl.apply_symm_apply τ

theorem crd_add (x y : (VS D).V) : X.crd (x + y) = X.crd x + X.crd y := by
  conv_lhs => rw [← Formalism.L2.SG.Pf.toV_crd X x, ← Formalism.L2.SG.Pf.toV_crd X y, ← Formalism.L2.SG.Pf.toV_add,
    Formalism.L2.SG.Pf.crd_toV]

theorem crd_smul (c : D.host.E) (x : (VS D).V) : X.crd (c • x) = X.ιE.symm c • X.crd x := by
  conv_lhs => rw [← X.ιE.apply_symm_apply c, ← Formalism.L2.SG.Pf.toV_crd X x, ← Formalism.L2.SG.Pf.toV_smul,
    Formalism.L2.SG.Pf.crd_toV]

theorem rv_add (v : InfinitePlace X.B.I.F) (a b : Fin X.B.I.n → X.B.I.E) :
    rv X.B.I v (a + b) = rv X.B.I v a + rv X.B.I v b := by
  unfold rv
  rw [← Matrix.mulVec_add]
  congr 1
  ext i
  simp

theorem rv_smul (v : InfinitePlace X.B.I.F) (c : X.B.I.E) (a : Fin X.B.I.n → X.B.I.E) :
    rv X.B.I v (c • a) = X.B.I.φ v c • rv X.B.I v a := by
  unfold rv
  rw [← Matrix.mulVec_smul]
  congr 1
  ext i
  simp

theorem phiV_add (C : Choice X 1) (τ : D.what₂.Tau) (x y : (VS D).V) :
    GlobalTheory.TypeAsm.phiV C τ (x + y) = GlobalTheory.TypeAsm.phiV C τ x + GlobalTheory.TypeAsm.phiV C τ y := by
  unfold GlobalTheory.TypeAsm.phiV
  rw [crd_add, rv_add, Matrix.mulVec_add]

theorem phiV_smul (C : Choice X 1) (τ : D.what₂.Tau) (c : D.host.E) (x : (VS D).V) :
    GlobalTheory.TypeAsm.phiV C τ (c • x) = embS D τ c • GlobalTheory.TypeAsm.phiV C τ x := by
  unfold GlobalTheory.TypeAsm.phiV
  rw [crd_smul, rv_smul, Matrix.mulVec_smul, X.φ_eq, pl_vOf, RingEquiv.apply_symm_apply]

theorem phiV_herm (C : Choice X 1) (τ : D.what₂.Tau) (x y : (VS D).V) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) (GlobalTheory.TypeAsm.phiV C τ x) (GlobalTheory.TypeAsm.phiV C τ y) =
      embS D τ ((GlobalTheory.TypeAsm.HV D).B x y) := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have hQ : ∀ w, C.Q τ *ᵥ (C.Qi τ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  unfold Formalism.QuantumDeterminants.herm GlobalTheory.TypeAsm.phiV
  rw [← hH, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Formalism.L2.SG.Pf.LTL.star_dot_conjT, hQ, hQ]
  have h2 := Formalism.L2.SG.Pf.hJ_rv X (vOf X τ) (X.crd y) (X.crd x)
  unfold hJ at h2
  rw [h2, X.φ_eq, pl_vOf, Formalism.L2.SG.PoincareInHH.Cut.hform_crd]
  rfl

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm.GramPf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {X : HidaSetting D}

theorem phiV_span (C : Choice X 1) (τ : D.what₂.Tau) :
    Submodule.span ℂ (Set.range (GlobalTheory.TypeAsm.phiV C τ)) = ⊤ := by
  obtain ⟨hQiQ, _, _, _⟩ := C.isT τ
  have hP : (X.B.I.P (vOf X τ))⁻¹ * X.B.I.P (vOf X τ) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit _))
  have hb : ∀ i : Fin X.B.I.n, C.Qi τ *ᵥ ((X.B.I.P (vOf X τ))⁻¹ *ᵥ Pi.single i 1) ∈
      Set.range (GlobalTheory.TypeAsm.phiV C τ) := by
    intro i
    refine ⟨Formalism.L2.SG.Pf.toV X (Pi.single i 1), ?_⟩
    unfold GlobalTheory.TypeAsm.phiV rv
    rw [Formalism.L2.SG.Pf.crd_toV]
    congr 2
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [eq_top_iff]
  intro w _
  have e : C.Qi τ * (X.B.I.P (vOf X τ))⁻¹ * X.B.I.P (vOf X τ) * C.Q τ = 1 := by
    rw [Matrix.mul_assoc (C.Qi τ), hP, Matrix.mul_one, hQiQ]
  have hw : w = C.Qi τ *ᵥ ((X.B.I.P (vOf X τ))⁻¹ *ᵥ (X.B.I.P (vOf X τ) *ᵥ (C.Q τ *ᵥ w))) := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, e, Matrix.one_mulVec]
  rw [hw]
  set v := X.B.I.P (vOf X τ) *ᵥ (C.Q τ *ᵥ w)
  rw [pi_eq_sum_univ v]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  have := hb i
  convert this using 3
  ext j
  simp [Pi.single_apply, eq_comm]

theorem gamT_mem (C : Choice X 1) {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u) (τ : D.what₂.Tau) :
    GlobalTheory.TypeAsm.gamT C t τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
  Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _

theorem gamT_act (C : Choice X 1) {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u) (τ : D.what₂.Tau)
    (y : (VS D).V) : GlobalTheory.TypeAsm.gamT C t τ *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (t.lin y) := by
  obtain ⟨_, hQQi, _, _⟩ := C.isT τ
  obtain ⟨M, _, hM1, _, hM3⟩ := t.rep.2.1
  have hM1' : uMat (t.pt.1 (vOf X τ)) = (X.B.I.P (vOf X τ))⁻¹ *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) * X.B.I.P (vOf X τ) := hM1 _
  have hM3' : X.crd (t.lin y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := hM3 y
  unfold GlobalTheory.TypeAsm.gamT GlobalTheory.TypeAsm.phiV Formalism.L2.SG.RealObj.trG
  rw [hM3', ← Formalism.L2.SG.Pf.rv_mulVec X (vOf X τ), ← hM1']
  have hQ : ∀ w, C.Q τ *ᵥ (C.Qi τ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  simp only [← Matrix.mulVec_mulVec]
  rw [hQ]

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm.GramPf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {X : HidaSetting D}

theorem frq_fvec {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u) (b : Fin (D.R.rS + 1)) :
    (frq X t.rep).fl.fvec b = t.lin ((X.Fu u).fvec b) := by
  have h : (frq X t.rep).fl = mapFlag t.lin t.rep.2.2.1 (X.Fu u) := by
    unfold frq mapLF
    simp only [dif_pos t.rep.2.2.1]
    rfl
  rw [h]
  refine Fin.lastCases ?_ (fun b' => ?_) b
  · simp only [FlagG.fvec, Fin.snoc_last]
    rfl
  · simp only [FlagG.fvec, Fin.snoc_castSucc]
    rfl

theorem zhat_gamT (C : Choice X 1) {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u) (τ : D.what₂.Tau)
    (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (GlobalTheory.TypeAsm.gamT C t τ) a b =
      ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl a b) := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  obtain ⟨M, _, hM1, _, hM3⟩ := t.rep.2.1
  have hM1' : uMat (t.pt.1 (vOf X τ)) = (X.B.I.P (vOf X τ))⁻¹ *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) * X.B.I.P (vOf X τ) := hM1 _
  have hM3' : ∀ y, X.crd (t.lin y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := hM3
  have hA : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (GlobalTheory.TypeAsm.gamT C t τ) a b =
      hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a)
        (uMat (t.pt.1 (vOf X τ)) *ᵥ (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) b)) := by
    unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm GlobalTheory.TypeAsm.gamT Formalism.L2.SG.RealObj.trG hJ
    rw [← hH, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT]
    congr 1
    simp only [Matrix.mulVec_mulVec]
    congr 1
    rw [show (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ *
        (C.Qi τ * uMat (t.pt.1 (vOf X τ)) * C.Q τ) =
      (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) * uMat (t.pt.1 (vOf X τ)) * C.Q τ by
        simp only [Matrix.mul_assoc], hQQi]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hC : ∀ y, uMat (t.pt.1 (vOf X τ)) *ᵥ rv X.B.I (vOf X τ) y =
      rv X.B.I (vOf X τ) ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
    intro y
    rw [hM1']
    exact Formalism.L2.SG.Pf.rv_mulVec X (vOf X τ) _ y
  rw [hA, Formalism.L2.SG.Pf.LTL.Q_fvec C u τ a, Formalism.L2.SG.Pf.LTL.Q_fvec C u τ b, Matrix.mulVec_smul, hC, ← hM3',
    Formalism.L2.SG.Pf.LTL.hJ_smul_real, Formalism.L2.SG.Pf.hJ_rv, X.φ_eq, pl_vOf, Formalism.L2.SG.PoincareInHH.Cut.hform_crd]
  unfold Formalism.MainNotions.S.Zhat brS
  rw [frq_fvec]

theorem det_scaled {K : Type*} [Field K] {N : ℕ} (ρ : Fin N → ℂ) (M : Matrix (Fin N) (Fin N) K) (e : K →+* ℂ) :
    (Matrix.of fun i j => ρ i * ρ j * e (M i j)).det = (∏ i, ρ i) ^ 2 * e M.det := by
  have h : (Matrix.of fun i j => ρ i * ρ j * e (M i j)) = Matrix.diagonal ρ * e.mapMatrix M * Matrix.diagonal ρ := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, RingHom.map_det]
  ring

theorem dmin_gamT (C : Choice X 1) {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u) (τ : D.what₂.Tau)
    (l : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (GlobalTheory.TypeAsm.gamT C t τ) l.castSucc =
      (∏ i : Fin l.val, ((rhoF D (Fin.castLE (by omega) i) : ℝ) : ℂ)) ^ 2 *
        embS D τ (Formalism.MainNotions.S.Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l.val) := by
  have hZ : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (GlobalTheory.TypeAsm.gamT C t τ) =
      Matrix.of fun a b => ((rhoF D a : ℝ) : ℂ) * ((rhoF D b : ℝ) : ℂ) *
        embS D τ (Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl a b) := by
    ext a b
    rw [zhat_gamT, Matrix.of_apply]
    push_cast
    ring
  unfold Formalism.QuantumDeterminants.Dmin Formalism.MainNotions.S.Dl leadMinorE
  rw [dif_pos (by omega), hZ, ← det_scaled]
  rfl

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm.GramPf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {X : HidaSetting D}

theorem rdE_pos' (D : D7) : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero D.host.E))) _

theorem frameExp_cast (r l : ℕ) (hl : l ≤ r + 1) :
    (frameExp r l : ℝ) = ∑ i : Fin l, ((r : ℝ) - (i : ℕ)) := by
  induction l with
  | zero => simp [frameExp]
  | succ l ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [← ih (by omega)]
    unfold frameExp
    rw [show Finset.Icc 1 (l + 1) = Finset.Ioc 0 (l + 1) from Finset.val_inj.mp rfl,
      show Finset.Icc 1 l = Finset.Ioc 0 l from Finset.val_inj.mp rfl, Finset.sum_Ioc_succ_top (Nat.zero_le l)]
    push_cast
    rw [Nat.cast_sub (by omega)]

theorem prod_rho (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    ∏ i : Fin l, rhoF D (Fin.castLE hl i) = D.host.rdE ^ (-(frameExp D.R.rS l : ℝ)) := by
  rw [frameExp_cast _ _ hl, ← Finset.sum_neg_distrib, Real.rpow_sum_of_pos (rdE_pos' D)]
  rfl

theorem norm_dmin (l : ℕ) (hl : l ≤ D.R.rS + 1) (x : ℂ) :
    ‖(∏ i : Fin l, ((rhoF D (Fin.castLE hl i) : ℝ) : ℂ)) ^ 2 * x‖ =
      ‖x‖ * D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ))) := by
  rw [← Complex.ofReal_prod, prod_rho l hl, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (rdE_pos' D) _), ← Real.rpow_natCast,
    ← Real.rpow_mul (rdE_pos' D).le, mul_comm ‖x‖]
  congr 2
  push_cast
  ring

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gramC_holds : GramC := by
  intro D X Y u C τ
  refine ⟨⟨GramPf.phiV_add C τ, GramPf.phiV_smul C τ, GramPf.phiV_herm C τ, GramPf.phiV_span C τ⟩,
    fun t => ⟨GramPf.gamT_mem C t τ, GramPf.gamT_act C t τ, fun l => ?_⟩⟩
  rw [GramPf.dmin_gamT, GramPf.norm_dmin]
  rfl

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoRescaledMeasureGaugeUnitBody
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
open scoped Pointwise

noncomputable section

namespace GlobalTheory.IwConst.VagBody

theorem integral_squeeze {X : Type} [MeasurableSpace X] (ν : Measure X) (φ : X → ℝ) (A B : Set X)
    (hφ : Measurable φ) (hA : MeasurableSet A) (hB : MeasurableSet B) (hB' : ν B ≠ ⊤)
    (h0 : ∀ x, 0 ≤ φ x) (h1 : ∀ x, φ x ≤ 1) (hA1 : ∀ x ∈ A, φ x = 1) (hB0 : ∀ x, x ∉ B → φ x = 0) :
    ν.real A ≤ ∫ x, φ x ∂ν ∧ ∫ x, φ x ∂ν ≤ ν.real B := by
  have hsub : A ⊆ B := by
    intro x hx
    by_contra hxB
    have h := hA1 x hx
    rw [hB0 x hxB] at h
    exact zero_ne_one h
  have hA' : ν A ≠ ⊤ := ne_top_of_le_ne_top hB' (measure_mono hsub)
  have lo : ∀ x, A.indicator (fun _ => (1:ℝ)) x ≤ φ x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, hA1 x hx]
    · simp only [Set.indicator, hx, if_false]
      exact h0 x
  have hi : ∀ x, φ x ≤ B.indicator (fun _ => (1:ℝ)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      exact h1 x
    · simp only [Set.indicator, hx, if_false]
      exact le_of_eq (hB0 x hx)
  have iB : Integrable (B.indicator fun _ => (1:ℝ)) ν :=
    (integrable_indicator_iff hB).2 (integrableOn_const hB')
  have iA : Integrable (A.indicator fun _ => (1:ℝ)) ν :=
    (integrable_indicator_iff hA).2 (integrableOn_const hA')
  have iφ : Integrable φ ν := by
    refine iB.mono' hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact hi x
  have eA : ∫ x, A.indicator (fun _ => (1:ℝ)) x ∂ν = ν.real A := by
    rw [integral_indicator_const _ hA, smul_eq_mul, mul_one]
  have eB : ∫ x, B.indicator (fun _ => (1:ℝ)) x ∂ν = ν.real B := by
    rw [integral_indicator_const _ hB, smul_eq_mul, mul_one]
  refine ⟨?_, ?_⟩
  · rw [← eA]
    exact integral_mono iA iφ lo
  · rw [← eB]
    exact integral_mono iφ iB hi

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem isCompact_body (ρ : V → ℝ) (hc : Continuous ρ) (h0 : ∀ v, 0 ≤ ρ v)
    (hs : ∀ s : ℝ, 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) (hd : ∀ v, ρ v = 0 → v = 0) (t : ℝ) :
    IsCompact {v | ρ v ≤ t} := by
  obtain ⟨m, hm, hmρ⟩ : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Metric.sphere (0 : V) 1, m ≤ ρ u := by
    rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨u0, hu0, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hne hc.continuousOn
      refine ⟨ρ u0, ?_, fun u hu => isMinOn_iff.1 hmin u hu⟩
      rcases (h0 u0).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz : u0 = 0 := hd u0 h.symm
        rw [mem_sphere_zero_iff_norm, hz, norm_zero] at hu0
        exact zero_ne_one hu0
  have hbd : ∀ v, m * ‖v‖ ≤ ρ v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, norm_zero, mul_zero]
      exact h0 0
    · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
      have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 := hmρ _ hu
      have h2 : ρ v = ‖v‖ * ρ (‖v‖⁻¹ • v) := by
        rw [← hs ‖v‖ (norm_nonneg v), smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [h2]
      nlinarith
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hc continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : V)) (r := t / m)).subset ?_
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hm]
  have h3 := hbd v
  have h4 : ρ v ≤ t := hv
  nlinarith

omit [FiniteDimensional ℝ V] in

theorem body_eq_smul (ρ : V → ℝ) (hs : ∀ s : ℝ, 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) {t : ℝ} (ht : 0 < t) :
    {v | ρ v ≤ t} = t • {v | ρ v ≤ 1} := by
  ext v
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', Set.mem_setOf_eq, Set.mem_setOf_eq,
    hs _ (inv_nonneg.2 ht.le), inv_mul_le_iff₀ ht, mul_one]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in

theorem exists_cutoff (ρ : V → ℝ) (hc : Continuous ρ) {s t : ℝ} (hst : s < t) :
    ∃ φ : V → ℝ, Continuous φ ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ 1) ∧ (∀ x, ρ x ≤ s → φ x = 1) ∧
      ∀ x, ¬ ρ x ≤ t → φ x = 0 := by
  have hpos : 0 < t - s := sub_pos.2 hst
  refine ⟨fun x => max 0 (min 1 ((t - ρ x) / (t - s))), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.max (continuous_const.min ((continuous_const.sub hc).div_const _))
  · intro x
    exact le_max_left _ _
  · intro x
    exact max_le zero_le_one (min_le_left _ _)
  · intro x hx
    have h1 : 1 ≤ (t - ρ x) / (t - s) := by
      rw [le_div_iff₀ hpos]
      linarith
    show max 0 (min 1 ((t - ρ x) / (t - s))) = 1
    rw [min_eq_left h1, max_eq_right zero_le_one]
  · intro x hx
    have h1 : (t - ρ x) / (t - s) ≤ 0 := by
      rw [div_le_iff₀ hpos]
      push_neg at hx
      linarith
    show max 0 (min 1 ((t - ρ x) / (t - s))) = 0
    exact max_eq_left (le_trans (min_le_right _ _) h1)

theorem tendsto_body : ∀ (α V : Type) [MeasurableSpace α] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure α) [IsFiniteMeasure μ] (c : α → V) (lam : Measure V) [lam.IsAddHaarMeasure] (d : ℕ) (ρ : V → ℝ), Measurable c → Continuous ρ → (∀ v, 0 ≤ ρ v) → (∀ (s : ℝ), 0 ≤ s → ∀ v, ρ (s • v) = s * ρ v) → (∀ v, ρ v = 0 → v = 0) → Vag μ c lam d → Filter.Tendsto (fun r : ℝ => μ {g | ρ (c g) ≤ r} / ENNReal.ofReal (r ^ d)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam {v | ρ v ≤ 1})) := by
  intro α V _ _ _ _ _ _ μ _ c lam _ d ρ hcm hρ h0 hs hd hv
  have hK : ∀ t, IsCompact {v | ρ v ≤ t} := fun t => isCompact_body ρ hρ h0 hs hd t
  have hfin : ∀ t, lam {v | ρ v ≤ t} ≠ ⊤ := fun t => (hK t).measure_lt_top.ne
  have hmV : ∀ t, MeasurableSet {v | ρ v ≤ t} := fun t =>
    measurableSet_le hρ.measurable measurable_const
  have hmα : ∀ t, MeasurableSet {g | ρ (c g) ≤ t} := fun t =>
    measurableSet_le (hρ.measurable.comp hcm) measurable_const
  have hmβ : ∀ r t : ℝ, MeasurableSet {g | ρ (r • c g) ≤ t} := fun r t =>
    measurableSet_le (hρ.measurable.comp (hcm.const_smul r)) measurable_const
  have hhom : ∀ r : ℝ, 0 < r → ∀ v, ρ (r⁻¹ • v) = r⁻¹ * ρ v := fun r hr v =>
    hs _ (inv_nonneg.2 hr.le) v
  have hscale : ∀ x : ℝ, 0 < x →
      lam.real {v | ρ v ≤ x} = x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1} := by
    intro x hx
    simp only [measureReal_def]
    rw [body_eq_smul ρ hs hx, Measure.addHaar_smul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), abs_of_pos (pow_pos hx _)]
  have hcont : Filter.Tendsto (fun x : ℝ => x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1})
      (nhds 1) (nhds (lam.real {v | ρ v ≤ 1})) := by
    have h : Filter.Tendsto (fun x : ℝ => x ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1})
        (nhds 1) (nhds ((1 : ℝ) ^ Module.finrank ℝ V * lam.real {v | ρ v ≤ 1})) :=
      ((continuous_pow _).mul continuous_const).tendsto 1
    rwa [one_pow, one_mul] at h
  have up : ∀ a, lam.real {v | ρ v ≤ 1} < a → ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} < a := by
    intro a ha
    have h2 := hcont.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
    obtain ⟨x, hxa, hx⟩ := ((h2.eventually (gt_mem_nhds ha)).and (Ioo_mem_nhdsGT one_lt_two)).exists
    obtain ⟨φ, hφc, hφ0, hφ1, hφA, hφB⟩ := exists_cutoff ρ hρ hx.1
    have hsupp : HasCompactSupport φ := HasCompactSupport.intro (hK x) (fun v hv' => hφB v hv')
    have hlim : ∫ v, φ v ∂lam < a := by
      have h3 := (integral_squeeze lam φ _ _ hφc.measurable (hmV 1) (hmV x) (hfin x) hφ0 hφ1
        hφA hφB).2
      have h4 := hscale x (by linarith [hx.1])
      linarith
    filter_upwards [(hv φ hφc hsupp).eventually (gt_mem_nhds hlim), self_mem_nhdsWithin] with r hr hr0
    have hr0' : 0 < r := hr0
    have hsq := (integral_squeeze μ (fun g => φ (r⁻¹ • c g)) _ _
      (hφc.measurable.comp (hcm.const_smul r⁻¹)) (hmα r) (hmβ r⁻¹ x) (measure_ne_top _ _)
      (fun g => hφ0 _) (fun g => hφ1 _)
      (fun g hg => hφA _ (by rw [hhom r hr0', inv_mul_le_iff₀ hr0', mul_one]; exact hg))
      (fun g hg => hφB _ hg)).1
    calc (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r}
        ≤ (r ^ d)⁻¹ * ∫ g, φ (r⁻¹ • c g) ∂μ :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.2 (pow_nonneg hr0'.le d))
      _ < a := hr
  have lo : ∀ a, a < lam.real {v | ρ v ≤ 1} → ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      a < (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} := by
    intro a ha
    have h2 := hcont.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    obtain ⟨x, hxa, hx⟩ := ((h2.eventually (lt_mem_nhds ha)).and (Ioo_mem_nhdsLT zero_lt_one)).exists
    obtain ⟨φ, hφc, hφ0, hφ1, hφA, hφB⟩ := exists_cutoff ρ hρ hx.2
    have hsupp : HasCompactSupport φ := HasCompactSupport.intro (hK 1) (fun v hv' => hφB v hv')
    have hlim : a < ∫ v, φ v ∂lam := by
      have h3 := (integral_squeeze lam φ _ _ hφc.measurable (hmV x) (hmV 1) (hfin 1) hφ0 hφ1
        hφA hφB).1
      have h4 := hscale x hx.1
      linarith
    filter_upwards [(hv φ hφc hsupp).eventually (lt_mem_nhds hlim), self_mem_nhdsWithin] with r hr hr0
    have hr0' : 0 < r := hr0
    have hsq := (integral_squeeze μ (fun g => φ (r⁻¹ • c g)) _ _
      (hφc.measurable.comp (hcm.const_smul r⁻¹)) (hmβ r⁻¹ x) (hmα r) (measure_ne_top _ _)
      (fun g => hφ0 _) (fun g => hφ1 _) (fun g hg => hφA _ hg)
      (fun g hg => hφB _ (by rw [hhom r hr0', inv_mul_le_iff₀ hr0', mul_one]; exact hg))).2
    calc a < (r ^ d)⁻¹ * ∫ g, φ (r⁻¹ • c g) ∂μ := hr
      _ ≤ (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r} :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.2 (pow_nonneg hr0'.le d))
  have hreal : Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * μ.real {g | ρ (c g) ≤ r})
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam.real {v | ρ v ≤ 1})) :=
    tendsto_order.2 ⟨lo, up⟩
  have h5 := ENNReal.tendsto_ofReal hreal
  rw [measureReal_def, ENNReal.ofReal_toReal (hfin 1)] at h5
  refine h5.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : 0 < r := hr
  have hp : 0 < r ^ d := pow_pos hr0 d
  rw [measureReal_def, ENNReal.ofReal_mul (inv_nonneg.2 hp.le),
    ENNReal.ofReal_toReal (measure_ne_top _ _), div_eq_mul_inv, ENNReal.ofReal_inv_of_pos hp, mul_comm]

end GlobalTheory.IwConst.VagBody
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaSmulCompletedLatticeIffTypePrimeMulStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_smul_completedLattice_iff_typePrimeMul : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (VS D) D.R.rS T) (F'0 : LFlag (VS D) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ (Λ : G.Lt) (x : (G.S (below D P)).V), (G.S (below D P)).InTh ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) Λ) x ↔ x ∈ (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  first | exact @GlobalTheory.HL.ThetaG.inTh_lat_iff | exact GlobalTheory.HL.ThetaG.inTh_lat_iff | (intros; apply GlobalTheory.HL.ThetaG.inTh_lat_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelProductActionMeasurePreserving
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem actM_measurePreserving (E : Type) [Field E] [NumberField E] (k r : ℕ)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (hN : ∀ w, gM A γ w ∈ Nset k r) :
    MeasurePreserving (actM A γ) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1)
      (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) := by
  have hH := (GlobalTheory.T.haar_lie_nilpotent_coordinates k r).1
  haveI : SigmaFinite (haarLie (Nset k r) 1) := hH.1
  have hf : ∀ w, MeasurePreserving (lmulM (gM A γ w)) (haarLie (Nset k r) 1) (haarLie (Nset k r) 1) :=
    fun w => ⟨GlobalTheory.Amp.StabMeas.meas_lmul _, hH.2.2.2 _ (hN w)⟩
  exact measurePreserving_pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) (fun _ => haarLie (Nset k r) 1) hf

end GlobalTheory.SnMass.VolN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarySubgroupChartSurjectiveNearOriginStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySubgroupChart_surjective_near_origin : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < ρ → ∃ g : Formalism.REAL.UJ ε, uMat g - 1 ∈ A ∧ Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < δ ∧ (WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) = x := by
  first | exact @GlobalTheory.GaugeSubChartSurj.chart_surj | exact GlobalTheory.GaugeSubChartSurj.chart_surj | (intros; apply GlobalTheory.GaugeSubChartSurj.chart_surj <;> assumption)
end

