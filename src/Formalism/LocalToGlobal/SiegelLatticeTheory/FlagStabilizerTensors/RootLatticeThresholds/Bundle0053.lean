import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFrameW
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0050
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0041
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0018
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0036
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0042
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0017
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0036
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLoc
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx

section Gen

variable {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {g : ℕ}

theorem zmod_Wq (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {c : I.E ⊗[I.F] Af I.F} (h : ZMod' I g c) : c ∈ Wq I w := by
  obtain ⟨t, ht, rfl⟩ := h
  have : (g : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    have := iE_mem (I := I) hg
    simpa [iE] using this
  exact Wq_mul' this ht

theorem zmod_sg {c : I.E ⊗[I.F] Af I.F} (h : ZMod' I g c) : ZMod' I g (sg I c) := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨sg I t, DictLat.sigR_int I ht, by rw [map_mul, sg_natCast]⟩

theorem mL_le (hg : (g : 𝓞 I.E) ∈ w.asIdeal) : mL I g ≤ Lq I w := by
  unfold mL
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have := smul_mem I w hg hx
  simpa using this

theorem hhat_neg_left (u v : Fin I.n → I.E ⊗[I.F] Af I.F) : hhat I (-u) v = -hhat I u v := by
  have := hhat_sub_left I 0 u v
  rwa [zero_sub, DictLat.hhat_zero_left, zero_sub] at this

theorem hhat_neg_right (u v : Fin I.n → I.E ⊗[I.F] Af I.F) : hhat I u (-v) = -hhat I u v := by
  have := hhat_sub_right I u 0 v
  rwa [zero_sub, DictLat.hhat_zero_right, zero_sub] at this

theorem pair_right (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {u : Fin I.n → I.E ⊗[I.F] Af I.F} (hu : u ∈ I.Lf)
    {S : Set (VA I)} (hS : ∀ s ∈ S, hhat I u s ∈ Wq I w) {v : VA I} (hv : InMod I g S v) : hhat I u v ∈ Wq I w := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  clear hv
  rw [DictLat.hhat_add_right]
  refine add_mem ?_ (hhat_Lq_right hu (mL_le hg hz))
  induction hy using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero => rw [DictLat.hhat_zero_right]; exact zero_mem _
  | add a b _ _ ha hb => rw [DictLat.hhat_add_right]; exact add_mem ha hb
  | smul r a _ ha =>
    show hhat I u ((r : I.E ⊗[I.F] Af I.F) • a) ∈ Wq I w
    rw [DictLat.hhat_smul_right]; exact Wq_mul ha r.2

theorem pair_left (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {v : Fin I.n → I.E ⊗[I.F] Af I.F} (hv : v ∈ I.Lf)
    {S : Set (VA I)} (hS : ∀ s ∈ S, hhat I s v ∈ Wq I w) {u : VA I} (hu : InMod I g S u) : hhat I u v ∈ Wq I w := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hu
  clear hu
  rw [DictLat.hhat_add_left]
  refine add_mem ?_ ?_
  · induction hy using Submodule.span_induction with
    | mem s hs => exact hS s hs
    | zero => rw [DictLat.hhat_zero_left]; exact zero_mem _
    | add a b _ _ ha hb => rw [DictLat.hhat_add_left]; exact add_mem ha hb
    | smul r a _ ha =>
      show hhat I ((r : I.E ⊗[I.F] Af I.F) • a) v ∈ Wq I w
      rw [DictLat.hhat_smul_left]; exact Wq_mul ha (DictLat.sigR_int I r.2)
  · have hgW : (g : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
      have := iE_mem (I := I) hg
      simpa [iE] using this
    unfold mL at hz
    induction hz using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨x, hx, rfl⟩ := hs
      rw [DictLat.hhat_smul_left, sg_natCast]
      exact Wq_mul' hgW (dual_hat_integral I x hx v hv)
    | zero => rw [DictLat.hhat_zero_left]; exact zero_mem _
    | add a b _ _ ha hb => rw [DictLat.hhat_add_left]; exact add_mem ha hb
    | smul r a _ ha =>
      show hhat I ((r : I.E ⊗[I.F] Af I.F) • a) v ∈ Wq I w
      rw [DictLat.hhat_smul_left]; exact Wq_mul ha (DictLat.sigR_int I r.2)

theorem dir_col (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {x : I.Gf} {u v : VA I} (hu : u ∈ I.Lf) {S : Set (VA I)}
    (hS : ∀ s ∈ S, hhat I u s ∈ Wq I w) (hx : InMod I g S ((I.fmat x - 1) *ᵥ v)) :
    hhat I u (I.fmat x *ᵥ v) - hhat I u v ∈ Wq I w := by
  have := pair_right hg hu hS hx
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, hhat_sub_right] at this

theorem dual_col (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {x : I.Gf} {u v : VA I} (hv : v ∈ I.Lf) {S : Set (VA I)}
    (hS : ∀ s ∈ S, hhat I s v ∈ Wq I w) (hx : InMod I g S ((I.fmat x⁻¹ - 1) *ᵥ u)) :
    hhat I u (I.fmat x *ᵥ v) - hhat I u v ∈ Wq I w := by
  have h1 : hhat I u (I.fmat x *ᵥ v) = hhat I (I.fmat x⁻¹ *ᵥ u) v := by
    have := hhat_fmat I x (I.fmat x⁻¹ *ᵥ u) v
    rw [Matrix.mulVec_mulVec, ← fmat_mul, mul_inv_cancel, fmat_one, Matrix.one_mulVec] at this
    exact this
  have := pair_left hg hv hS hx
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, hhat_sub_left, ← h1] at this

variable {p : ℕ} {r : ℕ}

theorem cong_dir (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {fr frd : Fin r → VA I} (hfrd : ∀ i, frd i ∈ I.Lf)
    (hgr : GramW w fr frd) {x : I.Gf} (i j : Fin r) {S : Set (VA I)}
    (hS : ∀ s ∈ S, ∃ j', s = fr j' ∧ j' ≠ i) (hx : InMod I g S ((I.fmat x - 1) *ᵥ fr j)) :
    CongW (w := w) p (hhat I (frd i) (I.fmat x *ᵥ fr j)) (if i = j then 1 else 0) := by
  have h1 := dir_col hg (hfrd i) (fun s hs => by
    obtain ⟨j', rfl, hj'⟩ := hS s hs
    have := hgr i j'
    rwa [if_neg (Ne.symm hj'), sub_zero] at this) hx
  refine congW_of_sub ?_ h1
  refine congW_of_sub (t := ((if i = j then 1 else 0 : ℤ) : I.E ⊗[I.F] Af I.F)) ?_ ?_
  · have := congW_intCast (I := I) (w := w) (p := p) (if i = j then 1 else 0)
    convert this using 2
    split_ifs <;> simp
  · have := hgr i j
    convert this using 2
    split_ifs <;> simp

theorem cong_dual (hg : (g : 𝓞 I.E) ∈ w.asIdeal) {fr frd : Fin r → VA I} (hfr : ∀ j, fr j ∈ I.Lf)
    (hgr : GramW w fr frd) {x : I.Gf} (i j : Fin r) {S : Set (VA I)}
    (hS : ∀ s ∈ S, ∃ i', s = frd i' ∧ i' ≠ j) (hx : InMod I g S ((I.fmat x⁻¹ - 1) *ᵥ frd i)) :
    CongW (w := w) p (hhat I (frd i) (I.fmat x *ᵥ fr j)) (if i = j then 1 else 0) := by
  have h1 := dual_col hg (hfr j) (fun s hs => by
    obtain ⟨i', rfl, hi'⟩ := hS s hs
    have := hgr i' j
    rwa [if_neg hi', sub_zero] at this) hx
  refine congW_of_sub ?_ h1
  refine congW_of_sub (t := ((if i = j then 1 else 0 : ℤ) : I.E ⊗[I.F] Af I.F)) ?_ ?_
  · have := congW_intCast (I := I) (w := w) (p := p) (if i = j then 1 else 0)
    convert this using 2
    split_ifs <;> simp
  · have := hgr i j
    convert this using 2
    split_ifs <;> simp

theorem inMod_neg {S : Set (VA I)} {v : VA I} (h : InMod I g S v) : InMod I g S (-v) := neg_mem h

end Gen

variable {D : D7} (X : HidaSetting D)

theorem hrD (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  unfold Ranks.r Ranks.rS
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

def fr (ob : Bool) (j : Fin D.R.r) : VA X.B.I :=
  if h1 : j.1 < D.R.rS then X.e0 ⟨j.1, h1⟩
  else if h2 : j.1 < D.R.rS + D.R.k then
    (if ob then X.bw ⟨j.1 - D.R.rS, by omega⟩ else X.bwd ⟨D.R.k - 1 - (j.1 - D.R.rS), by omega⟩)
  else if j.1 = D.R.rS + D.R.k then X.z0
  else if h4 : j.1 - (D.R.rS + D.R.k + 1) < D.R.rS then X.f0 ⟨D.R.rS - 1 - (j.1 - (D.R.rS + D.R.k + 1)), by omega⟩
  else 0

def frd (ob : Bool) (j : Fin D.R.r) : VA X.B.I :=
  if h1 : j.1 < D.R.rS then X.f0 ⟨j.1, h1⟩
  else if h2 : j.1 < D.R.rS + D.R.k then
    (if ob then X.bwd ⟨j.1 - D.R.rS, by omega⟩ else X.bw ⟨D.R.k - 1 - (j.1 - D.R.rS), by omega⟩)
  else if j.1 = D.R.rS + D.R.k then -X.z0
  else if h4 : j.1 - (D.R.rS + D.R.k + 1) < D.R.rS then X.e0 ⟨D.R.rS - 1 - (j.1 - (D.R.rS + D.R.k + 1)), by omega⟩
  else 0

def rv {n : ℕ} (a : Fin n) : Fin n := ⟨n - 1 - a.1, by omega⟩

@[simp] theorem rv_val {n : ℕ} (a : Fin n) : (rv a).1 = n - 1 - a.1 := rfl

theorem rv_rv {n : ℕ} (a : Fin n) : rv (rv a) = a := Fin.ext (by simp <;> omega)

theorem frame_isotropic (ob : Bool) (a : Fin D.R.rS) : fr X ob (xI (hrD D) a) = X.e0 a := by
  unfold fr; rw [dif_pos (show (xI (hrD D) a).1 < D.R.rS from a.2)]; rfl

theorem fr_w (ob : Bool) (i : Fin D.R.k) : fr X ob (wI (hrD D) i) = if ob then X.bw i else X.bwd (rv i) := by
  unfold fr
  rw [dif_neg (show ¬ (wI (hrD D) i).1 < D.R.rS by simp), dif_pos (show (wI (hrD D) i).1 < D.R.rS + D.R.k by simp)]
  congr 1 <;> congr 1 <;> ext <;> simp

theorem frame_anisotropic (ob : Bool) : fr X ob (zI (hrD D)) = X.z0 := by
  unfold fr
  rw [dif_neg (show ¬ (zI (hrD D)).1 < D.R.rS by simp <;> omega),
    dif_neg (show ¬ (zI (hrD D)).1 < D.R.rS + D.R.k by simp), if_pos (by simp)]

theorem fr_y (ob : Bool) (a : Fin D.R.rS) : fr X ob (yI (hrD D) a) = X.f0 (rv a) := by
  unfold fr
  rw [dif_neg (show ¬ (yI (hrD D) a).1 < D.R.rS by simp <;> omega),
    dif_neg (show ¬ (yI (hrD D) a).1 < D.R.rS + D.R.k by simp <;> omega), if_neg (by simp <;> omega),
    dif_pos (show (yI (hrD D) a).1 - (D.R.rS + D.R.k + 1) < D.R.rS by simp)]
  congr 1; ext; simp

theorem dual_frame_isotropic (ob : Bool) (a : Fin D.R.rS) : frd X ob (xI (hrD D) a) = X.f0 a := by
  unfold frd; rw [dif_pos (show (xI (hrD D) a).1 < D.R.rS from a.2)]; rfl

theorem frd_w (ob : Bool) (i : Fin D.R.k) : frd X ob (wI (hrD D) i) = if ob then X.bwd i else X.bw (rv i) := by
  unfold frd
  rw [dif_neg (show ¬ (wI (hrD D) i).1 < D.R.rS by simp), dif_pos (show (wI (hrD D) i).1 < D.R.rS + D.R.k by simp)]
  congr 1 <;> congr 1 <;> ext <;> simp

theorem dual_frame_anisotropic (ob : Bool) : frd X ob (zI (hrD D)) = -X.z0 := by
  unfold frd
  rw [dif_neg (show ¬ (zI (hrD D)).1 < D.R.rS by simp <;> omega),
    dif_neg (show ¬ (zI (hrD D)).1 < D.R.rS + D.R.k by simp), if_pos (by simp)]

theorem frd_y (ob : Bool) (a : Fin D.R.rS) : frd X ob (yI (hrD D) a) = X.e0 (rv a) := by
  unfold frd
  rw [dif_neg (show ¬ (yI (hrD D) a).1 < D.R.rS by simp <;> omega),
    dif_neg (show ¬ (yI (hrD D) a).1 < D.R.rS + D.R.k by simp <;> omega), if_neg (by simp <;> omega),
    dif_pos (show (yI (hrD D) a).1 - (D.R.rS + D.R.k + 1) < D.R.rS by simp)]
  congr 1; ext; simp

end Formalism.L2.SG.Pf.KppLoc
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
section
noncomputable section

open scoped Classical
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.LoopBPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X}

theorem isFundR_fundOf {u u' : D.what₂.Word} (s : TT Y u u') : LoopTerm.IsFundR s (TermOp.FundOf s) := by
  obtain ⟨hm, hex, huniq⟩ := KappaOffDiagonal.fundOf_spec (Closed.FundExistsC_holds D X Y u u') s
  refine ⟨hm, fun r _ => ?_⟩
  obtain ⟨q, hq, hqr⟩ := hex r
  refine ⟨q, ⟨hq, hqr⟩, fun q' hq' => ?_⟩
  have hmem : q' * q⁻¹ ∈ TermOp.ROinf s :=
    (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin).mul_mem hq'.1
      ((TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin).inv_mem hq)
  have e : q' * q⁻¹ * (q * r) = q' * r := by group
  have h1 := huniq (q * r) hqr (q' * q⁻¹) hmem (by rw [e]; exact hq'.2)
  exact mul_inv_eq_one.1 h1

theorem pinAll_holds (u u' : D.what₂.Word) : LoopTerm.PinAll (Y := Y) u u' := by
  intro s hrel hG
  have hAt := LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'
  have hRD := Pf.RowForm.RealDecompL.realDecompC_of X Y u u' hAt
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := Pf.RowForm.realDecompC_gamW X Y u u' hRD s hrel hG
  obtain ⟨μw, hH, hmap⟩ := NGPin.pinned_at X u u' (NGPin.pinHaarEx_of_place NGPin.placeHaar_holds) hpt
  obtain ⟨w0, hw0⟩ := hAt s.toTerm hG hrel
  have hw : s.toTerm.atPt (PairVal.ptOf s.toTerm) := PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  refine ⟨⟨PairVal.ptOf s.toTerm, μw.map (fun y => g * y * g⁻¹), TermOp.FundOf s⟩, hw, ?_, isFundR_fundOf s⟩
  exact ⟨RealObj.gamW X u u' (PairVal.ptOf s.toTerm), g, g', μw, NGPin.isPtRep_gamW X u u' hpt, hg, hg', hdec, hH,
    hmap, rfl⟩

section Covol

open Set TermOp TermOp.Vanish

theorem roinf_sub_rset {u u' : D.what₂.Word} (s : TT Y u u') {q : X.B.I.Ginf} (hq : q ∈ ROinf s) : q ∈ Rset s := by
  have hs0 : q ∈ ROset X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin := hq
  obtain ⟨z, n, hz, hzs, hn, hn'⟩ := hs0
  have hl : RatLink X (s.pt⁻¹ * z * s.pt) (s.lin⁻¹ * n * s.lin) :=
    ratLink_mul X (ratLink_mul X (ratLink_inv X s.rep.2.1) hz) s.rep.2.1
  have hs2 := Pf.nLamNinf_holds D X u' s.lam' _ _ hl hn'
  rw [Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, ← hzs] at hs2
  exact ⟨hzs ▸ Pf.nLamNinf_holds D X u s.lam z n hz hn, hs2⟩

theorem stCoord_cont (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) :
    Continuous (RealObj.stCoord X u' w γ) := by
  unfold RealObj.stCoord Formalism.L2.SG.HidaSetting.hJ
  refine continuous_pi fun v => continuous_pi fun p => continuous_const.mul ?_
  refine Continuous.dotProduct continuous_const (Continuous.matrix_mulVec continuous_const ?_)
  refine Continuous.matrix_mulVec ?_ continuous_const
  exact Units.continuous_val.comp (continuous_subtype_val.comp ((continuous_apply v).comp
    ((continuous_const.mul continuous_id).mul continuous_const)))

theorem muStab_compact (w : Point D.host.E (D.R.rS + 1)) {C : Set (InfinitePlace X.B.I.F → RealObj.FreeE w → ℂ)}
    (hC : IsCompact C) : RealObj.muStab X w C < ⊤ := by
  have e : RealObj.muStab X w = Measure.pi fun _ => Measure.pi fun _ =>
      ((D.host.ka / (X.B.g : ℝ) / Real.pi).toNNReal) • (volume : Measure ℂ) := rfl
  rw [e]
  exact hC.measure_lt_top

theorem covolPos_holds (u u' : D.what₂.Word) : LoopTerm.CovolPos (Y := Y) u u' := by
  intro s hrel hG w μR K hw hP hK
  obtain ⟨γw, g, g', μw, hrep, hg, hg', hdec, hH, hmap, rfl⟩ := hP
  obtain ⟨hσ, h0, hconc, hinvw⟩ := hH
  obtain ⟨hKm, hKu⟩ := hK
  have := TermOp.Vanish.ROsub_countable X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin
  have hcc : Continuous fun y : X.B.I.Ginf => g * y * g⁻¹ := (continuous_const.mul continuous_id).mul continuous_const
  have hcm := hcc.measurable
  have hRm : MeasurableSet (Rset s) := (Pf.rClosedC_holds D X Y u u' s).measurableSet
  have hRc : (μw.map fun y => g * y * g⁻¹) (Rset s)ᶜ = 0 := by
    rw [Measure.map_apply hcm hRm.compl]
    exact measure_mono_null (fun y hy hySt => hy (LoopTerm.stInf_conj hg hg' hdec hySt)) hconc
  have hinv : ∀ q ∈ TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹).map (fun x => q * x) = μw.map fun y => g * y * g⁻¹ := by
    intro q hq
    have hq' := LoopTerm.stInf_conj_inv hg hg' hdec (roinf_sub_rset s hq)
    rw [Measure.map_map (measurable_const_mul q) hcm]
    have e : (fun x => q * x) ∘ (fun y => g * y * g⁻¹) =
        (fun y => g * y * g⁻¹) ∘ (fun y => (g⁻¹ * q * g) * y) := by
      funext y; simp only [Function.comp]; group
    rw [e, ← Measure.map_map hcm (measurable_const_mul _), hinvw _ hq']
  have hpre : ∀ q ∈ TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin, ∀ B, MeasurableSet B →
      (μw.map fun y => g * y * g⁻¹) ((fun x => q * x) ⁻¹' B) = (μw.map fun y => g * y * g⁻¹) B := by
    intro q hq B hB
    rw [← Measure.map_apply (measurable_const_mul q) hB, hinv q hq]

  have hpos : (μw.map fun y => g * y * g⁻¹) K ≠ 0 := by
    intro hK0
    have hd := Pf.FormAllPf.decomp (μw.map fun y => g * y * g⁻¹) (Rset s) hRc
      (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) Set.univ K MeasurableSet.univ hKm hKu
    have hz : (μw.map fun y => g * y * g⁻¹) Set.univ = 0 := by
      rw [hd]
      have : ∀ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
          (μw.map fun y => g * y * g⁻¹) (Set.univ ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K) = 0 := by
        intro q
        rw [Set.univ_inter, hpre q q.2 K hKm, hK0]
      simp only [this, tsum_zero]
    rw [Measure.measure_univ_eq_zero, Measure.map_eq_zero_iff hcm.aemeasurable] at hz
    exact h0 hz

  obtain ⟨K0, hK0c, hK0⟩ := rational_cocompact_holds D X Y u u' s
  have hK0m : MeasurableSet K0 := hK0c.isClosed.measurableSet
  have h1 : (μw.map fun y => g * y * g⁻¹) K ≤ ∑' q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) := by
    calc (μw.map fun y => g * y * g⁻¹) K = (μw.map fun y => g * y * g⁻¹) (K ∩ Rset s) :=
          (measure_inter_conull hRc).symm
      _ ≤ (μw.map fun y => g * y * g⁻¹) (⋃ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
            K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) := by
          refine measure_mono fun r hr => ?_
          obtain ⟨q, hq, hqr⟩ := hK0 r hr.2
          exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hr.1, hqr⟩
      _ ≤ _ := measure_iUnion_le _
  have h2 : ∀ q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) =
        (μw.map fun y => g * y * g⁻¹) (K0 ∩ (fun x => ((q⁻¹ : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) :
          X.B.I.Ginf) * x) ⁻¹' K) := by
    intro q
    have hB : MeasurableSet (K0 ∩ (fun x => ((q⁻¹ : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) :
        X.B.I.Ginf) * x) ⁻¹' K) := hK0m.inter (hKm.preimage (measurable_const_mul _))
    rw [← hpre q q.2 _ hB]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Subgroup.coe_inv, inv_mul_cancel_left]
    exact and_comm
  have h3 := Pf.FormAllPf.decomp (μw.map fun y => g * y * g⁻¹) (Rset s) hRc
    (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin) K0 K hK0m hKm hKu
  have h4 : ∑' q : TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin,
      (μw.map fun y => g * y * g⁻¹) (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K0) =
        (μw.map fun y => g * y * g⁻¹) K0 := by
    rw [h3]
    simp_rw [h2]
    exact (Equiv.inv (TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin)).tsum_eq
      (fun q => (μw.map fun y => g * y * g⁻¹) (K0 ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K))
  have hC : IsCompact ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0) := by
    have e : (fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0 = (fun k => g⁻¹ * k * g) '' K0 := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hy; exact ⟨g * y * g⁻¹, hy, by group⟩
      · rintro ⟨k, hk, rfl⟩; convert hk using 1; group
    rw [e]
    exact hK0c.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hfin : (μw.map fun y => g * y * g⁻¹) K0 < ⊤ := by
    rw [Measure.map_apply hcm hK0m]
    have hsc := stCoord_cont u' w γw
    have hI : IsCompact (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)) := hC.image hsc
    calc μw ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)
        ≤ μw (RealObj.stCoord X u' w γw ⁻¹' (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0))) :=
          measure_mono (Set.subset_preimage_image _ _)
      _ = RealObj.muStab X w (RealObj.stCoord X u' w γw '' ((fun y : X.B.I.Ginf => g * y * g⁻¹) ⁻¹' K0)) := by
          rw [← hmap, Measure.map_apply hsc.measurable hI.isClosed.measurableSet]
      _ < ⊤ := muStab_compact w hI
  exact ENNReal.toReal_pos hpos (lt_of_le_of_lt (h1.trans_eq h4) hfin).ne

end Covol

end Formalism.L2.SG.Pf.LoopBPin
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsSumCPf
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
open Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.SpectralTiesReal

namespace Formalism.L2.SG.PoincareAmplitudeLowerBounds

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.DataInst Formalism.L2.SG.CntLocal Formalism.L2.SG.RowsConc Formalism.L2.SG.RealObj

def AmpValLowerAll : Prop :=
  ∀ (D : D7) (T : STies D) (u u' : D.what₂.Word) (i0 i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k)
    (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf),
    u ≠ u' → Formalism.MainNotions.S.Cnt.Stand D u u' → ConcTie T.X T.Y → (∀ v, i0 v = i0' v) → PtRepExists T.X u u' 1 i0 i0' →
      NuQPin T.X u u' νq →
      Formalism.L2.SG.Pf.RowForm.ClassAbs.AmpValLowerC T.X T.Y u u'
        (Formalism.L2.SG.PairVal.vRdef D u u' (T.X.Fu u) (T.Y.what₂ u) T.Y.δ T.Y.M) i0 i0' νq

theorem tprod_alpD_pos (D : D7) (hk : 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k) (u u' : D.what₂.Word) :
    0 < ∏' p, alpD u u' p := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  set s := D.R.k - 2 * D.R.rS - 2 with hs
  have hs2 : 2 ≤ s := by omega
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hs2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have hαb := Formalism.L2.SG.Pf.alpBound_holds D hk u u'
  have hal0 : ∀ p, 0 < alpD u u' p := fun p => lt_of_lt_of_le (Real.exp_pos _) (hαb p).1
  have hlogα : Summable fun p => Real.log (alpD u u' p) := by
    refine Summable.of_norm_bounded (g := fun p => 2 * a p) (haS.mul_left 2) (fun p => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have h1 := Real.log_le_log (Real.exp_pos _) (hαb p).1
    have h2 := Real.log_le_log (hal0 p) (hαb p).2
    rw [Real.log_exp] at h1 h2
    constructor <;> linarith
  rw [← Real.rexp_tsum_eq_tprod hal0 hlogα]
  exact Real.exp_pos _

theorem rowsSumC_of (hFC : FormulaC) (hAV : AmpValLowerAll) : RowsSumC := by
  intro D T u u' i0 i0' νq Lsp κ hne hSt hCT _hg3 hk hcong hi hPR hNu hRL
  have hWD : Formalism.L2.SG.WuDecay.WuDecay T.X := hCT.2.2.2.2.1
  have hAbs : (T.Y.tO u u').AbsConv :=
    Formalism.L2.SG.Pf.absConvC_outright D T.X T.Y u u'
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Closed.FoldOKC_outright D T.X T.Y u' (Formalism.L2.SG.Closed.level_subgroup_properties T.X) hWD)
      (Formalism.L2.SG.Pf.fundExistsC_holds D T.X T.Y u u')
      (Formalism.L2.SG.Pf.KernelOfEmbedding.ooIntAll_of (Y := T.Y) hWD u u')
  have hL := Formalism.L2.SG.Pf.liftOntoC_of (fun D => Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) D T.X T.Y u u'
  have hAF : Formalism.L2.SG.PairVal.AutFin D (T.X.Fu u) (T.Y.what₂ u) := fun Λ hΛ =>
    _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u).A.T_prime.pos (T.X.Fu u) Λ ((T.Y.rowsOK u).1 Λ hΛ)
  have hAF' : Formalism.L2.SG.PairVal.AutFin D (T.X.Fu u') (T.Y.what₂ u') := fun Λ hΛ =>
    _root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u').A.T_prime.pos (T.X.Fu u') Λ ((T.Y.rowsOK u').1 Λ hΛ)
  have hLT : Formalism.L2.SG.Pf.LocCP.LocTied D := by
    obtain ⟨_, _, _, _, _, _, _, hL⟩ := hCT.2.2.2.2.2.2.1
    exact hL
  have hnc : 0 < Formalism.L2.SG.Pf.Cnt.cExpl D (T.X.Fu u) (T.Y.what₂ u) * ∏' p, alpD u u' p :=
    mul_pos (hFC D T u u' Lsp hLT hSt hcong).1 (tprod_alpD_pos D hk u u')
  exact Formalism.L2.SG.RowsAbsX.rowsSum_of_val _ κ _ i0 i0' (T.Y.FN u) (T.Y.FN u') νq hAbs hL
    (hAV D T u u' i0 i0' νq hne hSt hCT hi hPR hNu) hAF hAF' hnc

end Formalism.L2.SG.PoincareAmplitudeLowerBounds
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThresholdLevels
section
noncomputable section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.ThresholdLevels

variable (C0 : ℝ)

theorem thrRow_holds {𝒞 : FamClass} : ∀ CA : ℝ, 1 ≤ CA → Closed 𝒞 fun Fm _ => OwnEv Fm fun C' Cl x i =>
    AdmissibleBoundsFromSource.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu →
      ∀ u u' : (Fm.D x i).what₂.Word, u ≠ u' → Formalism.L2.SG.Pf.SzHypOf.ThresholdAtPlaces CA (Fm.D x i) u u' := by
  intro CA hCA

  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 40⟩, fun Fm CH _ hL => ?_⟩⟩
  have h40 : (40 : ℝ) ≤ sCl Fm := (le_sC'_sCl hL).2
  refine ⟨0, fun x _ i hH u u' _ => ?_⟩
  obtain ⟨hD, hHy, _⟩ := hH
  exact ThresholdOrder.thrAt_of_pos CA (Fm.D x i) u u' (ThresholdAtPlaceBounds.thrSet_pos_at hD hHy h40 _ hCA u u')

end Formalism.L2.SG.Pf.ThresholdLevels
end
end

