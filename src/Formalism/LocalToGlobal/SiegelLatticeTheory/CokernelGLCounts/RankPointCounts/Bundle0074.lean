import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0072
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0035
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.KapEqParts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0058
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0071
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.GramNondeg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.MemThPairs

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CjTFromBlocks
section
noncomputable section

open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

section Block

variable {K : Type*} [CommRing K] (cj : K →+* K) {n : Type*} [Fintype n] [DecidableEq n]

def cjT {m n : Type*} (A : Matrix m n K) : Matrix n m K := (A.map cj)ᵀ

theorem cjT_mul {l m n : Type*} [Fintype m] (A : Matrix l m K) (B : Matrix m n K) :
    cjT cj (A * B) = cjT cj B * cjT cj A := by
  unfold cjT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cjT_cjT {m n : Type*} (h : ∀ x, cj (cj x) = x) (A : Matrix m n K) : cjT cj (cjT cj A) = A := by
  ext i j; simp [cjT, h]

theorem cjT_fromBlocks {a b c d : Type*} (A : Matrix a c K) (B : Matrix a d K) (C : Matrix b c K) (D : Matrix b d K) :
    cjT cj (Matrix.fromBlocks A B C D) = Matrix.fromBlocks (cjT cj A) (cjT cj C) (cjT cj B) (cjT cj D) := by
  unfold cjT
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem cjT_zero {m n : Type*} : cjT cj (0 : Matrix m n K) = 0 := by
  ext i j; simp [cjT]

theorem block_cong (h : ∀ x, cj (cj x) = x) (G₁ G₁' X X' G₂ G₂' Mm U : Matrix n n K)
    (h1 : cjT cj Mm * G₁ * Mm = G₁') (h2 : cjT cj Mm * X * U = X') (h3 : cjT cj U * G₂ * U = G₂') :
    cjT cj (Matrix.fromBlocks Mm 0 0 U) * Matrix.fromBlocks G₁ X (cjT cj X) G₂ * Matrix.fromBlocks Mm 0 0 U =
      Matrix.fromBlocks G₁' X' (cjT cj X') G₂' := by
  rw [cjT_fromBlocks, cjT_zero, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [h1, h3, ← h2]
  congr 1 <;> first
    | (simp only [Matrix.mul_assoc]; done)
    | (rw [cjT_mul, cjT_mul, cjT_cjT cj h]; simp only [Matrix.mul_assoc])

end Block

section GaBlocks

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

def gDiag (p : PlF D) (T : D.host.E) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.of fun a b => frFac δ p b * (M p).L.cj (frFac δ p a) *
    (D.s.atP p).ιE (if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0)

theorem gaLoc_blocks (hA : ∀ q, Agree δ M q) (p : PlF D) (T T' : D.host.E) (Z : MatZ D) :
    GaLoc M δ p T T' Z = Matrix.fromBlocks (gDiag δ M p T) (ZhatLoc M δ p Z)
      (cjT ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (ZhatLoc M δ p Z)) (gDiag δ M p T') := by
  have hcj : (M p).L.cj = (D.s.atP p).cj := (hA p).2.2.1
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · simp [GaLoc, gDiag, Ga, phi]
  · simp [GaLoc, ZhatLoc, Ga, phi]
  · simp only [GaLoc, Matrix.of_apply, phi, Sum.elim_inl, Sum.elim_inr, Ga, Matrix.fromBlocks_apply₂₁,
      Matrix.conjTranspose_apply, cjT, Matrix.transpose_apply, Matrix.map_apply, ZhatLoc, RingHom.coe_coe]
    rw [map_mul, map_mul, (M p).L.cj_cj, hcj, Formalism.MainNotions.S.Inh.tie_cj_iota]
    ring
  · simp [GaLoc, gDiag, Ga, phi]

end GaBlocks

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoordCovolOfCut
section
noncomputable section

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S

theorem coordCovol_of_cut (hL : KapLaw) (hS : KapSurj) (hN : NOfib) (hB : BlockCovol)
    (hP : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word), ∏ p, cVal X u p = LsNc5.covolN X u / LsNc5.twoU X) :
    LsNc5.CoordCovol := by
  intro D X u FdN hF
  obtain ⟨hFm, hFex, hFu⟩ := hF
  obtain ⟨B, hBm, hBd, hB0, hlaw⟩ := hL X u
  obtain ⟨σ, hσm, hσ⟩ := hS X u
  obtain ⟨hNO, hNOmul, hNOinv, τ, hτ, hset⟩ := hN X u
  obtain ⟨-, hmulN, hinvN⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  set NO := Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u
  have hinj : Set.InjOn (blk X u) (X.NinfU u) := fun s hs s' hs' h =>
    LsNc5.kapInj D X u hs hs' (by rw [kap_eq_Φc, kap_eq_Φc, h])
  set K' := blk X u '' (FdN ∩ X.NinfU u) with hK'def
  have hK'eq : K' = σ ⁻¹' FdN := by
    ext t; constructor
    · rintro ⟨s, ⟨hsF, hsN⟩, rfl⟩
      show σ (blk X u s) ∈ FdN
      rw [hinj (hσ _).1 hsN (hσ _).2]; exact hsF
    · intro ht; exact ⟨σ t, ⟨ht, (hσ t).1⟩, (hσ t).2⟩
  have hK'm : MeasurableSet K' := by rw [hK'eq]; exact hσm hFm

  have hmulB : ∀ δ ∈ X.NinfU u, ∀ g : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
      Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B (blk X u δ) g = blk X u (δ * σ g) := by
    intro δ hδ g
    rw [hlaw δ hδ (σ g) (hσ g).1, (hσ g).2]
  have hinv : ∀ γ : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, (∀ p, γ p - τ p γ ∈ cLat X u p) →
      ∃ γ' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, (∀ p, γ' p - τ p γ' ∈ cLat X u p) ∧
        ∀ g, Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ' (Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ g) = g ∧ Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ (Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ' g) = g := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := (hset γ).2 hγ
    have hδN := hNO hδ
    have hδiN := hNO (hNOinv δ hδ)
    refine ⟨blk X u δ⁻¹, (hset _).1 ⟨δ⁻¹, hNOinv δ hδ, rfl⟩, fun g => ⟨?_, ?_⟩⟩
    · have hg := hσ g
      have hdg : δ * σ g ∈ X.NinfU u := (hmulN δ hδN (σ g) hg.1).1
      rw [hmulB δ hδN g, ← hlaw δ⁻¹ hδiN (δ * σ g) hdg, inv_mul_cancel_left, hg.2]
    · have hg := hσ g
      have hdg : δ⁻¹ * σ g ∈ X.NinfU u := (hmulN δ⁻¹ hδiN (σ g) hg.1).1
      rw [hmulB δ⁻¹ hδiN g, ← hlaw δ hδN (δ⁻¹ * σ g) hdg, mul_inv_cancel_left, hg.2]
  have hKd : ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q, ∃! γ : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
      (∀ p, γ p - τ p γ ∈ cLat X u p) ∧ Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B γ x ∈ K' := by
    intro x
    set g := σ x
    have hg := hσ x
    obtain ⟨δ, hδ, hδF⟩ := hFex g
    have hδN := hNO hδ
    refine ⟨blk X u δ, ⟨(hset _).1 ⟨δ, hδ, rfl⟩, ?_⟩, ?_⟩
    · rw [hmulB δ hδN x]
      exact ⟨δ * g, ⟨hδF, (hmulN δ hδN g hg.1).1⟩, rfl⟩
    · rintro γ' ⟨hγ', hγ'K⟩
      obtain ⟨δ', hδ', rfl⟩ := (hset γ').2 hγ'
      have hδ'N := hNO hδ'
      rw [hmulB δ' hδ'N x] at hγ'K
      obtain ⟨s, ⟨hsF, hsN⟩, hs⟩ := hγ'K
      have hs' : s = δ' * g := hinj hsN (hmulN δ' hδ'N g hg.1).1 hs
      have h1 : δ' * δ⁻¹ = 1 := hFu (δ * g) hδF (δ' * δ⁻¹) (hNOmul δ' hδ' δ⁻¹ (hNOinv δ hδ)) (by
        rw [show δ' * δ⁻¹ * (δ * g) = δ' * g by group, ← hs']; exact hsF)
      rw [mul_inv_eq_one.1 h1]
  have hfd : ∀ p, ∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k p), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u p, (a : CSpc (InfinitePlace X.B.I.F) D.R.k p) + v ∈ F := fun p => (hB X u p).2.1
  choose F hF hFd using hfd
  have hcount : ∀ p, Countable (cLat X u p) := fun p => (hB X u p).1
  have hmain := Formalism.L2.SG.NGCut.SplitEmbedding.triFundT (CBlk D.R.rS) (CSpc (InfinitePlace X.B.I.F) D.R.k) (cMeas (InfinitePlace X.B.I.F) D.R.k)
    cHgt B hBm hBd hB0 τ hτ (cLat X u) hinv F hF hFd K' hK'm hKd
  have hvol : ∀ p, cMeas (InfinitePlace X.B.I.F) D.R.k p (F p) = ENNReal.ofReal (cVal X u p) :=
    fun p => (hB X u p).2.2 (F p) (hF p) (hFd p)
  have hcv : ∀ p, 0 ≤ cVal X u p := by
    intro p
    rcases p with ((p | b) | (p | a)) <;> simp only [cVal]
    · exact mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _)
    · refine mul_nonneg (mul_nonneg ?_ (pow_nonneg (by norm_num) _)) (Real.rpow_nonneg (abs_nonneg _) _)
      exact pow_nonneg (show (0 : ℝ) ≤ Formalism.L2.SG.RealObj.Tw (D := D) u from Nat.cast_nonneg _) _
    · exact mul_nonneg (pow_nonneg (by norm_num) _) (Real.rpow_nonneg (abs_nonneg _) _)
    · exact Real.rpow_nonneg (abs_nonneg _) _

  have himg : LsNc5.kap X u '' (FdN ∩ X.NinfU u) = Ψc ⁻¹' K' := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [kap_eq_Φc, Ψc_Φc]
      exact ⟨s, hs, rfl⟩
    · rintro ⟨s, hs, hsy⟩
      refine ⟨s, hs, ?_⟩
      rw [kap_eq_Φc, hsy, Φc_Ψc]
  rw [himg]
  refine ⟨measurable_Ψc hK'm, ?_⟩
  rw [← map_Φc, Measure.map_apply measurable_Φc (measurable_Ψc hK'm)]
  have hpre : Φc ⁻¹' (Ψc ⁻¹' K') = K' := by
    ext x; simp only [Set.mem_preimage, Ψc_Φc]
  rw [hpre, hmain, Finset.prod_congr rfl fun p _ => hvol p, ← ENNReal.ofReal_prod_of_nonneg fun p _ => hcv p, hP]

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIA
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BetaI

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdNP

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

section Frame

variable (p : PlF D) {T' : D.host.E} (G : LFlag (VS D) D.R.rS T')

theorem locF'_eq (b : Fin (D.R.rS + 1)) : locF' Zd p G b = sF' Zd p b • baseChange₂ D p (frame G b) := rfl

theorem bcP_frameG (b : Fin (D.R.rS + 1)) :
    baseChange₂ D p (frame G b) = (((isUnit_sF' Zd p b).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep) • locF' Zd p G b := by
  rw [locF'_eq, smul_smul, (isUnit_sF' Zd p b).val_inv_mul, one_smul]

theorem frame_csG (i : Fin D.R.rS) : frame G i.castSucc = G.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_lastG : frame G (Fin.last D.R.rS) = G.fl.z := by
  simp [frame, FlagG.fvec]

theorem sF'_last : sF' Zd p (Fin.last D.R.rS) = 1 := by
  unfold sF'
  rw [frFac_last' Zd p, mul_one]
  unfold TermLoc.sgnP'
  split
  · exact sgnP_last p
  · simp

theorem locF'_last : locF' Zd p G (Fin.last D.R.rS) = baseChange₂ D p G.fl.z := by
  rw [locF'_eq, sF'_last, one_smul, frame_lastG]

theorem bcP_X' {x : (VS D).V} (hx : x ∈ Xsp G) : baseChange₂ D p x ∈ (locH Zd p).X (locF' Zd p G) := by
  change x ∈ Submodule.span D.host.E (Set.range G.fl.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← frame_csG, bcP_frameG Zd p G]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem baseChangeAt_perp' {m : (VS D).V} (hm : m ∈ orth (VS D) (Xsp G)) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p G)) := by
  show ∀ w ∈ (locH Zd p).X (locF' Zd p G), (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [locF'_eq, frame_csG, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _ (Submodule.subset_span ⟨i, rfl⟩), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

end Frame

theorem z_memG {T' : D.host.E} (G : LFlag (VS D) D.R.rS T') {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsLattice D.host.E Λ) (h : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (locF' Zd p G)) :
    G.fl.z ∈ Λ :=
  mem_of_bcP Zd hΛ fun p => by rw [← locF'_last Zd p G]; exact (h p).1 _

theorem coef_intG {T' : D.host.E} (G : LFlag (VS D) D.R.rS T') {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (locF' Zd p G)) (c : Fin (D.R.rS + 1) → D.host.E)
    (hc : ∑ a, c a • frame G a ∈ Λ) : IsIntegral ℤ (c (Fin.last D.R.rS)) := by
  refine int_of_loc Zd fun p => ?_
  set m := ∑ a, c a • frame G a with hm
  have hbm : baseChange₂ D p m = ∑ a, ((D.s.atP p).ιE (c a) *
      ((((isUnit_sF' Zd p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep)) • locF' Zd p G a := by
    rw [hm, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, bcP_frameG Zd p G, smul_smul]
  have hspan : baseChange₂ D p m ∈ Submodule.span (D.s.atP p).Ep (Set.range (locF' Zd p G)) := by
    rw [hbm]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h2 := (hprim p).2.2 _ (baseChange_mem_localLattice Zd hc p) hspan
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have hli := (hprim p).2.1
  have hz : ∑ a, (((o a : (Zd.M p).L.O) : (D.s.atP p).Ep) -
      (D.s.atP p).ιE (c a) * ((((isUnit_sF' Zd p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep)) •
        locF' Zd p G a = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hbm, ← ho]
    simp only [sub_eq_zero]
    rfl
  have h3 := Fintype.linearIndependent_iff.1 hli _ hz (Fin.last D.R.rS)
  have key : ∀ {a : (D.s.atP p).Ep} (h : IsUnit a), a = 1 →
      (((h.unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep) = 1 := by
    intro a h ha
    subst ha
    have : h.unit = 1 := Units.ext (IsUnit.unit_spec h)
    rw [this, inv_one, Units.val_one]
  have hone := key (isUnit_sF' Zd p (Fin.last D.R.rS)) (sF'_last Zd p)
  rw [hone, mul_one, sub_eq_zero] at h3
  rw [← h3]
  exact (o (Fin.last D.R.rS)).2

theorem exists_yG {T' : D.host.E} (G : LFlag (VS D) D.R.rS T') {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsLattice D.host.E Λ) (hSD : BwdNA.SD (VS D) Λ)
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (locF' Zd p G)) (hzX : G.fl.z ∉ Xsp G) :
    ∃ y ∈ Λ, y ∈ orth (VS D) (Xsp G) ∧ (VS D).hT y G.fl.z = 1 := by
  obtain ⟨f, hfz, hfX⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hzX inferInstance
  let ρ : Module.Dual D.host.E (VS D).V := (f G.fl.z)⁻¹ • f
  have hρz : ρ G.fl.z = 1 := by
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hfz
  have hρX : ∀ x ∈ Xsp G, ρ x = 0 := fun x hx => by
    have h1 : f x ∈ (Xsp G).map f := ⟨x, hx, rfl⟩
    rw [hfX, Submodule.mem_bot] at h1
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  have hρe : ∀ i : Fin D.R.rS, ρ (frame G i.castSucc) = 0 := fun i => by
    rw [frame_csG]; exact hρX _ (Submodule.subset_span ⟨i, rfl⟩)
  have hρl : ρ (frame G (Fin.last D.R.rS)) = 1 := by
    rw [frame_lastG, hρz]
  obtain ⟨v, hv⟩ := BwdNA.riesz (VS D) ρ
  let U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range (frame G))
  have hint : ∀ m ∈ Λ, m ∈ U → IsIntegral ℤ ((VS D).hT m v) := fun m hm hmU => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hmU
    have hρm : ρ m = c (Fin.last D.R.rS) := by
      rw [← hc, map_sum, Fin.sum_univ_castSucc]
      simp only [map_smul, smul_eq_mul, hρe, mul_zero, Finset.sum_const_zero, zero_add, hρl, mul_one]
    rw [BwdNA.hsw (VS D) v m, hv, hρm]
    exact BwdNA.isInt_star (coef_intG Zd G hprim c (by rw [hc]; exact hm))
  obtain ⟨w, hwΛ, hvw⟩ := BwdNA.dual_sum (VS D) Λ hΛ hSD U v hint
  have hw : ∀ a, (VS D).hT w (frame G a) = ρ (frame G a) := fun a => by
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hvw _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [map_sub, sub_eq_zero] at h0
    rw [BwdNA.hsw (VS D) (frame G a) w, ← h0, ← BwdNA.hsw (VS D) (frame G a) v, hv]
  refine ⟨w, hwΛ, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_, ?_⟩
  · change x ∈ Submodule.span D.host.E (Set.range G.fl.e) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [BwdNA.hsw (VS D) w (G.fl.e i), ← frame_csG, hw, hρe, star_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
    | smul c x _ hx => rw [BwdNA.hT_smulL, hx, mul_zero]
  · rw [← frame_lastG, hw, hρl]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BetaI
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfH
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohGoodPf

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace GramNePf

theorem sign_norm {l : ℕ} (hl : l ≤ D.R.rS + 1) :
    leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l *
      star (leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l) = 1 := by
  have hsub : (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)).submatrix
      (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i : Fin l => (-1 : D.host.E) ^ (D.R.rS - (Fin.castLE hl i).val)) := by
    ext i j
    rcases eq_or_ne i j with rfl | h
    · simp [ZhatOM]
    · have h' : Fin.castLE hl i ≠ Fin.castLE hl j := fun e => h (Fin.castLE_injective hl e)
      simp [ZhatOM, Matrix.one_apply_ne h', Matrix.diagonal_apply_ne _ h]
  have hdet : Formalism.MainNotions.S.leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l =
      (-1 : D.host.E) ^ (∑ i : Fin l, (D.R.rS - (Fin.castLE hl i).val)) := by
    unfold Formalism.MainNotions.S.leadMinorE
    rw [dif_pos hl, hsub, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  rw [hdet, star_pow, star_neg, star_one, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

theorem conjF_star (x : D.host.E) : D.conjF x = star x := by
  rw [D.conjF_eq]
  exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm

private lemma submatrix_castLE_mul_of_upper {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (A B : Matrix (Fin n) (Fin n) K)
    (hB : ∀ i j, j < i → B i j = 0) :
    (A * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun k => rfl)
  intro k hk
  have hkl : l ≤ k.val := by
    by_contra h
    exact hk ⟨⟨k.val, by omega⟩, Fin.ext rfl⟩
  rw [hB k (Fin.castLE hl j) (by rw [Fin.lt_def, Fin.val_castLE]; exact lt_of_lt_of_le j.isLt hkl), mul_zero]

private lemma submatrix_castLE_mul_of_lower {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (A B : Matrix (Fin n) (Fin n) K)
    (hA : ∀ i j, i < j → A i j = 0) :
    (A * B).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * B.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl) _ _ ?_ (fun k => rfl)
  intro k hk
  have hkl : l ≤ k.val := by
    by_contra h
    exact hk ⟨⟨k.val, by omega⟩, Fin.ext rfl⟩
  rw [hA (Fin.castLE hl i) k (by rw [Fin.lt_def, Fin.val_castLE]; exact lt_of_lt_of_le i.isLt hkl), zero_mul]

private lemma det_submatrix_castLE_of_isLoUni {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (L : Matrix (Fin n) (Fin n) K)
    (hL : IsLoUni L) : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  have hb : (L.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := by simpa using hij
    show L (Fin.castLE hl i) (Fin.castLE hl j) = 0
    exact (hL _ _).1 (by rw [Fin.lt_def, Fin.val_castLE, Fin.val_castLE]; exact hij')
  rw [Matrix.det_of_lowerTriangular _ hb]
  exact Finset.prod_eq_one (fun i _ => (hL _ _).2 rfl)

private lemma det_submatrix_castLE_of_isUpUni {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (U : Matrix (Fin n) (Fin n) K)
    (hU : IsUpUni U) : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  have hb : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := by simpa using hij
    show U (Fin.castLE hl i) (Fin.castLE hl j) = 0
    exact (hU _ _).1 (by rw [Fin.lt_def, Fin.val_castLE, Fin.val_castLE]; exact hij')
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one (fun i _ => (hU _ _).2 rfl)

private lemma det_submatrix_castLE_LPU_eq {K : Type*} [Field K] {n l : ℕ} (hl : l ≤ n) (L P U : Matrix (Fin n) (Fin n) K)
    (hL : IsLoUni L) (hU : IsUpUni U) :
    ((L * P * U).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (P.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  rw [submatrix_castLE_mul_of_upper hl _ _ (fun i j h => (hU i j).1 h), submatrix_castLE_mul_of_lower hl _ _ (fun i j h => (hL i j).1 h),
    Matrix.det_mul, Matrix.det_mul, det_submatrix_castLE_of_isLoUni hl L hL, det_submatrix_castLE_of_isUpUni hl U hU, one_mul, mul_one]

private lemma zhatOM_eq_mul_zhatOM_one {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM Z = Z * ZhatOM (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) := by
  ext a b
  simp [ZhatOM, Matrix.mul_apply, Matrix.one_apply]
  try ring

theorem gflag_ne (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (hC : Ctx γ Z) (hZ : ZhatL (lf D F0) F'₂ = Z) :
    Gflag (lf D F0).fl F'₂.fl ≠ 0 := by
  obtain ⟨w, -, w', hG, -, hA⟩ := hC
  obtain ⟨L, U, hL, hU, hM⟩ := hA
  have hS : ∀ i j : Fin (D.R.rS + 1), j < i →
      ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) i j = 0 := by
    intro i j h
    simp [ZhatOM, Matrix.one_apply_ne (ne_of_gt h)]
  have hsq : ∀ l, l ≤ D.R.rS + 1 →
      Formalism.MainNotions.S.leadMinorE Z l * star (Formalism.MainNotions.S.leadMinorE Z l) = Dmin w' l * D.conjF (Dmin w' l) := by
    intro l hl
    have h1 : Dmin w' l = Formalism.MainNotions.S.leadMinorE Z l *
        Formalism.MainNotions.S.leadMinorE (ZhatOM (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)) l := by
      unfold Dmin Formalism.MainNotions.S.leadMinorE
      simp only [dif_pos hl]
      rw [← Matrix.det_mul, ← submatrix_castLE_mul_of_upper hl _ _ hS, ← zhatOM_eq_mul_zhatOM_one, hM, det_submatrix_castLE_LPU_eq hl _ _ _ hL hU]
    rw [h1, conjF_star, star_mul']
    linear_combination (-(Formalism.MainNotions.S.leadMinorE Z l * star (Formalism.MainNotions.S.leadMinorE Z l))) * sign_norm hl
  intro h0
  apply hG
  unfold Formalism.MainNotions.S.LocalSplitGroups.Gpt
  rw [← hsq _ le_rfl, ← hsq _ (Nat.le_succ _)]
  refine Eq.trans ?_ h0
  unfold Formalism.MainNotions.S.Gflag Formalism.MainNotions.S.Dl
  rw [show Formalism.MainNotions.S.Zhat (lf D F0).fl F'₂.fl = Z from hZ]
  rfl

end GramNePf

open GramNePf

theorem globGramNe_holds : GlobGramNe u u' F0 what₂ := by
  intro _ γ Z F'₂ hC hZ hdet
  have hG := gflag_ne γ Z F'₂ hC hZ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hw : ∀ k, (VS D).hT (wG F0 F'₂ k) (∑ j, v j • wG F0 F'₂ j) = 0 := by
    intro k
    have hk := congr_fun hv k
    simp only [Matrix.mulVec, dotProduct, gramG, Matrix.of_apply, brS, Pi.zero_apply] at hk
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    exact (Finset.sum_congr rfl (fun j _ => mul_comm _ _)).trans hk
  obtain ⟨h1, h2⟩ := PI.UnitaryGroupMassFormula.BetaLUniq.GN.coeffs_zero F0 F'₂.fl (v ∘ Sum.inl) (v ∘ Sum.inr)
    (∑ j, v j • wG F0 F'₂ j) (by rw [Fintype.sum_sum_type]; rfl)
    (fun a => hw (Sum.inl a)) (fun b => hw (Sum.inr b)) hG
  apply hv0
  funext k
  rcases k with a | b
  · exact congr_fun h1 a
  · exact congr_fun h2 b

variable (Zd : LocDat D)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

