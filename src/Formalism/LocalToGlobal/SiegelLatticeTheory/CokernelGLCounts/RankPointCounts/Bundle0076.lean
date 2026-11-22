import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0064
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0036
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0050
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0034
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0074
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0040
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0038
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0071
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormTransp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0057
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0022
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0038
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocalCountZeroLocalHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocCntUL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0004
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0045
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohLp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0069

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieIdx
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTieIdx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_one_sub_inv_pow_pos (q : ℝ) (hq : 1 < q) (s : Finset ℕ) (hs : ∀ j ∈ s, 1 ≤ j) :
    0 < ∏ j ∈ s, (1 - 1 / q ^ j) :=
  Finset.prod_pos fun j hj => by
    have h1 : 1 < q ^ j := one_lt_pow₀ hq (by have := hs j hj; omega)
    have h2 : 1 / q ^ j < 1 := by rw [div_lt_one (by linarith)]; exact h1
    linarith

theorem cardGL_A (g m : ℕ) [hg : Fact g.Prime] :
    (Nat.card (GL (Fin m) (ZMod g)) : ℝ) = (g : ℝ) ^ (m * m) * ∏ j ∈ Finset.Ioc 0 m, (1 - 1 / (g : ℝ) ^ j) := by
  have hq0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.out.ne_zero
  rw [Matrix.card_GL_field, ZMod.card, Nat.cast_prod]
  have hterm : ∀ i : Fin m, (((g ^ m - g ^ (i : ℕ) : ℕ)) : ℝ) = (g : ℝ) ^ m * (1 - 1 / (g : ℝ) ^ (m - i)) := by
    intro i
    rw [Nat.cast_sub (Nat.pow_le_pow_right hg.out.pos i.2.le), Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one,
      mul_one_div, div_eq_mul_inv, ← pow_sub₀ _ hq0 (Nat.sub_le m i), Nat.sub_sub_self i.2.le]
  rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul]
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun i => 1 - 1 / (g : ℝ) ^ (m - i)) m]
  have h1 : ∏ i ∈ Finset.range m, (1 - 1 / (g : ℝ) ^ (m - i)) =
      ∏ i ∈ Finset.range m, (fun j => 1 - 1 / (g : ℝ) ^ (j + 1)) (m - 1 - i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    show _ = 1 - 1 / (g : ℝ) ^ (m - 1 - i + 1)
    rw [show m - 1 - i + 1 = m - i by omega]
  rw [h1, Finset.prod_range_reflect (fun j => 1 - 1 / (g : ℝ) ^ (j + 1)) m, Finset.range_eq_Ico,
    Finset.prod_Ico_add' (fun j => 1 - 1 / (g : ℝ) ^ j) 0 m 1]
  have h2 : Finset.Ico (0 + 1) (m + 1) = Finset.Ioc 0 m := by ext; simp; omega
  rw [h2]

theorem idx_arith (g r k : ℕ) (hg : g.Prime) :
    (glkC k g : ℝ) * (nnC r k g : ℝ) / (ggC r k g : ℝ) =
      (g : ℝ) ^ (-(((r + 1) * (2 * k + 2 * r + 1) : ℕ) : ℤ)) /
        ∏ i ∈ Finset.Icc (k + 1) (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ i) := by
  have : Fact g.Prime := ⟨hg⟩
  have hq : (1 : ℝ) < g := by exact_mod_cast hg.one_lt
  have hq0 : (g : ℝ) ≠ 0 := by linarith
  have hc : Fintype.card (Formalism.FourierDecayAlt.S3.Idx r k) = 2 * r + k + 1 := by
    simp only [Formalism.FourierDecayAlt.S3.Idx, Formalism.FourierDecayAlt.S3.Mid, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  have hG : (ggC r k g : ℝ) = (Nat.card (GL (Fin (2 * r + k + 1)) (ZMod g)) : ℝ) := by
    unfold ggC
    exact_mod_cast Nat.card_congr
      (Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod g) (ZMod g) (Fintype.equivFinOfCardEq hc)).toMulEquiv)
  have hN : (nnC r k g : ℝ) = (g : ℝ) ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
    unfold nnC
    rw [MassDataIdxStIm.card_isN, ZMod.card]
    push_cast
    try rfl
  unfold glkC
  rw [hG, hN, cardGL_A, cardGL_A]
  have hIcc : Finset.Icc (k + 1) (2 * r + k + 1) = Finset.Ioc k (2 * r + k + 1) := by
    ext; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, ← Finset.prod_Ioc_consecutive _ (Nat.zero_le k) (by omega : k ≤ 2 * r + k + 1)]
  have hA : 0 < ∏ j ∈ Finset.Ioc 0 k, (1 - 1 / (g : ℝ) ^ j) :=
    prod_one_sub_inv_pow_pos _ hq _ (fun j hj => (Finset.mem_Ioc.1 hj).1)
  have hB : 0 < ∏ j ∈ Finset.Ioc k (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ j) :=
    prod_one_sub_inv_pow_pos _ hq _ (fun j hj => by have := (Finset.mem_Ioc.1 hj).1; omega)
  have hpow : (g : ℝ) ^ (k * k) * (g : ℝ) ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) /
      (g : ℝ) ^ ((2 * r + k + 1) * (2 * r + k + 1)) = (g : ℝ) ^ (-(((r + 1) * (2 * k + 2 * r + 1) : ℕ) : ℤ)) := by
    rw [← pow_add, ← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hq0]
    congr 1
    rcases r with _ | s
    · simp; ring
    · simp only [Nat.add_sub_cancel]; push_cast; ring
  rw [← hpow]
  generalize (∏ j ∈ Finset.Ioc 0 k, (1 - 1 / (g : ℝ) ^ j)) = A at hA ⊢
  generalize (∏ j ∈ Finset.Ioc k (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ j)) = B at hB ⊢
  have hA' := hA.ne'
  have hB' := hB.ne'
  have hgn : (g : ℝ) ^ ((2 * r + k + 1) * (2 * r + k + 1)) ≠ 0 := pow_ne_zero _ hq0
  field_simp
  try ring

variable {D : D7} (X : HidaSetting D)

theorem ratio_eq (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal / (MassDataIdxSteps.muP X p (MassDataIdxSteps.KvX X p)).toReal =
      (glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ) / (ggC D.R.rS D.R.k (gOf p) : ℝ) := by
  obtain ⟨j, hj, hj0, hμj, hB0, hBt⟩ := MassDataIdxSteps.measB_of X MassDataIdxSteps.haarIdx MassDataIdxSteps.redIdx u p
    (MassDataIdxSteps.stTop X p) (Formalism.L2.SG.Pf.MassDataX.stK_holds X p) (Formalism.L2.SG.Pf.MassDataX.stRed_holds X p)
    (Formalism.L2.SG.Pf.MassDataX.stImB_holds X hb u p)
  have h1 : (MassDataIdxSteps.muP X p (MassDataIdxSteps.KvX X p)).toReal =
      (j : ℝ) * (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal := by
    rw [hμj, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hpos : (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hB0, hBt⟩
  rw [h1, ← hj]
  rcases eq_or_ne (j : ℝ) 0 with h0 | h0
  · simp [h0]
  · rw [mul_comm (j : ℝ) (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal, mul_comm (j : ℝ),
      div_mul_eq_div_div, div_self hpos, div_mul_eq_div_div, div_self hj0]

theorem gAt_eq (p : TypX X) : gAt X p.1 = gOf p := by
  unfold gAt gOf
  split_ifs <;> rfl

theorem aP_typed (u : D.what₂.Word) (p : TypX X) :
    aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u) =
      ∏ i ∈ Finset.Icc (D.R.k + 1) (2 * D.R.rS + D.R.k + 1), (1 - 1 / (gOf p : ℝ) ^ i) := by
  obtain ⟨hN, hη⟩ := Formalism.L2.SG.Pf.gSplitX_holds X p
  have hT := Formalism.L2.SG.Pf.AlTieFD.T_not_mem X u p
  unfold aP
  rw [if_neg (by unfold Tw; exact hT), X.n_eq, ← Formalism.MainNotions.S.dimS_eq D.R, hη, hN, gAt_eq X p]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

theorem indexTypC_holds (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    Formalism.L2.SG.Pf.NcIdx.IndexTypC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  intro p
  refine (ratio_eq X hb u p).trans ?_
  rw [idx_arith (gOf p) D.R.rS D.R.k (MassDataIdxSteps.gOf_prime X p), aP_typed X u p, gAt_eq X p]

end Formalism.L2.SG.Pf.AlTieIdx
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AutLzNonempty
section
noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField

namespace Formalism.L2.SG.RhoPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem autLz_nonempty {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (autLz D F0 Λ).Nonempty := by
  have h1 : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 := ⟨one_mem _, fun j => kmap_one _, rfl⟩
  exact ⟨ind F0 h1, (autLz_iff F0 Λ _).2 ⟨1, h1, gmap_one' Λ, rfl⟩⟩

theorem massRows_pos {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u : D.what₂.Word) :
    0 < Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) := by
  have hne : (Y.what₂ u).Nonempty := ⟨_, (cls_spec (Y.rowsOK u) (latRowLat X u) 1).1⟩
  unfold Formalism.MainNotions.S.Cnt.massRows
  refine Finset.sum_pos (fun Λ hΛ => ?_) hne
  haveI := Formalism.L2.SG.Pf.FibreCounting.autLz_finite (Y := Y) (Formalism.L2.SG.Closed.NeatKu_holds X u Y.hK) hΛ
  have hpos : 0 < Nat.card ↥(autLz D (X.Fu u) Λ) := by
    obtain ⟨φ, hφ⟩ := autLz_nonempty (X.Fu u) Λ
    haveI : Nonempty ↥(autLz D (X.Fu u) Λ) := ⟨⟨φ, hφ⟩⟩
    exact Nat.card_pos
  unfold Formalism.MainNotions.S.wRow
  exact inv_pos.2 (Nat.cast_pos.2 hpos)

end Formalism.L2.SG.RhoPf

namespace Formalism.L2.SG.MassDataConc

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Full MeasureTheory

theorem RhoTieC_closed {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Full X) (u u' : D.what₂.Word)
    (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (sd C Th : ℝ) (vR : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (i0 i0' : NumberField.InfinitePlace X.B.I.F → Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    RhoTieC X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq :=
  RhoTieC_holds X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.latRowLat X u) (Formalism.L2.SG.Pf.latInj X u)
    (Formalism.L2.SG.Pf.latSurj X u)

end Formalism.L2.SG.MassDataConc
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoordCovolOf
section
namespace Formalism.L2.SG.Pf.NcReal.JX

theorem coordCovol_of (hL : KapLaw) (hN : NOfib) (hB : BlockCovol) : Formalism.L2.SG.Pf.LsNc5.CoordCovol :=
  coordCovol_of_cut hL kapSurj_holds hN hB (fun X u => cVal_prod X u)

end Formalism.L2.SG.Pf.NcReal.JX
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolumeSpans
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vector_eq_zero_of_orbital_zero {D : D7} {X : HidaSetting D} (Y : Full X) {u : D.what₂.Word} (t : GTu Y u)
    (h : OOt t = 0) : (Y.tO u u).vec t = 0 := by
  unfold Full.tO tOf
  dsimp only
  unfold vec ampN
  rw [h]
  simp only [map_zero, smul_zero, ite_self]
  first
    | rfl
    | simp

theorem irrVec_nohyp {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (t : GTu Y u) (ht : ¬ t.relevant) :
    (Y.tO u u).vec t = 0 :=
  vector_eq_zero_of_orbital_zero Y t
    (Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds
      Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds
      Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t ht)

theorem IrrVecC_holds : IrrVecC := by
  intro D X Y u _ _ t _ ht
  exact irrVec_nohyp Y u t ht

end Formalism.L2.SG.KappaOffDiagonal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DetEqLeadMinorE
section
noncomputable section

open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cross

variable {D : D7}

theorem ld_eq_leadMinorE (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    ld Z = leadMinorE Z D.R.rS := by
  unfold ld leadMinorE
  rw [dif_pos (Nat.le_succ _)]
  rfl

theorem det_eq_leadMinorE (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    Z.det = leadMinorE Z (D.R.rS + 1) := by
  unfold leadMinorE
  rw [dif_pos le_rfl]
  rfl

theorem cross_global {w w' : Point D.host.E (D.R.rS + 1)} {Z Z' : PairVal.MatR D} (hk : kind w = kind w')
    (hZ : AtMat w Z) (hZ' : AtMat w' Z') : Cross Z Z' := by
  unfold Cross
  rw [ld_eq_leadMinorE, ld_eq_leadMinorE, det_eq_leadMinorE, det_eq_leadMinorE]
  exact cross_of_kind hk hZ hZ'

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

theorem cross_zhatLoc (p : PlF D) {Z Z' : MatZ D} (h : Cross Z Z') :
    Cross (ZhatLoc M δ p Z) (ZhatLoc M δ p Z') := by
  have e : ∀ Y : MatZ D, ZhatLoc M δ p Y =
      Matrix.of fun a b => frFac δ p b * (M p).L.cj (frFac δ p a) * (Y.map (D.s.atP p).ιE) a b := by
    intro Y; ext a b; simp [ZhatLoc]
  rw [e, e]
  exact cross_scale (fun a => (M p).L.cj (frFac δ p a)) (frFac δ p) (cross_map _ h)

end Cross

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelPf
section
noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.Pf.FormRelPf

def ofPts {K : Type} {i : ℕ} (s : Σ c : Composition (i + 1), (Fin c.length → K)) : List (K × ℕ) :=
  List.ofFn fun a => (s.2 a, s.1.blocksFun a)

theorem ofPts_toPts {K : Type} [Zero K] {i : ℕ} (p : Point K (i + 1)) : ofPts (toPts p) = p.1 := by
  apply List.ext_get
  · simp [ofPts, toPts, Composition.length]
  · intro n h1 h2
    simp [ofPts, toPts, Composition.blocksFun]

theorem toPts_injective {K : Type} [Zero K] {i : ℕ} :
    Function.Injective (toPts : Point K (i + 1) → Σ c : Composition (i + 1), (Fin c.length → K)) := by
  intro p q h
  apply Subtype.ext
  rw [← ofPts_toPts p, ← ofPts_toPts q, h]

end Formalism.L2.SG.Pf.FormRelPf

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.FormRel Formalism.L2.SG.Pf.FormRelPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem formRelC_of (hRD : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.Pf.RowForm.RealDecompC X Y u u')
    (hRC : Formalism.L2.SG.Pf.RelCharC) : FormRelC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ ν hν t ht hv => ?_⟩
  have hG : t.G ≠ 0 := Formalism.L2.SG.Pf.RowForm.realDecomp_G_ne X Y u u' t ht
  have hrel : t.relevant := by
    by_contra hr
    apply hv
    have h0 : OOt t = 0 := Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t hr
    show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
    unfold vec ampN
    rw [h0]
    simp
    rfl
  obtain ⟨hpt, hall⟩ := hRD D X Y u u' t hrel hG
  refine ⟨⟨_, rfl, hpt⟩, fun w hw hwr => ?_⟩
  have hw' : w = Formalism.L2.SG.PairVal.ptOf t.toTerm := toPts_injective hw
  subst hw'
  have hγ := Formalism.L2.SG.Pf.RowForm.isPtRep_gamW X u u' hwr
  obtain ⟨g, hg, g', hg', hdec⟩ := hall _ hγ
  obtain ⟨c, hc⟩ := formTransp_any (X := X) (Y := Y) (u := u) (u' := u') (νq := ν) hν.2 hRC t hrel hwr g hg g' hg'
    hdec
  have := FiniteDimensional.complete ℂ (X.Vpi u)
  have := FiniteDimensional.complete ℂ (X.Vpi u')
  refine ⟨(c : ℂ) * (X.psiInfU u g * conj (X.psiInfU u' g')),
    ((Formalism.L2.SG.RealObj.InfCut.piIso X u g hg).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u),
    ((Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg').symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'), ?_⟩
  rw [hc, hdec, Formalism.L2.SG.Pf.RowForm.ClassFrameNormal.oo_map_mulLeft _ _ _ _ g g' (X.psiInfU u g) (X.psiInfU u' g')
    (Formalism.L2.SG.RealObj.InfCut.piIso X u g hg) (Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg')
    (fun x => (X.Wu_spec u).1 g hg x) (fun x => (X.Wu_spec u').1 g' hg' x), ← Complex.coe_smul, smul_smul]

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaVLift
section
noncomputable section

namespace Formalism.L2.SG.Pf.LiftCellVolume

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

theorem lemmaVLiftC_of (hRC : Formalism.L2.SG.TermOp.Vanish.RCocompactC) {D : D7} (X : HidaSetting D)
    (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word) (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) :
    Formalism.L2.SG.Pf.RowForm.LemmaVLiftC X Y u u' κ := by
  intro R ρ s hs
  exact Formalism.L2.SG.TermOp.Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds
    Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Pf.chiTrivialC_outright Formalism.L2.SG.Pf.psiInfChar_holds
    Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds hRC Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y s.1 hs

theorem LemmaVLiftC_holds {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ) :
    Formalism.L2.SG.Pf.RowForm.LemmaVLiftC X Y u u' κ :=
  lemmaVLiftC_of Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds X Y u u' κ

end Formalism.L2.SG.Pf.LiftCellVolume
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ModSideUL
section
namespace Formalism.L2.SG.LsDatumA

theorem modSide0L : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n false) :=
  Formalism.L2.SG.LocalCountModules.localCountZeroLocal_holds

theorem modSideUL : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n false) :=
  Formalism.L2.SG.LocalCountModules.localCountUnitLocal_holds

end Formalism.L2.SG.LsDatumA
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
section
namespace Formalism.L2.SG.NGCut.NormalCount

theorem NormCountG_holds : Formalism.L2.SG.NGCut.NormalInvariants.NormCountG := by
  intro E _ _ _ J m hJ hm S hS
  exact Formalism.L2.SG.NGCut.TorsionTotientBound.card_mul_conj_eq_le_of_fractionalIdeal E J m hJ hm S hS

theorem NormCount_holds : Formalism.L2.SG.NGCut.NormalInvariants.NormCount :=
  Formalism.L2.SG.NGCut.NormalInvariants.normCount_of NormCountG_holds

end Formalism.L2.SG.NGCut.NormalCount
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StarExists2OfGood
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem starExists2_of_good (hP : CtxP u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    StarExists2 Zd u u' F0 what₂ :=
  starExists2_of_parts Zd u u' F0 what₂ hP (cohGen_of Zd (cohInt_holds Zd) (cohDG_holds Zd) hGood)
    (cohIota_holds Zd) hGood

theorem starExists2_holds (hP : CtxP u u' F0 what₂) : StarExists2 Zd u u' F0 what₂ :=
  starExists2_of_good Zd u u' F0 what₂ hP (cohGood_of Zd globGramNe_holds)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

