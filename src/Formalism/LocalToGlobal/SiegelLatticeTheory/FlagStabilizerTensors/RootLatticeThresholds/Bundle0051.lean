import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0046
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0044
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionConvolutionIdentity
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0038
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.DegIUp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0049

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairAmpConstWd
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X}

theorem ooIntAll_of (hWD : Formalism.L2.SG.WuDecay.WuDecay X) (w w' : D.what₂.Word) :
    OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w') :=
  Formalism.L2.SG.Closed.OOIntAllC_outright D X Y w w'
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y w (Formalism.L2.SG.Closed.level_subgroup_properties X) hWD)
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y w' (Formalism.L2.SG.Closed.level_subgroup_properties X) hWD)
    (Formalism.L2.SG.Pf.fundExistsC_holds D X Y w w')

variable {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))

theorem pvalForm_holds (hWD : Formalism.L2.SG.WuDecay.WuDecay X) : ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists_oi W hI (ooIntAll_of hWD) (Formalism.L2.SG.Pf.FibreEq.FibreCountEq_holds hF)

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsGoodRed
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.RowDict Formalism.L2.SG.AllRowsOf
open scoped InnerProductSpace
open MeasureTheory

namespace Formalism.L2.SG.Pf.RowsGoodRed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def VT (t : Tup2 D) : Submodule ℂ (L2X X) :=
  Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X ⊓ LinearMap.ker ((ReT X {t} : L2X X →ₗ[ℂ] L2X X) - LinearMap.id)

def labOf (σ : Fin D.what₂.Drows) : Tup2 D := fun k => D.nd.lab k (D.what₂.ft σ)

def bRow (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (σ : Fin D.what₂.Drows) : L2X X :=
  ((ι (D.sEE (D.what₂.onb σ)) : Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : L2X X)

def LabTie (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : Prop :=
  (∀ σ k v, IsLabel D k (D.nd.lab k (D.what₂.ft σ) v)) ∧ (∀ σ, D.ntypes.goodTuple (labOf σ)) ∧
    ∀ σ, bRow X ι σ ∈ VT X (labOf σ)

def ProjT (G : GoodOp X) : Prop :=
  (∀ t : Tup2 D, D.ntypes.goodTuple t → VT X t ≤ goodSub X G) ∧
    ∀ t t' : Tup2 D, t ≠ t' → ∀ φ ∈ VT X t, ∀ φ' ∈ VT X t', ⟪φ, φ'⟫_ℂ = 0

def DcountEq : Prop :=
  ∀ t ∈ labT (D := D), D.ntypes.goodTuple t → dimX X {t} = Module.finrank ℂ (VT X t)

theorem rowsGood_of (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (hT : RowDictTie X G ι)
    (hL : LabTie X ι) (hP : ProjT X G) (hD : DcountEq X) : RowsGood X := by
  classical
  obtain ⟨hl1, hl2, hl3⟩ := hL
  refine ⟨hl1, hl2, fun t ht hg => ?_⟩
  have hT' := hT
  obtain ⟨j, hj⟩ := hT
  have hb : ∀ σ, bRow X ι σ = star ((j (D.what₂.onb σ) : EEC X G) : L2X X) := fun σ => by
    have h1 := hj (D.what₂.onb σ)
    simp only at h1
    unfold bRow; rw [h1]; rfl

  have hf : LinearIndependent ℂ (fun σ => ((j (D.what₂.onb σ) : EEC X G) : L2X X)) :=
    (D.what₂.onb.toBasis.linearIndependent.map' j.toLinearEquiv.toLinearMap j.toLinearEquiv.ker).map'
      (EEC X G).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent ℂ (bRow X ι) := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have h0 : conjL (muX X) (∑ i ∈ s, (starRingEnd ℂ (g i)) • ((j (D.what₂.onb i) : EEC X G) : L2X X)) = 0 := by
      rw [map_sum]
      rw [← hs]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [LinearIsometryEquiv.map_smulₛₗ, conjL_apply, hb σ]
      simp
    have h1 : (∑ i ∈ s, (starRingEnd ℂ (g i)) • ((j (D.what₂.onb i) : EEC X G) : L2X X)) = 0 :=
      (conjL (muX X)).map_eq_zero_iff.1 h0
    have := (linearIndependent_iff'.1 hf) s (fun i => starRingEnd ℂ (g i)) h1 i hi
    simpa using this

  have hspan : ∀ φ ∈ goodSub X G, φ ∈ Submodule.span ℂ (Set.range (bRow X ι)) := by
    intro φ hφ
    obtain ⟨F, hF⟩ := (range_sEE X hT' ⟨φ, hφ.1⟩).1 hφ
    have e : φ = ((ι (D.sEE F) : Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : L2X X) := by rw [hF]
    rw [e, ← D.what₂.onb.sum_repr F, map_sum, map_sum, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [map_smulₛₗ, map_smul, Submodule.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)

  let Sf : Finset (Fin D.what₂.Drows) := Finset.univ.filter fun σ => labOf σ = t
  have hEq : VT X t = Submodule.span ℂ (Set.range (fun σ : Sf => bRow X ι σ)) := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan φ (hP.1 t hg hφ))
      set φ1 := ∑ σ ∈ Sf, c σ • bRow X ι σ with hφ1
      set φ2 := ∑ σ ∈ Finset.univ.filter (fun σ => ¬ labOf σ = t), c σ • bRow X ι σ with hφ2
      have hsplit : φ = φ1 + φ2 := by
        rw [← hc, hφ1, hφ2, Finset.sum_filter_add_sum_filter_not]
      have h1V : φ1 ∈ VT X t := Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ (by
        have := hl3 σ; rwa [(Finset.mem_filter.1 hσ).2] at this)
      have h2V : φ2 ∈ VT X t := by
        have := Submodule.sub_mem _ hφ h1V
        rwa [hsplit, add_sub_cancel_left] at this
      have horth : ⟪φ2, φ2⟫_ℂ = 0 := by
        conv_lhs => rw [hφ2]
        rw [sum_inner]
        refine Finset.sum_eq_zero fun σ hσ => ?_
        rw [inner_smul_left, hP.2 (labOf σ) t (Finset.mem_filter.1 hσ).2 _ (hl3 σ) _ h2V, mul_zero]
      have h20 : φ2 = 0 := inner_self_eq_zero.1 horth
      rw [hsplit, h20, add_zero, hφ1]
      exact Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨σ, hσ⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨σ, rfl⟩
      have := hl3 σ
      rwa [(Finset.mem_filter.1 σ.2).2] at this
  have hli' : LinearIndependent ℂ (fun σ : Sf => bRow X ι σ) := hli.comp (Subtype.val : Sf → _) Subtype.val_injective
  rw [hD t ht hg, hEq, finrank_span_eq_card hli', Fintype.card_coe]
  rfl

def EtConv : Prop := ∀ (S S' : Set (Tup2 D)) (φ : L2X X), ReT X S (ReT X S' φ) = ReT X (S ∩ S') φ

def EtEmpty : Prop := ∀ φ : L2X X, ReT X ∅ φ = 0

def EtAdj : Prop := ∀ (S : Set (Tup2 D)) (φ ψ : L2X X), ⟪ReT X S φ, ψ⟫_ℂ = ⟪φ, ReT X S ψ⟫_ℂ

def EtGood (G : GoodOp X) : Prop :=
  ∀ t : Tup2 D, D.ntypes.goodTuple t → ∀ φ : L2X X, G.Rg (ReT X {t} φ) = ReT X {t} φ

theorem mem_VT {t : Tup2 D} {φ : L2X X} (h : φ ∈ VT X t) : ReT X {t} φ = φ := by
  have h2 := (Submodule.mem_inf.mp h).2
  rw [LinearMap.mem_ker] at h2
  simpa [sub_eq_zero] using h2

theorem projT_of (G : GoodOp X) (hC : EtConv X) (hE : EtEmpty X) (hA : EtAdj X) (hG : EtGood X G) : ProjT X G := by
  refine ⟨fun t ht φ hφ => ?_, fun t t' htt φ hφ φ' hφ' => ?_⟩
  · refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hφ).1, ?_⟩
    have h1 := hG t ht φ
    rw [mem_VT X hφ] at h1
    rw [LinearMap.mem_ker]
    simpa [sub_eq_zero] using h1
  · rw [← mem_VT X hφ, ← mem_VT X hφ', hA, hC]
    have hE0 : ({t} : Set (Tup2 D)) ∩ {t'} = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl
      exact htt
    rw [hE0, hE, inner_zero_right]

theorem etEmpty : EtEmpty X := by
  intro φ
  have hES : ∀ g, (ES (D := D) ∅).coeff g = 0 := by
    intro g
    simp [ES]
  have hg : egA X (ES (D := D) ∅) = 0 := by
    funext y
    simp [egA, hES]
  have he : eT X ∅ = 0 := by
    funext x
    simp [eT, Formalism.MainNotions.S.AutInst.convF, hg]
  unfold ReT
  split_ifs with h
  · have hT := (Classical.choose_spec h).2
    have h0 : ∀ x, ⟪x, (Classical.choose h) φ⟫_ℂ = 0 := fun x => by
      rw [hT x φ, he]
      simp
    exact inner_self_eq_zero.mp (h0 _)
  · rfl

theorem invInvariant_muf : X.B.μf.IsInvInvariant := by
  have : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have he1 : X.B.e 1 ≠ 0 := by
    rw [X.e_eq]
    have h1 : (1 : X.B.I.Gf) ∈ X.K2 := hK.1
    rw [if_pos (show (1 : X.B.I.Gf) ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw from h1)]
    have hc : X.chi2 1 ≠ 0 := by
      intro h0; have := hK.2.2.2.2 1 h1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hv : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact (ENNReal.toReal_pos hL.2.2.1.ne' hL.2.2.2.ne).ne'
    exact div_ne_zero (star_ne_zero.2 hc) hv
  exact Formalism.MainNotions.BridgeLemma.inv_invariant_of_bi_invariant X.B.μf (fun g => ‖X.B.e g‖) X.B.e_adm.1.continuous.norm
    X.B.Re_spec.1.norm (norm_pos_iff.2 he1)

def EtSA : Prop := ∀ (S : Set (Tup2 D)) (x : X.B.I.Gf), star (eT X S x⁻¹) = eT X S x

theorem etAdj_of (hSA : EtSA X) : EtAdj X := by
  haveI := invInvariant_muf X
  intro S φ ψ
  have hT := reT_spec X (etInt_holds X) S
  have hreg : ∀ g : X.B.I.Gf, ⟪X.B.R ((1, g) : X.B.I.GA) φ, ψ⟫_ℂ = ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ := by
    intro g
    have := Formalism.L2.SG.EvalTOntoPhi.inner_reg X ((1, g⁻¹) : X.B.I.GA) φ ψ
    rw [this, Prod.inv_mk, inv_one, inv_inv]
  calc ⟪ReT X S φ, ψ⟫_ℂ = star ⟪ψ, ReT X S φ⟫_ℂ := (inner_conj_symm _ _).symm
    _ = star (∫ g, eT X S g * ⟪ψ, X.B.R ((1, g) : X.B.I.GA) φ⟫_ℂ ∂X.B.μf) := by rw [hT.2]
    _ = ∫ g, star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        rw [← starRingEnd_apply, ← integral_conj]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (starRingEnd ℂ) (eT X S g * ⟪ψ, X.B.R ((1, g) : X.B.I.GA) φ⟫_ℂ) = _
        rw [map_mul]
        show _ = star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ
        rw [← hreg g, inner_conj_symm]
        rfl
    _ = ∫ g, star (eT X S g⁻¹) * ⟪φ, X.B.R ((1, g) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        rw [← MeasureTheory.integral_inv_eq_self (fun g => star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ) X.B.μf]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show star (eT X S g⁻¹) * ⟪φ, X.B.R ((1, g⁻¹⁻¹) : X.B.I.GA) ψ⟫_ℂ = _
        rw [inv_inv]
    _ = ∫ g, eT X S g * ⟪φ, X.B.R ((1, g) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show star (eT X S g⁻¹) * _ = _
        rw [hSA S g]
    _ = ⟪φ, ReT X S ψ⟫_ℂ := (hT.2 φ ψ).symm

theorem etGood_of (G : GoodOp X)
    (hEC : ∀ S S' : Set (Tup2 D), X.B.I.convF X.B.μf (egA X (ES S')) (eT X S) = eT X (S' ∩ S)) : EtGood X G := by
  intro t ht φ
  have h1 := Formalism.L2.SG.Pf.AllRowsRMul.isRConvF_conv X G.Rg_spec (reT_spec X (etInt_holds X) {t})
  have e : X.B.I.convF X.B.μf (eg X) (eT X {t}) = eT X {t} := by
    rw [← goodIdempotent_eq, ← ES_good, hEC]
    congr 1
    exact Set.inter_eq_right.2 (Set.singleton_subset_iff.2 ht)
  rw [e] at h1
  have h2 := isRConvF_unique X h1 (reT_spec X (etInt_holds X) {t})
  exact congrArg (fun T : L2X X →L[ℂ] L2X X => T φ) h2

end Formalism.L2.SG.Pf.RowsGoodRed
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

namespace Formalism.L2.SG.Pf.SzHypFD

variable {D : D7}

def DsigHC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → 1 ≤ Cl * large₂.sc.L →
    ∀ τ : D.what₂.Tau, D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ))

theorem dsig_eq [hF : Fact DsigHC] {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) :
    D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := hF.out D large₂ C' Cl Cg cb Cu cT CT hT hH hCL τ

variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in

theorem vv_eq_vand {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) : VV D τ = vand (lamSH D.R (D.hc τ)) := by
  have hanti := Formalism.MainNotions.BridgeLemma.szh_anti hH τ
  have hSF : (0 : ℝ) < ∏ i ∈ range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [dsig_eq hT hH hCL τ, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← dimS_eq]
  field_simp

variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in

theorem fdl_of_ties {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) :
    Sz.FormalDegreeLower (Formalism.MainNotions.BridgeLemma.cfgOf D τ) (1 / 2) (VV D τ) := by
  unfold Sz.FormalDegreeLower
  rw [Formalism.MainNotions.BridgeLemma.Vand_lam D τ, vv_eq_vand hT hH hCL τ]
  have h0 : 0 ≤ vand (lamSH D.R (D.hc τ)) := Formalism.MainNotions.BridgeLemma.szh_vand_nonneg _ (Formalism.MainNotions.BridgeLemma.szh_anti hH τ)
  linarith

end Formalism.L2.SG.Pf.SzHypFD
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TheoremBFixedOfExpansionLemmaJ
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.JointAmplitudePoints Formalism.L2.SG.Pf.ThmBChain Formalism.L2.SG.RealObj
open scoped ENNReal

namespace Formalism.L2.SG.Pf.OOCore3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section K

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
  {θ : ℝ} (C : Choice X θ) (hB : WuBessel C) (large₂ : SizeData₂ D) (C1 : ℝ)

def sclV : ℝ :=
  Complex.normSq ((Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ)

def WinK (K : ℝ) : Prop := normWin D large₂ C1 (K ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)))

def OOCorePK : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) →
    ∃ K : ℝ, 0 < K ∧ WinK large₂ C1 K ∧
      sclV Y u u' * Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.Pf.OOCore.OOP u u' ν w) * K = localAmplitudeProduct u u' hB w

def JFactPK : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    0 < J2of Y u u' ν (toPts w) →
    ∃ K : ℝ, 0 < K ∧ WinK large₂ C1 K ∧ J2of Y u u' ν (toPts w) * K = localAmplitudeProduct u u' hB w

theorem jFactPK_of_core (h : OOCorePK Y u u' ν C hB large₂ C1) : JFactPK Y u u' ν C hB large₂ C1 := by
  intro w hb hJ
  obtain ⟨w', hw', g, hg⟩ := isPtRep_of_J2of hJ
  have hw'w : w' = w := toPts_injective hw'
  subst hw'w
  rw [Formalism.L2.SG.Pf.OOCore.joint_amplitude_eq_normSq Y u u' ν w' ⟨g, hg⟩]
  exact h w' hb ⟨g, hg⟩

theorem localAmplitudesPositive_of_kernel (h : JFactPK Y u u' ν C hB large₂ C1) : LocalAmplitudesPositive Y u u' ν C hB := by
  intro w hb hJ
  obtain ⟨K, hK, -, e⟩ := h w hb hJ
  rw [← e]
  exact mul_pos hJ hK

theorem thetaWinP_of_K (h : JFactPK Y u u' ν C hB large₂ C1) : ThetaWinP Y u u' ν C hB large₂ C1 := by
  intro w hb hJ
  obtain ⟨K, hK, hW, e⟩ := h w hb hJ
  have hP : 0 < localAmplitudeProduct u u' hB w := by rw [← e]; exact mul_pos hJ hK
  have e2 : thetaP u u' hB (J2of Y u u' ν (toPts w)) w = K ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) := by
    unfold thetaP
    rw [if_pos ⟨hJ, hP⟩, ← e, mul_div_cancel_left₀ _ hJ.ne']
  rw [e2]
  exact hW

def LocNormPK (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) →
    ∃ K : ℝ, 0 < K ∧ WinK large₂ C1 K ∧
      sclV Y u u' * (∏ v, Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))) * K = localAmplitudeProduct u u' hB w

theorem ooCorePK_of (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl) (hN : LocNormPK Y u u' C hB large₂ C1 νl) :
    OOCorePK Y u u' ν C hB large₂ C1 := by
  intro w hb hw
  rw [Formalism.L2.SG.Pf.OOCoreHilbertSchmidt.hsNormSq_OOP_quot u u' ν νl hQ w hw (Formalism.L2.SG.Pf.OOCoreHilbertSchmidt.gxPos_holds u u' w hb hw)]
  exact hN w hb hw

end K

def LocalAmplitudeBounds {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (ν : X.B.I.Ginf → Measure X.B.I.Ginf) (C1 Cn Ire : ℝ) : Prop :=
  0 ≤ Ire ∧ ∃ (θ : ℝ) (C : Choice X θ) (hB : WuBessel C), 0 < θ ∧ normWin D large₂ C1 θ ∧
    (∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u' τ ∧ ZTr C u τ ∧ ZTr C u' τ ∧ HaarTr C τ ∧ GoodSRest hB u u' τ) ∧
    (∃ νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)),
      Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl ∧ LocNormPK Y u u' C hB large₂ C1 νl) ∧
    ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
      (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (WX C u u' τ).z (WX C u u' τ).z' (sec τ)) →
      ∏ τ, MMv D u u' (AX hB u u' τ) (sec τ) ≤ ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)

theorem remainingFactsSecond_of_local {D : D7} {large₂ : SizeData₂ D} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}
    {ν : X.B.I.Ginf → Measure X.B.I.Ginf} {C1 Cn Ire : ℝ} (h : LocalAmplitudeBounds large₂ Y u u' ν C1 Cn Ire) :
    AmplitudeMeasureBounds large₂ Y u u' ν C1 Cn Ire := by
  obtain ⟨hIre, θ, C, hB, h0, hw, hl, ⟨νl, hQ, hN⟩, hM⟩ := h
  have hJ := jFactPK_of_core Y u u' ν C hB large₂ C1 (ooCorePK_of Y u u' ν C hB large₂ C1 νl hQ hN)
  exact ⟨hIre, θ, C, hB, h0, hw, hl, localAmplitudesPositive_of_kernel Y u u' ν C hB large₂ C1 hJ, thetaWinP_of_K Y u u' ν C hB large₂ C1 hJ, hM⟩

def LocalAmplitudeBoundsUniform : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C1 Cn : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
        (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ →
      ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
        (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
        (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
        (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (Irat Ire : ℝ),
        MassDataAdmissible X Y u u' (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq) Irat Ire →
      ∀ ν, Pinned X u u' ν → LocalAmplitudeBounds large₂ Y u u' ν C1 Cn Ire

theorem theoremB_fixed_of_expansion_lemmaJ (hE : Formalism.MainNotions.RotatedPoints.WeightedExpansionRotated) (hA : AmpUnif) (hR : LocalAmplitudeBoundsUniform) :
    StepThmBPinnedC := by
  refine theoremB_fixed_of_expansion_measure hE hA fun Cg cb Cw cT CT C0 => ?_
  obtain ⟨C1, Cn, a, b, h2⟩ := hR Cg cb Cw cT CT C0
  exact ⟨C1, Cn, a, b, fun C' Cl h1 h3 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hO ν hp =>
    remainingFactsSecond_of_local (h2 C' Cl h1 h3 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hO ν hp)⟩

end Formalism.L2.SG.Pf.OOCore3
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThresholdOrder
section
noncomputable section

open scoped Classical
open Finset Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt

namespace Formalism.L2.SG.Pf.ThresholdOrder

theorem isGreatest_pow_inv {s : Set ℝ} (hs : s.Finite) (hne : s.Nonempty) (hpos : ∀ x ∈ s, 0 < x) {f : ℕ} (hf : 0 < f) :
    ∃ Th : ℝ, 0 < Th ∧ IsGreatest s ((Th ^ f)⁻¹) := by
  obtain ⟨m, hm, hmax⟩ := Set.exists_max_image s id hs hne
  have hm0 : 0 < m⁻¹ := inv_pos.mpr (hpos m hm)
  refine ⟨m⁻¹ ^ ((f : ℝ)⁻¹), Real.rpow_pos_of_pos hm0 _, ?_⟩
  rw [Real.rpow_inv_natCast_pow hm0.le hf.ne', inv_inv]
  exact ⟨hm, fun b hb => hmax b hb⟩

variable {ι : Type} [Fintype ι] (G : Sz.Glob ι)

theorem thrSet_finite (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) : (G.thrSet C de de' T T' l).Finite := by
  have key : G.thrSet C de de' T T' l ⊆ ⋃ i ∈ Finset.range (G.r + 2), ⋃ s ∈ Finset.range (G.r + 3),
      ({∏ w, Sz.xHat 1 C G.ka G.N G.lenI G.g (G.cutSupLong de de' T T' l w),
        ∏ w, Sz.xHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w),
        ∏ w, Sz.lamHat i s C G.ka G.N G.lenI G.g (G.supI de de' T T' l w),
        ∏ w, Sz.lamPrimeHat i C G.ka G.N G.lenI G.g (G.supI de de' T T' l w) (T * T')} : Set ℝ) := by
    rintro x ⟨i, hi1, hir, h⟩
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨s, _, hsi, rfl⟩ | rfl
    · exact ⟨i, by omega, 0, by omega, Or.inl rfl⟩
    · exact ⟨i, by omega, 0, by omega, Or.inr (Or.inl rfl)⟩
    · exact ⟨i, by omega, s, by omega, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨i, by omega, 0, by omega, Or.inr (Or.inr (Or.inr rfl))⟩
  refine Set.Finite.subset ?_ key
  refine Set.Finite.biUnion (Finset.range _).finite_toSet fun i _ => ?_
  refine Set.Finite.biUnion (Finset.range _).finite_toSet fun s _ => ?_
  exact Set.toFinite _

theorem thrSet_nonempty (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ) : (G.thrSet C de de' T T' l).Nonempty :=
  ⟨_, 1, le_rfl, by omega, Or.inl ⟨rfl, rfl⟩⟩

theorem thrAt_of_pos (CA : ℝ) (D : D7) (u u' : D.what₂.Word)
    (hpos : ∀ x ∈ (Formalism.L2.SG.SpectralTiesReal.gOf D (Formalism.L2.Geo.Rec.StarEmbeddingNorm.ePl D).symm).thrSet CA
      (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u') (D.mem u).A.T (D.mem u').A.T
      (Formalism.L2.SG.SpectralTiesReal.lOf D (Formalism.MainNotions.BridgeLemma.deOf D u) (Formalism.MainNotions.BridgeLemma.deOf D u')), 0 < x) :
    Formalism.L2.SG.Pf.SzHypOf.ThresholdAtPlaces CA D u u' := by
  unfold Formalism.L2.SG.Pf.SzHypOf.ThresholdAtPlaces
  refine isGreatest_pow_inv (thrSet_finite _ _ _ _ _ _ _) (thrSet_nonempty _ _ _ _ _ _ _) hpos ?_
  unfold Formalism.FourierDecayAlt.Sz.Glob.f
  exact Fintype.card_pos

end Formalism.L2.SG.Pf.ThresholdOrder
end
end

