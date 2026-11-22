import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0231
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0585
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0579
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0573
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentMemLevelOfReduction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical

namespace GlobalTheory.LevAssembly

theorem gAt_mem_levG_of_red : ∀ (D : D7) (S : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank), L.P.H = ⊥ → ∀ (g : GA D S), ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg, PP'.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) → PP' = PP) → (∀ PP' ∈ L.Q, PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F)) → Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g) ∈ Formalism.L2.DIV.St βS → Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) → Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g))) = 1 → gAt S (.inl (PP.under (𝓞 D.host.F))) g ∈ Lev.levG S βS L := by
  intro D S βS L hH g PP hPP huniq hQ hSt hred hr
  have hone : ∀ PP' : Pl D.host.E, PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F) →
      Formalism.L2.DIV.redFn βS PP' (Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g)) = 1 := by
    intro PP' hne
    exact GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D S βS _ PP' hSt (GlobalTheory.AdelicU.proj_emb_ne _ _ hne _)
  refine ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC S _ _, ?_⟩
  show Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g) ∈ Formalism.L2.DIV.lev D.sp.cm S.gram βS L
  refine ⟨⟨⟨⟨GlobalTheory.LevSplit.finE_mem_UA S _, hSt⟩, ?_⟩, ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun PP' => Subgroup.mem_iInf.2 fun hPP' => ?_
    refine Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    by_cases h : PP'.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F)
    · rw [huniq PP' hPP' h]; exact hred
    · rw [hone PP' h]; exact Subgroup.one_mem _
  · refine Subgroup.mem_iInf.2 fun PP' => Subgroup.mem_iInf.2 fun hPP' => ?_
    refine Formalism.L2.DIV.mem_parah.2 ⟨hSt, ?_⟩
    rw [hone PP' (hQ PP' hPP')]; exact Subgroup.one_mem _
  · show Formalism.L2.DIV.rTup βS L _ ∈ L.P.H
    rw [hH, Subgroup.mem_bot]
    funext PP'
    show Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP'.1 _) = 1
    by_cases h : PP'.1.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F)
    · rw [huniq PP'.1 PP'.2 h]; exact hr
    · rw [hone PP'.1 h]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _

end GlobalTheory.LevAssembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrincipalPlaceComponentStabilisesLatticeTwisted
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Classical

namespace GlobalTheory.LocSuppTw

variable {D : D7}

theorem datum_specQ (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (e : AE D)
    (x : WO S T)
    (hx : (if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) *
      omegaQ Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) ≠ 0) :
    IsIntM (frMapO S T βS βT x) ∧
    (∀ PP ∈ L.Pg, IsUnit (topL S.rank (redM PP (frMapO S T βS βT x))).det) ∧
    ∃ a : ∀ PP : ↥L.Pg, GL (Fin S.rank) (kP PP.1),
      (∀ PP : ↥L.Pg, ((a PP : GL (Fin S.rank) (kP PP.1)) : Matrix (Fin S.rank) (Fin S.rank) (kP PP.1)) =
        topL S.rank (redM PP.1 (frMapO S T βS βT x))) ∧
      (∀ PP : ↥L.Pg, a PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (a PP)) ∈ L.P.H := by
  by_cases hc : IsHalf e x ∧ IsIntM (frMapO S T βS βT x)
  · rw [if_pos hc] at hx
    have hG := left_ne_zero_of_mul hx
    unfold omegaG at hG
    split_ifs at hG with hd
    · refine ⟨hc.2, fun PP hPP => ?_, hd.2⟩
      obtain ⟨a, ha, -, -⟩ := hd.2
      rw [← ha ⟨PP, hPP⟩]
      exact Matrix.isUnits_det_units (a ⟨PP, hPP⟩)
    · exact absurd rfl hG
  · rw [if_neg hc] at hx
    exact absurd rfl hx

theorem idemSum_left {e : AE D} {P Q : Finset (Pl D.host.E)} (h : IsIdemSum e (P ∪ Q)) :
    ∃ e₁ : AE D, IsIdemSum e₁ P := by
  obtain ⟨e₁, h₁⟩ := GlobalTheory.ExportSeries.SplitSet.mono ⟨e, h⟩ Finset.subset_union_left
  exact ⟨e₁, h₁⟩

theorem isIntM_smul' {b a : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) : IsIntM (c • N) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_mem hc (hN i j)

theorem redM_smul_of_res {b a : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (PP : Pl D.host.E)
    (h1 : Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = 1) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    redM PP (c • N) = redM PP N := by
  ext i j
  have h2 : (c • N) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := isIntM_smul' hc hN i j
  have hsub : (⟨(c • N) i j, h2⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨c, hc⟩ * ⟨N i j, hN i j⟩ :=
    Subtype.ext (by simp [Matrix.smul_apply])
  unfold redM
  rw [dif_pos h2, dif_pos (hN i j), hsub, map_mul, h1, one_mul]

end GlobalTheory.LocSuppTw

namespace GlobalTheory.LocSuppTw

theorem smul_mul_gen {R : Type} [CommRing R] {a b c : ℕ} (f : R) (A : Matrix (Fin a) (Fin b) R)
    (G : Matrix (Fin b) (Fin c) R) : (f • A) * G = f • (A * G) := by
  ext i k
  simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

theorem tri_of_mul_eq {κ : Type} [Field κ] {n r t : ℕ} (hr : r ≤ n) {a b R : GL (Fin n) κ} (h : b * R = a)
    (ha : a ∈ blockTri (blkOf r t)) (hb : b ∈ blockTri (blkOf r t)) (ha1 : upperLeftBlock hr a = 1) (hb1 : upperLeftBlock hr b = 1) :
    R ∈ blockTri (blkOf r t) ∧ upperLeftBlock hr R = 1 := by
  have hR : R = b⁻¹ * a := by rw [← h, inv_mul_cancel_left]
  have hmem : R ∈ blockTri (blkOf r t) := by
    rw [hR]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) ha
  refine ⟨hmem, ?_⟩
  have hle := blockTri_blkOf_le (κ := κ) (n := n) r t
  have ha2 := hle ha
  have hb2 := hle hb
  unfold upperLeftBlock at ha1 hb1 ⊢
  rw [hR, extendMatrixByIdentityAlongIndices_mul (blkR hr) (Subgroup.inv_mem _ hb2) ha2, extendOne_inv (blkR hr) hb2, ha1, hb1, inv_one, one_mul]

set_option maxHeartbeats 1000000 in

theorem finE_gAt_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D), IsSelfDualC S ΛS → Formalism.L2.DIV.IsFrame βS ΛS → S.rank ≤ T.rank → IsIdemSum e (L.Pg ∪ L.Q) → L.P.H = ⊥ → ∀ (g : GA D S) (x : WO S T), (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) x ≠ 0 → (fun x : WO S T => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ L.Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x)) else 0) (actO S T g 1 x) ≠ 0 → ∀ PP ∈ L.Pg, (∀ PP' ∈ L.Pg ∪ L.Q, PP'.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) → PP' = PP) → Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g) ∈ Formalism.L2.DIV.St βS ∧ Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g))) = 1 := by
  intro D S T ΛS βS βT L χ ξ e hSD hFr hST hId hH g x hx hgx PP hPP _
  have hHalf : IsHalf e x := by
    by_contra hn
    exact hx (if_neg fun h => hn h.1)
  obtain ⟨hI1, hU1, a, ha, haT, haH⟩ := datum_specQ S T βS βT L χ ξ L.Q e x hx
  obtain ⟨hI2, hU2, a', ha', ha'T, ha'H⟩ := datum_specQ S T βS βT L χ ξ L.Q e (actO S T g 1 x) hgx

  obtain ⟨γ, hγ⟩ : ∃ γ : GL (Fin S.rank) (Lev.EAf D), γ = βS⁻¹ * Lev.finE S g * βS := ⟨_, rfl⟩
  have hact : frMapO S T βS βT (actO S T g 1 x) = frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val := by
    rw [hγ]
    exact GlobalTheory.T.frameMatrix_weilPairAction_left_inv D S T βS βT g x

  obtain ⟨e₁, h₁⟩ := idemSum_left hId
  obtain ⟨hc, hres⟩ := GlobalTheory.InnerSteps.resS_idemSum h₁
  have hcc : toEAf D e₁ * toEAf D e₁ = toEAf D e₁ := by
    rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self h₁]
  have hmul : toEAf D e₁ • frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val =
      toEAf D e₁ • (frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) := smul_mul_gen _ _ _
  have hI2' : IsIntM (frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) := by
    rw [← hact]
    exact hI2
  have hu1 : IsIntM (toEAf D e₁ • frMapO S T βS βT x) := isIntM_smul' hc hI1
  have hu1g : IsIntM (toEAf D e₁ • frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) := by
    rw [hmul]
    exact isIntM_smul' hc hI2'
  have hsupp : ∀ i j, toEAf D e₁ * (toEAf D e₁ • frMapO S T βS βT x) i j = (toEAf D e₁ • frMapO S T βS βT x) i j := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hcc]
  have hred1 : ∀ PP ∈ L.Pg, redM PP (toEAf D e₁ • frMapO S T βS βT x) = redM PP (frMapO S T βS βT x) :=
    fun PP hP => redM_smul_of_res hc PP (hres PP hP) hI1
  have hred2 : ∀ PP ∈ L.Pg, redM PP (toEAf D e₁ • frMapO S T βS βT x * (γ⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) =
      redM PP (frMapO S T βS βT (actO S T g 1 x)) := by
    intro PP hP
    rw [hmul, hact]
    exact redM_smul_of_res hc PP (hres PP hP) hI2'

  obtain ⟨hγ1, hγ2, htop⟩ := GlobalTheory.T.integral_idempotent_mul_of_unit_topBlock_reductions (D := D) T.rank S.rank hST L.Pg e₁ h₁ (toEAf D e₁ • frMapO S T βS βT x) γ
    hu1 hu1g hsupp (fun PP hP => by rw [hred1 PP hP]; exact hU1 PP hP) (fun PP hP => by rw [hred2 PP hP]; exact hU2 PP hP)
  obtain ⟨hγ3, hγ4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral S ΛS βS hSD hFr (Lev.finE S g) (GlobalTheory.LevSplit.finE_mem_UA S g) γ hγ e₁ hγ1 hγ2

  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed L.Pg e₁ h₁
  obtain ⟨k, -, hk⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element S (GlobalTheory.LevelNbhd.finPartG S g) (e₁ + cA D e₁)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC S g) hεε hεc
  have hkE := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame S βS (GlobalTheory.LevelNbhd.finPartG S g) k (e₁ + cA D e₁) hk
  rw [GlobalTheory.SuppLevO.finE_finPartG, ← hγ] at hkE
  obtain ⟨hkSt, hkred⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction S.rank βS γ (Lev.finE S k) L.Pg e₁ h₁ hγ1 hγ2 hγ3 hγ4 hkE
  have hpk : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) g :=
    (GlobalTheory.T.localProjection_eq_of_idempotent_patch S _ (GlobalTheory.LevelNbhd.finPartG S g) k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one L.Pg e₁ h₁ PP hPP) hk).trans
      (GlobalTheory.SuppLevO.proj_finPartG S g _)
  have hyv : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) (gAt S (.inl (PP.under (𝓞 D.host.F))) g) =
      GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) g :=
    GlobalTheory.AdelicU.proj_emb_self (σ := D.sp.cm.sig) (J := S.gram) _ _

  have hkloc := (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hFr k).mp hkSt
  have hyS : Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g) ∈ Formalism.L2.DIV.St βS := by
    rw [GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D S βS ΛS hFr]
    intro w
    by_cases hw : w = PP.under (𝓞 D.host.F)
    · subst hw
      rw [hyv, ← hpk]
      exact hkloc _
    · show GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram w (GlobalTheory.AdelicU.emb D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F))
        (GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F)) g)) ∈ _
      rw [GlobalTheory.AdelicU.proj_emb_ne (h := hw)]
      exact one_mem _

  have hk' : Lev.finE S k = Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g) *
      Lev.finE S ((gAt S (.inl (PP.under (𝓞 D.host.F))) g)⁻¹ * k) := by
    rw [map_mul, map_inv, mul_inv_cancel_left]
  have hk'S : Lev.finE S ((gAt S (.inl (PP.under (𝓞 D.host.F))) g)⁻¹ * k) ∈ Formalism.L2.DIV.St βS := by
    rw [map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) hkSt
  have hproj1 : GlobalTheory.AdelicU.proj D.sp.cm.sig S.gram (PP.under (𝓞 D.host.F))
      ((gAt S (.inl (PP.under (𝓞 D.host.F))) g)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hpk, hyv, inv_mul_cancel]
  have hR : Formalism.L2.DIV.redFn βS PP (Lev.finE S k) =
      Formalism.L2.DIV.redFn βS PP (Lev.finE S (gAt S (.inl (PP.under (𝓞 D.host.F))) g)) := by
    rw [hk', Formalism.L2.DIV.redFn_mul hyS hk'S, GlobalTheory.T.latticeReduction_eq_one_of_local_component_one D S βS _ PP hk'S hproj1, mul_one]

  have hmulGL : a' ⟨PP, hPP⟩ * Formalism.L2.DIV.redFn βS PP (Lev.finE S k) = a ⟨PP, hPP⟩ := by
    apply Units.ext
    rw [Units.val_mul, hkred PP hPP, ha' ⟨PP, hPP⟩, ha ⟨PP, hPP⟩]
    have htopPP := htop PP hPP
    rw [hred2 PP hPP, hred1 PP hPP] at htopPP
    exact htopPP
  have hrb : ∀ b : ∀ PP : ↥L.Pg, GL (Fin S.rank) (kP PP.1), (fun PP => upperLeftBlock L.hr (b PP)) ∈ L.P.H →
      ∀ PP, upperLeftBlock L.hr (b PP) = 1 := by
    intro b hb PP'
    rw [hH, Subgroup.mem_bot] at hb
    exact congrFun hb PP'
  obtain ⟨h1, h2⟩ := tri_of_mul_eq L.hr hmulGL (haT _) (ha'T _) (hrb a haH _) (hrb a' ha'H _)
  rw [← hR]
  exact ⟨hyS, h1, h2⟩

end GlobalTheory.LocSuppTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeFramePinsFiniteIntegralLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSawAll

variable {D : D7}

theorem real_pos_of_open_compact {X : Type} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] {S : Set X} (ho : IsOpen S) (hc : IsCompact S) (hn : S.Nonempty) : 0 < μ.real S :=
  ENNReal.toReal_pos (ho.measure_ne_zero μ hn) hc.measure_lt_top.ne

theorem level_open_compact (V : HSp D) (L : Lat V) (hL : IsSelfDualC V L) (gP : Finset (Pl D)) (JG : Subgroup (GA D V))
    (hJ : JG ≤ grpAt V (· ∈ gP)) (hJc : IsCompact (JG : Set (GA D V)))
    (hJo : IsOpen (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP)))) :
    IsOpen {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} ∧
      IsCompact {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} ∧
      (1 : GfC V) ∈ {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} := by
  obtain ⟨-, -, -, -, hcomm, ⟨e, he⟩, -, -, hK, -⟩ := GlobalTheory.FinPl.SetCut.grp_split D V gP
  obtain ⟨⟨K₁, hK₁, hK₁c, hK₁o⟩, -⟩ := hK L hL (· ∉ gP)
  have hS : {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} =
      e '' ((((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) ×ˢ
        (((K₁.subgroupOf (grpAt V (· ∉ gP))) : Subgroup _) : Set (grpAt V (· ∉ gP)))) := by
    ext g
    constructor
    · rintro ⟨κ, hκ, k, hk, hg⟩
      have hκ' : κ ∈ grpAt V (· ∉ gP) := hκ.1
      refine ⟨(⟨k, hJ hk⟩, ⟨κ, hκ'⟩), ⟨Subgroup.mem_subgroupOf.2 hk, Subgroup.mem_subgroupOf.2 ((hK₁ κ).2 hκ)⟩, ?_⟩
      apply Subtype.ext
      rw [he, hg, hcomm k (hJ hk) κ hκ']
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      refine ⟨p.2.1, (hK₁ _).1 (Subgroup.mem_subgroupOf.1 hp2), p.1.1, Subgroup.mem_subgroupOf.1 hp1, ?_⟩
      rw [he, hcomm p.1.1 p.1.2 p.2.1 p.2.2]
  have hAc : IsCompact (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) := by
    have h1 : ((JG.subgroupOf (grpAt V (· ∈ gP)) : Subgroup _) : Set (grpAt V (· ∈ gP))) =
        Subtype.val ⁻¹' (JG : Set (GA D V)) := rfl
    rw [h1, Topology.IsInducing.subtypeVal.isCompact_preimage_iff]
    · exact hJc
    · intro x hx; exact ⟨⟨x, hJ hx⟩, rfl⟩
  have hBc : IsCompact (((K₁.subgroupOf (grpAt V (· ∉ gP))) : Subgroup _) : Set (grpAt V (· ∉ gP))) := by
    have h1 : ((K₁.subgroupOf (grpAt V (· ∉ gP)) : Subgroup _) : Set (grpAt V (· ∉ gP))) =
        Subtype.val ⁻¹' (K₁ : Set (GA D V)) := rfl
    rw [h1, Topology.IsInducing.subtypeVal.isCompact_preimage_iff]
    · exact hK₁c
    · intro x hx; exact ⟨⟨x, ((hK₁ x).1 hx).1⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]; exact e.isOpenMap _ (hJo.prod hK₁o)
  · rw [hS]; exact (hAc.prod hBc).image e.continuous
  · exact ⟨1, (hK₁ 1).1 (one_mem _), 1, one_mem _, by simp⟩

variable {c : Comm D}

theorem vr_ne_zero (v : VCom c) (hv : v.Is) (j : ℕ) (hj : j < D.R.m) (hμ : (c.μf j).IsHaarMeasure)
    (R : Subgroup (GA D (c.V j))) (hR : IsClosed (R : Set (GA D (c.V j))))
    (ρ : Measure (R.subgroupOf (GfC (c.V j)))) (hρ : ρ.IsHaarMeasure) : v.vr j R ρ ≠ 0 := by
  obtain ⟨hJle, hJc, hJo⟩ := hv.JG j hj
  obtain ⟨hSo, hSc, hS1⟩ := level_open_compact (c.V j) (v.N j) (hv.sd j hj) v.gP (v.JG j) hJle hJc hJo
  have h1 : 0 < (c.μf j).real {g | g.1 ∈ v.K j} := by
    exact real_pos_of_open_compact (c.μf j) hSo hSc ⟨1, hS1⟩
  have hT : IsClosed (((R.subgroupOf (GfC (c.V j))) : Subgroup _) : Set (GfC (c.V j))) :=
    hR.preimage continuous_subtype_val
  have h2 : 0 < ρ.real {g | g.1.1 ∈ v.K j} := by
    exact real_pos_of_open_compact ρ (hSo.preimage continuous_subtype_val)
      (hT.isClosedEmbedding_subtypeVal.isCompact_preimage hSc) ⟨1, hS1⟩
  unfold VCom.vr
  exact_mod_cast (div_pos h1 h2).ne'

theorem kap_ne_zero (v : VCom c) (hc : c.Is) (hv : v.Is) : ∀ j σ h, v.kap j σ h ≠ 0 := by
  intro j σ h
  unfold VCom.kap
  refine mul_ne_zero ?_ ?_
  · exact vr_ne_zero v hv (j + 1) (by omega) (hc.μf _) _ (GlobalTheory.jacGrp_isClosed _ _ _ _ _) _ (hc.ρJ _ _ _)
  · exact vr_ne_zero v hv (j + 1 + 1) (by omega) (hc.μf _) _ (GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ _ _) _ (hc.ρB _ _ _)

theorem is_withCG (v : VCom c) (a : ℕ → ℂ) (h : v.Is) : (v.withCG a).Is :=
  ⟨h.disj, h.sd, h.sdT, h.b, h.bT, h.Ψ, h.ΨT, h.JG, h.atG, h.atT, h.ram⟩

theorem weilOK_of_tau {t : Tup c} (v v' : VCom c) (hτ : v'.τ = v.τ) (h : WeilOK (t := t) v) : WeilOK (t := t) v' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by rw [hτ]; exact h3⟩

theorem unrOn_mono {t : Tup c} {P P' : Pl D → Prop} (h : t.UnrOn P) (hPP : ∀ x, P' x → P x) : t.UnrOn P' where
  bf j ρ hh x hx := h.bf j ρ hh x (hPP x hx)
  fb j σ hh x hx := h.fb j σ hh x (hPP x hx)
  top j hh := by
    obtain ⟨χS, χT, h1, h2⟩ := h.top j hh
    exact ⟨χS, χT, h1, fun x hx => h2 x (hPP x hx)⟩

end GlobalTheory.SeeSawAll

namespace GlobalTheory.SeeSaw

theorem pins_finiteIntegrals : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (n : ℕ) (G : Fin n → GLoc v), c.Is → c.VolLast → v.Is → ShapeOff v o → GPin G → ∃ (ε : ℕ → ι → 𝓀[k]ˣ) (op : ∀ j, BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ℕ → ι → ℝ) (e : ℕ → ι → ℤ) (a : ℕ → ℂ), (∀ j i, 0 < r j i) ∧ (∀ j, a j ≠ 0) ∧ (∀ j σ h, v.kap j σ h ≠ 0) ∧ ((v.withT (o.S ε) op).withCG a).Is ∧ ∀ (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), (∀ s, (t s).Is ∧ VForm ((v.withT (o.S ε) op).withCG a) (w s) ∧ WeilOK (t := t s) v ∧ TopSph (t := t s) v ∧ (t s).UnrOn (offP v (w s)) ∧ (t s).UnrK (· ∈ v.tP) ∧ (∀ i, (G i).Chars (t s)) ∧ QLaw v (w s) ∧ QLast v (w s) ∧ QFin v (w s) ∧ (∀ j ρ h, (w s).cT j = o.mono (r j) (e j) ((t s).sBF j ρ h).χW) ∧ CVEq ((v.withT (o.S ε) op).withCG a) (w s)) → (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  intro D c v k _ _ _ _ ι o n G hc hvl hv hsh hG
  obtain ⟨ε, op, r, e, hr, hvT, hT⟩ := GlobalTheory.T.seesaw_levelPrime_law_all_tuples D c v k ι o hc hv hsh
  obtain ⟨a, ha, hGa⟩ := GlobalTheory.T.seeSawUnfolded_support_and_value_at_fixed_level D c v n G hc hv hG
  have hv' : ((v.withT (o.S ε) op).withCG a).Is := GlobalTheory.SeeSawAll.is_withCG _ a hvT
  refine ⟨ε, op, r, e, a, hr, ha, GlobalTheory.SeeSawAll.kap_ne_zero v hc hv, hv', ?_⟩
  intro 𝒯 t w hw
  refine GlobalTheory.T.seesaw_place_laws_give_finite_integral_laws D c ((v.withT (o.S ε) op).withCG a) 𝒯 t w hc hvl hv' (fun s => (hw s).1) (fun s => ?_)
  obtain ⟨hts, hform, hweil, hsph, hunr, hunrK, hch, hql, hqlast, hqfin, hcT, hcv⟩ := hw s
  have hdisjT : Disjoint (w s).Q v.tP := hform.disjT
  have hoff : OffLaw v (w s) := GlobalTheory.T.seesaw_support_off_level_of_lattice_shape D c v k ι o hc hv hsh (t s) (w s) hts hdisjT hunr
  have hvac : VacLaw (t := t s) v := GlobalTheory.T.seeSawUnfoldedVacuaOfShape_proof D c v k ι o hc hv hsh (t s)
  have hunrT : (t s).UnrOn (· ∈ v.tP) := GlobalTheory.SeeSawAll.unrOn_mono hunr fun x hx =>
    ⟨fun hg => Finset.disjoint_left.mp hv.disj hg hx, fun hq => Finset.disjoint_left.mp hdisjT hq hx⟩
  have htl : TLaw (v.withT (o.S ε) op) (w s) := hT (t s) (w s) hts hweil hunrT hunrK hcT
  obtain ⟨hgs, hgv⟩ := hGa (t s) hts hweil hch
  exact ⟨hform, GlobalTheory.SeeSawAll.weilOK_of_tau v _ rfl hweil, hoff, hgs, hgv, hvac, htl, hql, hqlast, hqfin, hcv, hsph⟩

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_bound : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ∀ hy : (y : GL _ _) ∈ (F0 W u).cls0.lev.U, ∃ x : ∀ i, (a.G i).S.P.J, (∀ (i : Fin _) (p q : Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (p' q' : Fin (I.rec7 l Z).R.r),
        p'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ p → q'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ q → ∀ z : 𝓞 (I.rec7 l Z).host.E,
        Ideal.Quotient.mk (a.pl i).1.asIdeal z = (GlobalTheory.FamTraceChi.reductionYZero W ((show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)⁻¹ * embA a.d.B.d a.d.B.o κ * (show GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0) from a.g.b 0)) (a.pl i)).val p' q' →
        valuation (a.G i).k (((x i : GL (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.G i).s + 1)) (a.G i).k)).val p q - (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) < 1) ∧
      (((F0 W u).cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) * ∏ i, (((a.G i).S.P.lam (x i) : ℂˣ) : ℂ) = 1 := by
  first | exact @GlobalTheory.FamTraceChiCol.colChi_mul_prod_lam | exact GlobalTheory.FamTraceChiCol.colChi_mul_prod_lam | (intros; apply GlobalTheory.FamTraceChiCol.colChi_mul_prod_lam <;> assumption)
end

