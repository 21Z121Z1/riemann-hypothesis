import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatLConjIIffHform
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0762
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0698
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0697
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0696
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0702
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0699
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0705
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0763
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalGrid
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCongruenceSubgroupOfStabilisesAndCongruent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section

namespace GlobalTheory.CongAssemble

open Matrix

variable {D : D7}

theorem isIntM_of_smul_maps {n : ℕ} {β : GL (Fin n) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hfr : Formalism.L2.DIV.IsFrame β Λ) (s : Lev.EAf D) (M : Matrix (Fin n) (Fin n) (Lev.EAf D))
    (h : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, s • (M *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    IsIntM (s • ((β⁻¹ : GL (Fin n) (Lev.EAf D)).1 * M * β.1)) := by
  intro i j
  have h1 := (hfr _).1 (h _ (GlobalTheory.FrameIdeal.col_mem_hatL hfr j)) i
  have e1 : (β⁻¹ : GL (Fin n) (Lev.EAf D)).1 *ᵥ (s • (M *ᵥ (β.1 *ᵥ Pi.single j 1))) =
      s • (((β⁻¹ : GL (Fin n) (Lev.EAf D)).1 * M * β.1) *ᵥ Pi.single j 1) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e1, Matrix.mulVec_single_one] at h1
  simpa [Matrix.smul_apply] using h1

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem cong_assemble : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ →
    ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ 𝔪 : Ideal (𝓞 D.host.E),
    (∀ PP : Pl D.host.E, 𝔪 ≤ PP.asIdeal → PP ∈ Z) → ∀ g : GA D V,
    (∀ v, (∀ PP ∈ Z, PP.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) →
    (∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      toEAf D e • ((Lev.finE V g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • (((Lev.finE V g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ∧
      toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) →
    Lev.finE V g ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  classical
  intro D V Λ hsd Z e hZe 𝔪 h𝔪 g hg hx
  obtain ⟨β, hfr⟩ := frame_exists_alt D.host.F D.host.E V.rank Λ hsd.1
  have hUA := GlobalTheory.LevSplit.finE_mem_UA V g
  have hγ : (β⁻¹ * Lev.finE V g * β : GL (Fin V.rank) (Lev.EAf D)).1 =
      (β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * (Lev.finE V g).1 * β.1 := by
    simp only [Units.val_mul]
  have hγi : ((β⁻¹ * Lev.finE V g * β)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 =
      (β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * ((Lev.finE V g)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 * β.1 := by
    simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  have h1 : IsIntM (toEAf D e • (β⁻¹ * Lev.finE V g * β : GL (Fin V.rank) (Lev.EAf D)).1) := by
    rw [hγ]; exact isIntM_of_smul_maps hfr _ _ fun x hx' => (hx x hx').1
  have h2 : IsIntM (toEAf D e • ((β⁻¹ * Lev.finE V g * β)⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1) := by
    rw [hγi]; exact isIntM_of_smul_maps hfr _ _ fun x hx' => (hx x hx').2.1
  obtain ⟨h3, h4⟩ := GlobalTheory.T.selfDualFrame_conj_integral_smul_of_integral V Λ β hsd hfr _ hUA _ rfl e h1 h2
  obtain ⟨hεε, hεc⟩ := GlobalTheory.T.idempotentSum_add_conj_idempotent_conj_fixed Z e hZe
  obtain ⟨k, -, hmt⟩ := GlobalTheory.T.exists_idempotent_component_of_group_element V (GlobalTheory.LevelNbhd.finPartG V g) (e + cA D e)
    (GlobalTheory.LevelNbhd.finPartG_mem_GfC V g) hεε hεc
  have hfk := GlobalTheory.T.finiteEmbedding_idempotent_patch_in_frame V β _ k (e + cA D e) hmt
  rw [GlobalTheory.SuppLevO.finE_finPartG] at hfk
  obtain ⟨hSt, -⟩ := GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction V.rank β _ _ Z e hZe h1 h2 h3 h4 hfk
  have hcomp : ∀ PP ∈ Z, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (PP.under (𝓞 D.host.F)) k =
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (PP.under (𝓞 D.host.F)) g := fun PP hP => by
    rw [← GlobalTheory.SuppLevO.proj_finPartG V g]
    exact GlobalTheory.T.localProjection_eq_of_idempotent_patch V _ _ k _ (GlobalTheory.T.adeleTensorComponent_idempotentSum_add_conj_eq_one Z e hZe PP hP) hmt
  have hkloc := (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr k).1 hSt
  have hgSt : Lev.finE V g ∈ Formalism.L2.DIV.St β := by
    refine (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D V β Λ hfr g).2 fun v => ?_
    by_cases hv : ∃ PP ∈ Z, PP.under (𝓞 D.host.F) = v
    · obtain ⟨PP, hP, rfl⟩ := hv
      rw [← hcomp PP hP]
      exact hkloc _
    · push_neg at hv
      exact hg v hv
  have hfw := GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β _ hfr hgSt
  have hbw := GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β _ hfr (inv_mem hgSt)

  have h𝔪0 : 𝔪 ≠ ⊥ := by
    intro h0
    haveI := GlobalTheory.LvT.Inh.ResFin.infinite_places D.host.E
    exact Set.infinite_univ (Z.finite_toSet.subset fun PP _ => h𝔪 PP (by rw [h0]; exact bot_le))
  have hrad : (∏ PP ∈ Z, PP.asIdeal) ≤ 𝔪.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun J ⟨hJ, hJp⟩ => ?_
    have hJ0 : J ≠ ⊥ := fun h => h𝔪0 (le_bot_iff.1 (h ▸ hJ))
    have hQ := h𝔪 ⟨J, hJp, hJ0⟩ hJ
    calc (∏ PP ∈ Z, PP.asIdeal) = (∏ PP ∈ Z.erase ⟨J, hJp, hJ0⟩, PP.asIdeal) * J := (Finset.prod_erase_mul _ _ hQ).symm
      _ ≤ J := by first | exact Ideal.mul_le_left | exact Ideal.mul_le_right | exact Ideal.mul_le_left'
  obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg 𝔪 (IsNoetherian.noetherian _)
  have hle : (∏ PP ∈ Z, PP.asIdeal ^ N) ≤ 𝔪 := by
    rw [Finset.prod_pow]
    exact (Ideal.pow_right_mono hrad N).trans hN
  obtain ⟨t, ht, htv⟩ := (GlobalTheory.IdemSumIdeal.isIdemSum_props e Z (fun _ => N) hZe).2.2
  refine GlobalTheory.ChiGrid.mem_congLev.2 ⟨hUA, fun x => ⟨fun hx' => hfw x hx', fun hx' => ?_⟩, fun x hx' => ?_⟩
  · have := hbw _ hx'
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  · have hw : (Lev.finE V g).1 *ᵥ x - x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := Submodule.sub_mem _ (hfw x hx') hx'
    have e1 : (Lev.finE V g).1 *ᵥ x - x = toEAf D e • ((Lev.finE V g).1 *ᵥ x - x) +
        (1 - toEAf D e) • ((Lev.finE V g).1 *ᵥ x - x) := by
      rw [← add_smul, add_sub_cancel, one_smul]
    rw [e1]
    refine Submodule.add_mem _ (hx x hx').2.2 ?_
    rw [← htv]
    exact Submodule.span_mono (Set.image_mono (Submodule.smul_mono_left hle)) (GlobalTheory.FrameIdeal.idS_smul_mem_hatL Λ ht hw)

end GlobalTheory.CongAssemble
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestColumnInductionLocalToGlobalExpansion
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

set_option maxHeartbeats 1000000 in

theorem columnInduction : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∀ (I : locPl ch.G t → Type) (S : ∀ w, Finset (I w)) (x : ∀ w, I w → ℂ) (d : ∀ w, I w → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : ∀ w, I w → Combs ch.G), (∀ w, ∀ i ∈ S w, ∀ j : Fin D.R.m, (d w i j).e = eL w ∧ IsCombOf ch.W (d w i j) ((c w i).1 j)) → (∀ w (y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))), (∀ j, IsHalf (eL w) (y j)) → ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 y) 0) → ∃ (J : Type) (SJ : Finset J) (xJ : J → ℂ) (dJ : J → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (cJ : J → ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ a ∈ SJ, ∀ j : Fin D.R.m, (dJ a j).e = e ∧ IsCombOf ch.W (dJ a j) (cJ a j)) ∧ (∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (u j)) → ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 u) 0) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ u : ColPt ch.G, evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) 1 u 0 = (∏ w, ζ w) * ∑ a ∈ SJ, xJ a * evT (combC ch.W (cJ a, 0) (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
  refine big_mono (fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch h => ?_)
    (((GlobalTheory.T.rowTest_doubleCosetPoints_chain_place_by_place.and GlobalTheory.T.subset_place_vectors_and_steps).and (GlobalTheory.T.fockVectors_pass_placeModels_largeDepth.and GlobalTheory.T.exists_combinationOperator_columnProduct)).and ((GlobalTheory.T.columnCombinations_compose_largeDepth.and GlobalTheory.T.productFiniteDatum_largeDepth).and (GlobalTheory.T.columnAt_reads_placePart_largeDepth.and GlobalTheory.T.vacuumDatum_trivialCombination_largeDepth)))
  obtain ⟨⟨⟨hA, hB⟩, hC, hD⟩, ⟨hE, hF⟩, hG, hZ⟩ := h
  intro s t β ζ hζ M hM b b₀ hb hb₀ e he φ hφ fd hfd eL heL I S x d c hdc hexp
  obtain ⟨he_sum, hsub, hmul⟩ := GlobalTheory.T.isIdemSum_eq_sum_singlePlaces D e (locPl ch.G t) he eL heL
  obtain ⟨V, hV0, hVu, hVth, hVst⟩ := hB t e he φ hφ fd hfd eL heL
  have hpts := fun (p : Pts ch.G) (hp : IsRealPt p) => hA s t β b b₀ hb hb₀ eL heL p hp
  choose q hq0 hqu hqst using hpts
  choose Tc hTc using hD
  obtain ⟨fl, hfl⟩ : ∃ fl : locPl ch.G t → (∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) → ℂ,
      ∀ w y, fl w y = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1)
        (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w))
          ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 y) 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hexp' : ∀ w y, (∀ j, IsHalf (eL w) (y j)) → ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (y j) = fl w y :=
    fun w y hy => (hexp w y hy).trans (hfl w y).symm
  have hflG : ∀ (w' : locPl ch.G t) (e' : AE D), e' * eL w' = eL w' → ∀ u, fl w' (fun j => e' • u j) = fl w' u := by
    intro w' e' he' u
    rw [hfl, hfl, hG t w' (eL w') e' (heL w') he' u]

  have hcomb1 : ∀ (S' T' : HSp D) (f : WO S' T' → ℂ), comb ch.W.ψ S' T' (Finsupp.single 0 1) f = f := by
    intro S' T' f
    rw [GlobalTheory.DisjComb.comb_single]
    funext y
    simp [heisO, symplOH, symplO, hO]
  have hcombC1 : ∀ C : BiFam ch.G, combC ch.W ((fun _ => Finsupp.single 0 1), 0) C = C := by
    intro C
    funext j y z
    simp only [combC, biComb, hcomb1]

  have hidem : ∀ (S' : Finset (locPl ch.G t)), (∑ w ∈ S', eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S', eL w := by
    intro S'
    rw [hmul, Finset.inter_self]
  have hidem1 : ∀ w : locPl ch.G t, eL w * eL w = eL w := by
    intro w
    have h := hmul {w} {w}
    rw [Finset.inter_self, Finset.sum_singleton] at h
    exact h
  have hsubmul : ∀ (S' : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∈ S' → (∑ w ∈ S', eL w) * eL w = eL w := by
    intro S' w hw
    have h := hmul S' {w}
    rw [Finset.inter_singleton_of_mem hw, Finset.sum_singleton] at h
    exact h
  have hhalf : ∀ (a : AE D), a * a = a → ∀ {m n : ℕ} (y : Mx D m n), IsHalf a (a • y) := by
    intro a ha m n y i j
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ha]
  have key : ∀ S' : Finset (locPl ch.G t), ∃ (J : Type) (SJ : Finset J) (xJ : J → ℂ)
      (dJ : J → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j))
      (cJ : J → ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ),
      (∀ a ∈ SJ, ∀ j : Fin D.R.m, (dJ a j).P = S'.map (Function.Embedding.subtype _) ∧
        (dJ a j).e = ∑ w ∈ S', eL w ∧ IsCombOf ch.W (dJ a j) (cJ a j)) ∧
      (∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf (∑ w ∈ S', eL w) (u j)) →
        ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j) = ∏ w ∈ S', fl w u) ∧
      ∀ (P : PolDown ch.G) (p : Pts ch.G) (hp : IsRealPt p) (u : ColPt ch.G),
        evT (conAt ch.W hM (fockD ch.W t (V S') P) (q p hp S')) 1 u 0 = (∏ w ∈ S', ζ w) * ∑ a ∈ SJ, xJ a *
          evT (combC ch.W (cJ a, 0) (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
    intro S'
    induction S' using Finset.induction_on with
    | empty =>
      refine ⟨Unit, {()}, fun _ => 1, fun _ j => FinDatum.vacuum ch.G t (.top t j), fun _ _ => Finsupp.single 0 1, ?_, ?_, ?_⟩
      · intro a _ j
        refine ⟨?_, ?_, hZ t j⟩
        · rw [Finset.map_empty]; rfl
        · rw [Finset.sum_empty]; rfl
      · intro u hu
        have h0 : ∀ j, u j = 0 := by
          intro j
          ext a b'
          have := hu j a b'
          rw [Finset.sum_empty, zero_mul] at this
          exact this.symm
        simp only [Finset.sum_singleton, Finset.prod_empty, one_mul]
        refine Finset.prod_eq_one fun j _ => ?_
        rw [h0 j]
        show halfInd (0 : AE D) _ 0 = 1
        unfold halfInd
        rw [if_pos ⟨zero_mem _, fun a b' => by simp⟩]
      · intro P p hp u
        simp only [hV0, hq0 p hp, Finset.prod_empty, Finset.sum_singleton, one_mul, hcombC1]
    | insert w S₀ hw ih =>
      obtain ⟨J, SJ, xJ, dJ, cJ, h1, h2, h3⟩ := ih
      have hPw : ∀ i ∈ S w, ∀ j : Fin D.R.m, (d w i j).P = {w.1} := by
        intro i hi j
        have h := (d w i j).e_is
        rw [(hdc w i hi j).1] at h
        exact GlobalTheory.T.isIdemSum_places_unique D _ _ _ h (heL w)
      have hsum : ∑ w' ∈ insert w S₀, eL w' = eL w + ∑ w' ∈ S₀, eL w' := Finset.sum_insert hw
      have hmap : (insert w S₀).map (Function.Embedding.subtype (· ∈ locPl ch.G t)) =
          {w.1} ∪ S₀.map (Function.Embedding.subtype (· ∈ locPl ch.G t)) := by
        rw [Finset.map_insert, Finset.insert_eq]; rfl
      have hs : IsIdemSum (eL w + ∑ w' ∈ S₀, eL w') ({w.1} ∪ S₀.map (Function.Embedding.subtype _)) := by
        have := hsub (insert w S₀)
        rwa [hsum, hmap] at this
      have hF' : ∀ (k : I w × J) (j : Fin D.R.m),
          ∃ (dd : FinDatum ch.G t (.top t j)) (cc : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), k.1 ∈ S w → k.2 ∈ SJ →
            dd.P = (d w k.1 j).P ∪ (dJ k.2 j).P ∧ dd.e = (d w k.1 j).e + (dJ k.2 j).e ∧ IsCombOf ch.W dd cc ∧
            (∀ y, IsHalf dd.e y → dd.fn y = (d w k.1 j).fn ((d w k.1 j).e • y) * (dJ k.2 j).fn ((dJ k.2 j).e • y)) ∧
            ∀ f, comb ch.W.ψ _ _ cc f = comb ch.W.ψ _ _ ((c w k.1).1 j) (comb ch.W.ψ _ _ (cJ k.2 j) f) := by
        intro k j
        by_cases hk : k.1 ∈ S w ∧ k.2 ∈ SJ
        · have hId : IsIdemSum ((d w k.1 j).e + (dJ k.2 j).e) ((d w k.1 j).P ∪ (dJ k.2 j).P) := by
            rw [(hdc w k.1 hk.1 j).1, (h1 k.2 hk.2 j).2.1, hPw k.1 hk.1 j, (h1 k.2 hk.2 j).1]
            exact hs
          obtain ⟨dd, cc, hh⟩ := hF t j (d w k.1 j) (dJ k.2 j) ((c w k.1).1 j) (cJ k.2 j) hId
            (hdc w k.1 hk.1 j).2 (h1 k.2 hk.2 j).2.2
          exact ⟨dd, cc, fun _ _ => hh⟩
        · exact ⟨FinDatum.vacuum ch.G t (.top t j), 0, fun h1' h2' => absurd ⟨h1', h2'⟩ hk⟩
      choose dF cF hdF using hF'
      refine ⟨I w × J, S w ×ˢ SJ, fun k => x w k.1 * xJ k.2, dF,
        fun k j => if h : j < D.R.m then cF k ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
      · intro k hk j
        obtain ⟨hk1, hk2⟩ := Finset.mem_product.1 hk
        obtain ⟨hP, he', hc, -, -⟩ := hdF k j hk1 hk2
        refine ⟨?_, ?_, ?_⟩
        · rw [hP, hPw k.1 hk1 j, (h1 k.2 hk2 j).1, hmap]
        · rw [he', (hdc w k.1 hk1 j).1, (h1 k.2 hk2 j).2.1, hsum]
        · dsimp only
          rw [dif_pos j.2]
          exact hc
      · intro u hu
        have hu' : ∀ j, IsHalf (eL w + ∑ w' ∈ S₀, eL w') (u j) := fun j => by rw [← hsum]; exact hu j
        have hfn : ∀ k ∈ S w ×ˢ SJ, ∀ j, (dF k j).fn (u j) =
            (d w k.1 j).fn (eL w • u j) * (dJ k.2 j).fn ((∑ w' ∈ S₀, eL w') • u j) := by
          intro k hk j
          obtain ⟨hk1, hk2⟩ := Finset.mem_product.1 hk
          obtain ⟨-, he', -, hfn', -⟩ := hdF k j hk1 hk2
          rw [hfn' (u j) (by rw [he', (hdc w k.1 hk1 j).1, (h1 k.2 hk2 j).2.1]; exact hu' j), (hdc w k.1 hk1 j).1,
            (h1 k.2 hk2 j).2.1]
        have hA' : ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (eL w • u j) = fl w u :=
          (hexp' w _ fun j => hhalf _ (hidem1 w) (u j)).trans (hflG w (eL w) (hidem1 w) u)
        have hB' : ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn ((∑ w' ∈ S₀, eL w') • u j) = ∏ w' ∈ S₀, fl w' u :=
          (h2 _ fun j => hhalf _ (hidem S₀) (u j)).trans
            (Finset.prod_congr rfl fun w' hw' => hflG w' _ (hsubmul S₀ w' hw') u)
        rw [Finset.sum_congr rfl fun k hk => by rw [Finset.prod_congr rfl fun j _ => hfn k hk j],
          Finset.sum_product, Finset.prod_insert hw, ← hA', ← hB', Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
      · intro P p hp u
        obtain ⟨r, r₀, h, hr, hr₀, htl, hhr, hhr₀⟩ := hqst p hp S₀ w hw
        have hloc := fun j => hC t (eL w) (V S₀) (V (insert w S₀)) P j _ (hVth S₀ j) (hVst S₀ w hw j)
        have hPC := hζ w (eL w) (heL w) M hM r r₀ h hr hr₀ htl (GlobalTheory.LocAsm.exOne (φ w)) (fun _ _ _ => rfl)
          (fockD ch.W t (V S₀) P) (fockD ch.W t (V (insert w S₀)) P) (fun j => (hloc j).1) (fun j => (hloc j).2)
          (I w) (S w) (x w) (d w) (c w) (hdc w) (hexp w) u
        rw [← hhr, hPC, hhr₀]
        have hIH : (fun u => evT (conAt ch.W hM (fockD ch.W t (V S₀) P) (q p hp S₀)) 1 u 0) =
            (∏ w' ∈ S₀, ζ w') • ∑ a ∈ SJ, xJ a • (fun u => evT (combC ch.W (cJ a, 0)
              (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0) := by
          funext u'
          rw [h3 P p hp u']
          simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
        have hstep : ∀ i ∈ S w, evT (combC ch.W (c w i) (conAt ch.W hM (fockD ch.W t (V S₀) P) (q p hp S₀))) 1 u 0 =
            (∏ w' ∈ S₀, ζ w') * ∑ a ∈ SJ, xJ a * evT (combC ch.W ((fun j => if h : j < D.R.m then cF (i, a) ⟨j, h⟩ else 0), 0)
              (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
          intro i hi
          rw [congrFun (hTc (c w i) _) u, hIH, map_smul, map_sum]
          simp only [map_smul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
          congr 1
          refine Finset.sum_congr rfl fun a ha => ?_
          congr 1
          rw [← congrFun (hTc (c w i) _) u]
          refine hE (c w i) (cJ a) _ ?_ _ u
          intro j hj f
          rw [dif_pos hj]
          exact (hdF (i, a) ⟨j, hj⟩ hi ha).2.2.2.2 f
        rw [Finset.prod_insert hw, Finset.sum_product, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hstep i hi]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
  obtain ⟨J, SJ, xJ, dJ, cJ, h1, h2, h3⟩ := key Finset.univ
  refine ⟨J, SJ, xJ, dJ, cJ, fun a ha j => ⟨(h1 a ha j).2.1.trans he_sum.symm, (h1 a ha j).2.2⟩, fun u hu => ?_,
    fun P p hp u => ?_⟩
  · rw [h2 u (fun j => by rw [← he_sum]; exact hu j)]
    exact Finset.prod_congr rfl fun w _ => hfl w u
  · have := h3 P p hp u
    rwa [hVu, hqu p hp] at this

end GlobalTheory.LocAsm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSquareIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.SquareAgree.StabKW

theorem stab_kW : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (1, k) ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
  intro _hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _hθ _hTr _hO hT Pi rf rl p p' _hm k hk ΦD hΦD
  have hdet : Γ.V.J.det ≠ 0 ∧ Γ.W.J.det ≠ 0 :=
    ⟨GlobalTheory.FinUniq.det_ne_zero_herm hT.geo.hV, GlobalTheory.FinUniq.det_ne_zero_skew hT.geo.hW⟩
  have key := GlobalTheory.T.compactUnitary_preserves_polynomialFock D.host.F D.host.E D.sp.cm.sig hT.base.cm W.rank (W.rank + W₁.rank) Γ.V Γ.W Γ.M Bs.ψ Xc.β
    (Xc.β / Xc.α) om hT.base.std hT.geo.hV.herm hdet.1 hT.geo.hW.skew hdet.2 hT.chars.resβ
    (GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resβ hT.chars.resα) hT.chars.heckeβ
    (GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeβ hT.chars.heckeα) hT.weil Bs.emb hT.geo.hV.cartan hT.geo.hW.cartan k hk
  have hgen : {Φ | ∃ f φ, f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧
      (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) ∧ Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ} ⊆
      ((algD Γ.M Bs.ψ Bs.emb).comap (om (1, k)) : Set _) := by
    rintro _ ⟨f, φ, hf, hSB, hcof, rfl⟩
    obtain ⟨⟨f₁, hf₁⟩, hpol⟩ := key f hf
    have hstd : ∀ᶠ v in Filter.cofinite,
        φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
      (hcof.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2
    have hrest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑f) (GlobalTheory.EvZeroInf.finPart φ) :=
      ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add φ x z hz, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have h := hf₁ _ hrest
    rw [← GlobalTheory.EvZeroInf.pure_eq_tens, ← GlobalTheory.EvZeroInf.pure_eq_tens] at h
    show om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ algD Γ.M Bs.ψ Bs.emb
    rw [h]
    exact Submodule.subset_span ⟨f₁, φ, hpol f₁ hf₁, hSB, hcof, rfl⟩
  exact (Submodule.span_le.2 hgen) hΦD

end GlobalTheory.SquareAgree.StabKW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdExpansionFunctionsRowVertexInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_prod_expansion_functions_rowVertex_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ c₁ c₂ : ℂ, W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) → W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) = c₂ • S.Z.vac (.chi (j + 1) D.R.m) → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) (z a)) = τ.sum fun d c => c * ∏ a, fnOf d a (z a) := by
  first | exact @GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq | exact GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq | (intros; apply GlobalTheory.RowVertexInv.sum_prod_scale_movFn_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridPairingBoundMemCompletionOfMapBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGrid_pairingBound_mem_completion_of_mapBound : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))) (v : GlobalTheory.FinPl.Pl D), (∀ y ∈ latV (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) (· = v)) → ∀ p : Fin (σ + 1), GlobalTheory.FinPlLoc.idem D (· = v) * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) ∈ GlobalTheory.SeeSaw.idV (D.host.AA * D.host.AAbar) v := by
  first | exact @GlobalTheory.CharXFB.PairAt.pair_mem_AA_AAbar | exact GlobalTheory.CharXFB.PairAt.pair_mem_AA_AAbar | (intros; apply GlobalTheory.CharXFB.PairAt.pair_mem_AA_AAbar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalGridStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_vertical_cuspidal_grid : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F l (v l) g) (G.meas t i j).fd (G.meas t i j).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F l (v l) g ∂(G.meas t i j).ν‖ < ε := by
  first | exact @GlobalTheory.CuspApproxX.approx_lift_main | exact GlobalTheory.CuspApproxX.approx_lift_main | (intros; apply GlobalTheory.CuspApproxX.approx_lift_main <;> assumption)
end

