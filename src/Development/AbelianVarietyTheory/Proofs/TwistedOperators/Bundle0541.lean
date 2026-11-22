import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsRemoveBlockArrow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0432
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowArrowExistsCommonRealIntertwiner
section
noncomputable section

section Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix
open GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowThetaIt

theorem itPair_of_par (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) {D : D7} {V W : HSp D}
    {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') {θ : InfFam D} (hθ : IsInfFam θ)
    (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ)
    (hP : ∀ τ, ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      S τ = dualPar (signed (al ++ be) (ga ++ de) (aT τ)) ∧
      S' τ = dualPar (signed (al ++ Formalism.BasicNotions.TH.block t ++ de) (ga ++ be) (aS τ))) :
    ∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, It ≠ 0 ∧
      ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ),
        GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ => by
    obtain ⟨t, al, be, ga, de, hd, e1, e2⟩ := hP τ
    exact exists_locIt hX h1 h2 (GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D) M M' τ hd e1 e2
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  refine ⟨It, hI.ne, fun ω f ⟨χS, χT, hω, he⟩ hf => ?_⟩
  have hv := fun τ => GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2 (fun τ => (hv τ).2.1)
    fun τ => (hv τ).2.2

end GlobalTheory.RowThetaIt

end Gen

section Par

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid GlobalTheory.PairLift GlobalTheory.SignedHC GlobalTheory.RemoveBlock
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowThetaIt

theorem dataAR_row (D : D7) (hS : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (i j : ℕ) (τ : D.what₂.Tau) (hi : i ≤ D.R.m) (hj : j < D.R.m) :
    ∃ (t : ℕ) (al be ga de : List ℚ), Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧
      parV D i j τ = dualPar (signed (al ++ be) (ga ++ de) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1)))) ∧
      parV D i (j + 1) τ =
        dualPar (signed (al ++ Formalism.BasicNotions.TH.block t ++ de) (ga ++ be) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j))) := by
  have he : (D.hc τ).e ⟨j, hj⟩ = ((grid D τ).e (j + 1) : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)).2.2 ⟨j, hj⟩
  set G := grid D τ with hG
  set δ : ℚ := if Odd (i + j) then -(1 / 2) else 0 with hδ
  set δ' : ℚ := if Odd (i + (j + 1)) then -(1 / 2) else 0 with hδ'
  have hT : att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1)) = -(G.e (j + 1) : ℚ) + δ := by
    simp only [att, he, hδ]
    by_cases h : Odd (i + j)
    · have h' : Odd (rkV D i (j + 1)) := by rw [odd_rkV, show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h, h', if_true]; ring
    · have h' : ¬ Odd (rkV D i (j + 1)) := by rw [odd_rkV, show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h, h', if_false]; ring
  have hS' : att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j) = -(G.e (j + 1) : ℚ) + δ' := by
    simp only [att, he, hδ']
    by_cases h : Odd (i + j)
    · have h' : Odd (rkV D i j) ↔ False := by rw [odd_rkV]; tauto
      have h'' : Odd (i + (j + 1)) ↔ False := by rw [show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h', h'', if_false]; ring
    · have h' : Odd (rkV D i j) := by rw [odd_rkV]; tauto
      have h'' : Odd (i + (j + 1)) := by rw [show i + (j + 1) = i + j + 1 by ring, Nat.odd_add_one]; tauto
      simp only [h', h'', if_true]; ring
  rw [hT, hS']
  set P := shift δ (G.parD i j) with hP
  have hpart := partner_parD D τ i j hi hj δ δ'
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hN : 1800 < bigN D := by
    have h1 := hS.1
    have h2 : D.R.m ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold bigN; unfold Ranks.r at h1
    omega
  have hgap : GapOver P (2 * (bigN D : ℚ) ^ 3) := GlobalTheory.RemoveBlock.gapOver_shift (gapOver_parD D hS τ i j hi hj.le)
  have hgap' : GapOver (partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) (-(G.e (j + 1) : ℚ) + δ') P)
      (2 * (bigN D : ℚ) ^ 3) := by
    rw [hP, ← hpart]; exact GlobalTheory.RemoveBlock.gapOver_shift (gapOver_parD D hS τ i (j + 1) hi hj)
  have hreg : IsRegular P := isRegular_of_gapOver (by positivity) hgap
  have hfar3 : FarFrom (-(G.e (j + 1) : ℚ) + δ) (((D.R.t : ℚ) + 3) / 2) P := farFrom_shift (farFrom_parD D τ i j hi hj)
  have hfar1 : FarFrom (-(G.e (j + 1) : ℚ) + δ) (((D.R.t : ℚ) + 1) / 2) P := fun x hx =>
    le_trans (by linarith) (hfar3 x hx)
  have hne : P.Nonempty := by
    have hv : ((grid D τ).v 2 : ℚ) ∈ (grid D τ).cloud :=
      GridData.mem_cloud.2 ⟨2, le_rfl, by have := D.R.m_add_three_le_k; show 2 ≤ D.R.k; omega, rfl⟩
    have hmem : (((grid D τ).v 2 : ℚ), true) ∈ (grid D τ).parD i j := GridData.mem_parD.2 (Or.inl ⟨hv, rfl⟩)
    exact ⟨_, mem_shift' hmem⟩
  have hcard : P.card + D.R.t ≤ bigN D := by
    rw [hP, card_shift]
    have h0 : (G.parD i j).card ≤ rkV D i j := card_parD_le D τ i j hi
    have a : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
    have b : i * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
    have c : D.R.m * (D.R.t + sLen D + 1) = D.R.m * D.R.t + D.R.m * sLen D + D.R.m := by ring
    have d : (j + 1) * D.R.t = j * D.R.t + D.R.t := by ring
    show _ ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
    unfold rkV Ranks.r at h0
    omega
  have hcos : InCoset (-(G.e (j + 1) : ℚ) + δ + ((D.R.t : ℚ) + 1) / 2) (entries P) := by
    intro x hx
    obtain ⟨s, hs⟩ := mem_entries.1 hx
    have hy := fst_mem_entries (mem_shift.1 hs)
    obtain ⟨z, hz⟩ := int_parD D τ i j _ hy
    simp only at hz
    obtain ⟨q, hq⟩ := D.R.t_odd
    have htq : ((D.R.t : ℚ) + 1) / 2 = q + 1 := by rw [hq]; push_cast; ring
    refine ⟨z + G.e (j + 1) - (q + 1), ?_⟩
    rw [htq]; push_cast; linarith
  obtain ⟨al, be, ga, de, hPe, hP'⟩ :=
    GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter D.R.t true _ _ P (bigN D) ht hne hreg hcos hfar1 hcard hN hgap hgap'
  rcases hP' with ⟨hd, hP'⟩ | ⟨-, hP'⟩
  · refine ⟨D.R.t, al, be, ga, de, hd, ?_, ?_⟩
    · rw [← hPe]; rfl
    · rw [← hP', ← hpart]; rfl
  · exfalso
    set c' : ℚ := -(G.e (j + 1) : ℚ) + δ' with hc'
    have hx0 : ((D.R.t : ℚ) - 1) / 2 ∈ Formalism.BasicNotions.TH.block D.R.t :=
      by simp only [Formalism.BasicNotions.TH.block, List.mem_map, List.mem_range]; simp; exact ⟨0, by omega, by simp⟩
    have m1 : (((D.R.t : ℚ) - 1) / 2 + c', false) ∈ partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) c' P := by
      rw [hP']
      simp only [signed, Finset.mem_union, List.mem_toFinset, List.mem_map]
      exact Or.inr ⟨_, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hx0))), rfl⟩
    have m2 : (((D.R.t : ℚ) - 1) / 2 + c', true) ∈ partner D.R.t true (-(G.e (j + 1) : ℚ) + δ) c' P := by
      simp only [partner, Finset.mem_union, Finset.mem_image]
      refine Or.inr ⟨_, mem_block.2 ⟨0, by omega, by push_cast; ring⟩, rfl⟩
    have := hgap' _ m1 _ m2 (by simp)
    simp only [sub_self, abs_zero] at this
    have : (0 : ℚ) ≤ 2 * (bigN D : ℚ) ^ 3 := by positivity
    linarith

end GlobalTheory.RowThetaIt

end Par

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowThetaIt

theorem rowTheta_it : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i + 1 ≤ D.R.m → j < D.R.m → ∀ (ω : T → GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V) (f : WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ), (∀ t, GlobalTheory.Grid.IsWeil R.ψ false (G.nV i j).V (G.nV i (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) (ω t)) → GlobalTheory.Grid.IsVac R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f → ∃ It : GlobalTheory.Grid.Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M, ∀ t, IsItW R.θ (G.nV i j).M (G.nV i (j + 1)).M (ω t) (GlobalTheory.Grid.fock R.ψ R.θ false (G.nV i j) (G.nV i (j + 1)) f) It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hD hH _ hSz F hc _ G' W _ G hSp _ _ _ i j hi hj ω f hω hf
  have hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R := ⟨hc.lev, hc.models.inf, hc.models.νY, hc.models.νY', hc.models.νX⟩
  have hV := hSp.vert i j hi hj.le
  have hV' := hSp.vert i (j + 1) hi hj
  obtain ⟨It, -, hIt⟩ := itPair_of_par hD hH (G.nV i j).M (G.nV i (j + 1)).M hR.inf R.ψ
    (fun τ => GlobalTheory.PairLift.att (-(D.hc τ).e ⟨j, hj⟩) (rkV D (i + 1) j))
    (fun τ => GlobalTheory.PairLift.att (-(D.hc τ).e ⟨j, hj⟩) (rkV D (i + 1) (j + 1)))
    (fun τ => by rw [hV.par, hV'.par]; exact dataAR_row D hSz (i + 1) j τ hi hj)
  refine ⟨It, fun t => hIt (ω t) f ⟨_, _, hω t, fun τ =>
    ⟨GlobalTheory.PairLift.hasInfExp_att (GlobalTheory.PairLift.exp_mu hR t hj τ) (GlobalTheory.PairLift.exp_eta hR τ) _,
      GlobalTheory.PairLift.hasInfExp_att (GlobalTheory.PairLift.exp_mu hR t hj τ) (GlobalTheory.PairLift.exp_eta hR τ) _⟩⟩
    ⟨hf.isFinVec.1, GlobalTheory.PairLift.vac_ne hf, hf.isFinVec.2⟩⟩

end GlobalTheory.RowThetaIt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergRootSmulFiniteRationalLatticeDecomp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MultLatDecomp

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem heisO_eq_root_smul_finRat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ n : ℕ, 0 < n → ∀ w : WO S T, n • w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (ζ : ℂ), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ GlobalTheory.VacUnique.finRat S T (n • M) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ heisO ψ S T w f = ζ • heisO ψ S T (GlobalTheory.VacUnique.finRat S T M) f := by
  intro D ψ S T ΛS ΛT hψ hS hT f hf n hn w hw
  classical
  have hinf : w.map (infPart D) = 0 := by
    have h1 := GlobalTheory.VacUnique.latO_inf S T _ _ _ hw
    funext i j
    have h2 : infPart D ((n • w) i j) = 0 := congrFun (congrFun h1 i) j
    rw [Matrix.smul_apply, map_nsmul] at h2
    have hn' : (n : D.host.F) ≠ 0 := by exact_mod_cast hn.ne'
    have h3 : (n : D.host.F) • infPart D (w i j) = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact h2
    show infPart D (w i j) = 0
    rw [← inv_smul_smul₀ hn' (infPart D (w i j)), h3, smul_zero]
  obtain ⟨M, u, hu, hM⟩ := GlobalTheory.LatVac.approx hS hT w
  have hw_eq : w = GlobalTheory.VacUnique.finRat S T M + u := by
    ext i j
    rw [← sub_eq_zero]
    apply GlobalTheory.LatVac.eq_zero_of_parts
    · have h1 : infPart D (w i j) = 0 := congrFun (congrFun hinf i) j
      have h2 : infPart D (GlobalTheory.VacUnique.finRat S T M i j) = 0 :=
        congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T M) i) j
      rw [Matrix.add_apply, RingHom.map_sub, RingHom.map_add, h1, h2, GlobalTheory.LatVac.infPart_of_mem hu, add_zero,
        sub_zero]
    · rw [Matrix.add_apply, RingHom.map_sub, RingHom.map_add, hM, sub_eq_zero]
      rfl
  have hmem : GlobalTheory.VacUnique.finRat S T (n • M) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    have e : GlobalTheory.VacUnique.finRat S T (n • M) = n • w - n • u := by
      rw [map_nsmul, hw_eq, smul_add, add_sub_cancel_right]
    rw [e]
    exact sub_mem hw (nsmul_mem hu n)
  obtain ⟨ε, hε, hεf⟩ := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).2.2 f hf u hu
  have h1 := GlobalTheory.LatVac.heisO_heisO ψ (GlobalTheory.VacUnique.finRat S T M) u f
  rw [hεf f hf, GlobalTheory.LatVac.heisO_smul] at h1
  have hinv : ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) = 1 := by
    rw [← ψ.map_add_eq_mul, neg_add_cancel, ψ.map_zero_eq_one]
  have hX : ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) =
      ψ (symplO S T (GlobalTheory.VacUnique.finRat S T M) u) := by
    rw [← ψ.map_add_eq_mul, symplOH, ← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]
  have hY : ψ (symplO S T (GlobalTheory.VacUnique.finRat S T M) u) ^ n = 1 := by
    rw [← AddChar.map_nsmul_eq_pow]
    have e : n • symplO S T (GlobalTheory.VacUnique.finRat S T M) u = symplO S T (GlobalTheory.VacUnique.finRat S T (n • M)) u := by
      change n • GlobalTheory.LatVac.symplHom S T (GlobalTheory.VacUnique.finRat S T M) u =
        GlobalTheory.LatVac.symplHom S T (GlobalTheory.VacUnique.finRat S T (n • M)) u
      rw [map_nsmul (GlobalTheory.VacUnique.finRat S T), map_nsmul (GlobalTheory.LatVac.symplHom S T), AddMonoidHom.nsmul_apply]
    rw [e]
    exact GlobalTheory.LatVac.char_sympl_eq_one hψ hS hT hmem hu
  have e1 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have e2 : (ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ n = 1 := by
    rw [hX]; exact hY
  refine ⟨M, ε * ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u), ⟨2 * n, by omega, ?_⟩, hmem, ?_⟩
  · calc (ε * ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ (2 * n)
        = (ε * ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ (2 * n) *
          (ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) * ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ n := by
          rw [e2, mul_one]
      _ = (ε ^ 2) ^ n * ((ψ (-symplOH S T (GlobalTheory.VacUnique.finRat S T M) u) *
          ψ (symplOH S T (GlobalTheory.VacUnique.finRat S T M) u)) ^ 2) ^ n := by ring
      _ = 1 := by rw [e1, hinv]; simp
  · rw [hw_eq, mul_comm, mul_smul, h1, smul_smul, hinv, one_smul]

end GlobalTheory.MultLatDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdVLeOfLoc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff Pointwise

noncomputable section

namespace GlobalTheory.StairLine

open GlobalTheory.SeeSaw (FI idV dI)

variable {D : D7}

set_option maxHeartbeats 800000 in

theorem line_mem_iff {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FI D) (q : Fin c) (hq : 2 * q.1 + 1 ≠ c)
    {x : D.host.E} (hx : x ≠ 0) (v : GlobalTheory.FinPl.Pl D) (a : AE D) :
    (fun k => a * incA D (x * d.a k q)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔
      a ∈ idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q) v := by
  classical
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσdef
  have hσ : ∀ e, σ (σ e) = e := fun e => star_star e
  have hG : Formalism.UG.cT σ B.gram = B.gram := by funext i j; exact B.herm.eq (B.frame j) (B.frame i)
  have eT : ∀ {m n p : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E) (Y : Matrix (Fin n) (Fin p) D.host.E),
      Formalism.UG.cT σ (X * Y) = Formalism.UG.cT σ Y * Formalism.UG.cT σ X := by
    intros; simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have eTT : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), Formalism.UG.cT σ (Formalism.UG.cT σ X) = X := by
    intros; ext i j; simp [Formalism.UG.cT, hσ]
  have hperp : Formalism.UG.cT σ d.a * B.gram * frameMat B A d.ι = 0 := by
    have h1 := congrArg (Formalism.UG.cT σ) d.perp
    rw [eT, eT, eTT, hG, ← Matrix.mul_assoc] at h1
    rw [h1]; ext i j; simp [Formalism.UG.cT]
  let P := Formalism.UG.cT σ d.a * B.gram
  let r : Fin B.rank → D.host.E := x⁻¹ • P q.rev
  have hrow : ∀ {n : ℕ} (N : Matrix (Fin B.rank) (Fin n) D.host.E), r ᵥ* N = x⁻¹ • (P * N) q.rev := by
    intros; funext j; simp [r, Matrix.vecMul, dotProduct, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  have hrM : ∀ y, r ⬝ᵥ (frameMat B A d.ι *ᵥ y) = 0 := by
    intro y
    rw [Matrix.dotProduct_mulVec, hrow, show P * frameMat B A d.ι = 0 from hperp,
      show ((0 : Matrix (Fin c) (Fin A.rank) D.host.E) q.rev) = 0 from rfl, smul_zero, zero_dotProduct]
  have hgram : P * d.a = antiDiagonalSignGramMatrix c ε := d.gram
  have hra : ∀ u : Fin c → D.host.E, r ⬝ᵥ (d.a *ᵥ u) = x⁻¹ * u q := by
    intro u
    rw [Matrix.dotProduct_mulVec, hrow, hgram]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, antiDiagonalSignGramMatrix]
    rw [Finset.sum_eq_single q]
    · have h1 : q.rev.1 + q.1 + 1 = c := by rw [Fin.val_rev]; omega
      have h2 : q.rev ≠ q := by intro h; rw [Fin.ext_iff, Fin.val_rev] at h; omega
      rw [if_pos h1, if_neg h2, mul_one]
    · intro p _ hp
      have : ¬ (q.rev.1 + p.1 + 1 = c) := by
        intro h; apply hp; rw [Fin.ext_iff]; rw [Fin.val_rev] at h; omega
      rw [if_neg this, mul_zero, zero_mul]
    · simp
  have hlat : ∀ y ∈ d.lat Λ 𝔟, r ⬝ᵥ y ∈ FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q := by
    rintro _ ⟨y, -, u, hu, rfl⟩
    rw [dotProduct_add, hrM, zero_add, hra]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) (hu q)
  have hcol : r ⬝ᵥ (fun k => x * d.a k q) = 1 := by
    have e : (fun k => x * d.a k q) = d.a *ᵥ Pi.single q x := by
      funext k; simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    rw [e, hra, Pi.single_eq_same, inv_mul_cancel₀ hx]
  constructor
  · intro hmem
    have hΦ : ∀ Y ∈ latV B (d.lat Λ 𝔟) (· = v), ∑ k, incA D (r k) * Y k ∈
        idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟 q) v := by
      intro Y hY
      induction hY using AddSubgroup.closure_induction with
      | mem Y hY =>
        obtain ⟨α, h1, h2, b, hb, y, hy, rfl⟩ := hY
        rw [Set.mem_singleton_iff] at hb
        subst hb
        refine AddSubgroup.subset_closure ⟨α, h1, h2, _, hlat y hy, ?_⟩
        simp only [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul, ← TensorProduct.tmul_sum, dotProduct]
      | zero => simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]; exact zero_mem _
      | add Y Z _ _ hY hZ =>
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; exact add_mem hY hZ
      | neg Y _ hY =>
        simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]; exact neg_mem hY
    have h := hΦ _ hmem
    have e : ∑ k, incA D (r k) * (a * incA D (x * d.a k q)) = a := by
      calc _ = a * incA D (r ⬝ᵥ (fun k => x * d.a k q)) := by
            simp only [dotProduct, map_sum, map_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
        _ = a := by rw [hcol, map_one, mul_one]
    rwa [e] at h
  · intro ha
    induction ha using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, h1, h2, b, hb, rfl⟩ := hz
      obtain ⟨b', hb', rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hb
      refine AddSubgroup.subset_closure ⟨α, h1, h2, 1, rfl, d.a *ᵥ Pi.single q b', ?_, ?_⟩
      · refine ⟨0, Λ.zero_mem, Pi.single q b', fun p => ?_, by simp⟩
        by_cases hp : p = q
        · subst hp; simpa using hb'
        · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
      · funext k
        have e1 : x * d.a k q * (x⁻¹ * b') = 1 * (d.a *ᵥ Pi.single q b') k := by
          simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
            if_true]
          field_simp
        rw [mul_comm (pairA D.host.F 0 α ⊗ₜ[D.host.F] (x⁻¹ * b')), GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, e1]
    | zero =>
      have e0 : (fun k => (0 : AE D) * incA D (x * d.a k q)) = 0 := by funext k; exact zero_mul _
      rw [e0]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : (fun k => (y + z) * incA D (x * d.a k q)) =
          (fun k => y * incA D (x * d.a k q)) + fun k => z * incA D (x * d.a k q) := by
        funext k; simp [add_mul]
      rw [this]; exact add_mem hy hz
    | neg y _ hy =>
      have : (fun k => -y * incA D (x * d.a k q)) = -fun k => y * incA D (x * d.a k q) := by
        funext k; simp [neg_mul]
      rw [this]; exact neg_mem hy

theorem idV_le_of_loc {𝔞 𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D}
    (h : ∀ z ∈ 𝔞, ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap D.host.F D.host.E t * z ∈ 𝔟) : idV 𝔞 v ≤ idV 𝔟 v := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, h1, h2, a, ha, rfl⟩
  obtain ⟨t, ht, htb⟩ := h a ha
  obtain ⟨g1, g2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht h1 h2
  exact AddSubgroup.subset_closure ⟨_, g1, g2, _, htb, GlobalTheory.IdVGen.tmul_eq ht α a⟩

theorem exists_modul {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∉ P.S0) :
    ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ algebraMap D.host.F D.host.E t ∈
      (((P.modul sc * P.modulBar sc : Ideal (𝓞 D.host.E))) : FI D) := by
  classical
  have hu : ∀ u ∈ P.S0, ∃ t : 𝓞 D.host.F, t ∈ u.asIdeal ∧ t ∉ v.asIdeal := by
    intro u hu
    by_contra hcon
    push_neg at hcon
    have e : u = v := IsDedekindDomain.HeightOneSpectrum.ext
      (u.isMaximal.eq_of_le v.isPrime.ne_top hcon)
    exact hv (e ▸ hu)
  choose! tu htu htv using hu
  let t : 𝓞 D.host.F := ∏ u ∈ P.S0, tu u ^ P.depth sc u
  have htv' : t ∉ v.asIdeal := by
    intro hmem
    obtain ⟨u, hu, hmem'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hmem
    exact htv u hu (v.isPrime.mem_of_pow_mem _ hmem')
  have hmod : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
    simp only [t, map_prod, map_pow, Places.modul]
    refine Ideal.prod_mem_prod fun u hu => Ideal.pow_mem_pow ?_ _
    have e := P.under_w hu
    have : tu u ∈ ((P.w u).under (𝓞 D.host.F)).asIdeal := by rw [e]; exact htu u hu
    exact this
  have hfix : D.host.conj • algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t := by
    apply Subtype.ext
    exact (D.host.conjE_mem_hostF_iff _).1 (t : D.host.F).2
  have hbar : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modulBar sc := by
    rw [← hfix]
    exact Ideal.smul_mem_pointwise_smul _ _ _ hmod
  refine ⟨t * t, v.isPrime.mul_notMem htv' htv', ?_⟩
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mul_mem_mul hmod hbar, ?_⟩
  rw [← map_mul]
  rfl

end GlobalTheory.StairLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmThetaLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaLiftSmoothAut

theorem isAutFunSm_thetaLift {D : D7} (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ)
    {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT om)
    {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ S T Φ) {ν : Measure (GA D T)} {𝓕 : Set (GA D T)}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ T) 𝓕 ν) {φ : GA D T → ℂ}
    (hφ : IsAutFunSm θ T φ) (hc : IsCuspFun T φ) :
    IsAutFunSm θ S fun h => ∫ g in 𝓕, thetaKO om h g Φ * φ g ∂ν := by
  have hκ := (GlobalTheory.Mem.Lift.isKerSys_thKer hθ hω.std (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont).swap
  exact (hκ.lift hP hθ ⟨hν, h𝓕⟩ ⟨hφ, hc⟩ ⟨Φ, hΦ⟩).2

end GlobalTheory.ThetaLiftSmoothAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LargeScaleSizesImplyGapConditionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.largeScaleSizes_imply_gapConditions : SizeGap := by
  first | exact @GlobalTheory.SepRows.sizeGap_of_sizes | exact GlobalTheory.SepRows.sizeGap_of_sizes | (intros; apply GlobalTheory.SepRows.sizeGap_of_sizes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarIdentityOffFixedPlaceBaseLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftScalarIdentity_offFixedPlace_baseLevel : GlobalTheory.Hk3.HoweUnram → GlobalTheory.LowRow.ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ), A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.ConjScalar.ConjScalarAt R.toRealDat → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i))) i) → R.toRealDat.LUnif → ((R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso) → (R.toCx3 F).GalD F.cr false := by
  first | exact @GlobalTheory.ConjScalarOff.galD_base | exact GlobalTheory.ConjScalarOff.galD_base | (intros; apply GlobalTheory.ConjScalarOff.galD_base <;> assumption)
end

