import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0914
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0002
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0040
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0006
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0013
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0329
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0042
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLinearForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Development.AutomorphicArithmetic.ResidueCharacters.Bundle0007
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0545

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherLastStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bound_tieChi_of_prints : Hypotheses₂ → ∃ CT : ℕ, ∀ (D : D7) (nch : NChoice D), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → (PairedCharacterCondition.tieChi (D := D) ∧ (∃ Q : PairedCharacterCondition.Pend (D), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) ∧ GlobalTheory.Pass.TieInePoly (D) ∧ GlobalTheory.TypeLeaf.SerLoc (D)) → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) (8 * (CT : ℝ)) CT := by
  first | exact @_root_.GlobalTheory.NormFromFacts.main_alt_alt | exact _root_.GlobalTheory.NormFromFacts.main_alt_alt | (intros; apply _root_.GlobalTheory.NormFromFacts.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerLast
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.RecPinsTie
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S), ∀ r : _root_.GlobalTheory.Mem.R3.RecursiveInput y, (∀ hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y), _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt Rc.T.n.gal.lp x.R.θ x.Y.PY (x.R.MY 0) (fun b => levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun b => Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun _ => x.R.e0) x.Y.eFT → _root_.Formalism.IndefR.IndefiniteRealisationCompatible hp (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r)) ∧ (Formalism.IndefR.RecTie.PartsRec x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.PY x.Y.PW x.Y.eFT r.E r.labPi r.piOf x.Y.Ish.prt x.Y.IL.prtW → (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r).PartsRow) ∧ PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG := by
  intro D L hT Gi Gl K Yd cX ex x Rc S y r
  refine ⟨fun hp h => ⟨?_, ?_⟩, fun h => ?_, ?_⟩
  · exact x.Y.stdPsi
  · exact h
  · exact h
  · exact x.pins.keep.psi
end GlobalTheory.Mem.R3.RecPinsTie
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpLemmaAOfAdmissible
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Classical
variable {D : D7}
theorem jumpLemma_a_of_admissible_alt_alt {L : SizeData₂ D} (hP : AdmPar L) (hG2 : _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D) (hCr : CrysIffWD D.nd D.naut)
    (hG2g : _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D) (hDi : AdmDict D) (hRd : AdmRead D) : ConclusionJa D := by
  obtain ⟨ep, hdict⟩ := hDi
  refine ⟨ep, ?_⟩
  intro i r hr w hw C τ
  obtain ⟨hInd, ⟨g, hg⟩, hread⟩ := hRd i r hr w hw C τ
  obtain ⟨ρ, hρ⟩ := exists_placeOf (D := D) g
  have hRA : ReadAt D i (gEmb C τ) g ρ := ⟨hg, hρ⟩
  obtain ⟨sg, cτ, hsU, hsD, hJ0, hchi⟩ := hdict i (gEmb C τ) g ρ hRA
  obtain ⟨hχdR, hχJ⟩ := hchi w hInd
  rw [Multiset.map_eq_singleton] at hχJ
  obtain ⟨c, hc, hcq⟩ := hχJ
  have hjr := D.nd.j_range i
  have hF := jFacts_of hP (D.nd.j i) hjr.1 hjr.2 ρ
  set up := decide (TypeU D ep g) with hup
  have hsU' : up = true → sg = 1 := fun h => hsU (by simpa [hup] using h)
  have hsD' : up = false → sg = -1 := fun h => hsD (by simpa [hup] using h)
  have hx : ∀ x, D.naut.IsdRW i (rQ D i r x) w ∧
      D.naut.jumpsW i (rQ D i r x) (gEmb C τ) = D.naut.locAutHodgeTateWeightsLevelZero i (gEmb C τ) := by
    intro x
    by_cases hl : D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1
    · have h := _root_.UpperTheory.GalS.g2g' hG2g i r hr hl w hw x
      exact ⟨h.1, h.2 _ hInd⟩
    · push Not at hl
      have h := _root_.UpperTheory.GalS.g2a' (hG2 i r hr) w hw hl.1 hl.2 x
      have hcont := SumRepresentations.contQ_of_continuous D.nd D.naut i (r x) (hr x).1
      exact ⟨((hCr i _ _ w hw hcont).1 h.1).1, h.2 _ hInd⟩
  have hkey : ∀ a : ℤ, (((D.naut.locAutHodgeTateWeightsLevelZero i (gEmb C τ)).count (a + c) : ℕ) : ℤ) =
      if (a : ℚ) ∈ JJ D up (D.nd.j i) ρ then 1 else 0 :=
    count_key hF _ sg cτ c up hsU' hsD' hJ0 hcq
  have hTw : ∀ x (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a =
      if (a : ℚ) ∈ JJ D up (D.nd.j i) ρ then 1 else 0 := by
    intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    rw [(h1 a).1, (hx x).2, hkey]
  have hDu : ∀ x (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a =
      if (a : ℚ) ∈ dualS (JJ D up (D.nd.j i) ρ) then 1 else 0 := by
    intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    rw [(h1 a).2, (hx x).2, dualS_int, ← hkey]
    congr 3; ring
  refine ⟨g, ρ, hRA, ?_, ?_⟩
  · intro x a
    obtain ⟨h1, h2, h3⟩ := hread x (hx x).1 hχdR c hc
    refine ⟨?_, hTw x a, ?_, hDu x a⟩
    · rw [h2 _ (Or.inl rfl) a, hTw x a]; exact ite_ne_zero_iff' _
    · rw [h2 _ (Or.inr rfl) a, hDu x a]; exact ite_ne_zero_iff' _
  · intro ρπ π hπ hdec a
    obtain ⟨h1, h2, h3⟩ := hread π (hx π).1 hχdR c hc
    have hW : ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a =
        if (a : ℚ) ∈ JW D up (D.nd.j i) ρ then 1 else 0 := by
      intro a
      rw [(h3 ρπ hπ hdec a).1, hTw π a]
      by_cases hb : (a : ℚ) ∈ blockJ D
      · have hb' := (block_mem_iff (D := D) a).1 hb
        rw [if_pos (block_sub_JJ up _ ρ _ hb), if_pos hb', if_neg (block_not_mem_JW hF up _ hb)]
        simp
      · have hb' : ¬ (0 ≤ a ∧ a < (D.R.t : ℤ)) := fun h => hb ((block_mem_iff a).2 h)
        rw [if_neg hb', sub_zero]
        simp only [JJ_iff_JW hF up _ hb]
    have hT : ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a =
        if (a : ℚ) ∈ dualS (JW D up (D.nd.j i) ρ) then 1 else 0 := by
      intro a
      rw [(h3 ρπ hπ hdec a).2.1, hW, dualS_int]
    refine ⟨?_, hW a, ?_, hT a⟩
    · rw [(h3 ρπ hπ hdec a).2.2.1, hW a]; exact ite_ne_zero_iff' _
    · rw [(h3 ρπ hπ hdec a).2.2.2, hT a]; exact ite_ne_zero_iff' _
end GlobalTheory.JumpSets
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeFamilyAdoptionFirstStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_family_adoption_first_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q), NChTie D ex.nch → ∃ (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → (B.Q.Sx.A j).IsKsForm) ∧ (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) ∧ (∀ w j (a : B.Q.Sx.Ks) (m : D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (ex.nch.embW w (algebraMap B.Q.Sx.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m : FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) = (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] ((show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK B.Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) • m)) ∧ (∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → LinearIndependent (FractionRing (ex.nch.Oe w)) (fun a => eM w j ((Y.MjH j).b a))) := by
  first | exact @_root_.GlobalTheory.Adopt.lattice_family_adoption_first_alt | exact _root_.GlobalTheory.Adopt.lattice_family_adoption_first_alt | (intros; apply _root_.GlobalTheory.Adopt.lattice_family_adoption_first_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeFamilyAdoptionSecondAlt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_family_adoption_second_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), NChTie D ex.nch → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → NForms.IsLatIn (Submodule.span (ex.nch.Oe w) (eM w j '' ((Y.MjH j).L : Set (Y.MjH j).V))) ((((NForms.V0 D (ex.nch.twI w) j (ex.nch.sd w)).restrictScalars (D.ntw.O (ex.nch.twI w))).baseChange (FractionRing (ex.nch.Oe w))).restrictScalars (ex.nch.Oe w)) := by
  first | exact @_root_.GlobalTheory.Adopt.lattice_family_adoption_second_alt | exact _root_.GlobalTheory.Adopt.lattice_family_adoption_second_alt | (intros; apply _root_.GlobalTheory.Adopt.lattice_family_adoption_second_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LitCharCrys
section
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.Lit.heckeLAdicCharacterCrystalline_of_deRham (h1 : GlobalTheory.Published.HeckeLAdicCharacterDeRham) (h2 : GlobalTheory.Published.DeRhamPotSemistable)
    (h3 : GlobalTheory.Published.AlgebraicCharacterWD) (h4 : _root_.UpperTheory.Zero.LLC.RecTExists) : GlobalTheory.Published.HeckeLAdicCharacterCrystalline :=
  _root_.GlobalTheory.Published.CharCrysModel.of_hypotheses_m_alt h1 h2 h3 h4
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainOfAlt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.FormAllLevels
theorem main_of_alt (pet : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), GlobalTheory.CoefDuty.IsInvForm a β → ∃ B, GlobalTheory.CoefDuty.IsPetersson a B ∧ ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (T : Finset (GAf L n)), GlobalTheory.CoefDuty.IsBounded J → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → GlobalTheory.CoefDuty.IsClassReps J T → ∃ c : ℝ, 0 < c ∧ ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ f' ∈ NG.TypeSp a.ρ J χ, GlobalTheory.CoefDuty.classSum a β J T f f' = (c : ℂ) * B f f') (cls : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp), GlobalTheory.NJoin.Agree X P.M P.rep → ∀ i, ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) (T : Finset (GAf D.host.E D.R.nV)) (β : (P.M.loc i).wt.W →ₗ⋆[ℂ] (P.M.loc i).wt.W →ₗ[ℂ] ℂ) (c : ℝ), GlobalTheory.CoefDuty.IsInvForm (P.M.loc i).wt β ∧ GlobalTheory.CoefDuty.IsBounded J ∧ (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧ GlobalTheory.CoefDuty.IsClassReps J T ∧ 0 < c ∧ (∀ x, (P.M.loc i).real x ∈ NG.TypeSp (P.M.loc i).wt.ρ J χ) ∧ ∀ x y, inner ℂ x y = (c : ℂ) * GlobalTheory.CoefDuty.classSum (P.M.loc i).wt β J T ((P.M.loc i).real x) ((P.M.loc i).real y)) : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ i, MtForm D P.M i := by
  intro hL D P X hA i
  obtain ⟨J, χ, T, β, c, hβ, hJb, hJo, hT, hc, hmem, hin⟩ := cls hL D P X hA i
  obtain ⟨B, hB, hcs⟩ := pet D.host.E D.R.nV (P.M.loc i).wt β hβ
  obtain ⟨c', hc', hcs'⟩ := hcs J χ T hJb hJo hT
  have hpos : (0 : ℝ) < c * c' := mul_pos hc hc'
  refine ⟨((c * c' : ℝ) : ℂ) • B, ?_, ?_⟩
  · intro f hf f' hf'
    obtain ⟨h1, h2, h3⟩ := hB f hf f' hf'
    refine ⟨?_, ?_, ?_⟩
    · simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
      rw [h1]
    · intro hne
      simp only [LinearMap.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
      exact mul_pos hpos (h2 hne)
    · intro h
      simp only [LinearMap.smul_apply, h3 h]
  · intro x y
    rw [hin x y, hcs' _ (hmem x) _ (hmem y)]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ i, MtForm D P.M i :=
  _root_.GlobalTheory.FormAllLevels.main_of_alt GlobalTheory.T.exists_pos_classSum_eq_mul_invariantForm _root_.GlobalTheory.T.invariant_form_bounded_congruence_alt
end GlobalTheory.FormAllLevels
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemOmIOfTheta
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.ThetaTri in
theorem mem_omI_of_theta_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), (∀ v, Formalism.IndefR.Datum.IsThetaFunO X.R.ψ (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) (φ v)) → φ ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ := by
  intro _ hP hL D P X A i j hj Y hc hμ φ hφ
  have hm := X.given.core.models
  have hθ : IsInfFam X.R.θ := hm.inf
  have hω := X.given.core.thP.ωP j (X.tupT (D.nd.mu i))
  have hp : (Vc D j).IsPosDef := hm.vpos j
  have hpd : ∀ τ, (gramAt D (Vc D j) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((j : ℕ) + 1)) τ
  have hHV := (hm.νV j (X.tupT (D.nd.mu i))).1.1
  have hfdV := (hm.νV j (X.tupT (D.nd.mu i))).2
  have hHW : (X.R.νW j).IsHaarMeasure := (hm.νW j).1.1
  have hfdW : IsFundamentalDomain (GQ (Wc D j)) (X.R.fdW j) (X.R.νW j) := (hm.νW j).2
  intro p
  have hφ' : ∀ v, IsThetaFunO X.R.ψ (Vc D j) (Wc D j) (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ v) :=
    fun v => hω.om_pres _ _ (hφ v)
  refine ⟨hφ', fun F g => ?_, fun F y => ?_⟩
  · obtain ⟨hc1, hc2⟩ := _root_.GlobalTheory.T.form_to_vector_map_continuous_invariant hL D P X A i j hj hμ F
    exact GlobalTheory.DefiniteQuotient.integrableOn_theta D X.R.ψ hω.std (Vc D j) (Wc D j) _ _ _ hω hpd _
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ) hφ' _ hc1 hc2 _ _ hHV hfdV g
  · obtain ⟨hc1, hc2⟩ := _root_.GlobalTheory.T.form_to_vector_map_continuous_invariant hL D P X A i j hj hμ F
    have hmap := (Classical.choose_spec (Classical.choose_spec hc)).2.2.1
    have hey : _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A) ∈ Formalism.IndefR.principalLevelFrame.Minf X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) := by
      rw [← hmap]; exact ⟨y, y.2, rfl⟩
    have hyv : _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y = _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A) (fun τ => ((Classical.epsilon fun u : ↥(lowT (X.R.MW j (sg0 D X.A)) τ) =>
        ‖((u : (X.R.MW j (sg0 D X.A)).sm τ) : (X.R.MW j (sg0 D X.A)).H τ)‖ = 1 : ↥(lowT (X.R.MW j (sg0 D X.A)) τ)) :
          (X.R.MW j (sg0 D X.A)).sm τ)) := by
      simp [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap, kUnit, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod]
    obtain ⟨haut, hcu⟩ := GlobalTheory.T.multiplicitySpaceAllLevels_values_smooth_cuspidal X.R.θ (X.PW j) (X.R.MW j (sg0 D X.A)) _ hey
      (fun τ => ((Classical.epsilon fun u : ↥(lowT (X.R.MW j (sg0 D X.A)) τ) =>
        ‖((u : (X.R.MW j (sg0 D X.A)).sm τ) : (X.R.MW j (sg0 D X.A)).H τ)‖ = 1 : ↥(lowT (X.R.MW j (sg0 D X.A)) τ)) :
          (X.R.MW j (sg0 D X.A)).sm τ))
    rw [← hyv] at haut hcu
    have hR := (GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ haut hcu).conj
    have hgr := GlobalTheory.T.moderateGrowth_definiteThetaIntegral_vectorForm X.R.ψ (Vc D j) (Wc D j) _ _ _ hω hpd _ _ hHV hfdV _
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ) hφ' _ hc1 hc2
    have hct := GlobalTheory.T.continuous_definiteThetaIntegral_vectorForm X.R.ψ (Vc D j) (Wc D j) _ _ _ hω hpd _ _ hHV hfdV _
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ) hφ' _ hc1 hc2
    have hinv : ∀ γ ∈ GQ (Wc D j), ∀ g, (∫ h in X.R.fdV j (X.tupT (D.nd.mu i)),
        thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h (γ * g)
          (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h)) ∂(X.R.νV j (X.tupT (D.nd.mu i)))) =
        ∫ h in X.R.fdV j (X.tupT (D.nd.mu i)), thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h g
          (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) p φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h)) ∂(X.R.νV j (X.tupT (D.nd.mu i))) := by
      intro γ hγ g
      congr 1
      funext h
      have e : ((h, γ * g) : GA D (Vc D j) × GA D (Wc D j)) = (1, γ) * (h, g) := by simp
      unfold thetaKO
      rw [e, map_mul]
      exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ (hφ' _))
    have := hR.integrableOn_modGrowth_mul hHW hfdW hgr hinv hct.aestronglyMeasurable
    convert this using 1
    funext g
    simp only [Pi.mul_apply, thIn]
    rw [mul_comm]
    rfl
end GlobalTheory.ThetaTri
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MjReadRealizationEqual
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.Reads
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
set_option maxHeartbeats 2000000 in
theorem mjRead_of_indefinite_down_join (x : TwIn ex) {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) :
    Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((indefiniteDownJoin (realisationOfInput y))) := by
  intro i v
  have h1 := x.Y.mjRead i (x.Z.jW i v)
  have h2 := x.Z.jW_read i v
  have h3 : x.Y.mj.eW i (x.Z.jW i v) ∈ LinearMap.range (x.Y.mj.eW i) := ⟨_, rfl⟩
  rw [x.Y.mj.eW_range i] at h3
  have h4 := h3.2
  have h5 : Mult.postOn _ (x.R.toRealDat.eWf i (sg0 D x.A3.A)) ((x.R.HW i (sg0 D x.A3.A)).e (x.Y.mj.eW i (x.Z.jW i v))) =
      (x.R.HW i (sg0 D x.A3.A)).e (x.Y.mj.eW i (x.Z.jW i v)) := sub_eq_zero.1 h4
  refine h1.trans (congrArg _ ?_)
  rw [← h5, h2]
  rfl
set_option maxHeartbeats 4000000 in
theorem mt_mj_read_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S), Holds x.R x.F → Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie) ∧ Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((indefiniteDownJoin (realisationOfInput y))) := by
  intro D L hT Gi Gl K Yd cX ex x Rc S y _
  exact ⟨liftGroupForms_eq_extended_rationalForms_companion x, _root_.GlobalTheory.Mem.R3.Reads.mjRead_of_indefinite_down_join x y⟩
end GlobalTheory.Mem.R3.Reads
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowOn
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
def RowOnAlt (Q : D7 → ℕ → Prop) (A B : ℝ) : Prop := ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ →
      RowOnAt (Fm.L x i) X.ρ (Q (Fm.D x i)) A B
def SecondBoundCondition (A B : ℝ) : Prop := _root_.UpperTheory.N.RowOnAlt (fun _ l => l = 2) A B
def ThirdBoundCondition (A B : ℝ) : Prop := _root_.UpperTheory.N.RowOnAlt (fun D l => l = 3 ∧ l ∉ D.host.small) A B
end UpperTheory.N
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OffBad
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SummandEig
theorem offBad_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), Formalism.L2.NG.OverPl Pp v → v ∉ Formalism.L2.badPl D i := _root_.GlobalTheory.T.place_below_good_not_mem_badPl
theorem main_alt_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (Q : D.naut.AV i), ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro hAF hL D P X hAg h41 h7 hTie i hμ j hj Q Pp hG hS d hd
  obtain ⟨s, α, hov, hα, hR1, hR2⟩ := frameReps D (Formalism.IndefR.Links.Vc D j) D.R.nV hAg.hF (hAg.PV j) (hAg.stdV j) Pp hS d hd
  obtain ⟨c, hc1⟩ := irrScalar D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s α hα _ _ _ hR1 hR2
  have hc := isoScalar D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s.v _ _ _ c hc1
  have hsB : s.v ∉ Formalism.L2.badPl D i := _root_.GlobalTheory.SummandEig.offBad_alt hL D P X i hμ Pp hG s.v hov
  refine ⟨c, fun f' hf' g => ?_⟩
  have hFI : (P.M.loc i).real (hj ▸ f') ∈ Formalism.L2.NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have h := hf'
    rw [P.H.av.typeV i Q] at h
    exact h
  have hFT : (P.M.loc i).real (hj ▸ f') ∈ Formalism.L2.NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]
    exact ⟨_, rfl⟩
  have hfix : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      Formalism.L2.NG.rt D.host.E D.R.nV κ ((P.M.loc i).real (hj ▸ f')) = (P.M.loc i).real (hj ▸ f') := by
    intro κ hκ ht
    have ht' : TrivOutside (Formalism.L2.badPl D i)ᶜ κ := fun v hv => ht v fun h => hv (by
      rw [Set.mem_singleton_iff.1 h]
      exact hsB)
    obtain ⟨h1, h2⟩ := P.H.hecke.J_hyp i κ ht'
    have hJ : κ ∈ (P.M.loc i).J := h1.2 hκ
    have e := hFT.2 ⟨κ, hJ⟩
    rw [h2 hJ] at e
    simpa using e
  have hkey := cast_sum P.M (D.nd.mu i) hj _ _ (by omega) (by omega) f' _ _ c (hc _ hFI hfix)
  have hreal : ∀ w, hAg.eW (D.nd.mu i) hμ j (X.fn hμ j f' ((hAg.PV j).ψ w)) =
      (P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f' (hAg.a j * w) := by
    intro w
    rw [hAg.real (D.nd.mu i) hμ j f' (hAg.a j * w), inv_mul_cancel_left]
  have hfin : ∀ w, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' ((hAg.PV j).ψ w * γ) =
      c • X.fn hμ j f' ((hAg.PV j).ψ w) := by
    intro w
    apply (hAg.eW (D.nd.mu i) hμ j).injective
    rw [map_sum, map_smul, hreal]
    have e1 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, hAg.eW (D.nd.mu i) hμ j (X.fn hμ j f' ((hAg.PV j).ψ w * γ)) =
        Formalism.L2.NG.rt D.host.E D.R.nV (Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ)
          ((P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f') (hAg.a j * w) := by
      intro γ hγ
      have e2 : (hAg.PV j).ψ w * γ = (hAg.PV j).ψ (w * Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ) := by
        rw [map_mul, Formalism.IndefR.principalLevelFrame.pre_spec (hAg.PV j) (rep_mem _ Pp d hγ)]
      rw [e2, hreal]
      show _ = (P.M (D.nd.mu i) (j.1 + 1) (by omega) (by omega)).real f' (hAg.a j * w * Formalism.IndefR.principalLevelFrame.pre (hAg.PV j) γ)
      rw [mul_assoc]
    rw [Finset.sum_congr rfl e1, ← Finset.sum_apply, hkey]
    rfl
  obtain ⟨a₀, ha₀, k, hk, rfl⟩ := (GlobalTheory.T.adelicUnitary_real_mul_finite_decomposition D (Formalism.IndefR.Links.Vc D j)).1 g
  obtain ⟨w, rfl⟩ := (hAg.PV j).onto k hk
  obtain ⟨y, hy, -⟩ := X.existsUnique_vec hμ j f'
  have hw := hfin w
  rw [← hy] at hw ⊢
  have e1 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
      X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w * γ) =
        (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := fun γ hγ =>
    (congrArg (X.R.extV j (X.tupT (D.nd.mu i)) y) (mul_assoc _ _ _)).trans
      (extV_inf X j _ y ha₀ (mul_mem ((hAg.PV j).into w) (rep_mem _ Pp d hγ)))
  calc ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w * γ)
      = ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
          (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := Finset.sum_congr rfl e1
    _ = (X.R.cV j).ρ a₀⁻¹ (∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d,
          X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w * γ)) := (map_sum _ _ _).symm
    _ = (X.R.cV j).ρ a₀⁻¹ (c • X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w)) := congrArg _ hw
    _ = c • (X.R.cV j).ρ a₀⁻¹ (X.R.extV j (X.tupT (D.nd.mu i)) y ((hAg.PV j).ψ w)) := map_smul _ _ _
    _ = c • X.R.extV j (X.tupT (D.nd.mu i)) y (a₀ * (hAg.PV j).ψ w) :=
      congrArg _ (extV_inf X j _ y ha₀ ((hAg.PV j).into w)).symm
end GlobalTheory.SummandEig
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvZrOfInputsRowsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedMultiplicity_of_inputs : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → _root_.GlobalTheory.NRows.PointConditions' D → SumRepresentations.ReducedMultiplicityStatement D := by
  first | exact @_root_.GlobalTheory.PtSt.reducedMultiplicity_of_rows' | exact _root_.GlobalTheory.PtSt.reducedMultiplicity_of_rows' | (intros; apply _root_.GlobalTheory.PtSt.reducedMultiplicity_of_rows' <;> assumption)
end
end

