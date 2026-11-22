import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0906
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittBasisCompactStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExcSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2092
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddLeLminorSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2102
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitOfUnramifiedPrime

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitary
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameAut

theorem exists_locComp_hasSatGL_heckeVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ φ ∈ π, φ ≠ 0 →
    (∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w n → RU E n x φ = φ) →
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ S ∧
      ∀ k ≤ n, GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n w).subtype) ((GlobalTheory.LFun.KGL w n).comap ((cLoc w).comp (locU n w).subtype))
        (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E w) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k)) ((cLoc w).comp (locU n w).subtype x)) φ =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n S k • φ := by
  intro E _ _ _ n π hπ w hw φ hφ h0 hfix
  obtain ⟨σ, -, hloc, hiff⟩ := GlobalTheory.DefU.exists_locComp_split E n ⟨π, hπ⟩ w hw
  obtain ⟨S, hS⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred (hiff.1 ⟨φ, hφ, h0, hfix⟩)
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hp : Function.Surjective ((cLoc w).comp (locU n w).subtype) := fun g =>
    ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩
  refine ⟨σ, S, hloc, hS, fun k hk => ?_⟩
  rw [GlobalTheory.SphPar.divInd_dualLab_splitLab E w n k hϖ]
  exact GlobalTheory.SplitTransfer.heckeVec_eq_of_isCompAlong hπ w (Formalism.UG.Final.GLintComm E w n) _ hp σ.ρ hloc
    (GlobalTheory.LFun.Tj_mem_hecke hϖ k) (fun v hv hv0 => (hS.2 v hv hv0).2.2.2 ϖ hϖ k hk) hφ fun x hx => hfix x x.2 hx

end GlobalTheory.FrameAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchANe
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.SWLit

namespace GlobalTheory.SiegelCoefTheta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n m : ℕ} {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]

def antiPt (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ) (x : κ → AF F) :
    Matrix (Fin m) (Fin (n + n)) (AE F E) :=
  co.e.symm (x, 0)

def coefChar (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ) (ψ : AddChar (AF F) ℂ)
    (x : κ → AF F) (b : UA σ J₂) : ℂ :=
  ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂) (antiPt co x * (mat b)ᵀ) (antiPt co x))

variable (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ)

variable {co}

end GlobalTheory.SiegelCoefTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedLinearBarDualStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_linear_bar_dual : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    ∃ t : E →ₐ[F] Fv F v, ∃ (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ))
      (ν₀ : (Fv F v)ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧
      Set.BijOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), φ ∈ G.M'.SoLoc B.ψ t ↔
        ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι φ Y = 0) ∧
      (∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ)) ∧
      ∀ h₀ : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∃ c : ℂ, c ≠ 0 ∧
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = c • fun Y => ι φ (Y * h₀.1) := by
  first | exact @GlobalTheory.WeilTransfer.transfer | exact GlobalTheory.WeilTransfer.transfer | (intros; apply GlobalTheory.WeilTransfer.transfer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOfNumericsModel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Asm

open Formalism.L2.Indef Formalism.L2.Indef.Tree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jexpU_le_jrec7 (hcut : Formalism.CohomologicalDescent.E.ExCut) {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G]
    [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K))
    {ι : Type} [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι) (hN : NumOk P W)
    (hoff : ¬ W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → LIncl B ℓ Z w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w)))
    (hin : W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∃ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam),
      Covers B ℓ Z w X ∧ ∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) :
    B.JexpU ℓ Z w ≤ (W.Jrec7 P (Formalism.EigenvalueLevelCeiling.plc w) : ℚ) := by
  have hp := Formalism.EigenvalueLevelCeiling.plc_prime w
  have hrec := GlobalTheory.exponent_of_record_vs_formulas hcut P hN.1 hN.2.1 ι W hN.2.2.1 _ hp
  by_cases hR : W.WRange P (Formalism.EigenvalueLevelCeiling.plc w)
  · obtain ⟨fr, cj, I, X, hc, hX⟩ := hin hR
    have h1 := GlobalTheory.T.primePowerLatticeInclusion_of_localModels K G Pl0 B ℓ Z w ι P W hN hp hR fr cj I X hc hX
    have h2 := (GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion K G Pl0 B ℓ Z w _ h1).2
    rw [hrec.2 hR] at h2
    exact h2
  · have h2 := (GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion K G Pl0 B ℓ Z w _ (hoff hR)).2
    exact h2.trans (by exact_mod_cast hrec.1 hR)

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem splitPartNumbers_exponent_eq_liftExponent (C CH : ℝ) (t : p.P.T) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m) :
    ((R2 p).num (F2 p) C CH).J0 t w j = (((blk p j t).JexpU (lvlL p) (subZ p j t) w : ℚ) : ℝ) := rfl

open Classical in

theorem hasExpBound_at (hcut : Formalism.CohomologicalDescent.E.ExCut) {c : OnConst} (O : Obj p c)
    (hm : O.m = (D.R.m : ℝ)) (hx : O.x = L.sc.x) (heps : O.eps = L.sc.eps) (hT2 : O.T2 = D.host.T2.card)
    (Pj : Fin D.R.m → Par) (Wj : Fin D.R.m → Wts D.what₂.Tau) (hD : ∀ j, Dict L j (Pj j) (Wj j))
    (hN : ∀ j, NumOk (Pj j) (Wj j))
    (hS : ∀ j t w, LIncl (blk p j t) (lvlL p) (subZ p j t) w ((Wj j).JA (Pj j) (Formalism.EigenvalueLevelCeiling.plc w)))
    (hM : ∀ j, ∀ w ∈ p.R.twPl, (Wj j).WRange (Pj j) (Formalism.EigenvalueLevelCeiling.plc w) → ModelAt p j (Pj j) (Wj j) w) (C CH : ℝ) :
    HasExpBound ((R2 p).num (F2 p) C CH) O := by
  refine ⟨fun w _ j => ?_, fun j l => ((Wj j).Jrec7 (Pj j) l : ℝ), fun j => ⟨fun l => Nat.cast_nonneg _, fun Q hQ => ?_⟩,
    fun w hw j => ?_⟩
  · have h := (GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion _ _ _ _ _ _ w _ (hS j ((S2 p).μ w) w)).1
    rw [splitPartNumbers_exponent_eq_liftExponent]
    exact_mod_cast h
  · obtain ⟨hHyp, hLarge, hOk, X', A, hRows, hBig⟩ := hN j
    have hcard : Fintype.card D.what₂.Tau = (Pj j).f := by rw [← Nat.card_eq_fintype_card]; exact (hD j).card
    have h := UpperTheory.ExcSet.sum_exponent_log_le hcut D (Pj j) X' A hHyp hLarge hRows hBig D.what₂.Tau (Wj j) hOk hcard (hD j).f
      (hD j).special O.T2
      (by rw [hT2]; exact (hD j).thick) Q hQ
    have hxe : O.xe = (Pj j).L := by rw [(hD j).log]; show O.x ^ O.eps = _; rw [hx, heps]
    have hb : O.b = (Pj j).b := by rw [(hD j).b]; show Real.exp O.xe = _; rw [hxe, (hD j).log]; rfl
    have hm' : O.m = ((Pj j).m : ℝ) := by rw [hm, (hD j).m]
    show _ ≤ 30 * (O.T2 : ℝ) * O.m * O.b * O.xe ^ 2 + 2 * O.m * O.b
    rw [hxe, hb, hm']
    exact h
  · have hle := jexpU_le_jrec7 hcut (blk p j (p.R.mu w)) (lvlL p) (subZ p j (p.R.mu w)) w (Pj j) (Wj j) (hN j)
      (fun _ => hS j _ w) (fun hR => hM j w hw hR)
    show (((blk p j (p.R.mu w)).JexpU (lvlL p) (subZ p j (p.R.mu w)) w : ℚ) : ℝ) ≤ ((Wj j).Jrec7 (Pj j) (Formalism.EigenvalueLevelCeiling.plc w) : ℝ)
    exact_mod_cast hle

end Point

theorem expSt_of : Formalism.CohomologicalDescent.E.ExCut → NumSt → SumExpSt → ModelSt → ExpSt := by
  intro hcut hN hS hM
  obtain ⟨a, ha, H⟩ := (hN.and hS).and hM
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := H e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨⟨x1, N1⟩, ⟨x2, S1⟩⟩, ⟨x3, M1⟩⟩ := hK Fm CH hc hL
  refine ⟨0, fun c _ _ => ⟨max x1 (max x2 x3), fun x hx hle i p hp hMo r O hR => ?_⟩⟩
  have h1 : x1 ≤ x := (le_max_left _ _).trans hle
  have h2 : x2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hle)
  have h3 : x3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hle)
  choose Pj Wj hPW using N1 x hx h1 i p hp hMo
  obtain ⟨st, hRT⟩ := hR.1.depth
  letI := st
  letI := hostAlg (Fm.D x i)
  intro C CH'
  exact hasExpBound_at p hcut O hRT.m_eq hRT.x_eq hRT.eps_eq hR.1.realisedChain_torus_eq Pj Wj (fun j => (hPW j).1) (fun j => (hPW j).2)
    (fun j t w => S1 x hx h2 i p hp hMo j (Pj j) (Wj j) (hPW j).1 (hPW j).2 t w)
    (fun j w hw hR' => M1 x hx h3 i p hp hMo j (Pj j) (Wj j) (hPW j).1 (hPW j).2 w hw hR') C CH'

end GlobalTheory.ExpTie.Asm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBetweenZeroAndBoundStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorDepth_between_zero_and_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (f : Lt1 Dw) (k : ℕ), FacBetween Xo la f k 0 (boundAll p (rk f) k) ∧ (k < p → FacBetween Xo la f k 0 0) := by
  first | exact @GlobalTheory.RefSum.facBetween_zero_boundAll | exact GlobalTheory.RefSum.facBetween_zero_boundAll | (intros; apply GlobalTheory.RefSum.facBetween_zero_boundAll <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstantIffCoveringGroupInvariant
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

open CategoryTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevInv

theorem evR_actLev {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {G : Type} [Group G]
    {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (hL : ActLev (Xo := Xo) c lev) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c} (hg : g ∈ sec Xo c a n)
    (γ : G) {k : Type} [Field k] [IsAlgClosed k] [Algebra c.F k] (y y' : FrPt Xo c k)
    (h : levR (Xo := Xo) (c := c) (lev γ) y y') :
    evR Xo c (actLev c lev γ g) y = evR Xo c g y' := by
  obtain ⟨p, φ, w, hw⟩ := GlobalTheory.TransferCompare.allTest_framed Xo c k y
  have hact : actLev c lev γ g ∈ sec Xo c a n :=
    Formalism.L2.Pj.actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ hg
  rw [GlobalTheory.FlatLine.evR_of_frMap_test hact.1 hw]
  have hm := Formalism.L2.Pj.mvPt_spec hL.total γ w
  have hw' := hL.nat γ p.R k φ w _ y y' hw hm h
  rw [GlobalTheory.FlatLine.evR_of_frMap_test hg.1 hw']
  rfl

theorem fibConst_iff_invariant : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → ((Dw.p ≠ Dw.q ∧ l.A = 1) ∨ GlobalTheory.ClsVal.Cmp.OverBase d) → ∀ (lift : Gam Dw d.l₂ → Dw.La →ₗ[𝓞 D.host.E] Dw.La), IsLift lift → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ sec d.Xo₂ d.c₂ a n, (FibConst d g ↔ ∀ γ, CongMod l.Mb (lift γ) LinearMap.id → actLev d.c₂ (fun γ => (lift γ, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) γ g = g) := by
  intro D j H Dw l Xo c d hpq hlev hA hB lift hlift a n g hg
  obtain ⟨hd, -, -, -, -, -, -, -, -⟩ := id hlev
  have hOB : GlobalTheory.ClsVal.Cmp.OverBase d := by
    rcases hB with ⟨hne, hA'⟩ | h
    · exact GlobalTheory.ClsVal.Cmp.overBase_of_ne hne hA' d
    · exact h
  have hO : GlobalTheory.CoverSec.AllOver d := GlobalTheory.CoverSec.allOver_of_overBase d hd.2.2 hOB
  have hq : ∀ (γ : Gam Dw d.l₂) (x : Dw.La),
      (Submodule.Quotient.mk (lift γ x) : LaQ Dw d.l₂) = γ (Submodule.Quotient.mk x) := fun γ x => by
    have e := congrArg (fun f => f x) (hlift γ)
    simpa using e
  have h1 : ∀ x, lift 1 x - x ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := fun x =>
    (Submodule.Quotient.eq _).1 ((hq 1 x).trans rfl)
  have hm : ∀ γ δ x, lift (γ * δ) x - lift γ (lift δ x) ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
    fun γ δ x => (Submodule.Quotient.eq _).1 (by rw [hq, hq, LinearEquiv.mul_apply, ← hq])
  have hL := GlobalTheory.LevelActionOfLifts.actLev_of_lifts_of_eq_one D H Dw d.l₂ d.Xo₂ d.c₂ (Gam Dw d.l₂) lift hpq hA h1 hm
  have hact : ∀ γ, actLev d.c₂ (fun γ => (lift γ, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La))) γ g ∈
      sec d.Xo₂ d.c₂ a n := fun γ => Formalism.L2.Pj.actL_mem _ _ _ _ hL.total hL.nat hL.bor _ γ hg
  constructor
  · intro hF γ hγ
    refine GlobalTheory.CoverSec.eq_of_geometric (hact γ).1 hg.1 fun k _ _ _ y₂ => ?_
    letI := GlobalTheory.CoverSec.algBelow d k
    have hk : ∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t := fun _ => rfl
    obtain ⟨y₂', hy₂'⟩ := hL.total γ k y₂
    obtain ⟨y, hy⟩ := GlobalTheory.CoverSec.exists_frOver_below d hk y₂ (hO k hk y₂)
    have ho := (GlobalTheory.LevOrbit.fibre_torsor D.host.E H Dw l Xo c d hpq hlev hA hOB lift hlift k hk y₂ y₂' y hy).1.2
      ⟨γ, hγ, hy₂'⟩
    rw [evR_actLev hL hg γ y₂ y₂' hy₂']
    exact (hF k hk y₂ y₂' y hy ho).symm
  · intro hI k _ _ _ _ hk y₂ y₂' y hy hy'
    obtain ⟨γ, hγ, hr⟩ :=
      (GlobalTheory.LevOrbit.fibre_torsor D.host.E H Dw l Xo c d hpq hlev hA hOB lift hlift k hk y₂ y₂' y hy).1.1 hy'
    rw [← evR_actLev hL hg γ y₂ y₂' hr, hI γ hγ]

end GlobalTheory.LevInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleClassesRationalLiftFormsLevel
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.FrameOf

theorem finite_classes_of_pres {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) :
    ∃ T : Finset G, ∀ g, ∃ γ ∈ ι.range, ∃ s ∈ T, ∃ κ ∈ presJ P, g = γ * s * κ := by
  classical
  have hf : (Set.range P.y).Finite := Set.finite_range _
  refine ⟨hf.toFinset, fun g => ?_⟩
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := P.reps g
  exact ⟨ι γ, ⟨γ, rfl⟩, P.y c, hf.mem_toFinset.2 ⟨c, rfl⟩, k, k.2, e⟩

theorem classesAt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T),
    ClassesAt p j t := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t
  exact finite_classes_of_pres (p.R.B.L j t).pres

end GlobalTheory.FrameOf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FittedTiesBoundEventualStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fitted_ties_bound_eventual : ∀ Q : GlobalTheory.SqTop.GP, SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.SqTop.GBig @Q → Lf (@Fitted @Comparison₂) fun p _ d C _ => Q d.G p.P.A3.A.μ0 C p.Z.x p.Z.b := by
  first | exact @GlobalTheory.BigTop.Fun.gBig_atTied | exact GlobalTheory.BigTop.Fun.gBig_atTied | (intros; apply GlobalTheory.BigTop.Fun.gBig_atTied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatThetaQuotientAtPrincipalLevelProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatThetaQuotientAtPrincipalLevel_proof : GlobalTheory.BaseCmp.FlatTwoStep := by
  first | exact @GlobalTheory.BaseCmp.flatTwoStep_holds | exact GlobalTheory.BaseCmp.flatTwoStep_holds | (intros; apply GlobalTheory.BaseCmp.flatTwoStep_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeBallNoContractionUnitaryUpperLevel
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.FreeBallAt

open GlobalTheory.Up GlobalTheory.Up.BallExPf
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem noContraction_of_rmul (X : DataX E r) {x1 b : Frame X.Ψ r} (hx1 : x1 ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) (h : GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X (rmul x1 b)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x1 := by
  intro N hN hop
  refine h N hN fun τ => ?_
  obtain ⟨c, hc0, hc1, hc⟩ := hop τ
  refine ⟨c, hc0, hc1, fun u => ?_⟩
  rw [GlobalTheory.MajInv.maj_rmul X.toData hx1 hb, GlobalTheory.MajInv.maj_rmul X.toData hx1 hb]
  exact hc u

theorem opNormLe_of_ball (hr : 0 < r) (X : Data E r) {x0 z1 : Frame X.Ψ r} {γ : GL (Fin r) E}
    (h0 : IsOrth X x0) (h1 : IsOrth X z1) (h2 : IsOrth X (lact γ z1))
    (hlt : rhX X x0 z1 < 1 / (49 * (r : ℝ) ^ 2))
    (hlt2 : rhX X x0 (lact γ z1) < 1 / (49 * (r : ℝ) ^ 2)) (τ : X.Ψ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.OpNormLe X x0 τ (γ : Matrix (Fin r) (Fin r) E) (Real.exp (1 / (3 * (r : ℝ)))) := by
  intro u
  rw [ModeHalfA.maj_orth X h0, ModeHalfA.maj_orth X h0]
  change ReciprocityTheory.MultiplicativeHeights.normSq _ ≤ _ * ReciprocityTheory.MultiplicativeHeights.normSq _
  have hk := ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_nonneg hr
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  have hu1 : IsUnit (mat z1 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X z1 h1 τ)
  have b1 := (frame_bound hr X h0 h1 hlt τ ((mat x0 τ)⁻¹ *ᵥ u)).1
  have b2 := (frame_bound hr X h0 h2 hlt2 τ ((mat z1 τ)⁻¹ *ᵥ u)).2
  have e : mat (lact γ z1) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat z1 τ := rfl
  rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv_cancel_right _ _ hu] at b1
  rw [e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu1,
    ← Matrix.mulVec_mulVec] at b2
  have hn : 0 ≤ ReciprocityTheory.MultiplicativeHeights.normSq ((mat x0 τ)⁻¹ *ᵥ u) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : ReciprocityTheory.MultiplicativeHeights.ballRatio r ^ 2 ≤ Real.exp (1 / (3 * (r : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hk (ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_le hr) 2
  calc _ ≤ _ := b2
    _ ≤ _ := mul_le_mul_of_nonneg_left b1 hk
    _ = ReciprocityTheory.MultiplicativeHeights.ballRatio r ^ 2 * ReciprocityTheory.MultiplicativeHeights.normSq ((mat x0 τ)⁻¹ *ᵥ u) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hE hn

theorem freeBall_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (G : Subgroup (GL (Fin r) E)) (g : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g → 3 * r < g → X.Γ ≤ G → (∀ γ ∈ G, IsUStab X.Gm X.L' γ) → (∀ γ ∈ G, IsUStab X.Gm X.Λ γ) → (∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) → ∀ x ∈ X.dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x → ∃ x0 : Frame X.Ψ r, IsOrth X.toData x0 ∧ (∃ b ∈ Bor X.Ψ r, x = rmul x0 b) ∧ GlobalTheory.Up.FreeBall X.toData G x0 (1 / (49 * (r : ℝ) ^ 2)) := by
  intro E _ _ _ r X G g hsp hg hΓ hL' hΛ hU x hx hNC
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X.toData x hx
  have hx1 : x1 ∈ X.dom := IW.orth_mem_dom X.toData x1 h1
  have hNC1 := noContraction_of_rmul X hx1 hb hNC
  refine ⟨x1, h1, ⟨b, hb, rfl⟩, hΓ, hΛ, fun γ hγ hne z hz hlt => ?_⟩
  by_contra hlt2
  rw [not_le] at hlt2
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have := rhX_nonneg h1 hz
    simp at hlt
    linarith
  obtain ⟨z1, hz1, b', hb', rfl⟩ := ortho_holds r X.toData z hz
  rw [FundSetPf.lact_rmul, rhX_rmul _ _ hb'] at hlt2
  rw [rhX_rmul _ _ hb'] at hlt
  have h2 := isOrth_lact_of_isUStab (hΛ γ hγ) hz1
  exact hne (GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof E r X g hsp hg G hL' hU x1 hx1 hNC1 γ hγ
    (opNormLe_of_ball hr X.toData h1 hz1 h2 hlt hlt2))

end GlobalTheory.FreeBallAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslateStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeLowerBlockVector_multiple_kernelTranslate : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (p : ℕ), (∀ PP ∈ Q, (p : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ x, ((ξ.1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → Formalism.L2.Host.ValLL0 D R.C → ∃ φ₁, VecOf R i Q (omegaFree R i Q ξR (fun PP : Pl D.host.E => Matrix.of fun (a : Fin (Vc D i).rank) (b : Fin (Wc D i).rank) => if (a : ℕ) = (b : ℕ) then (1 : kP PP) else 0)) φ₁ ∧ ∃ k ∈ GfC (Vc D i), ∃ (c : D.what₂.LL) (m : ℕ), φ₁ = D.what₂.embLL c • ω (k, 1) φ ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c) ∧ IsIntegral ℤ ((p : D.what₂.LL) ^ m * c⁻¹) ∧ c ≠ 0 ∧ ∀ h ∈ GfC (Vc D i), ∀ w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ m) • w) := by
  first | exact @GlobalTheory.FreeBlockTwist.vecFree_base_translate | exact GlobalTheory.FreeBlockTwist.vecFree_base_translate | (intros; apply GlobalTheory.FreeBlockTwist.vecFree_base_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitOfUnramifiedPrimeStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_orbit_of_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), ¬ (p : ℤ) ∣ discr E → FrobOnType io X ∧ ∀ τ : E →+* ℂ, ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h ∧ ∃ lab : ZMod h → (E →+* ℂ), IsOrbit io X τ lab := by
  first | exact @GlobalTheory.FrobOrbit.frobOnType_and_orbit | exact GlobalTheory.FrobOrbit.frobOnType_and_orbit | (intros; apply GlobalTheory.FrobOrbit.frobOnType_and_orbit <;> assumption)
end

