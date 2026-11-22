import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0322
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0251
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0323
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0299
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0319
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsConjPlOfUnderEqOfNe
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

namespace GlobalTheory.UnderConj
open Formalism.L2.Col Formalism.HermitianLatticesTheory GlobalTheory.SplitOffPlaces

theorem isConjPl_of_under_eq_of_ne : ∀ (D : D7) (PP PP' : Pl D.host.E), PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F) →
    PP ≠ PP' → Formalism.IndefR.Lev.IsConjPl PP PP' := by
  intro D PP PP' hu hne
  have key : PP' = conjSpec PP := by
    by_contra hc
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem (Q := PP') (P := PP) (P' := conjSpec PP) (Ne.symm hne) hc
    have hfix : star ((x * Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = ((x * Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) := by
      change star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)
      rw [star_mul, star_star]
    obtain ⟨a, ha⟩ := (D.sp.cm.fixed _).1 hfix
    have hint : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective, ha]
      exact (x * Formalism.L2.Col.cO D.host.E x).isIntegral_coe
    have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ = x * Formalism.L2.Col.cO D.host.E x := RingOfIntegers.ext ha
    have h1 : (⟨a, hint⟩ : 𝓞 D.host.F) ∈ (PP'.under (𝓞 D.host.F)).asIdeal := by
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP'.asIdeal
      rw [e]
      exact Ideal.mul_mem_right _ _ hx
    rw [← hu] at h1
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP.asIdeal at h1
    rw [e] at h1
    rcases PP.isPrime.mem_or_mem h1 with h | h
    · exact hx1 h
    · exact hx2 h
  rw [key]
  exact GlobalTheory.LevelPlaces.isConjPl_conjSpec PP

end GlobalTheory.UnderConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteDatumOfHomLatticeCosetSelfDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFiniteDatum_of_homLatticeCoset_selfDual : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {ε : Bool} {S T : GlobalTheory.Grid.Node D} {e : AE D}
    {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (c : GlobalTheory.Grid.Coset S T I) {f₀ f : WO S.V T.V → ℂ},
    GlobalTheory.Grid.IsVac ψ θ ε S T f₀ → IsSelfDualC S.V S.Λ → IsSelfDualC T.V T.Λ → IsIdemSum e P → I ≠ ⊥ →
    GlobalTheory.Grid.IsCosetVec ψ ε S T e I c f₀ f → GlobalTheory.Grid.IsFinVec ψ θ ε S T f := by
  first | exact @GlobalTheory.Grid.isFinVec_of_isCosetVec | exact GlobalTheory.Grid.isFinVec_of_isCosetVec | (intros; apply GlobalTheory.Grid.isFinVec_of_isCosetVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHilbertSchmidtOfAePointwiseBoundedLpTwoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHilbertSchmidt_of_ae_pointwise_bounded_Lp_two : ∀ {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ), (∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) → GlobalTheory.OpTrace.IsHilbertSchmidt T := by
  first | exact @GlobalTheory.isHilbertSchmidt_of_ae_bounded | exact GlobalTheory.isHilbertSchmidt_of_ae_bounded | (intros; apply GlobalTheory.isHilbertSchmidt_of_ae_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRegularSemisimpleOfTestFunctionNeZero
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer

open GlobalTheory.Orb

namespace GlobalTheory.RegSupp

theorem mem_iwahori_valued {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    {g : GL (Fin n) (Fv F v)} :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    g ∈ GlobalTheory.SmGL.iwahori (Fv F v) (Fin n) → g ∈ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.iwahori (Fv F v) n := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  intro hg
  haveI hc : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he : (ValuativeRel.valuation (Fv F v)).IsEquiv Valued.v := ValuativeRel.isEquiv _ _
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  have hle : (ValuativeRel.valuation (Fv F v)).integer ≤ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.Int (Fv F v) :=
    fun x hx => he.le_one_iff_le_one.1 hx
  refine Subgroup.mem_map.2 ⟨Matrix.GeneralLinearGroup.map (Subring.inclusion hle) h, ?_, ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.mem_iwahoriInt_iff]
    intro i j hij
    have hb := (Subgroup.mem_comap.1 hh) (i := i) (j := j) (by
      rw [show i = (GlobalTheory.SmGL.points (Fin n)) ⟨i, ()⟩ from rfl, show j = (GlobalTheory.SmGL.points (Fin n)) ⟨j, ()⟩ from rfl,
        GlobalTheory.SmGL.blk_apply, GlobalTheory.SmGL.blk_apply]
      exact hij)
    change IsLocalRing.residue _ (h.1 i j) = 0 at hb
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers _).isUnit_iff_valuation_eq_one] at hb
    have h1 : ValuativeRel.valuation (Fv F v) ((h.1 i j : _) : Fv F v) < 1 :=
      lt_of_le_of_ne (h.1 i j).2 hb
    exact he.lt_one_iff_lt_one.1 h1
  · ext i j
    rfl

end GlobalTheory.RegSupp

namespace GlobalTheory.RegSupp

theorem isRegSS_of_tensor_ne_zero : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (δ : GF V) (x : GA D V), tensor D.sp.cm.sig V.gram fa ff (x⁻¹ * rat V δ * x) ≠ 0 → IsRegSS δ.1.1 := by
  intro hI D V T U μf ff hT fa δ x h
  obtain ⟨-, -, ⟨t, ht, hfu⟩, -, hcof⟩ := hT
  have hfin : (Function.mulSupport fun v =>
      ff v (proj D.sp.cm.sig V.gram v (x⁻¹ * rat V δ * x))).Finite :=
    Filter.eventually_cofinite.1 ((hcof.and (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (frameLat V)
      (x⁻¹ * rat V δ * x))).mono fun v hv => by
        show ff v _ = 1
        rw [hv.1, unitLoc, Set.indicator_of_mem hv.2, Pi.one_apply])
  have hne : ff U.u (proj D.sp.cm.sig V.gram U.u (x⁻¹ * rat V δ * x)) ≠ 0 := by
    intro h0
    apply h
    show (∏ w, fa w (projArch D.sp.cm.sig V.gram w _)) * ∏ᶠ v, ff v (proj D.sp.cm.sig V.gram v _) = 0
    rw [finprod_eq_zero _ U.u h0 hfin, mul_zero]
  rw [hfu] at hne
  have hmem := Set.mem_of_indicator_ne_zero hne
  obtain ⟨A, hA, rfl⟩ := ht
  obtain ⟨a, ha, b, hb, e⟩ := U.frame.mem_iwahoriCoset.1 hmem
  have key := (hI _ (U.ϖ : Fv _ U.u) U.unif _ A hA
    (U.frame.equiv (proj D.sp.cm.sig V.gram U.u (x⁻¹ * rat V δ * x))).1
    ⟨a, mem_iwahori_valued U.u ha, b, mem_iwahori_valued U.u hb, by
      rw [e, Units.val_mul, Units.val_mul, GlobalTheory.SmGL.val_diagT]
      congr 2
      unfold GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.diagPow
      congr 1
      funext i
      exact Units.val_zpow_eq_zpow_val _ _⟩).2
  have e1 : U.frame.equiv (proj D.sp.cm.sig V.gram U.u (x⁻¹ * rat V δ * x)) =
      (U.frame.equiv (proj D.sp.cm.sig V.gram U.u x))⁻¹ * U.frame.equiv (proj D.sp.cm.sig V.gram U.u (rat V δ)) *
        U.frame.equiv (proj D.sp.cm.sig V.gram U.u x) := by
    simp only [map_mul, map_inv]
  rw [e1, charpoly_conj_GL] at key
  change (splitEquivIn _ _ U.frame.emb U.frame.basis _).1.charpoly.Separable at key
  rw [splitEquivIn_apply, charpoly_conj_GL, splitHom_val, rat, proj_ratEmb,
    show (matHom _ D.sp.cm.sig V.gram (ratLoc D.sp.cm.sig V.gram U.u δ)).1 = δ.1.1.map (inclR _) from rfl,
    Matrix.map_map, show (splitProj U.frame.emb) ∘ (inclR (Fv _ U.u)) = (U.frame.emb : _ →+* Fv _ U.u) from
      funext (splitProj_inclR _), Matrix.charpoly_map] at key
  exact (Polynomial.separable_map _).1 key

end GlobalTheory.RegSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothAutomorphicFormMultMapValue
section
noncomputable section

open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S GlobalTheory.SmVec GlobalTheory.MultGelf Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EquivValues

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def IsEquivMap (θ : InfFam D) (M : DSModel V S) (T : MMap M) : Prop :=
  ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
    (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)

def IsSobValued (M : DSModel V S) (T : MMap M) : Prop :=
  ∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x

variable {θ : InfFam D} {M : DSModel V S} {T : MMap M}

theorem rder_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieG (gramAt D V τ)) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRep (trRep (M.σ τ) (M.fr τ)) X u) :
    Rder θ V τ X (T (Function.update v τ u)) = T (Function.update v τ w) := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hC τ v x
  obtain ⟨m, ls, a, hls, ha⟩ := GlobalTheory.T.sobolevContinuousForm_sum_lieWord_inner _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 ℓ hℓ
  have hu := (mem_sm M τ).1 u.2
  have hmem : ∀ t : ℝ, trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u ∈
      smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := fun t =>
    rep_mem hG (isURep M τ) hu (exp_mem_UH hG hX t)
  have h1 : (fun t : ℝ => T (Function.update v τ u) (x * oneP θ V τ X t)) = fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ := by
    funext t
    rw [← ha _ (hmem t)]
    have h2 := hE τ _ (exp_mem_UH hG hX t) (Function.update v τ u) ⟨_, (mem_sm M τ).2 (hmem t)⟩
      (by rw [Function.update_self]; rfl)
    rw [Function.update_idem] at h2
    have h3 := hℓT ⟨_, (mem_sm M τ).2 (hmem t)⟩
    rw [h2] at h3
    exact h3.symm
  have h4 : HasDerivAt (fun t : ℝ =>
      ∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (trRep (M.σ τ) (M.fr τ) (NormedSpace.exp (t • X)) u)⟫_ℂ)
      (∑ i, ⟪a i, word (trRep (M.σ τ) (M.fr τ)) (ls i) (dRep (trRep (M.σ τ) (M.fr τ)) X u)⟫_ℂ) 0 := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have h5 := (hasDerivAt_const (0 : ℝ) (a i)).inner ℂ
      (GlobalTheory.T.lieWord_commutes_oneParameter_derivative _ _ _ (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (ls i) (hls i) _ hu X hX)
    simpa using h5
  unfold Rder
  rw [h1, h4.deriv, ← hℓT w, hw, ha _ (dRep_mem hG (isURep M τ) hu hX)]

theorem rderC_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (u w : M.sm τ)
    (hw : (w : M.H τ) = dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z u) :
    RderC θ V τ Z (T (Function.update v τ u)) = T (Function.update v τ w) := by
  have hG := gram_unit (M.fr_unit τ) (M.fr_gram τ)
  have hp := parts_mem hG (gram_herm (M.fr_gram τ)) Z
  have hu := (mem_sm M τ).1 u.2
  have h1 := rder_apply hE hC τ v hp.1 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ rfl
  have h2 := rder_apply hE hC τ v hp.2 u ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ rfl
  have h3 : w = ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.1)⟩ +
      Complex.I • ⟨_, (mem_sm M τ).2 (dRep_mem hG (isURep M τ) hu hp.2)⟩ := Subtype.ext hw
  rw [h3, T.map_update_add, T.map_update_smul, ← h1, ← h2]
  rfl

theorem foldr_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (v : M.Vec)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (u : M.sm τ) :
    ∃ w : M.sm τ, (w : M.H τ) =
        (l.map fun Z => dRepC (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) Z).foldr (fun f acc => f acc) (u : M.H τ) ∧
      (l.map fun Z => RderC θ V τ Z).foldr (fun f acc => f acc) (T (Function.update v τ u)) =
        T (Function.update v τ w) := by
  induction l with
  | nil => exact ⟨u, rfl, rfl⟩
  | cons Z l ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨⟨_, (mem_sm M τ).2 (dRepC_mem (gram_unit (M.fr_unit τ) (M.fr_gram τ)) (gram_herm (M.fr_gram τ))
      (isURep M τ) Z ((mem_sm M τ).1 w.2))⟩, ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1]
    · rw [List.map_cons, List.foldr_cons, h2]
      exact rderC_apply hE hC τ v Z w _ rfl

theorem gelf_apply (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = gelfH (gramAt D V τ) (M.rep τ) k (v τ)) :
    gelf θ V τ k (T v) = T (Function.update v τ w) := by
  choose f hf1 hf2 using fun idx : Fin (k + 1) → Fin V.rank =>
    foldr_apply hE hC τ v (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) (1 : ℂ)) (v τ)
  simp only [List.map_ofFn, Function.comp_def, Function.update_eq_self] at hf1 hf2
  have h1 : w = ∑ idx, f idx := by
    refine Subtype.ext ?_
    rw [hw, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun idx _ => (hf1 idx).symm
  rw [h1]
  refine Eq.trans ?_ (map_sum (T.toLinearMap v τ) f Finset.univ).symm
  exact Finset.sum_congr rfl fun idx _ => hf2 idx

theorem gelf_eigen (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (τ : D.what₂.Tau) (k : ℕ) (v : M.Vec) :
    ∃ c : ℂ, gelf θ V τ k (T v) = c • T v := by
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  obtain ⟨c, hc⟩ := GelfScalar.gelfH_scalar _ (M.ε τ) (M.H τ) (M.σ τ) (M.fr τ) (gramAt D V τ) (M.fr_unit τ)
    (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 k
  refine ⟨c, ?_⟩
  have hv := hc _ ((mem_sm M τ).1 (v τ).2)
  rw [gelf_apply hE hC τ k v (c • v τ) (by rw [Submodule.coe_smul]; exact hv.symm)]
  have := T.map_update_smul v τ c (v τ)
  rw [Function.update_eq_self] at this
  exact this

theorem zfin (hθ : IsInfFam θ) (hE : IsEquivMap θ M T) (hC : IsSobValued M T) (v : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ T v ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨ℂ ∙ T v, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := gelf_eigen hE hC τ k v
  rw [(GlobalTheory.Mem.AutSpace.linOnSm_gelf τ k).smul, hc]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

theorem isAutFunSm : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : MMap M) (U : Subgroup (GA D V)) (N : ℕ), IsOpen (U : Set (GA D V)) → (∀ v, Continuous (T v) ∧ (∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g) ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, T v (g * k) = T v g) ∧ T v ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (T v) ≠ ⊤) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v)) → (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) → ∀ v, IsAutFunSm θ V (T v) := by
  intro _ D θ hθ V S M T U N hU hT hE hC v
  obtain ⟨h1, h2, h3, h4, h5⟩ := hT v
  exact GlobalTheory.Grow.UnifModGrowth.isAutFunSm hθ ((GlobalTheory.Size.unifModGrowth_iff_growthSob hθ h4).2 ⟨N, h5⟩)
    ⟨h2, ⟨U, hU, h3⟩, h1⟩ h4 (zfin hθ hE hC v)

end GlobalTheory.EquivValues

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteLeOfGKStableDiscreteSeriesModelStatement
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_le_of_gKStable_discreteSeriesModel : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (W : Submodule ℂ (M.H τ)), W ≤ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → (∀ X ∈ lieAt V τ, ∀ w ∈ W, dRep (M.rep τ) X w ∈ W) → (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ, ∀ w ∈ W, M.rep τ k w ∈ W) → W ≠ ⊥ → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ W := by
  first | exact @GlobalTheory.HCModIrred.kFin_le_of_stable | exact GlobalTheory.HCModIrred.kFin_le_of_stable | (intros; apply GlobalTheory.HCModIrred.kFin_le_of_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteOrthogonalComplementStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_finite_orthogonal_complement : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → ∀ Z : Submodule ℂ H, Z ≤ kFinVec ε ρ → IsKStableOn ε ρ Z → Z ≠ kFinVec ε ρ → ∃ a : H, a ≠ 0 ∧ IsKFin ε ρ a ∧ ∀ z ∈ Z, ⟪a, z⟫_ℂ = 0 := by
  first | exact @GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec | exact GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec | (intros; apply GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFamOfNotMem
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.TrIdem

def normInd {G : Type} [MeasurableSpace G] (μ : Measure G) (H : Set G) : G → ℂ :=
  (μ.real H : ℂ)⁻¹ • H.indicator 1

variable {D : D7} {V : HSp D}

def kerSub (T : TypeDataG V) (v : T.S) : Subgroup (GLoc D.sp.cm.sig V.gram v) :=
  ((T.frame v).red.ker).map (Kv V v).subtype

def levelFam (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v) :=
  Function.update (fun v => if hv : v ∈ T.S then kerSub T ⟨v, hv⟩ else Kv V v) U.u U.frame.iwahori

def fam (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ :=
  fun v => if hv : v ∈ T.S ∧ v ∈ A then T.idem μf ⟨v, hv.1⟩ else normInd (μf v) (levelFam T U v : Set _)

variable (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
  (A : Finset (HeightOneSpectrum (𝓞 D.host.F)))

theorem levelFam_u : levelFam T U U.u = U.frame.iwahori := Function.update_self ..

theorem levelFam_of_mem (hu : U.u ∉ T.S) (v : T.S) : levelFam T U v = kerSub T v := by
  have : (v : HeightOneSpectrum (𝓞 D.host.F)) ≠ U.u := fun e => hu (e ▸ v.2)
  rw [levelFam, Function.update_of_ne this, dif_pos v.2]

theorem levelFam_of_notMem {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ T.S) (hu : v ≠ U.u) :
    levelFam T U v = Kv V v := by
  rw [levelFam, Function.update_of_ne hu, dif_neg hv]

theorem fam_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ T.S) (hA : v ∈ A) :
    fam T U μf A v = T.idem μf ⟨v, hv⟩ := dif_pos ⟨hv, hA⟩

theorem fam_of_not {v : HeightOneSpectrum (𝓞 D.host.F)} (h : ¬ (v ∈ T.S ∧ v ∈ A)) :
    fam T U μf A v = normInd (μf v) (levelFam T U v : Set _) := dif_neg h

end GlobalTheory.TrIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinkedLineHomTransportLatticeVacuaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linked_line_hom_transport_lattice_vacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ x, ‖ψ x‖ = 1) → ∀ (L S : HSp D) (ζ ζ' : Fin L.rank → D.host.E), IsLineVec L ζ' → ∀ (l : Lnk L ζ L ζ') (Λ : AddSubgroup (WO S L)) (Ξ : WO L S → ℂ), IsLatVac (heisO ψ S L) Λ (fun w => star (Ξ (l.κ S w))) → ∀ w ∈ Λ, heisO ψ L S (2 • l.κ S w) Ξ = Ξ ∧ ∀ e, IsSplitIdem D e → IsHalf e (l.κ S w) → heisO ψ L S (l.κ S w) Ξ = Ξ := by
  first | exact @GlobalTheory.KapVac.kappa_vac | exact GlobalTheory.KapVac.kappa_vac | (intros; apply GlobalTheory.KapVac.kappa_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorFinitePlaceHeisenbergSumBaseVectorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_factor_finite_place_heisenberg_sum_base_vector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → IsLocOp ψ S T μ 𝓕 f₀ (.inl v) x := by
  first | exact @GlobalTheory.PlaceTensorFin.isLocOp_of_isLocal_fin | exact GlobalTheory.PlaceTensorFin.isLocOp_of_isLocal_fin | (intros; apply GlobalTheory.PlaceTensorFin.isLocOp_of_isLocal_fin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapConjSmallerUnitaryFlagUnipotentHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlagModulus

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem wittHyperbolic_conj_smallerGroup_coords (d : HypDec S S₀ ρ) (h : GA D S₀) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank)
    (c : skewA D ρ) : d.emb0 h * (d.levi u * (d.nB b * d.nC c)) * (d.emb0 h)⁻¹ =
      d.levi u * (d.nB (b ⬝ mt S₀ h⁻¹) * d.nC c) := by
  simp only [mul_assoc]
  rw [← mul_assoc (d.emb0 h) (d.levi u), d.wittHyperbolic_anisotropic_commute_levi h u, mul_assoc, ← mul_assoc (d.emb0 h) (d.nB b),
    d.wittHyperbolic_anisotropic_conj_nB b h, mul_assoc, ← mul_assoc (d.emb0 h) (d.nC c), d.wittHyperbolic_anisotropic_commute_nC c h, mul_assoc, mul_inv_cancel,
    mul_one]

theorem map_conj_smallerUnitary_flagUnipotent_haar : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (ν : Measure (flagN d)),
    ν.IsHaarMeasure → ∀ h : GA D S₀,
      ν.map (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) = ν.map Subtype.val := by
  intro D S S₀ ρ d ν hν h
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  obtain ⟨hlc, hsc, -, -⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  obtain ⟨μ, lB, lC, hμ, hB, hC, sμ, sB, sC, hΦ, ν₀, hν₀, hmap⟩ := GlobalTheory.HaarCoords.haar_coords D S S₀ ρ d
  have hk : ν = Measure.haarScalarFactor ν ν₀ • ν₀ := Measure.isMulLeftInvariant_eq_smul ν ν₀
  have hconj : Measurable (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hval : Measurable (Subtype.val : flagN d → GA D S) := measurable_subtype_coe
  have hf : Measurable (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hT : Measurable (Prod.map (id : UX D ρ → UX D ρ)
      (Prod.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) (id : skewA D ρ → skewA D ρ))) :=
    measurable_id.prodMap (hf.prodMap measurable_id)
  have key : ν₀.map (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) = ν₀.map Subtype.val := by
    have e1 : (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) =
        (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) ∘ Subtype.val := rfl
    rw [e1, ← Measure.map_map hconj hval, hmap, Measure.map_map hconj hΦ]
    have e2 : (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) ∘
        (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) =
        (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) ∘
          Prod.map (id : UX D ρ → UX D ρ)
            (Prod.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) (id : skewA D ρ → skewA D ρ)) :=
      funext fun p => wittHyperbolic_conj_smallerGroup_coords d h p.1.1 p.2.1 p.2.2
    rw [e2, ← Measure.map_map hΦ hT]
    congr 1
    rw [← Measure.map_prod_map _ _ measurable_id (hf.prodMap measurable_id), ← Measure.map_prod_map _ _ hf measurable_id,
      Measure.map_id, Measure.map_id, GlobalTheory.AdelicModulus.RowMat.map_mul_mt_eq D S₀ ρ lB hB h⁻¹]
  rw [hk, Measure.map_smul, Measure.map_smul, key]

end GlobalTheory.FlagModulus

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticRestrictionIsotropicPartEqPairingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_restriction_isotropic_part_eq_pairing : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → ∀ a t : Mx D W.rank r, symplO V W (restEmb V W K t) (isoPart V W C a) = halfSympl W a t := by
  first | exact @GlobalTheory.HalfAverage.sympl_restEmb_isoPart | exact GlobalTheory.HalfAverage.sympl_restEmb_isoPart | (intros; apply GlobalTheory.HalfAverage.sympl_restEmb_isoPart <;> assumption)
end

