import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0223
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0167
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0131
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0222
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0217
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0206
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm7OfAutomorphicCsdTemperedPurity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TempClose

open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

theorem rankOneUnitary (hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7)
    (P : Pin hL D) : RankOneUnitary P.T := by
  intro π w σ _ α hα
  obtain ⟨ξ, hξ, -, hξu⟩ := GlobalTheory.HeckeComp.main D.host.E (P.chr.e1 π).1 w
  have he := GlobalTheory.RankOneComp.locG_rankOne_eq_rcAt hAF hL D P π w ξ hξ
  rw [WDTie.eig, he] at hα
  unfold WD.inePol at hα
  split_ifs at hα with hσ
  · exact GlobalTheory.LocLanglands.IsRec.recUnit (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) ξ
      (Irr.ofDet 1 ξ hξ.1) (hξu (P.chr.e1 π).2) ⟨Representation.Equiv.refl _⟩ ⟨σ, hσ⟩ α hα
  · simp at hα

theorem rankTwo (hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hT : GlobalTheory.Published.CohomologicalCsdTempered)
    (hRP : GlobalTheory.Published.RegularAlgebraicPurity) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D)
    (a : ℕ) (π : D.naut.CG a) (ha : 2 ≤ a) (hc : D.naut.csd π) (hr : D.naut.ralg π) (w : PlE D.host) :
    D.naut.tempered (D.naut.locG π w) := by
  have := host_isCMField D.host
  have ha1 : 1 ≤ a := by omega
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (P.cg.e a π).1
  have hmk : CG.mk π₀ = (P.cg.e a π).1 := hπ₀
  have hc₀ : π₀.IsCsd := by
    have h1 := (P.cg.csd a π).1 hc
    rw [CGu.IsCsd, ← hmk] at h1
    exact h1
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [P.cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  have hcoh := (hRP D.host.E a ha1 π₀ hr₀).2
  obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp hAF D.host.E a π₀ w
  have htG := hT D.host.E a ha π₀ hc₀ hcoh w σ₀ hσ₀
  rw [P.T.tempered, P.cg.loc]
  show (ParLaws.locPar hL (P.cg.e a π).1 (D.nd.plOm.2 w)).tempered
  rw [← hmk, ParLaws.locPar_mk hL hσ₀ (D.nd.plOm.2 w)]
  exact GlobalTheory.T.tempered_rep_tempered_parameter D.host.E D.nd.Om _ w (D.nd.plOm.2 w) _ (ParLaws.isRec_locRec hL (D.nd.plOm.2 w)) a (ParLaws.toRep σ₀) htG

end GlobalTheory.TempClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardLeUnramifiedTwistsCuspidalSupportJacquetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_le_unramifiedTwists_cuspidalSupport_jacquet : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s s' : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k n) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (d' : Fin s' → ℕ) (e : (Σ j, Fin (d' j)) ≃ Fin n) (A : Finset (Fin s')) (x : GlobalTheory.PRep.Jacquet π.π (GlobalTheory.SmGL.unipRad k e)), GlobalTheory.SmGL.IsSmoothChar χ → GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) → (∀ j ∈ A, d' j = 1) → x ≠ 0 → (∀ j ∈ A, ∀ g ∈ GlobalTheory.SplitWeil.KO k (Fin (d' j)), GlobalTheory.SmGL.jac e π.π (Pi.mulSingle j g) x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → A.card ≤ Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
  first | exact @GlobalTheory.JacSuppCount.card_le_ncard_unrTwist | exact GlobalTheory.JacSuppCount.card_le_ncard_unrTwist | (intros; apply GlobalTheory.JacSuppCount.card_le_ncard_unrTwist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClTwistEqSelfOfEqOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory

open GlobalTheory.SmGL GlobalTheory.LocGL in
private theorem clTwist_eq_self_of_eq_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (c : IrrCl G) (χ : G →* ℂˣ) (hχ : IsSmoothChar χ) (h1 : χ = 1) : clTwist c χ hχ = c := by
  subst h1; exact clTwist_one c hχ

theorem rankOne_algNorm_locComp (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (π : CuspSub E 1)
    (ψ : HChar E) (hπ : CG.mk π = CG.ofChar ψ) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin 1) (w.adicCompletion E))) (hσ : π.IsLocComp w σ) :
    algNorm σ = IrrGL.ofChar (ψ.loc w) (ParLaws.isSmoothChar_loc ψ w) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [hπ] at h1
  have h2 := CG.IsLoc.unique E 1 _ w _ _ h1 (CG.isLoc_ofChar ψ w)
  obtain ⟨e⟩ := Quotient.exact h2
  unfold algNorm IrrGL.nu IrrGL.tw IrrGL.of IrrGL.ofChar
  congr 1
  refine (clTwist_eq_self_of_eq_one _ _ _ ?_).trans ?_
  · ext g
    simp [GlobalTheory.SmGL.detChar, GlobalTheory.SmGL.absPow]
  apply Quotient.sound
  exact ⟨e.trans (Representation.Equiv.refl _)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSph

def Gv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside {v} x}
  mul_mem' := fun hx hy => GlobalTheory.SatInd.CosetFin.trivOutside_mul hx hy
  one_mem' := by
    intro u _
    exact Matrix.map_one _ (map_zero _) (map_one _)
  inv_mem' := fun hx => GlobalTheory.SatInd.CosetFin.trivOutside_inv hx

def Kv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : Subgroup (GAf L n) :=
  Umax L n ⊓ Gv L n v

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem mem_Gv {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {x : GAf L n} :
    x ∈ Gv L n v ↔ TrivOutside {v} x := Iff.rfl

theorem trivOutside_one (T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    TrivOutside T (1 : GAf L n) := by
  intro u _
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem commute_of_trivOutside (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n)
    (hx : TrivOutside {v} x) (hy : TrivOutside {v}ᶜ y) : Commute x y := by
  show x * y = y * x
  apply Subtype.ext; apply Units.ext
  change (((x * y : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
    (((y * x : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
  apply GlobalTheory.SplitAdelic.mat_ext
  intro u
  rw [GlobalTheory.SplitAdelic.mul_coe, GlobalTheory.SplitAdelic.mul_coe, Matrix.map_mul, Matrix.map_mul]
  obtain rfl | hu := eq_or_ne u v
  · rw [hy _ (by simp), mul_one, one_mul]
  · rw [hx u hu, mul_one, one_mul]

theorem heckeFunI_rt {W : Type} [AddCommGroup W] [Module ℂ W] (U : Subgroup (GAf L n))
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}
    (Dv : InertDatum L n v w) (h : Formalism.UG.GU Dv.σw n → ℂ) (φ : GAf L n → W) (b : GAf L n)
    (hb : TrivOutside {v}ᶜ b) :
    heckeFunI L n U Dv h (NG.rt L n b φ) = NG.rt L n b (heckeFunI L n U Dv h φ) := by
  funext g
  show heckeFunI L n U Dv h (NG.rt L n b φ) g = heckeFunI L n U Dv h φ (g * b)
  unfold heckeFunI
  refine finsum_congr fun c => ?_
  split_ifs with hc
  · show _ • φ (g * hc.choose * b) = _ • φ (g * b * hc.choose)
    rw [mul_assoc, mul_assoc, (commute_of_trivOutside v _ _ hc.choose_spec.2 hb).eq]
  · rfl

end GlobalTheory.InertSph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG6OfAdmissible
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.ClosingSixth

theorem conclusionG6_of_adm : ∀ D : D7, SumRepresentations.admitted D → RbEx D → SumRepresentations.ConclusionG6 D :=
  GlobalTheory.T.conclusionG6_of_all_parts GlobalTheory.T.sixth_decomposition GlobalTheory.T.sixth_weight_statement GlobalTheory.T.sixth_character_equality GlobalTheory.T.mu_character GlobalTheory.T.eigencharacter_of_summand_charZero
    (GlobalTheory.T.residue_count_of_ss_rank GlobalTheory.T.valuation_ring_model GlobalTheory.T.exists_irreducible_constituents_charpoly_product GlobalTheory.T.absIrreducible_constituent_ranks_unique_of_charpoly)
    GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton.1 GlobalTheory.T.stringRankOneLength_and_multisetSumSingleton.2

end GlobalTheory.ClosingSixth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecomposeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_element_decompose : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ) (c : GAf L n), NG.Cong L n N c → ∃ a b : GAf L n, c = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x := by
  first | exact @GlobalTheory.CongSplit.decomp | exact GlobalTheory.CongSplit.decomp | (intros; apply GlobalTheory.CongSplit.decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepOneEqOfCharacter
section
noncomputable section

namespace GlobalTheory.RankOneChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.NPin
open GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem cg_eq_ofChar : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D)
    (π : D.naut.CG 1), haveI := GlobalTheory.CuspRep.host_isCMField D.host;
    ((P.cg.e 1 π).1 : GlobalTheory.CuspRep.CG D.host.E 1) = GlobalTheory.CuspRep.CG.ofChar (P.chr.e1 π).1 := by
  intro _ hL D P π
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (P.cg.e 1 π)).1 with hχ'
  set χ := (P.chr.e1 π).1 with hχ
  have hloc : ∀ v, P.T.e v (D.naut.locG π v) = ParLaws.locPar hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [P.cg.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [P.T.unr, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_unr_iff hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (P.chr.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [HChar.loc_mul, HChar.loc_inv, u1 x hx, u2 x hx, inv_one, mul_one]
    · have hf := P.chr.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [P.T.frobEig _ _ hv, hloc v]; exact GlobalTheory.RankOneComp.locPar_ofChar_frob hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  rw [← hchar, hχ', CGu.ofChar_equivChar]

end GlobalTheory.RankOneChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalPairIrreducibleProduct
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SwapTwo

open GlobalTheory.JacTensor GlobalTheory.EmptyFirstBlock

theorem nonempty_equiv_of_apply_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : ρ.IsIrreducible)
    (hσ : σ.IsIrreducible) (f : ρ.IntertwiningMap σ) {v : V} (hv : f v ≠ 0) : Nonempty (ρ.Equiv σ) := by
  let K : Subrepresentation ρ := ⟨LinearMap.ker f.toLinearMap, fun g x hx => by
    show f (ρ g x) = 0
    rw [f.isIntertwining]
    have hx' : f x = 0 := hx
    rw [hx', map_zero]⟩
  let R : Subrepresentation σ := ⟨LinearMap.range f.toLinearMap, by
    rintro g _ ⟨x, rfl⟩
    exact ⟨ρ g x, f.isIntertwining _ _ g x⟩⟩
  refine ⟨GlobalTheory.LocGL.equivOfBijective f ⟨?_, ?_⟩⟩
  · rcases eq_bot_or_eq_top K with h | h
    · refine (injective_iff_map_eq_zero f.toLinearMap).2 fun x hx => ?_
      have : x ∈ K := hx
      rw [h] at this
      exact this
    · exact absurd (show v ∈ K from h ▸ trivial) hv
  · rcases eq_bot_or_eq_top R with h | h
    · exact absurd (show f v ∈ R from ⟨v, rfl⟩) (by rw [h]; exact hv)
    · intro w
      obtain ⟨x, hx⟩ := (show w ∈ R from h ▸ trivial)
      exact ⟨x, hx⟩

theorem exists_jac_map_ne_zero : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : Type) [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)),
    (∀ i, 0 < d i ∧ IsCuspidal (σ i).π) → d 1 = 1 →
    (∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv
      (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α))))) →
    ∀ (e : (Σ i, Fin (d i)) ≃ n) (e' : (Σ i, Fin (d (Equiv.swap 0 1 i))) ≃ n),
    ∃ (φ : (jac e' (multiProd e fun i => (σ i).π)).IntertwiningMap
        (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)) (x : Jacquet (multiProd e fun i => (σ i).π) (unipRad k e')), φ x ≠ 0 := by
  intro _ hGL k _ _ _ _ n _ _ d σ hσ hd1 hnt e e'
  obtain ⟨z, c, c', hz, hcc, hX, hbad⟩ := GlobalTheory.T.exists_central_scalar_distinct_geometricLemma_cells k d σ hσ hd1 hnt
  obtain ⟨N, b, hb⟩ := (hGL k).1 (Fin 2) (Fin 2) n (fun i => Fin (d i)) (fun j => Fin (d (Equiv.swap 0 1 j))) e e'
  obtain ⟨S, hmono, h0, hN, h4⟩ := hb _ (piTensor fun i => (σ i).π) (isSmooth_piTensor fun i => (σ i).smooth)
  obtain ⟨G0, hG0⟩ : ∃ G0 : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j))),
      G0.1 = ![![0, d 0], ![1, 0]] := ⟨⟨![![0, d 0], ![1, 0]], by
      refine ⟨fun i => ?_, fun j => ?_⟩
      · fin_cases i <;> simp [Fin.sum_univ_two, hd1]
      · fin_cases j <;> simp [Fin.sum_univ_two, hd1]⟩, rfl⟩
  have hgood : (b (b.symm G0)).1 1 0 = 1 := by rw [Equiv.apply_symm_apply, hG0]; rfl
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := GlobalTheory.T.geometricLemmaCell_one_block_swap_equiv k d σ hd1 (b (b.symm G0)) hgood
  have hbad' : ∀ t, t ≠ b.symm G0 → (b t).1 1 0 = 0 := by
    intro t ht
    have r1 := (b t).2.1 1
    have c0 := (b t).2.2 0
    have r0 := (b t).2.1 0
    have c1 := (b t).2.2 1
    simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at r1 c0 r0 c1
    by_contra hne
    apply ht
    rw [Equiv.eq_symm_apply]
    apply Subtype.ext
    funext i j
    rw [hG0]
    fin_cases i <;> fin_cases j <;> simp <;> omega
  have hstep : ∀ t, t ≠ b.symm G0 → ∀ y, subQuot (S t.succ) (S t.castSucc) z y = c' • y := by
    intro t ht y
    have E := (h4 t (b t).nonempty_rows.some (b t).nonempty_cols.some).some
    apply E.toLinearEquiv.injective
    have h1 : E.toLinearEquiv (subQuot (S t.succ) (S t.castSucc) z y) = _ := LinearMap.congr_fun (E.isIntertwining' z) y
    have h2 := hbad (b t) (hbad' t ht) (b t).nonempty_rows.some (b t).nonempty_cols.some (E.toLinearEquiv y)
    exact h1.trans (h2.trans (LinearEquiv.map_smul E.toLinearEquiv c' y).symm)
  obtain ⟨φ, v, hv⟩ := GlobalTheory.T.exists_intertwining_of_central_filtration_step (jac e' (multiProd e fun i => (σ i).π))
    (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) N S hmono h0 hN z hz (b.symm G0) c (fun _ => c')
    (fun _ _ => hcc.symm) hstep
    ⟨(h4 (b.symm G0) f₀ g₀).some.trans E₀⟩ hX
    (GlobalTheory.ProdSupport.nontrivial_piTensor _ fun j => Model.nontrivial_of_isIrreducible (σ (Equiv.swap 0 1 j)).irr)
  exact ⟨φ, v, hv⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_of_comp {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ H V} (φ : G →* H) (h : Representation.IsIrreducible (ρ.comp φ)) :
    ρ.IsIrreducible := by
  haveI : Nontrivial V := Model.nontrivial_of_isIrreducible h
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← e] at h1
    exact hv h1
  · rcases eq_bot_or_eq_top (⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (φ g) hv⟩ :
        Subrepresentation (ρ.comp φ)) with h' | h'
    · left
      have h2 := congrArg Subrepresentation.toSubmodule h'
      exact Subrepresentation.toSubmodule_injective h2
    · right
      have h2 := congrArg Subrepresentation.toSubmodule h'
      exact Subrepresentation.toSubmodule_injective h2

theorem not_equiv_twist_symm : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (π₁ : Irr k r) (π₂ : Irr k t),
    (∀ (h : r = t) (α : ℂˣ), ¬ Nonempty ((h ▸ π₁ : Irr k t).π.Equiv (twist π₂.π (detChar (Fin t) (unrChar k α))))) →
    ∀ (h : t = r) (α : ℂˣ), ¬ Nonempty ((h ▸ π₂ : Irr k r).π.Equiv (twist π₁.π (detChar (Fin r) (unrChar k α)))) := by
  intro k _ _ _ _ r t π₁ π₂ hnt h α ⟨φ⟩
  subst h
  refine hnt rfl α⁻¹ ?_
  have heq : twist (twist π₁.π (detChar (Fin t) (unrChar k α))) (detChar (Fin t) (unrChar k α⁻¹)) = π₁.π := by
    ext g v
    simp only [twist_apply, detChar_apply, unrChar_apply, smul_smul, inv_zpow]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have e := (GlobalTheory.LocGL.twistEquiv φ (detChar (Fin t) (unrChar k α⁻¹))).symm
  rw [heq] at e
  exact ⟨e⟩

theorem isIrreducible_multiProd_two (hU : GlobalTheory.Published.UnlinkedProductIrreducible) {n : Type} [Fintype n]
    [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)) (hσ : ∀ i, 0 < d i ∧ IsCuspidal (σ i).π)
    (hnt : ∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv
      (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α)))))
    (e : (Σ i, Fin (d i)) ≃ n) : (multiProd e fun i => (σ i).π).IsIrreducible := by
  have hd : ∑ a, d a = d 0 + d 1 := Fin.sum_univ_two d
  have hsupp : ∀ i, IsCuspSupport (σ i).π (fun _ : Fin 1 => d i) (fun _ => (σ i).π) := fun i => by
    obtain ⟨φ⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one (σ i).smooth (oneBlock (d i)) fun _ _ => rfl
    exact ⟨(σ i).irr, fun _ => ⟨(hσ i).1, (σ i).irr, (hσ i).2⟩, oneBlock (d i),
      .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective⟩
  have h2 := hU k (d 0) (d 1) 1 1 (σ 0) (σ 1) _ _ _ _ (hsupp 0) (hsupp 1) fun _ _ h α => hnt h α
  obtain ⟨E₁⟩ := GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd hd fun i => (σ i).π
  have h3 := GlobalTheory.Parabolic.isIrreducible_of_equiv E₁ h2
  have hc : Fintype.card (Fin (d 0 + d 1)) = Fintype.card n := by
    rw [Fintype.card_fin, ← hd, ← Fintype.card_congr e]; simp
  let ψ : Fin (d 0 + d 1) ≃ n := Fintype.equivOfCardEq hc
  obtain ⟨E₂⟩ := GlobalTheory.T.normalisedParabolicInduction_reindex_equiv k (Fin 2) (fun i => Fin (d i)) _ _ (stdBlocks d hd) ψ _ (piTensor fun i => (σ i).π)
  have h4 := isIrreducible_of_comp _ (GlobalTheory.Parabolic.isIrreducible_of_equiv E₂ h3)
  obtain ⟨E₃⟩ := (Placing.parInd_jac_placing k (Fin 2) n (fun i => Fin (d i)) ((stdBlocks d hd).trans ψ) e _).1
    (piTensor fun i => (σ i).π)
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E₃ h4

theorem swap_two_equiv : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), (∀ i, 0 < d i ∧ IsCuspidal (σ i).π) → d 1 = 1 → (∀ (h : d 0 = d 1) (α : ℂˣ), ¬ Nonempty ((h ▸ σ 0 : Irr k (d 1)).π.Equiv (twist (σ 1).π (detChar (Fin (d 1)) (unrChar k α))))) → ∀ (e : (Σ i, Fin (d i)) ≃ n) (e' : (Σ i, Fin (d (Equiv.swap 0 1 i))) ≃ n), Nonempty ((multiProd e fun i => (σ i).π).Equiv (multiProd e' fun i => (σ (Equiv.swap 0 1 i)).π)) := by
  intro hBZ hGL hU k _ _ _ _ n _ _ d σ hσ hd1 hnt e e'
  have h1 := isIrreducible_multiProd_two hU d σ hσ hnt e
  have h2 := isIrreducible_multiProd_two hU (fun i => d (Equiv.swap 0 1 i)) (fun i => σ (Equiv.swap 0 1 i))
    (fun i => hσ _) (not_equiv_twist_symm k (d 0) (d 1) (σ 0) (σ 1) hnt) e'
  obtain ⟨φ, x, hx⟩ := exists_jac_map_ne_zero hBZ hGL k n d σ hσ hd1 hnt e e'
  obtain ⟨f, hf⟩ := (Model.evalOne_bijective e' (isSmooth_parInd _ _)
    (piTensor fun i => (σ (Equiv.swap 0 1 i)).π)).2 φ
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hv : f v ≠ 0 := fun h => hx (by
    rw [← hf]
    show (f v).1.1 1 = 0
    rw [h]; rfl)
  exact nonempty_equiv_of_apply_ne_zero h1 h2 f hv

end GlobalTheory.SwapTwo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBalancedBilinearTensorProductMapStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
open GlobalTheory.Pst.TwistLetters
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_balancedBilinear_tensorProduct_map : ∀ {LL U D₁ D₂ D₃ : Type} [Field LL] [Field U] [AddCommGroup D₁] [Module LL D₁] [AddCommGroup D₂] [Module LL D₂] [AddCommGroup D₃] [Module LL D₃] (m₁ : U →+* Module.End LL D₁) (m₂ : U →+* Module.End LL D₂) (m₃ : U →+* Module.End LL D₃) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) (β : D₁ →ₗ[LL] D₂ →ₗ[LL] D₃), (∀ c x y, β (m₁ c x) y = m₃ c (β x y)) → (∀ c x y, β x (m₂ c y) = m₃ c (β x y)) → ∃ Φ : GlobalTheory.Pst.Letter m₁ F τ ⊗[F] GlobalTheory.Pst.Letter m₂ F τ →ₗ[F] GlobalTheory.Pst.Letter m₃ F τ, ∀ x y, Φ (GlobalTheory.Pst.letterMk m₁ F τ x ⊗ₜ GlobalTheory.Pst.letterMk m₂ F τ y) = GlobalTheory.Pst.letterMk m₃ F τ (β x y) := by
  first | exact @GlobalTheory.LetterDescent.exists_letter_tensor_map | exact GlobalTheory.LetterDescent.exists_letter_tensor_map | (intros; apply GlobalTheory.LetterDescent.exists_letter_tensor_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGLStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspidalSupport_irreducibleSmoothGL : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) := by
  first | exact @GlobalTheory.CuspSupportExist.main | exact GlobalTheory.CuspSupportExist.main | (intros; apply GlobalTheory.CuspSupportExist.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlaceStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localComponent_eigenvector_splitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)), IsAutRepU U → ∀ w, IsSplitAt w → ∀ (J : Subgroup (GL (Fin n) (w.adicCompletion E))), IsOpen (J : Set (GL (Fin n) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion E))) → ∀ (χ : J →* ℂˣ) (φ : UA E n → ℂ), φ ∈ U → φ ≠ 0 → (∀ x ∈ locU n w, ∀ hx : cLoc w x ∈ J, RU E n x φ = (χ ⟨_, hx⟩ : ℂ) • φ) → ∃ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ ∃ v : σ.V, v ≠ 0 ∧ ∀ g : J, σ.ρ g v = (χ g : ℂ) • v := by
  first | (exact @GlobalTheory.SplitEigen.exists_locComp_eigen) | (exact GlobalTheory.SplitEigen.exists_locComp_eigen) | (intros; apply GlobalTheory.SplitEigen.exists_locComp_eigen  <;> assumption)
end

