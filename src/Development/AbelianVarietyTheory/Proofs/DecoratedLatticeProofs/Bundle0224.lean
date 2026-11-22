import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0130
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0177
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.RealComp

theorem eq_zero_of_map_eq_zero {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]
    {I : Type} {B : I → Type} [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)] (f : ∀ i, A →ₐ[F] B i)
    (hf : ∀ a, (∀ i, f i a = 0) → a = 0) (z : A ⊗[F] E)
    (hz : ∀ i, Algebra.TensorProduct.map (f i) (AlgHom.id F E) z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis F E
  have key : ∀ i (y : A ⊗[F] E) k,
      (Algebra.TensorProduct.basis (B i) b).repr (Algebra.TensorProduct.map (f i) (AlgHom.id F E) y) k =
        f i ((Algebra.TensorProduct.basis A b).repr y k) := by
    intro i y k
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply (Algebra.TensorProduct.basis A b).repr.injective
  ext k
  rw [map_zero, Finsupp.zero_apply]
  refine hf _ fun i => ?_
  rw [← key, hz, map_zero, Finsupp.zero_apply]

theorem compInf_eq_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) (z : AF F ⊗[F] E) : compInf F E w z =
    Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {D : D7}

theorem compInf_eq (w : InfinitePlace D.host.F) (z : AE D) : compInf D.host.F D.host.E w z =
    Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E) (infPart D z) :=
  compInf_eq_map w z

theorem compInf_zero_iff (z : AE D) : (∀ w, compInf D.host.F D.host.E w z = 0) ↔ infPart D z = 0 := by
  refine ⟨fun h => ?_, fun h w => by rw [compInf_eq, h, map_zero]⟩
  exact eq_zero_of_map_eq_zero (fun w => GlobalTheory.AutFunCompare.evW w) (fun a ha => funext ha) _
    fun w => (compInf_eq w z).symm.trans (h w)

theorem theta_zero_iff {θ : InfFam D} (hθ : IsInfFam θ) (y : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    (∀ τ, θ τ y = 0) ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h τ => by rw [h, map_zero]⟩
  refine (GlobalTheory.Mem.VolExists.infEmb_bijective (isCMExt_host D)
    (GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau) hθ).1 (funext fun τ => ?_)
  exact (h τ).trans (map_zero _).symm

theorem infPart_conj (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem eq_zero_of_parts (z : AE D) (h1 : infPart D z = 0) (h2 : finPart D z = 0) : z = 0 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  rw [map_zero]
  exact Prod.ext ((he z).1.trans h1) ((he z).2.trans h2)

theorem real_components : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ z : AE D, (∀ w, compInf D.host.F D.host.E w z = 0) ↔ ∀ τ, θ τ (infPart D z) = 0) ∧ (∀ z τ, θ τ (infPart D (cA D z)) = conj (θ τ (infPart D z))) ∧ (∀ x τ, θ τ (infPart D (incA D x)) = tauE D τ x) ∧ (∀ z : AE D, (∀ τ, θ τ (infPart D z) = 0) → finPart D z = 0 → z = 0) := by
  intro D θ hθ
  refine ⟨fun z => (compInf_zero_iff z).trans (theta_zero_iff hθ _).symm, fun z τ => ?_, fun x τ => (hθ τ).1 x,
    fun z h1 h2 => eq_zero_of_parts z ((theta_zero_iff hθ _).1 h1) h2⟩
  rw [infPart_conj]
  exact GlobalTheory.Mem.VolExists.infEmb_sigR (isCMExt_host D) (hθ τ) _

end GlobalTheory.StdUnn.RealComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentFundamentalDomainLayersIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

set_option maxHeartbeats 1000000 in

theorem layers_integral : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ), ∃ 𝓐 : Set (flagN d), IsFundamentalDomain ((GQ V ⊓ radX d).subgroupOf (flagN d)) 𝓐 vN.ν ∧ ∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν := by
  intro D V V₀ ρ d vN vb vU
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_flagUnipotent_coordinate_measurableEquiv D V V₀ ρ d
  obtain ⟨lC, 𝓒, hH, hS, hF, h1⟩ := GlobalTheory.T.exists_haar_covolume_one_skewHermitian_adelic D ρ
  obtain ⟨sb, su⟩ := GlobalTheory.T.sFinite_covolume_one_matrix_unitriangular_measures D ρ V₀.rank vb vU
  have hν := GlobalTheory.T.flagUnipotentHaar_eq_map_coordinates D V V₀ ρ d vN vb vU e he lC 𝓒 hH hS hF h1
  refine ⟨e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ)), ?_, ?_⟩
  · rw [hν]; exact GlobalTheory.T.wittFlagUnipotentFixer_fundamentalDomain_layers D V V₀ ρ d e he lC 𝓒 hH hS hF vb vU.ν sb su
  · intro f hf hinv
    have hg : Measurable fun p => f (e p : GA D V) := hf.comp (measurable_subtype_coe.comp e.measurable)
    let g : Mx D ρ V₀.rank × UX D ρ → ENNReal := fun q => f (e (0, q) : GA D V)
    have hgm : Measurable g := hg.comp (measurable_const.prodMk measurable_id)
    have hge : ∀ q, g q = f (d.nB q.1 * d.levi q.2.1) := fun q => by
      show f (e (0, q) : GA D V) = _
      rw [he, d.nC_zero, one_mul]
    have hpt : ∀ p : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ), f (e p : GA D V) = g p.2 := fun p => by
      have hm : (e (0, p.2) : GA D V) ∈ flagN d := (e (0, p.2)).2
      rw [he, d.nC_zero, one_mul] at hm
      rw [hge, he, hinv _ _ hm]
    have s1 : ∫⁻ n in e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ)), f n.1 ∂((lC.prod (vb.μ.prod vU.ν)).map e) =
        ∫⁻ p in 𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ), f (e p : GA D V) ∂(lC.prod (vb.μ.prod vU.ν)) := by
      rw [e.restrict_map, lintegral_map_equiv, e.preimage_image]
    have s2 : (lC.prod (vb.μ.prod vU.ν)).restrict (𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ)) = (lC.restrict 𝓒).prod ((vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ)) :=
      (Measure.prod_restrict 𝓒 (vb.𝓕 ×ˢ Set.univ)).symm
    have s3 : (vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ) = (vb.μ.restrict vb.𝓕).prod vU.ν := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    have s4 : ∫⁻ p, g p.2 ∂((lC.restrict 𝓒).prod ((vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ))) =
        ∫⁻ q, g q ∂((vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ)) := by
      rw [lintegral_prod (fun p : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) => g p.2) (hgm.comp measurable_snd).aemeasurable]
      show ∫⁻ _ in 𝓒, (∫⁻ y in vb.𝓕 ×ˢ Set.univ, g y ∂(vb.μ.prod vU.ν)) ∂lC = _
      rw [lintegral_const, Measure.restrict_apply_univ, h1, mul_one]
    have s5 : ∫⁻ q, g q ∂((vb.μ.restrict vb.𝓕).prod vU.ν) = ∫⁻ u, ∫⁻ b in vb.𝓕, g (b, u) ∂vb.μ ∂vU.ν := by
      rw [lintegral_prod _ hgm.aemeasurable]
      exact lintegral_lintegral_swap (f := fun b u => g (b, u)) hgm.aemeasurable
    have s6 : ∫⁻ p in 𝓒 ×ˢ (vb.𝓕 ×ˢ Set.univ), f (e p : GA D V) ∂(lC.prod (vb.μ.prod vU.ν)) =
        ∫⁻ p, g p.2 ∂((lC.restrict 𝓒).prod ((vb.μ.prod vU.ν).restrict (vb.𝓕 ×ˢ Set.univ))) := by
      rw [s2]; exact lintegral_congr fun p => hpt p
    rw [hν]
    refine s1.trans (s6.trans (s4.trans ?_))
    rw [s3]
    refine s5.trans ?_
    exact lintegral_congr fun u => lintegral_congr fun b => hge (b, u)

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapSupportFirstHalfAtLevelPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_map_support_first_half_at_level_place : ∀ (D : D7), OmLoc D → FlatBF D → GlobalTheory.LocFlat.SymCollapse → GSupp1 D := by
  first | exact @GlobalTheory.LocMod.SuppFirst.gsupp1 | exact GlobalTheory.LocMod.SuppFirst.gsupp1 | (intros; apply GlobalTheory.LocMod.SuppFirst.gsupp1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartanStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ K : Subgroup (GA D S), IsCompact (K : Set (GA D S)) → (∀ k ∈ K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ f, IsFockVec ψ θ S T sS sT f → IsKFinVec om K f := by
  first | exact @GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec | exact GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec | (intros; apply GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierInversionInverseRowTransformNegOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KappaModel

theorem finv_hat_neg_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψk : AddChar k Circle) (ν : Measure k), Continuous ψk → ψk ≠ 1 → ν.IsAddHaarMeasure → ∃ C : ℂ, ∀ c : Matrix n Unit k → ℂ, c ∈ SB (Matrix n Unit k) → ∀ Φ : Matrix Unit n k → ℂ, (∀ η, Φ η = GlobalTheory.StepData.hat ψk ν (-1) (fun y => c (Matrix.of fun r _ => y r)) (η ())) → GlobalTheory.KappaModel.finv ψk ν C Φ = c := by
  intro k _ _ _ _ _ _ n _ _ ψk ν hψ hne hν
  have := secondCountable k
  have := t2Space k
  let ψ' : AddChar k Circle :=
    { toFun := fun u => ψk (-u)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by intro a b; rw [neg_add, AddChar.map_add_eq_mul] }
  have hψ'app : ∀ u, ψ' u = ψk (-u) := fun _ => rfl
  have hψ' : Continuous ψ' := hψ.comp continuous_neg
  have hne' : ψ' ≠ 1 := by
    intro h
    apply hne
    refine DFunLike.ext _ _ fun u => ?_
    have := congrArg (fun χ : AddChar k Circle => χ (-u)) h
    simpa [hψ'app] using this
  obtain ⟨C', hC'pos, hC'⟩ :=
    GlobalTheory.LocFlat.PartialFourier.partial_fourier_inversion k ψ' ν hψ' hne' hν n
  refine ⟨((C' : ℂ))⁻¹, fun c hc Φ hΦ => ?_⟩
  funext x
  let e : (n → k) ≃ₜ Matrix n Unit k :=
    { toFun := fun y => Matrix.of fun r _ => y r
      invFun := fun M r => M r ()
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  set g : (n → k) → ℂ := fun y => c (Matrix.of fun r _ => y r) with hgdef
  have hg : g ∈ SB (n → k) := ⟨hc.1.comp_continuous e.continuous, hc.2.comp_homeomorph e⟩
  let p : (n → k) × (Empty → k) ≃ₜ (n → k) := Homeomorph.prodUnique (n → k) (Empty → k)
  set f : (n → k) × (Empty → k) → ℂ := fun q => g q.1 with hfdef
  have hf : f ∈ SB ((n → k) × (Empty → k)) := ⟨hg.1.comp_continuous p.continuous, hg.2.comp_homeomorph p⟩
  set a : n → k := fun r => x r () with hadef
  obtain ⟨-, hinv⟩ := hC' Empty a f hf
  set μJ : Measure (Empty → k) := Measure.pi fun _ => ν with hμJ
  have hJ : μJ.real Set.univ = 1 := by
    rw [hμJ, Measure.pi_of_empty (x := (fun e => e.elim))]
    simp
  have h1 : ∀ l : n → k, ∫ q : (n → k) × (Empty → k), f q * (ψ' (l ⬝ᵥ q.1) : ℂ) ∂((Measure.pi fun _ => ν).prod μJ) =
      ∫ y : n → k, g y * (ψk (-1 * (l ⬝ᵥ y)) : ℂ) ∂(Measure.pi fun _ => ν) := by
    intro l
    rw [hfdef]
    simp only [hψ'app, neg_one_mul]
    rw [integral_fun_fst (f := fun y : n → k => g y * (ψk (-(l ⬝ᵥ y)) : ℂ)), hJ, one_smul]
  have h2 : ∫ y : Empty → k, f (a, y) ∂μJ = g a := by
    rw [hfdef]
    simp only
    rw [integral_const, hJ, one_smul]
  simp only [h1, h2] at hinv
  simp only [hψ'app, neg_neg] at hinv
  have h3 : g a = c x := by
    rw [hgdef]; congr 1
  have hC0 : (C' : ℂ) ≠ 0 := by exact_mod_cast hC'pos.ne'
  simp only [finv, hΦ]
  rw [← h3, show ∫ η : n → k, GlobalTheory.StepData.hat ψk ν (-1) g ((Matrix.of fun _ r => η r : Matrix Unit n k) ()) * (ψk (η ⬝ᵥ fun r => x r ()) : ℂ) ∂(Measure.pi fun _ => ν) = ∫ l : n → k, (ψk (l ⬝ᵥ a) : ℂ) * ∫ y : n → k, g y * (ψk (-1 * (l ⬝ᵥ y)) : ℂ) ∂(Measure.pi fun _ => ν) ∂(Measure.pi fun _ => ν) from by
    congr 1; funext η; rw [mul_comm]; rfl]
  rw [hinv]
  field_simp

end GlobalTheory.KappaModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlaceSetNotConjugatePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeConjPg

theorem pg_places_not_isConjPl : ∀ {D : D7} (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D Pg _ he PP hP PP' hP'
  obtain ⟨e, he⟩ := he
  exact GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he PP hP PP' hP'

end GlobalTheory.SeeConjPg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlacesPairwiseNotConjugateStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genus_type_places_pairwise_not_conjugate : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  first | exact @GlobalTheory.Core.Mi.typePlaces_noConj | exact GlobalTheory.Core.Mi.typePlaces_noConj | (intros; apply GlobalTheory.Core.Mi.typePlaces_noConj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramUnimodular
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Unimod

theorem hform_frame {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (J B : Matrix (Fin n) (Fin n) R) (x y : Fin n → R) :
    Formalism.UG.hform σ J (B *ᵥ x) (B *ᵥ y) = ∑ i, σ (x i) * ((Formalism.UG.cT σ B * J * B) *ᵥ y) i := by
  have h1 : ∀ (u w : Fin n → R), Formalism.UG.hform σ J u w = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ w) := fun u w => by
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h2 : (fun i => σ ((B *ᵥ x) i)) = (B.map σ) *ᵥ (fun i => σ (x i)) := funext fun i => RingHom.map_mulVec σ B x i
  rw [h1, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Formalism.UG.cT, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec]
  rfl

theorem gram_int {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (O : Subring R) (hσ : ∀ z ∈ O, σ z ∈ O)
    (J B C H' : Matrix (Fin n) (Fin n) R) (L : (Fin n → R) → Prop) (hBC : B * C = 1)
    (hH : Formalism.UG.cT σ B * J * B * H' = 1)
    (hf : ∀ y, (∀ i, y i ∈ O) ↔ L (B *ᵥ y)) (hd : ∀ y, L y ↔ ∀ x, L x → Formalism.UG.hform σ J x y ∈ O) :
    (∀ i j, (Formalism.UG.cT σ B * J * B) i j ∈ O) ∧ ∀ i j, H' i j ∈ O := by
  have hs : ∀ i k : Fin n, (Pi.single i 1 : Fin n → R) k ∈ O := fun i k => by
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  constructor
  · intro i j
    have h := (hd _).1 ((hf _).1 (hs j)) _ ((hf _).1 (hs i))
    rw [hform_frame, Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)] at h
    simpa using h
  · intro i j
    have h : L (B *ᵥ (H' *ᵥ Pi.single j 1)) := by
      refine (hd _).2 fun x hx => ?_
      have e : x = B *ᵥ (C *ᵥ x) := by rw [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec]
      have hz : ∀ k, (C *ᵥ x) k ∈ O := (hf _).2 (e ▸ hx)
      rw [e, hform_frame]
      refine sum_mem fun k _ => mul_mem (hσ _ (hz k)) ?_
      rw [Matrix.mulVec_mulVec, hH, Matrix.one_mulVec]
      exact hs j k
    simpa using (hf _).2 h i

theorem compFin_cA {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) :
    compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_gram {D : D7} (A : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (b : Mx D A.rank A.rank) :
    (adj b * gA A * b).map (compFin D.host.F D.host.E v) =
      Formalism.UG.cT (sigR _ D.sp.cm.sig) (b.map (compFin D.host.F D.host.E v)) * JR (Fv D.host.F v) A.gram *
        b.map (compFin D.host.F D.host.E v) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  funext i j; exact compFin_cA v _

theorem gram_unimodular : ∀ (D : D7) (A : HSp D) (b : GL (Fin A.rank) (AE D)), IsLatticeFrame (frameLat A) b → ∃ Hm : GL (Fin A.rank) (AE D), Hm.1 = adj b.1 * gA A * b.1 ∧ IntGL Hm := by
  intro D A b hb
  have h1 : adj b.1 * adj (b⁻¹).1 = 1 := by
    rw [← adj_mul, Units.inv_mul, adj_one]
  have h2 : adj (b⁻¹).1 * adj b.1 = 1 := by
    rw [← adj_mul, Units.mul_inv, adj_one]
  let Hm : GL (Fin A.rank) (AE D) :=
    (⟨adj b.1, adj (b⁻¹).1, h1, h2⟩ * ⟨gA A, giA A, gA_mul_giA A, giA_mul_gA A⟩ * b : (Mx D A.rank A.rank)ˣ)
  have hH : Hm.1 = adj b.1 * gA A * b.1 := rfl
  have key := fun v : HeightOneSpectrum (𝓞 D.host.F) =>
    gram_int (sigR _ D.sp.cm.sig) (intLoc D.host.F D.host.E v) (fun z hz => sigR_mem_intLoc _ hz)
      (JR (Fv D.host.F v) A.gram) (b.1.map (compFin D.host.F D.host.E v)) ((b⁻¹).1.map (compFin D.host.F D.host.E v))
      ((Hm⁻¹).1.map (compFin D.host.F D.host.E v)) (fun y => y ∈ latLoc D.host.F (frameLat A) v)
      (by rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (by rw [← map_gram, ← hH, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)])
      (hb v) (fun y => by
        have := SelfDual.isSelfDualAt_frameLat D A v
        exact (SetLike.ext_iff.1 this) y)
  refine ⟨Hm, hH, fun i j v => ?_, fun i j v => (key v).2 i j⟩
  have := (key v).1 i j
  rw [← map_gram, ← hH] at this
  exact this

end GlobalTheory.StdUnn.Unimod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharQuotientNeOneCompletelySplitPrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.QuotVal

theorem val_quot_ne_one : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m → ∀ p : ℕ,
    GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains.SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    w.under (𝓞 D.host.F) ∉ c.S → GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w ≠ 1 := by
  intro D c hc i j hi hij hj p hp w hw hS h1
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
  have hoff : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := hS
  refine GlobalTheory.T.heckeChar_value_split_prime_not_root_of_unity D (c.μ (i' + 1) * (c.μ (j' + 1))⁻¹)
    (GlobalTheory.Chain.isHeckeChar_div (QuotL.isHecke hc (by omega) (by omega)) (QuotL.isHecke hc (by omega) hj))
    (fun τ => ⟨_, ?_, GlobalTheory.Chain.hasInfExp_div (hc.exp ⟨i', by omega⟩ τ) (hc.exp ⟨j', by omega⟩ τ)⟩) p hp w hw
    ((hc.unr ⟨i', by omega⟩ w hoff).mul (hc.unr ⟨j', by omega⟩ w hoff).inv) ?_
  · have := QuotL.e_strictMono (D.hc τ) (show (⟨i', by omega⟩ : Fin D.R.m) < ⟨j', by omega⟩ from
      Fin.mk_lt_mk.2 (by omega))
    intro h0
    linarith
  · rw [h1]
    exact IsOfFinOrder.one

end GlobalTheory.ChainOnto.QuotVal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharQuotientUnramifiedAtTwistPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_char_quotient_unramified_at_twist_place : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ PP ∈ w.Q, ∀ i j : ℕ, 1 ≤ i → i ≤ D.R.m → 1 ≤ j → j ≤ D.R.m → GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
  first | exact @GlobalTheory.ChainTw.quot_unrAt_twist | exact GlobalTheory.ChainTw.quot_unrAt_twist | (intros; apply GlobalTheory.ChainTw.quot_unrAt_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ x a, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.extX T a) f) x = d.mixS T ψ v.μ v.𝓕 f (x + a)) ∧ (∀ x a, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.extY T a) f) x = ψ (symplO S T (d.extX T x) (d.extY T a)) • d.mixS T ψ v.μ v.𝓕 f x) ∧ (∀ x w, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.ext0 T w) f) x = heisO ψ S₀ T w (d.mixS T ψ v.μ v.𝓕 f x)) ∧ (Continuous fun p : Mx D T.rank ρ × WO S₀ T => d.mixS T ψ v.μ v.𝓕 f p.1 p.2) ∧ ∀ w, HasSum (fun x : Matrix (Fin T.rank) (Fin ρ) D.host.E => d.mixS T ψ v.μ v.𝓕 f (rat x) w) (f (d.ext0 T w)) := by
  first | exact @GlobalTheory.HeisMixSource.heis_mixS | exact GlobalTheory.HeisMixSource.heis_mixS | (intros; apply GlobalTheory.HeisMixSource.heis_mixS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueNnrealPowFactor
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem holValueAt_npow_sub_mul : ∀ (h h' : ℂ → ℂ) (s₀ c : ℂ) (r : ℝ≥0) (σ : ℝ), 0 < r → HolValueAt h s₀ c →
    (∀ s : ℂ, σ < s.re → h' s = npow r (s₀ - s) * h s) → HolValueAt h' s₀ c := by
  intro h h' s₀ c r σ hr hh e
  have ha : AnalyticOnNhd ℂ (fun s => npow r (s₀ - s)) (GlobalTheory.Cont.rightOf (s₀.re - 1)) := by
    intro s _
    rw [funext fun s => npow_eq_exp hr (s₀ - s)]
    fun_prop
  have hg := GlobalTheory.Cont.holValueAt_self ha (s₀ := s₀) (by linarith)
  have h1 : npow r (s₀ - s₀) = 1 := by simp [npow_eq_exp hr]
  have hm := hg.mul hh
  simp only [h1, one_mul] at hm
  exact hm.congr ⟨σ, fun s hs => (e s hs).symm⟩

end GlobalTheory.StdUnn
end

