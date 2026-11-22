import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalInvariantSubspace
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOperatorActsByNoncompactQuadraticOps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

noncomputable section

namespace GlobalTheory.WeilConj

variable {D : D7}

theorem dag_dag {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (h : AdjLaw ψ T S) (f : WO T S → ℂ) :
    dag S T (dag T S f) = f := by
  funext y
  simp only [dag, Complex.conj_conj, h.invol y]

theorem dag_add (S T : HSp D) (f f' : WO S T → ℂ) : dag S T (f + f') = dag S T f + dag S T f' := by
  funext y; simp [dag]

theorem dag_smul (S T : HSp D) (c : ℂ) (f : WO S T → ℂ) : dag S T (c • f) = starRingEnd ℂ c • dag S T f := by
  funext y; simp [dag]

def conjE (S T : HSp D) (A : Module.End ℂ (WO S T → ℂ)) : Module.End ℂ (WO T S → ℂ) where
  toFun f := dag S T (A (dag T S f))
  map_add' f f' := by simp only [dag_add, map_add]
  map_smul' c f := by simp only [dag_smul, map_smul, Complex.conj_conj, RingHom.id_apply]

def conjRep {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S) (ω : WRep S T) :
    WRep T S where
  toFun p := conjE S T (ω (p.2, p.1))
  map_one' := by
    apply LinearMap.ext; intro f
    show dag S T (ω 1 (dag T S f)) = f
    rw [map_one, Module.End.one_apply, dag_dag hTS]
  map_mul' p q := by
    apply LinearMap.ext; intro f
    show dag S T (ω ((p * q).2, (p * q).1) (dag T S f)) = dag S T (ω (p.2, p.1) (dag T S (dag S T (ω (q.2, q.1) (dag T S f)))))
    rw [dag_dag hST]
    have : ((p * q).2, (p * q).1) = (p.2, p.1) * (q.2, q.1) := rfl
    rw [this, map_mul, Module.End.mul_apply]

theorem conjRep_apply {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S)
    (ω : WRep S T) (h : GA D T) (g : GA D S) (f : WO T S → ℂ) :
    conjRep hST hTS ω (h, g) f = dag S T (ω (g, h) (dag T S f)) := rfl

theorem adjO_zero {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (h : AdjLaw ψ S T) : adjO S T 0 = 0 := by
  have := h.add 0 0
  rw [add_zero] at this
  simpa using this

theorem unit_transport {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hST : AdjLaw ψ S T) (hTS : AdjLaw ψ T S)
    (μ : Measure (WO T S)) (𝓕 : Set (WO T S)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL S T) 𝓕 μ) :
    ∃ (μ' : Measure (WO S T)) (𝓕' : Set (WO S T)), μ'.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL T S) 𝓕' μ' ∧
      ∀ G : WO S T → ENNReal, ∫⁻ w in 𝓕, G (adjO S T w) ∂μ = ∫⁻ v in 𝓕', G v ∂μ' := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D S.rank T.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : BorelSpace (WO T S) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  let eA : WO T S ≃+ WO S T :=
    { toFun := adjO S T
      invFun := adjO T S
      left_inv := fun x => hTS.invol x
      right_inv := fun y => hST.invol y
      map_add' := hST.add }
  let eH : WO T S ≃ₜ WO S T := ⟨eA.toEquiv, hST.cont, hTS.cont⟩
  let eM : WO T S ≃ᵐ WO S T := eH.toMeasurableEquiv
  have hHaar : (μ.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ eA hST.cont hTS.cont
  have hmp : MeasurePreserving eM μ (μ.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (μ.map eM) μ := MeasurePreserving.symm eM hmp
  let eG : ratL S T → ratL T S := fun g => ⟨adjO S T g, (hST.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO T S g, (hTS.rat g).2 g.2⟩, Subtype.ext (hST.invol g)⟩⟩
    have e := congrArg (fun x : ratL T S => adjO T S (x : WO S T)) hg
    simp only [eG, hTS.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL T S) (eM.symm ⁻¹' 𝓕) (μ.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO T S (adjO S T g + x) = (g : WO T S) + adjO T S x
    rw [hTS.add, hTS.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' 𝓕) = 𝓕 := by
    ext a; simp
  refine ⟨μ.map eM, eM.symm ⁻¹' 𝓕, hHaar, hF, fun G => ?_⟩
  symm
  rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, hpre]
  rfl

theorem enorm_dag (S T : HSp D) (f : WO S T → ℂ) (y : WO T S) : ‖dag S T f y‖ₑ = ‖f (adjO S T y)‖ₑ := by
  simp only [dag]
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Complex.norm_conj]

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  refine ⟨by rw [← map_mul, h1], by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2], v, ε, hε, ?_⟩
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, h3]

theorem suppAt_cA {e : AE D} {V : HSp D} {g : GA D V} (h : SuppAt e V g) : SuppAt (cA D e) V g := by
  intro i j
  rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]
  exact h i j

theorem exists_detAt_cA {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} {x : (AE D)ˣ}
    (hx : IsDetAt e V g x) : ∃ x' : (AE D)ˣ, IsDetAt (cA D e) V g x' ∧
      ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D χ n → χ x' = χ x := by
  have hi : cA D e * cA D e = cA D e := by rw [← map_mul, he.1]
  refine ⟨GlobalTheory.SplitDetCharacter.cutDet (cA D e) hi V g, ?_, fun χ n hχ => ?_⟩
  · show _ = _
    rw [GlobalTheory.SplitDetCharacter.cutDet_val]; ring
  · refine GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hχ _ _ ?_
    rw [GlobalTheory.SplitDetCharacter.cutDet_val, hx, map_add, map_mul, map_sub, map_one]
    have hd := GlobalTheory.SplitDetCharacter.det_mul_conj V g
    linear_combination (1 - cA D (Formalism.L2.Theta.mt V g).det + (Formalism.L2.Theta.mt V g).det * cA D (Formalism.L2.Theta.mt V g).det
      - (Formalism.L2.Theta.mt V g).det) * hi + cA D e * hd

theorem exists_conj_weilDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : WRep S T), IsWeilDatumO ψ S T χS χT ω → ∃ ω' : WRep T S, IsWeilDatumO ψ T S χT χS ω' ∧ ∀ (g : GA D S) (h : GA D T) (f : WO S T → ℂ), ω' (h, g) (dag S T f) = dag S T (ω (g, h) f) := by
  intro D ψ S T χS χT ω H
  have hST : AdjLaw ψ S T := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ H.std S T
  have hTS : AdjLaw ψ T S := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ H.std T S
  refine ⟨conjRep hST hTS ω, ?_, fun g h f => by rw [conjRep_apply, dag_dag hST]⟩
  refine
    { std := H.std
      hecS := H.hecT
      hecT := H.hecS
      resS := H.resT
      resT := H.resS
      om_pres := fun p f hf => hST.theta _ (H.om_pres _ _ (hTS.theta f hf))
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro h g w₀ f hf
    rw [conjRep_apply, conjRep_apply]
    have e1 := hTS.Heisenberg₂ (adjO S T w₀) f
    rw [hTS.invol] at e1
    rw [← e1, H.om_heis g h (adjO S T w₀) _ (hTS.theta f hf), ← hST.act, hST.Heisenberg₂]
  · intro γ hγ γ' hγ' f hf
    rw [conjRep_apply]
    simp only [dag]
    rw [adjO_zero hST, H.om_aut γ' hγ' γ hγ _ (hTS.theta f hf)]
    simp only [dag]
    rw [adjO_zero hTS, Complex.conj_conj]
  · intro f hf w
    exact Complex.continuous_conj.comp ((H.om_cont _ (hTS.theta f hf) (adjO S T w)).comp continuous_swap)
  · intro μ 𝓕 hμ h𝓕 p f hf
    obtain ⟨μ', 𝓕', hμ', h𝓕', hG⟩ := unit_transport hST hTS μ 𝓕 hμ h𝓕
    have e1 : ∀ w, ‖conjRep hST hTS ω p f w‖ₑ ^ 2 = (fun v => ‖ω (p.2, p.1) (dag T S f) v‖ₑ ^ 2) (adjO S T w) := by
      intro w
      show ‖dag S T (ω (p.2, p.1) (dag T S f)) w‖ₑ ^ 2 = _
      rw [enorm_dag]
    have e2 : ∀ w, ‖f w‖ₑ ^ 2 = (fun v => ‖dag T S f v‖ₑ ^ 2) (adjO S T w) := by
      intro w
      show _ = ‖dag T S f (adjO S T w)‖ₑ ^ 2
      rw [enorm_dag, hTS.invol]
    simp only [e1, e2]
    exact (hG (fun v => ‖ω (p.2, p.1) (dag T S f) v‖ₑ ^ 2)).trans
      ((H.om_unit μ' 𝓕' hμ' h𝓕' _ _ (hTS.theta f hf)).trans (hG (fun v => ‖dag T S f v‖ₑ ^ 2)).symm)
  · intro e he h g hTh hSg y x hy hx
    obtain ⟨x', hx', hxx⟩ := exists_detAt_cA he hx
    obtain ⟨y', hy', hyy⟩ := exists_detAt_cA he hy
    obtain ⟨r, hr, hℓ⟩ := H.om_split (cA D e) (isSplitIdem_cA he) g h (suppAt_cA hSg) (suppAt_cA hTh) x' y' hx' hy'
    refine ⟨r, hr, fun ℓ hinv f hf => ?_⟩
    let ℓω : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun F => starRingEnd ℂ (ℓ (dag S T F))
        map_add' := fun F F' => by simp only [dag_add, map_add]
        map_smul' := fun c F => by simp only [dag_smul, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply] }
    have hinvω : ∀ u : WO S T, (∀ i j, cA D (cA D e) * u i j = u i j) → ∀ F, IsThetaFunO ψ S T F →
        ℓω (heisO ψ S T u F) = ℓω F := by
      intro u hu F hF
      show starRingEnd ℂ (ℓ (dag S T (heisO ψ S T u F))) = starRingEnd ℂ (ℓ (dag S T F))
      have e1 := hST.Heisenberg₂ (adjO T S u) F
      rw [hST.invol] at e1
      have hh : IsHalf (cA D (cA D (cA D e))) (adjO T S u) := hTS.half _ u hu
      rw [GlobalTheory.DualPairCheck.cA_cA] at hh
      rw [← e1, hinv _ hh _ (hST.theta F hF)]
    have key := hℓ ℓω hinvω (dag T S f) (hTS.theta f hf)
    have k1 : ℓω (ω (g, h) (dag T S f)) = starRingEnd ℂ (ℓ (conjRep hST hTS ω (h, g) f)) := rfl
    have k2 : ℓω (dag T S f) = starRingEnd ℂ (ℓ f) := by
      show starRingEnd ℂ (ℓ (dag S T (dag T S f))) = _
      rw [dag_dag hTS]
    rw [k1, k2] at key
    have hsf : (starRingEnd ℂ) ((splitFacO χS χT x' y' : Circle) : ℂ) = ((splitFacO χT χS y x : Circle) : ℂ) := by
      rw [← Circle.coe_inv_eq_conj]
      congr 1
      unfold splitFacO
      rw [hxx χT _ H.resT, hyy χS _ H.resS, _root_.mul_inv_rev, inv_inv]
    have key' := congrArg (starRingEnd ℂ) key
    rw [Complex.conj_conj, map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal, hsf] at key'
    exact key'

end GlobalTheory.WeilConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroup
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory

theorem exists_finset_sum_translate_fixed {G X : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X)
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (x : X) (hx : IsOpen {g | ρ g x = x}) :
    ∃ s : Finset G, (∀ g ∈ s, g ∈ K) ∧ s.Nonempty ∧
      ∀ k ∈ K, ρ k (∑ g ∈ s, ρ g x) = ∑ g ∈ s, ρ g x := by
  classical
  have hmul : ∀ (a b : G) (y : X), ρ (a * b) y = ρ a (ρ b y) := fun a b y => by
    rw [map_mul, Module.End.mul_apply]
  have hinv : ∀ (a : G) (y : X), ρ a⁻¹ (ρ a y) = y := fun a y => by
    rw [← hmul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinv' : ∀ (a : G) (y : X), ρ a (ρ a⁻¹ y) = y := fun a y => by
    rw [← hmul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun i : K => (fun g => (i : G)⁻¹ * g) ⁻¹' {g | ρ g x = x})
    (fun i => hx.preimage (continuous_const.mul continuous_id))
    (fun k hk => Set.mem_iUnion.2 ⟨⟨k, hk⟩, show ρ (k⁻¹ * k) x = x by
      rw [inv_mul_cancel, map_one, Module.End.one_apply]⟩)
  let F : Finset X := t.image (fun i : K => ρ (i : G) x)
  have hFmem : ∀ y, y ∈ F ↔ ∃ k ∈ K, ρ k x = y := by
    intro y
    constructor
    · intro hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.1 (ht hk)
      refine Finset.mem_image.2 ⟨i, hi, ?_⟩
      have h1 : ρ ((i : G)⁻¹ * k) x = x := hki
      calc ρ (i : G) x = ρ (i : G) (ρ ((i : G)⁻¹ * k) x) := by rw [h1]
        _ = ρ k x := by rw [← hmul, mul_inv_cancel_left]
  let f : X → G := fun y => if h : ∃ k ∈ K, ρ k x = y then h.choose else 1
  have hf : ∀ y ∈ F, f y ∈ K ∧ ρ (f y) x = y := by
    intro y hy
    have h := (hFmem y).1 hy
    simp only [f, dif_pos h]
    exact h.choose_spec
  refine ⟨F.image f, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hg
    exact (hf y hy).1
  · exact Finset.Nonempty.image ⟨x, (hFmem x).2 ⟨1, K.one_mem, by
      rw [map_one, Module.End.one_apply]⟩⟩ f
  · have hsum : ∑ g ∈ F.image f, ρ g x = ∑ y ∈ F, y := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl (fun y hy => (hf y hy).2)
      · intro y hy y' hy' h
        rw [← (hf y hy).2, ← (hf y' hy').2]
        exact congrArg (fun g => ρ g x) h
    intro k hk
    rw [hsum, map_sum]
    refine Finset.sum_nbij' (fun y => ρ k y) (fun y => ρ k⁻¹ y) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro y hy
      obtain ⟨k', hk', rfl⟩ := (hFmem y).1 hy
      exact (hFmem _).2 ⟨k * k', K.mul_mem hk hk', hmul _ _ _⟩
    · intro y hy
      obtain ⟨k', hk', rfl⟩ := (hFmem y).1 hy
      exact (hFmem _).2 ⟨k⁻¹ * k', K.mul_mem (K.inv_mem hk) hk', hmul _ _ _⟩
    · intro y _
      exact hinv k y
    · intro y _
      exact hinv' k y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntLevelSchwartzBruhatFiniteAdelic
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.SBLevel

theorem exists_int_level : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x u : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ i, ∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) v ∈ v.adicCompletionIntegers F) →
      g (x + u) = g x := by
  intro F _ _ κ _ g hg
  classical
  obtain ⟨N, hN, hNg⟩ := GlobalTheory.SBBox.exists_nhds_zero_add_eq hg.1 hg.2
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hW : (⋂ i, t i) ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun x u hu => hNg x u (hIt fun i _ => ?_)⟩
  have hdK : (algebraMap (𝓞 F) F d) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hmem := hd (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) (hu i)
  have he : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) *
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) = u i := by
    rw [← mul_assoc, ← map_mul]
    have : algebraMap (𝓞 F) F d * (d : F)⁻¹ = 1 := mul_inv_cancel₀ hdK
    rw [this, map_one, one_mul]
  rw [he] at hmem
  exact Set.mem_iInter.1 hmem i

end GlobalTheory.SBLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsL2AdelicQuotientModelEquivalence
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrModel

theorem exists_model : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∃ (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕))) (e : DividedPowerChartLift V μ ≃ₗᵢ[ℂ] Lp ℂ 2 (GlobalTheory.HolDict.nuQ V μ 𝓕)), GlobalTheory.HolDict.FinPair V μ 𝓕 ∧ GlobalTheory.HolDict.IsReg V μ 𝓕 ρ ∧ (∀ g F, e (RG V μ g F) = ρ g (e F)) ∧ ∀ F ψ, GlobalTheory.HolDict.Repr V μ 𝓕 (e F) ψ ↔ lift (GQ V) F =ᵐ[μ] ψ := by
  intro D V μ _ _
  refine ⟨GlobalTheory.AutomorphicL2Unitary.stdDom (GQ V), RG V μ, LinearIsometryEquiv.refl ℂ _, ?_, ?_, fun g F => rfl, fun F ψ => Iff.rfl⟩
  · exact ⟨inferInstance, inferInstance, GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ,
      (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ _ inferInstance
        (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ)).ne⟩
  · exact ⟨fun g F => GlobalTheory.AutomorphicL2Unitary.lift_R g F, fun g F => GlobalTheory.AutomorphicL2Unitary.norm_R g F,
      fun F => (isUnitaryRep_RG (V := V) (μ := μ)).continuous_apply F⟩

end GlobalTheory.TrModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalUnitaryGroupIsoConjIsometry
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

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocIsoConj

open Formalism.UG

theorem conj_unitary {R : Type} [CommRing R] (σ : R →+* R) {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1)
    (J : Matrix n n R) (J' : Matrix m m R) (hJ : cT σ a * J' * a = J) (g : Matrix n n R)
    (hg : cT σ g * J * g = J) : cT σ (a * g * b) * J' * (a * g * b) = J' := by
  calc cT σ (a * g * b) * J' * (a * g * b) = cT σ b * (cT σ g * (cT σ a * J' * a) * g) * b := by
        rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
    _ = cT σ b * (cT σ a * J' * a) * b := by rw [hJ, hg]
    _ = cT σ (a * b) * J' * (a * b) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]

def conjHom {R : Type} [CommRing R] {n m : Type} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1) (hba : b * a = 1) :
    Matrix n n R →* Matrix m m R where
  toFun g := a * g * b
  map_one' := by rw [Matrix.mul_one, hab]
  map_mul' g h := by
    calc a * (g * h) * b = a * g * (b * a) * h * b := by rw [hba, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_equiv {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (σ : R →+* R)
    {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (a : Matrix m n R) (b : Matrix n m R) (hab : a * b = 1) (hba : b * a = 1)
    (J : Matrix n n R) (J' : Matrix m m R) (hJ : cT σ a * J' * a = J) :
    ∃ φ : UJ σ J ≃ₜ* UJ σ J', ∀ g, ((φ g).1 : Matrix m m R) = a * (g.1 : Matrix n n R) * b := by
  have hJ' : cT σ b * J * b = J' := by
    rw [← hJ]
    calc cT σ b * (cT σ a * J' * a) * b = cT σ (a * b) * J' * (a * b) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J' := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]
  have hc : ∀ {k l : Type} [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l] (x : Matrix l k R)
      (y : Matrix k l R), Continuous fun g : Matrix k k R => x * g * y := by
    intro k l _ _ _ _ x y
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  let φ₀ : UJ σ J →* GL m R := (Units.map (conjHom a b hab hba)).comp (UJ σ J).subtype
  let ψ₀ : UJ σ J' →* GL n R := (Units.map (conjHom b a hba hab)).comp (UJ σ J').subtype
  have hφU : ∀ g, φ₀ g ∈ UJ σ J' := fun g => conj_unitary σ a b hab J J' hJ _ g.2
  have hψU : ∀ g, ψ₀ g ∈ UJ σ J := fun g => conj_unitary σ b a hba J' J hJ' _ g.2
  let φ : UJ σ J →* UJ σ J' := φ₀.codRestrict _ hφU
  let ψ : UJ σ J' →* UJ σ J := ψ₀.codRestrict _ hψU
  have hφc : Continuous φ :=
    ((Continuous.units_map _ (hc a b)).comp continuous_subtype_val).subtype_mk _
  have hψc : Continuous ψ :=
    ((Continuous.units_map _ (hc b a)).comp continuous_subtype_val).subtype_mk _
  have l : ∀ g, ψ (φ g) = g := by
    intro g
    apply Subtype.ext; apply Units.ext
    show b * (a * (g.1 : Matrix n n R) * b) * a = g.1
    calc b * (a * (g.1 : Matrix n n R) * b) * a = (b * a) * (g.1 : Matrix n n R) * (b * a) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hba, Matrix.one_mul, Matrix.mul_one]
  have r : ∀ g, φ (ψ g) = g := by
    intro g
    apply Subtype.ext; apply Units.ext
    show a * (b * (g.1 : Matrix m m R) * a) * b = g.1
    calc a * (b * (g.1 : Matrix m m R) * a) * b = (a * b) * (g.1 : Matrix m m R) * (a * b) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hab, Matrix.one_mul, Matrix.mul_one]
  exact ⟨{ toFun := φ, invFun := ψ, left_inv := l, right_inv := r, map_mul' := map_mul φ,
            continuous_toFun := hφc, continuous_invFun := hψc }, fun g => rfl⟩

theorem exists_locIso : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {r r' : ℕ} (J : Matrix (Fin r) (Fin r) E) (J' : Matrix (Fin r') (Fin r') E) (v : HeightOneSpectrum (𝓞 F)) (a : Matrix (Fin r') (Fin r) (Fv F v ⊗[F] E)) (b : Matrix (Fin r) (Fin r') (Fv F v ⊗[F] E)), a * b = 1 → b * a = 1 → Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a * JR (F := F) (Fv F v) J' * a = JR (F := F) (Fv F v) J → ∃ φ : GLoc σ J v ≃ₜ* GLoc σ J' v, ∀ g, (GlobalTheory.AdelicU.matHom _ σ J' (φ g)).val = a * (GlobalTheory.AdelicU.matHom _ σ J g).val * b := by
  intro F E _ _ _ _ _ σ r r' J J' v a b hab hba hJ
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨φ, hφ⟩ := exists_equiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) a b hab hba _ _ hJ
  exact ⟨φ, hφ⟩

end GlobalTheory.LocIsoConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupHalfCharactersSeparateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_half_characters_separate : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (e : AE D), IsSplitIdem D e → ∀ U : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (U : Set (halfMx (cA D e) W.rank r)) → ∃ L : AddSubgroup (halfMx (cA D e) W.rank r), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ L ≤ U ∧ ∀ x, x ∉ L → ∃ a : halfMx e W.rank r, (∀ l ∈ L, ψ (halfSympl W (a : Mx D W.rank r) (l : Mx D W.rank r)) = 1) ∧ ψ (halfSympl W (a : Mx D W.rank r) (x : Mx D W.rank r)) ≠ 1 := by
  first | exact @GlobalTheory.HalfSeparate.exists_open_separated | exact GlobalTheory.HalfSeparate.exists_open_separated | (intros; apply GlobalTheory.HalfSeparate.exists_open_separated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalInvariantSubspaceStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dimensional_invariant_subspace : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → ∀ T : ℕ → Module.End ℂ (kFinVec ε ρ), (∀ κ ∈ Kset ε, ∀ (k : ℕ) (v w : kFinVec ε ρ), (w : H) = ρ κ v → ((T k w : kFinVec ε ρ) : H) = ρ κ (T k v : H)) → ∃ S : Submodule ℂ (kFinVec ε ρ), FiniteDimensional ℂ S ∧ S ≠ ⊥ ∧ ∀ k, ∀ w ∈ S, T k w ∈ S := by
  first | exact @GlobalTheory.KFinStable.exists_finDim_stable | exact GlobalTheory.KFinStable.exists_finDim_stable | (intros; apply GlobalTheory.KFinStable.exists_finDim_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOperatorActsByNoncompactQuadraticOpsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_operator_acts_by_noncompact_quadratic_ops : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ (τ : D.what₂.Tau) YS YT, IsPMat (pS τ) YS → IsPMat (pT τ) YT → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ Gn : Module.End ℂ (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (BT τ * YT * (BT τ)⁻¹ * u - u * (BS τ * YS * (BS τ)⁻¹)) f) ∧ ∀ τ', τ' ≠ τ → ∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) → ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → (∀ g, IsThetaFunO ψ S T g → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) g) → ipO μ 𝓕 (Gn f) g = 0) → ∀ P, Gn (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT f (fockP τ (pS τ) (pT τ) YS YT P) := by
  first | exact @GlobalTheory.FockLieQuad.acts_by_fockP | exact GlobalTheory.FockLieQuad.acts_by_fockP | (intros; apply GlobalTheory.FockLieQuad.acts_by_fockP <;> assumption)
end

