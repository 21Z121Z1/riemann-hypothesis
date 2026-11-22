import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatiblePhaseExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1135
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0854
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0800
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftPhaseConjReadingsFiveClauses
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralShift

theorem exists_isCentralShift_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), ∀ z ∈ Subgroup.center G, ∃ ζ, IsCentralShift R i σ z ζ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i σ z hz
  obtain ⟨e, he⟩ := exists_idemSum R.Pg (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hC.lev.Pg)
  have h := exists_central_lift (Wc D i) (R.βW i) (R.datWp i R.triv) he (g := R.eG z) (map_center R.eG hz)
  obtain ⟨ζ, hc, hs, hl⟩ := h
  have ht : ∀ y v h, (R.HW i σ).e (R.gW i σ z y) v h = (R.HW i σ).e y v (h * ζ) := fun y v h =>
    (congrArg (fun T : MMap (R.MW i σ) => T v h) (hC.models.gW i σ z y)).trans
      (GlobalTheory.GeoActCompare.actW_apply R hC.models.HW σ hl y v h)
  refine ⟨ζ, hz, hc, hl.1, ⟨e, he, hs⟩, hl, ht,
    inner_eq_of_norm (R.gW i σ z) (GlobalTheory.gW_norm_eq R hC.models.HW hC.models.gW hC.models.νW i σ z),
    comm_of_center (R.gW i σ) hz, fun _ _ S _ y y' h => ?_⟩
  refine MultilinearMap.ext fun v => funext fun g => (ht y' v g).trans ?_
  refine (congrArg (fun T : MMap (R.MW i σ) => T v (g * ζ)) h).trans ?_
  show ∑ γ ∈ S, (R.HW i σ).e y v (g * ζ * γ) = ∑ γ ∈ S, (R.HW i σ).e (R.gW i σ z y) v (g * γ)
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [ht, mul_assoc, mul_assoc, Subgroup.mem_center_iff.1 hc γ]

end GlobalTheory.CentralShift

theorem GlobalTheory.CompPhase.exists_isCompPhase_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (u : GA D (Wc D i) → ℂ), PhaseFun R i u → ∃ U, IsCompPhase R i σ u U := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ u hu
  have hc := GlobalTheory.CompPhase.compFun_of_level _ _ hu.2.1 hu.2.2.1 hu.2.2.2
  have h := GlobalTheory.CompPhase.exists_unitary _ (hR.models.HW i σ) (postOn _ (LinearMap.mulLeft ℂ u))
    (fun T hT => Submodule.subset_span (hc.multMap hu.2.2.2 ((GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T).1 hT)))
    (fun T T' => congrArg (_ * ·) (GlobalTheory.CompPhase.ipM_phase hu.1 _ _ T T'))
  obtain ⟨U, hU⟩ := h
  exact ⟨U, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2, fun y v h => congrFun (DFunLike.congr_fun (hU y) v) h⟩

namespace GlobalTheory.ConjInner

set_option maxHeartbeats 1000000 in

theorem inner_reading_conj_five : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), JEvExists T R κw v₀ → JEvBar T R κw → BarTie fw → ∀ (σ : D.what₂.LL →+* ℂ), ¬ GoodEmb T.Q.c (res T σ) → ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ hC fw i hE hB hT σ hσ
  have hg : GoodEmb T.Q.c (resC T σ) := good_resC T hσ
  have hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i := fw.laws.spaceW _ (inR i) _ hg
  have h1 := (hT i σ hσ hV).1 (hB i σ hσ hV)
  obtain ⟨v, hv, h1⟩ := h1
  have h2 := fw.evaluates hE i ((starRingEnd ℂ).comp σ) hg hV
  have h3 : ∀ f g, evAt R i σ v (fw.jK i σ f) g =
      starRingEnd ℂ (evAt R i _ (v₀ i ((starRingEnd ℂ).comp σ)) (fw.jK i ((starRingEnd ℂ).comp σ) f) g) := fun f g =>
    (congrFun (h1 f) g).trans (congrArg (starRingEnd ℂ) (congrFun (h2 f) g).symm)
  have h4 : ∀ f f', ⟪fw.jK i σ f, fw.jK i σ f'⟫_ℂ =
      starRingEnd ℂ ⟪fw.jK i ((starRingEnd ℂ).comp σ) f, fw.jK i ((starRingEnd ℂ).comp σ) f'⟫_ℂ := fun f f' =>
    inner_conj_of_values R hC.models.HW i σ hv (fun τ => ((fw.hv₀ i _).1 τ).1) (h3 f) (h3 f')
  have h5 := fw.ks i
  obtain ⟨n, b, hb, -, -, -, h5⟩ := h5
  refine inner_conj_of_span σ _ _ _ h5 ?_
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  have e : ∀ k, ∃ f, ((fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = b k := fun k =>
    ⟨(fw.e i).symm ⟨b k, hb k⟩, congrArg Subtype.val ((fw.e i).apply_symm_apply _)⟩
  have e1 := e k
  have e2 := e l
  obtain ⟨f, e1⟩ := e1
  obtain ⟨f', e2⟩ := e2
  rw [← e1, ← e2]
  exact h4 f f'

end GlobalTheory.ConjInner

namespace GlobalTheory.CoreFive

theorem shift_phase_conj : (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ), ∀ z ∈ Subgroup.center G, ∃ ζ, IsCentralShift R i σ z ζ) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (u : GA D (Wc D i) → ℂ), PhaseFun R i u → ∃ U, IsCompPhase R i σ u U) ∧ (∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), JEvExists T R κw v₀ → JEvBar T R κw → BarTie fw → ∀ (σ : D.what₂.LL →+* ℂ), ¬ GoodEmb T.Q.c (res T σ) → ∀ y y', ⟪(R.FW i).j σ y, (R.FW i).j σ y'⟫_ℂ = starRingEnd ℂ ⟪(R.FW i).j ((starRingEnd ℂ).comp σ) y, (R.FW i).j ((starRingEnd ℂ).comp σ) y'⟫_ℂ) :=
  ⟨GlobalTheory.CentralShift.exists_isCentralShift_five, GlobalTheory.CompPhase.exists_isCompPhase_five,
    GlobalTheory.ConjInner.inner_reading_conj_five⟩

end GlobalTheory.CoreFive

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerFinitelyGeneratedModOpenStatement
section
open Matrix GlobalTheory.LKRes
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_finitely_generated_mod_open : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∃ G : Finset (GL (Fin n) (GlobalTheory.LKRes.KQ p K r)), (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) (GlobalTheory.LKRes.KQ p K r))) ∪
        ((Subgroup.centralizer {N} ⊓ GlobalTheory.LKRes.Kres p K n r : Subgroup _) : Set (GL (Fin n) (GlobalTheory.LKRes.KQ p K r)))) := by
  first | (exact @GlobalTheory.CentFG.centralizer_le_closure) | (exact GlobalTheory.CentFG.centralizer_le_closure) | (intros; apply GlobalTheory.CentFG.centralizer_le_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChangeOfFrameHolomorphicInvertibleHolomorphicChaStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.changeOfFrame_holomorphic_invertible_holomorphicChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ e.source → ∀ {A A' : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → MContDiffAt 2 (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) (e y) ∧ IsUnit (((A' * A⁻¹).map (ratVal · (e.symm (e y))) ())ᵀ).det ∧ ∀ᶠ x in 𝓝 (e y), ∀ η, mdbar (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) x η = 0 := by
  first | exact @GlobalTheory.GoodTop.changeFrame_holoChart | exact GlobalTheory.GoodTop.changeFrame_holoChart | (intros; apply GlobalTheory.GoodTop.changeFrame_holoChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegralStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧ ∀ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = mInt A (fun _ => φ.locPot) (fun _ => 1) := by
  first | exact @GlobalTheory.chernInt_one_eq_mInt | exact GlobalTheory.chernInt_one_eq_mInt | (intros; apply GlobalTheory.chernInt_one_eq_mInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassLineBundleWeightOfIsoStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMass_lineBundleWeightOfIso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (hA : A.IsLB) (w : L.Iso A) (hw : w.IsGen), φ.IsCInf → (φ.ofIso hA w hw).IsCInf ∧ Weight.chernInt (φ.ofIso hA w hw) Y.dim Set.univ (fun _ => 1) = Weight.chernInt φ Y.dim Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.ChernIso.chernMass_ofIso | exact GlobalTheory.ChernIso.chernMass_ofIso | (intros; apply GlobalTheory.ChernIso.chernMass_ofIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedFieldStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmExtension_conjugation_involutive_fixedField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧ ∀ x, σ x = x → ∃ f : F, algebraMap F E f = x := by
  first | exact @GlobalTheory.CMConjInvol.cm_conj_invol_fixed | exact GlobalTheory.CMConjInvol.cm_conj_invol_fixed | (intros; apply GlobalTheory.CMConjInvol.cm_conj_invol_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTraceEqAddStar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.TraceAddStar

theorem trace_eq_add_star : ∀ {D : D7} (x : D.host.E), ((Algebra.trace D.host.F D.host.E x : D.host.F) : D.host.E) = x + star x := by
  intro D x
  exact Formalism.MainNotions.BridgeLemma.tie_trace D.sp.cm x

end GlobalTheory.TraceAddStar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoePolyMapX
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GraphLocal

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

def rightInc (A : Subalgebra ℂ K) : κ' →+* tens (κ' := κ') A :=
  (Algebra.TensorProduct.includeRight : κ' →ₐ[ℂ] K ⊗[ℂ] κ').toRingHom.codRestrict
    (tens (κ' := κ') A).toSubring fun b => tmul_mem (one_mem A) b

def polyMap (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) :
    MvPolynomial (Fin m) κ' →+* tens (κ' := κ') A :=
  MvPolynomial.eval₂Hom (rightInc A) fun i => ⟨(v i : K) ⊗ₜ 1, tmul_mem (v i).2 1⟩

@[simp] theorem coe_rightInc (A : Subalgebra ℂ K) (b : κ') :
    (rightInc A b : K ⊗[ℂ] κ') = 1 ⊗ₜ b := rfl

@[simp] theorem coe_polyMap_X (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) (i : Fin m) :
    (polyMap (κ' := κ') A v (MvPolynomial.X i) : K ⊗[ℂ] κ') = (v i : K) ⊗ₜ 1 := by
  simp [polyMap]

@[simp] theorem coe_polyMap_C (A : Subalgebra ℂ K) {m : ℕ} (v : Fin m → A) (b : κ') :
    (polyMap (κ' := κ') A v (MvPolynomial.C b) : K ⊗[ℂ] κ') = 1 ⊗ₜ b := by
  simp [polyMap]

end GlobalTheory.GraphLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormsOf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ColNorms

theorem errUnit_nonneg (N : NumDatum) {T : ℕ} (hT : 1 ≤ T) : 0 ≤ errUnit N T := by
  have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
  have h1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
  have h2 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h3 : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * T) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1) h2)
  unfold errUnit
  positivity

theorem kernelBound_ge (N : NumDatum) (δ : Code N) (T : ℕ) (C₁ C₂ : ℝ) (j : ℕ) (lo : RPl N.R → ℝ) (lt : ℝ) (h h' n n' : ℕ) :
    kernelBound_sq N δ T C₁ j lo lt 1 1 1 1 + 2 * (C₂ * errUnit N T) ≤ kernelBound_sq N δ T (C₁ + C₂) j lo lt h h' n n' := by
  have a1 : 0 ≤ Real.log ((h : ℝ) * h') := by exact_mod_cast Real.log_natCast_nonneg (h * h')
  have a2 : 0 ≤ Real.log ((n : ℝ) * n') := by exact_mod_cast Real.log_natCast_nonneg (n * n')
  unfold kernelBound_sq errUnit
  simp only [Nat.cast_one, mul_one, Real.log_one]
  nlinarith

theorem SmallDatum.mono {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
    {S : Finset (HeightOneSpectrum (𝓞 E))} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {c : ℕ}
    {Ξ : HomE E a b → K} {β β' : ℝ} (h : SmallDatum S N N' c Ξ β) (hβ : β ≤ β') : SmallDatum S N N' c Ξ β' :=
  ⟨h.1, h.2.1, fun σ x => (h.2.2 σ x).trans hβ⟩

end GlobalTheory.ColNorms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingUnitsIntegralCofinite
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LocNormTau

variable {p : ℕ} [Fact p.Prime]

def tauR (G : HTGroup p) (β : G.Cˣ) (R : Type) [CommRing R] [Algebra ℚ R] (x : R ⊗[ℚ] G.C) : R ⊗[ℚ] G.C :=
  inC G R (β : G.C) * (starT G.star R x).unop * inC G R ((β⁻¹ : G.Cˣ) : G.C)

variable (G : HTGroup p) (β : G.Cˣ) (R : Type) [CommRing R] [Algebra ℚ R]

theorem tauR_add (x y : R ⊗[ℚ] G.C) : tauR G β R (x + y) = tauR G β R x + tauR G β R y := by
  simp only [tauR, map_add, MulOpposite.unop_add, mul_add, add_mul]

theorem inC_inv_mul : inC G R ((β⁻¹ : G.Cˣ) : G.C) * inC G R (β : G.C) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

theorem tauR_mul (x y : R ⊗[ℚ] G.C) : tauR G β R (x * y) = tauR G β R y * tauR G β R x := by
  have h := inC_inv_mul G β R
  simp only [tauR, map_mul, MulOpposite.unop_mul, mul_assoc]
  congr 2
  rw [← mul_assoc (inC G R ((β⁻¹ : G.Cˣ) : G.C)), h, one_mul]

theorem tauR_one : tauR G β R 1 = 1 := by
  simp only [tauR, map_one, MulOpposite.unop_one, mul_one]
  rw [← map_mul, Units.mul_inv, map_one]

theorem sh_mul (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem tauR_inC (c : G.C) :
    tauR G β R (inC G R c) = inC G R ((β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C)) := by
  have h : (starT G.star R (inC G R c)).unop = inC G R (sh G c) := by
    change (starT G.star R ((1 : R) ⊗ₜ c)).unop = (1 : R) ⊗ₜ (G.star c).unop
    exact starT_tmul G.star R 1 c
  simp only [tauR, h, map_mul]

theorem commute_inC_of_forall (e : G.C) (he : ∀ c : G.C, Commute e c) (x : R ⊗[ℚ] G.C) :
    Commute (inC G R e) x := by
  induction x using TensorProduct.induction_on with
  | zero => exact Commute.zero_right _
  | tmul r c =>
    change (1 : R) ⊗ₜ e * r ⊗ₜ c = r ⊗ₜ c * (1 : R) ⊗ₜ e
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, (he c).eq]
  | add x y hx hy => exact hx.add_right hy

end GlobalTheory.LocNormTau

namespace GlobalTheory.LocNormTau

variable {p : ℕ} [Fact p.Prime]

theorem exists_conj_neg (G : HTGroup p) : ∃ f : G.F, f ≠ 0 ∧ IsCMField.complexConj G.F f = -f := by
  have hne := IsCMField.complexConj_ne_one G.F
  obtain ⟨x, hx⟩ : ∃ x, IsCMField.complexConj G.F x ≠ x := by
    by_contra h
    push_neg at h
    exact hne (AlgEquiv.ext h)
  refine ⟨x - IsCMField.complexConj G.F x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
  simp [IsCMField.complexConj_apply_apply]

theorem norm_aux {A : Type*} [Ring A] (a b E : A) (ha : Commute E a) (hb : Commute E b) (hab : a * b = b * a) :
    (a + b * E) * (a - E * b) = a * a - E * E * (b * b) ∧ (a - E * b) * (a + b * E) = a * a - E * E * (b * b) := by
  have h1 : a * (E * b) = a * b * E := by rw [hb.eq, mul_assoc]
  have h2 : b * E * a = a * b * E := by rw [mul_assoc, ha.eq, ← mul_assoc, hab]
  have h3 : b * E * (E * b) = E * E * (b * b) := by
    calc b * E * (E * b) = b * (E * E) * b := by noncomm_ring
      _ = E * E * (b * b) := by rw [← (hb.mul_left hb).eq, mul_assoc]
  have h4 : E * b * a = a * b * E := by rw [mul_assoc, ← hab, (ha.mul_right hb).eq]
  have h5 : E * b * (b * E) = E * E * (b * b) := by
    calc E * b * (b * E) = E * ((b * b) * E) := by noncomm_ring
      _ = E * E * (b * b) := by rw [← (hb.mul_right hb).eq, mul_assoc]
  constructor
  · rw [show (a + b * E) * (a - E * b) = a * a - a * (E * b) + b * E * a - b * E * (E * b) by noncomm_ring,
      h1, h2, h3]
    abel
  · rw [show (a - E * b) * (a + b * E) = a * a + a * b * E - E * b * a - E * b * (b * E) by noncomm_ring,
      h4, h5]
    abel

end GlobalTheory.LocNormTau
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactDerivativeSeparatingDual
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CochainInv

theorem continuous_multilinear {ι : Type} [Fintype ι] {V G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup G] [NormedSpace ℝ G] (f : MultilinearMap ℝ (fun _ : ι => V) G) :
    Continuous f := by
  classical
  let b := Module.finBasis ℝ V
  have h : ∀ x : ι → V, f x = ∑ r : ι → Fin (Module.finrank ℝ V), (∏ i, b.coord (r i) (x i)) • f (fun i => b (r i)) := by
    intro x
    conv_lhs => rw [show x = fun i => ∑ j, b.coord j (x i) • b j from funext fun i => (b.sum_repr (x i)).symm]
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← MultilinearMap.map_smul_univ]
  rw [show (f : (ι → V) → G) = fun x => ∑ r : ι → Fin (Module.finrank ℝ V), (∏ i, b.coord (r i) (x i)) • f (fun i => b (r i))
    from funext h]
  refine continuous_finsetSum _ fun r _ => (continuous_finsetProd _ fun i _ => ?_).smul continuous_const
  exact ((b.coord (r i)).continuous_of_finiteDimensional).comp (continuous_apply i)

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def hermPart : Lie E a →ₗ[ℝ] Herm E a where
  toFun X := (2⁻¹ : ℝ) • ⟨Matrix.of X + star (Matrix.of X), IsSelfAdjoint.add_star_self _⟩
  map_add' X Y := by
    rw [← smul_add]; congr 1; ext1
    simp only [Submodule.coe_add, ← Matrix.of_add_of, star_add]; abel
  map_smul' c X := by
    rw [RingHom.id_apply, smul_comm]; congr 1; ext1
    simp only [SetLike.val_smul, ← Matrix.smul_of, star_smul, star_trivial, smul_add]

theorem hermPart_toL (X : Herm E a) : hermPart (toL X.1) = X := by
  ext1
  have h : star X.1 = X.1 := X.2.star_eq
  change (2⁻¹ : ℝ) • (Matrix.of (toL X.1) + star (Matrix.of (toL X.1))) = X.1
  rw [show Matrix.of (toL X.1) = X.1 from Matrix.of.apply_symm_apply _, h, ← two_smul ℝ, smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul]

end GlobalTheory.CochainInv

namespace GlobalTheory.CochainInv

open GlobalTheory.GKCoh in

theorem lie_apply_eq_sum : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (S : Set (Module.Dual ℂ M)) (c : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E)), star Z = -Z → c 0 = 1 → HasDerivAt (fun t => toL (c t).1) (toL Z) 0 → (∀ m, (∀ l ∈ S, l m = 0) → m = 0) → (∀ l ∈ S, ∀ m, HasDerivAt (fun t => l (κ (c t) m)) (l (L (toL Z) m)) 0) → ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → ∀ Y W : Fin q → Herm E a, (∀ i, (W i).1 = Z * (Y i).1 - (Y i).1 * Z) → L (toL Z) (ω Y) = ∑ i, ω (Function.update Y i (W i)) := by
  intro E _ _ a M _ _ _ _ κ L S c Z hZ hc0 hc hS hκ q ω hω Y W hW
  classical
  have hE : ∀ r m, HasDerivAt (fun t => (c t).1 r m) (Z r m) 0 := fun r m => hasDerivAt_pi.1 (hasDerivAt_pi.1 hc r) m
  let u : ℝ → Fin q → Lie E a := fun t i => toL ((c t).1 * (Y i).1 * star (c t).1)
  have hu : HasDerivAt u (fun i => toL (W i).1) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun r => hasDerivAt_pi.2 fun s => ?_
    have key : HasDerivAt (fun t => ((c t).1 * (Y i).1 * star (c t).1) r s)
        ((Z * (Y i).1 * star (c 0).1 + (c 0).1 * (Y i).1 * star Z) r s) 0 := by
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
      refine HasDerivAt.fun_sum fun k _ => ?_
      have h1 : HasDerivAt (fun t => ∑ m, (c t).1 r m * (Y i).1 m k) (∑ m, Z r m * (Y i).1 m k) 0 :=
        HasDerivAt.fun_sum fun m _ => (hE r m).mul_const _
      exact h1.mul (hE s k).star
    have e : Z * (Y i).1 * star (c 0).1 + (c 0).1 * (Y i).1 * star Z = (W i).1 := by
      rw [hW, hc0, hZ]; simp [sub_eq_add_neg]
    rw [e] at key
    exact key
  refine sub_eq_zero.1 (hS _ fun l hl => ?_)
  rw [map_sub, sub_eq_zero]
  let f : MultilinearMap ℝ (fun _ : Fin q => Lie E a) ℂ :=
    (l.restrictScalars ℝ).compMultilinearMap (ω.toMultilinearMap.compLinearMap fun _ => hermPart)
  let F : ContinuousMultilinearMap ℝ (fun _ : Fin q => Lie E a) ℂ := ⟨f, continuous_multilinear f⟩
  have hF : ∀ x, F x = l (ω (fun i => hermPart (x i))) := fun x => rfl
  have h1 := (F.hasFDerivAt (u 0)).comp_hasDerivAt (0 : ℝ) hu
  have h2 : (F ∘ u) = fun t => l (κ (c t) (ω Y)) := by
    funext t
    rw [Function.comp_apply, hF, ← hω (c t) Y]
    congr 2
    funext i
    exact hermPart_toL (adHerm (c t) (Y i))
  rw [h2, ContinuousMultilinearMap.linearDeriv_apply] at h1
  rw [(hκ l hl (ω Y)).unique h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hF]
  congr 2
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp [hermPart_toL]
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    change hermPart (toL ((c 0).1 * (Y j).1 * star (c 0).1)) = Y j
    simp [hc0, hermPart_toL]

end GlobalTheory.CochainInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothProjVarietyCompactManifoldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold : ∀ Y : Var ℂ, CompactSpace (CxPts Y.str (RingHom.id ℂ)) ∧ T2Space (CxPts Y.str (RingHom.id ℂ)) ∧ SecondCountableTopology (CxPts Y.str (RingHom.id ℂ)) ∧ ∃ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A := by
  first | exact @GlobalTheory.cxPts_var_compact_manifold | exact GlobalTheory.cxPts_var_compact_manifold | (intros; apply GlobalTheory.cxPts_var_compact_manifold <;> assumption)
end

