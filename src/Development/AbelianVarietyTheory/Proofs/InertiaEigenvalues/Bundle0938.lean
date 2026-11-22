import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0933
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0905
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0925
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0109
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0935
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0936
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleAtInertStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_at_inert : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → 1 ≤ C₂ → WachCoordinates.Conclusion2 D C₂ → KillingConditions.JointParametersHubConditions L HW X (rowC C₂) → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.InertK D (D.nd.l i) → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admitted i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) := by
  first | exact @GlobalTheory.NLink.InertStep.main | exact GlobalTheory.NLink.InertStep.main | (intros; apply GlobalTheory.NLink.InertStep.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockGLSupportedMemMirabolicSupportedStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockGL_supported_mem_mirabolic_supported : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
    ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S,
      GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.mirS E S (m + r + 1) := by
  first | (exact @GlobalTheory.BlockMirabolic.blockGL_mem_mirS) | (exact GlobalTheory.BlockMirabolic.blockGL_mem_mirS) | (intros; apply GlobalTheory.BlockMirabolic.blockGL_mem_mirS  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormReadingGaloisConjExpansion
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjExpand

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

set_option maxHeartbeats 1000000 in

theorem read_of_isBC (M : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c M.lev2)
    (cc : (C.U ((i : ℕ) + 1) M.s0).Comp → ℂ) (L : ℂ) (z : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n m : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) M.c'} (hf : f ∈ sec _ M.c' a n) {as : Fin m → M.c'.F}
    {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c} (hfs : ∀ k, fs k ∈ sec _ C.Q.c a n) (h : IsBC M.hle f as fs)
    (g : GA D (Wc D i)) :
    cc (M.dict g).1 * L * M.mu g * rdU (unfBC M.hle (C.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2 =
      ∑ k, (as k : ℂ) * (L * M.phi cc (actLev C.Q.c M.lev2 z (fs k)) g) := by
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ M.hle _ _ hact).2 a n z m as fs f hf hfs h
  have h2 := congrFun (congrFun (rdU_unfBC M.hle (C.U ((i : ℕ) + 1)) (inC M.c') h1) (M.dict g).1) (M.dict g).2
  rw [Finset.sum_apply, Finset.sum_apply] at h2
  refine (congrArg (fun w => cc (M.dict g).1 * L * M.mu g * w) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * L * M.mu _ * ((as k : ℂ) * _) = (as k : ℂ) * (L * (cc _ * M.mu _ * _))
  ring

end GlobalTheory.ConjExpand

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.ConjExpand.conjFun_galRul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (z : G), ∀ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) M.c' (unfBC M.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) → ConjFun M (κ i) τ 1 (fun g => T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2) (fun g => T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z (galRul hf f)) (M.dict g).1 (M.dict g).2) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup M hP τ ta hta hB hf z f hfc hE
  have hact := hP.act.1
  obtain ⟨ht⟩ := id hT
  have hn : (κ i).n = (Vc D i).rank :=
    (ht.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ M.hle).2 _ (T.U ((i : ℕ) + 1)) _ _ f hfc
  have hsec := ((mem_cusp _ _ _ _ _ _).1 hfc).1
  have hs : ∀ k, fs k ∈ sec _ T.Q.c (wtA (κ i)) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have hgal := GlobalTheory.GalTw.galRul_sec_val_semilinear _ _ (T.Q.Dw ((i : ℕ) + 1)) _ (T.Q.Xo ((i : ℕ) + 1)) M.c' ta hf
  have hFix : ∀ x : T.Q.c.F, ta (incF T.Q.c M.c' M.hle x) = incF T.Q.c M.c' M.hle x := by
    intro x
    apply Subtype.ext
    rw [hta]
    exact hB.core x
  have hgsec := ((hgal.1 _ _ f hsec).1)
  have hgBC := hgal.2.2 T.Q.c M.hle hFix _ _ m as fs f hsec hBC
  have hkeep : ∀ k, actLev T.Q.c M.lev2 z (fs k) ∈ T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := by
    intro k
    obtain ⟨y, hy, -⟩ := hP.lift.lev z
    refine (hE z y hy (fs k) ?_).1
    rw [hn]
    exact hfs k
  obtain ⟨Fk, hFk⟩ : ∃ Fk : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ∀ k, (Fk k : T.toCore.R ((i : ℕ) + 1)) = actLev T.Q.c M.lev2 z (fs k) := ⟨fun k => ⟨_, hkeep k⟩, fun _ => rfl⟩
  have e1 := fun g => GlobalTheory.ConjExpand.read_of_isBC M hact (T.cE ((i : ℕ) + 1) M.s0) (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) z hsec hs hBC g
  have e2 := fun g => GlobalTheory.ConjExpand.read_of_isBC M hact (T.cE ((i : ℕ) + 1) M.s0) (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) z hgsec hs hgBC g
  simp only [← hFk] at e1 e2
  refine ⟨⟨m, fun k => (as k : ℂ), Fk, fun g => e1 g⟩, ?_⟩
  intro n a h hex g
  have hz : Expands M (κ i) (fun _ => 0) (Fin.append a (fun k => -(as k : ℂ))) (Fin.append h Fk) := by
    intro g
    have h0 := (e1 g).symm.trans (hex g)
    show (0 : ℂ) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    linear_combination h0
  have hz' : (0 : ℂ) = _ := GlobalTheory.T.cuspForm_linear_relation_defined_over_core_field D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup M hP τ hB.core _ _ _ hz g
  rw [Fin.sum_univ_add] at hz'
  simp only [Fin.append_left, Fin.append_right, map_neg, neg_mul, Finset.sum_neg_distrib] at hz'
  refine (e2 g).trans ?_
  simp only [one_mul, hta]
  linear_combination hz'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFibreIdempotents
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.UnivCover

namespace GlobalTheory.FibreIdem

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem chi_eq_one_of_finPart : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A), IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := GlobalTheory.T.openKernel_ideleCharacter_trivial_finitePart_one

theorem chi_eq_one_of_cong : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := GlobalTheory.T.onePlaceTwist_trivial_on_congruent_units

theorem char_root_eq_one' (V : HSp D) {A : Type} [CommGroup A] (c : (AE D)ˣ →* A) (N : ℕ) (hN : Odd N)
    (hF : ∀ a, c (idF D a) = 1) (hinf : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1)
    (hcong : ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → c x = 1)
    (g : GA D V) (x : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hg : ∃ w ∈ intAE D, (((Matrix.GeneralLinearGroup.det (finHom V g)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
      (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • w) : c x = 1 := by
  obtain ⟨w, hw, hwe⟩ := hg
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add, hσ, add_comm]
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hwe
  have hn := GlobalTheory.RecDict.det_finHom_norm V g
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  have hcY : c Y = 1 := hcong Y ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩ ⟨p, hp, hY2 ▸ hpe⟩
  have hdet : (finHom V g).1.det = finPart D (matHom V g).1.det := ((finPart D).map_det _).symm
  have hxf : finPart D (x : AE D) =
      (finHom V g).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hdet, ← GlobalTheory.DetRootCong.finPart_sigR, ← RingHom.map_mul]
    exact congrArg _ hx
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom (x * Y⁻¹))
    (GlobalTheory.DetRootCong.quot_fixed (finPart D) _ x Y _ y y' hxf hroot hyy hY3)
  obtain ⟨a, ha⟩ := GlobalTheory.DetRootCong.exists_idF D b
  have hb' : finPart D (idF D a : AE D) = finPart D ((x * Y⁻¹ : (AE D)ˣ) : AE D) :=
    ha.trans (congrArg Units.val hb)
  have h1 := hinf (x * Y⁻¹ * (idF D a)⁻¹) (by
    rw [Units.val_mul, RingHom.map_mul, ← hb', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
  simpa [hcY, hF a] using h1

end GlobalTheory.FibreIdem

namespace GlobalTheory.FibreIdem

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

end GlobalTheory.FibreIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

theorem bc_invTr {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {N : ℕ} (g : GL (Fin N) A) :
    Formalism.UG.bc φ (inside₂ A N g) = inside₂ B N (Formalism.UG.bc φ g) := by
  apply Units.ext
  ext a b
  show φ (((g⁻¹ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) b a) = (((Formalism.UG.bc φ g)⁻¹ : GL (Fin N) B) : Matrix (Fin N) (Fin N) B) b a
  rw [← map_inv]
  rfl

theorem mapVV_rhoVr {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {n : ℕ} (φ : K →+* ℂ)
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (γ : GL (Fin n) E) (x : VV K lam) :
    mapVV φ lam (rhoVr emb lam γ x) = rhoVr (fun τ => φ.comp (emb τ)) lam γ (mapVV φ lam x) := by
  have h := mapVV_rhoK φ lam (invTrK (embGL emb γ)) x
  refine h.trans (congrArg (fun g : ι → GL (Fin n) ℂ => rhoK lam g (mapVV φ lam x)) ?_)
  funext τ
  show Formalism.UG.bc φ (inside₂ K n (Formalism.UG.bc (emb τ) γ)) = inside₂ ℂ n (Formalism.UG.bc (φ.comp (emb τ)) γ)
  rw [bc_invTr]
  congr 1

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

def conjVV {ι : Type} [Fintype ι] {n : ℕ} (τ : ℂ ≃+* ℂ) (lam : ι → DomWeight n) : VV ℂ lam ≃+ VV ℂ lam where
  toFun := mapVV (τ : ℂ →+* ℂ) lam
  invFun := mapVV (τ.symm : ℂ →+* ℂ) lam
  left_inv x := Subtype.ext (by
    have e : (τ.symm : ℂ →+* ℂ).comp (τ : ℂ →+* ℂ) = RingHom.id ℂ := by ext z; simp
    rw [mapVV_coe, mapVV_coe, MvPolynomial.map_map, e, MvPolynomial.map_id])
  right_inv x := Subtype.ext (by
    have e : (τ : ℂ →+* ℂ).comp (τ.symm : ℂ →+* ℂ) = RingHom.id ℂ := by ext z; simp
    rw [mapVV_coe, mapVV_coe, MvPolynomial.map_map, e, MvPolynomial.map_id])
  map_add' x y := map_add _ x y

theorem post_mem {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)
    (ρ : Γ →* Module.End ℂ W) {J J' : Subgroup G} (hJ : J' = J) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (τ : ℂ ≃+* ℂ) (T : W →+ W)
    (hs : ∀ (a : ℂ) w, T (a • w) = τ a • T w) (hρ : ∀ γ w, T (ρ γ w) = ρ γ (T w))
    (hχ : ∀ k (hk : k ∈ J) (hk' : k ∈ J'), ((χ' ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ ((χ ⟨k, hk⟩ : ℂˣ) : ℂ))
    {F : G → W} (hF : F ∈ Bridge.AdForms ι ρ J χ) : (fun g => T (F g)) ∈ Bridge.AdForms ι ρ J' χ' := by
  intro γ h k
  have hk : (k : G) ∈ J := hJ ▸ k.2
  have e := hF γ h ⟨k, hk⟩
  show T (F (ι γ * h * (k : G))) = ((χ' k : ℂˣ) : ℂ) • ρ γ (T (F h))
  have e' : F (ι γ * h * (k : G)) = ((χ ⟨k, hk⟩ : ℂˣ) : ℂ) • ρ γ (F h) := e
  rw [e', hs, hρ, ← hχ k hk k.2]

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

theorem c_rhoVr {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (M : OMDat T.toCore R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec}
    {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
    (hP : M.Pins κ v ι x₀) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (hc : ExtC R i (inC M.c') M.c0' c)
    (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E) (hγ : Bridge.IsRatMat (Vc D i) γ γE) (x : VsV D i ℂ) :
    c (rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE x) = (R.cV i).coef.ρ γ (c x) := by
  obtain ⟨gramR, c0R, c0L, hT, hbc⟩ := hP.lift.c0
  have hf : (inC M.c').comp M.jL = D.what₂.embLL := hP.lift.field
  have key : ∀ w : VsV D i D.what₂.LL, c (mapVV D.what₂.embLL (lamV D i) w) = c0L i w := by
    intro w
    obtain ⟨w', hw', hw''⟩ := hbc w
    refine (hc w' _ ?_).trans hw''
    rw [mapVV_coe, hw', MvPolynomial.map_map, hf]
  have hL : c ∘ₗ rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE = (R.cV i).coef.ρ γ ∘ₗ c := by
    apply LinearMap.ext_on_range (span_mapVV D.what₂.embLL (lamV D i))
    intro k
    show c (rhoVr (fun τ => D.what₂.embLL.comp (labLL D τ)) (lamV D i) γE (mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) k))) =
      (R.cV i).coef.ρ γ (c (mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) k)))
    rw [← mapVV_rhoVr]
    refine (key _).trans (((hT.mapL i).1 γ γE hγ _).trans ?_)
    exact congrArg _ (key _).symm
  exact LinearMap.congr_fun hL x

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

open GlobalTheory.CoefModel

theorem mapVV_tau_rhoVr (D : D7) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (hτ : ∀ (φ : D.host.E →+* ℂ) x, τ (φ x) = φ x)
    (γE : GL (Fin (Vc D i).rank) D.host.E) (x : VsV D i ℂ) :
    mapVV (τ : ℂ →+* ℂ) (lamV D i) (rhoVr (fun τ' => D.what₂.embLL.comp (labLL D τ')) (lamV D i) γE x) =
      rhoVr (fun τ' => D.what₂.embLL.comp (labLL D τ')) (lamV D i) γE (mapVV (τ : ℂ →+* ℂ) (lamV D i) x) := by
  rw [mapVV_rhoVr]
  have e : (fun τ' => (τ : ℂ →+* ℂ).comp (D.what₂.embLL.comp (labLL D τ'))) = fun τ' => D.what₂.embLL.comp (labLL D τ') := by
    funext τ'
    ext a
    exact hτ _ a
  rw [e]

theorem exists_conjW {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (M : OMDat T.toCore R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec}
    {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
    (hP : M.Pins κ v ι x₀) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (hc : ExtC R i (inC M.c') M.c0' c)
    (hb : Function.Bijective c) (τ : ℂ ≃+* ℂ) (hτ : ∀ (φ : D.host.E →+* ℂ) x, τ (φ x) = φ x) :
    ∃ TW : (R.cV i).W ≃+ (R.cV i).W, (∀ (a : ℂ) w, TW (a • w) = τ a • TW w) ∧
      (∀ x, TW (c x) = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) x)) ∧
      ∀ γ w, TW ((R.cV i).coef.ρ γ w) = (R.cV i).coef.ρ γ (TW w) := by
  let cb := LinearEquiv.ofBijective c hb
  have hcb : ∀ x, cb.symm (c x) = x := fun x => cb.symm_apply_apply x
  let TW : (R.cV i).W ≃+ (R.cV i).W := cb.symm.toAddEquiv.trans ((conjVV τ (lamV D i)).trans cb.toAddEquiv)
  have hTW : ∀ w, TW w = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) (cb.symm w)) := fun w => rfl
  have hTc : ∀ x, TW (c x) = c (mapVV (τ : ℂ →+* ℂ) (lamV D i) x) := fun x => by rw [hTW, hcb]
  refine ⟨TW, fun a w => ?_, hTc, fun γ w => ?_⟩
  · rw [hTW, hTW, map_smul, map_smulₛₗ, map_smul]
    rfl
  · obtain ⟨x, rfl⟩ := hb.2 w
    obtain ⟨γE, hγ⟩ := GlobalTheory.ConjForms.exists_ratMat (Vc D i) γ
    rw [← c_rhoVr M hP c hc γ γE hγ x, hTc, hTc, mapVV_tau_rhoVr D i τ hτ, c_rhoVr M hP c hc γ γE hγ]

end GlobalTheory.ConjTwist

namespace GlobalTheory.ConjTwist

set_option maxHeartbeats 8000000 in

theorem exists_conjForm_equiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), FixBase T R i τ → ConjTup R τ t t' → ∃ φ : (R.HV i t).H ≃+ (R.HV i t').H, (∀ (a : ℂ) y, φ (a • y) = τ a • φ y) ∧ ∀ y y', ConjForm R i τ c t t' y y' ↔ y' = φ y := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hCore hFW i Tp tup M hPins c hc τ t t' hFix hConj
  have hX := GlobalTheory.T.coefficientMap_unique_bijective_complex_extension D G Pl0 T0 A T R F κ v₀ hCore hFW i Tp tup M hPins
  obtain ⟨c₁, -, hb₁, hu⟩ := hX
  have hb : Function.Bijective c :=
    (congrArg (fun f : VsV D i ℂ →ₗ[ℂ] (R.cV i).W => Function.Bijective f) (hu c hc)).mpr hb₁
  have hY := exists_conjW M hPins c hc hb τ hFix.host
  obtain ⟨TW, hs, hTc, hρ⟩ := hY
  have hZ := (GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hCore τ t t' hConj).2.2.2 i hFix
  obtain ⟨hJ, hχ⟩ := hZ
  have hV := hCore.models.HV i t
  have hV' := hCore.models.HV i t'
  have hs' : ∀ (a : ℂ) w, TW.symm (a • w) = τ.symm a • TW.symm w := by
    intro a w
    apply TW.injective
    rw [hs, TW.apply_symm_apply, TW.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hρ' : ∀ γ w, TW.symm ((R.cV i).coef.ρ γ w) = (R.cV i).coef.ρ γ (TW.symm w) := by
    intro γ w
    apply TW.injective
    refine (TW.apply_symm_apply _).trans ?_
    refine Eq.trans ?_ (hρ γ (TW.symm w)).symm
    exact congrArg _ (TW.apply_symm_apply w).symm
  have hχ' : ∀ k (hk : k ∈ levJ R i t') (hk' : k ∈ levJ R i t),
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨k, hk'⟩ : ℂˣ) : ℂ) =
        τ.symm (((levEnv (Vc D i) (R.βV i) (R.datVt i t')).χ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
    intro k hk hk'
    exact (τ.symm_apply_apply _).symm.trans (congrArg τ.symm (hχ k hk' hk).symm)
  have hmem := fun y => hV.2.1.le (LinearMap.mem_range_self (R.HV i t).e y)
  have hmem' := fun y => hV'.2.1.le (LinearMap.mem_range_self (R.HV i t').e y)
  have hfwd : ∀ y, ∃ y', (R.HV i t').e y' = fun g => TW ((R.HV i t).e y g) := fun y =>
    LinearMap.mem_range.1 (hV'.2.1.ge
      (post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ _ _ τ TW.toAddMonoidHom hs hρ hχ (hmem y)))
  have hbwd : ∀ y', ∃ y, (R.HV i t).e y = fun g => TW.symm ((R.HV i t').e y' g) := fun y' =>
    LinearMap.mem_range.1 (hV.2.1.ge
      (post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ.symm _ _ τ.symm TW.symm.toAddMonoidHom hs' hρ' hχ' (hmem' y')))
  choose φ hφ using hfwd
  have hφadd : ∀ y z, φ (y + z) = φ y + φ z := by
    intro y z
    apply hV'.1
    funext g
    have e1 := congrFun (hφ (y + z)) g
    have e2 := congrFun (hφ y) g
    have e3 := congrFun (hφ z) g
    beta_reduce at e1 e2 e3
    refine e1.trans ?_
    exact (congrArg TW (congrFun (map_add (R.HV i t).e y z) g)).trans ((map_add TW _ _).trans
      ((congrArg₂ (· + ·) e2 e3).symm.trans (congrFun (map_add (R.HV i t').e (φ y) (φ z)) g).symm))
  have hφsmul : ∀ (a : ℂ) y, φ (a • y) = τ a • φ y := by
    intro a y
    apply hV'.1
    funext g
    have e1 := congrFun (hφ (a • y)) g
    have e2 := congrFun (hφ y) g
    beta_reduce at e1 e2
    refine e1.trans ?_
    exact (congrArg TW (congrFun (map_smul (R.HV i t).e a y) g)).trans ((hs _ _).trans
      ((congrArg (τ a • ·) e2).symm.trans (congrFun (map_smul (R.HV i t').e (τ a) (φ y)) g).symm))
  have hbij : Function.Bijective φ := by
    constructor
    · intro y z h
      apply hV.1
      funext g
      have := congrFun ((hφ y).symm.trans ((congrArg (R.HV i t').e h).trans (hφ z))) g
      exact TW.injective this
    · intro y'
      obtain ⟨y, hy⟩ := hbwd y'
      refine ⟨y, hV'.1 ?_⟩
      funext g
      exact (congrFun (hφ y) g).trans ((congrArg TW (congrFun hy g)).trans (TW.apply_symm_apply _))
  refine ⟨AddEquiv.ofBijective (AddMonoidHom.mk' φ hφadd) hbij, fun a y => hφsmul a y, fun y y' => ?_⟩
  show ConjForm R i τ c t t' y y' ↔ y' = φ y
  constructor
  · intro hC
    have key : ∀ h, (R.HV i t').e y' (Formalism.IndefR.FWT.fin (Vc D i) h) = TW ((R.HV i t).e y (Formalism.IndefR.FWT.fin (Vc D i) h)) := by
      intro h
      have h0 := hC h
      obtain ⟨x, x', hx, h1, h2⟩ := h0
      have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext (hx.trans (GlobalTheory.CoefModel.mapVV_coe _ _ _).symm)
      exact h2.trans ((congrArg c hx').trans ((hTc x).symm.trans (congrArg TW h1.symm)))
    apply hV'.1
    refine Eq.trans ?_ (hφ y).symm
    funext g
    have hs0 := (finHom (Vc D i)).rangeRestrict_surjective g
    obtain ⟨h, hh⟩ := hs0
    exact Eq.subst (motive := fun g => (R.HV i t').e y' g = TW ((R.HV i t).e y g)) hh (key h)
  · rintro rfl h
    have hs1 := hb.2 ((R.HV i t).e y (Formalism.IndefR.FWT.fin (Vc D i) h))
    obtain ⟨x, hx⟩ := hs1
    refine ⟨x, GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x, GlobalTheory.CoefModel.mapVV_coe _ _ _, hx.symm, ?_⟩
    refine (congrFun (hφ y) (Formalism.IndefR.FWT.fin (Vc D i) h)).trans ?_
    exact (congrArg TW hx.symm).trans (hTc x)

end GlobalTheory.ConjTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedLiftDataConjugatePrimeValueSqrtNor
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjFix

variable {D : D7}

noncomputable def starOEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  { Formalism.L2.DIV.starOHom (E := D.host.E) with
    invFun := Formalism.L2.DIV.starOHom (E := D.host.E)
    left_inv := fun a => Formalism.L2.DIV.starO_starO a
    right_inv := fun a => Formalism.L2.DIV.starO_starO a }

theorem natCast_mem_conjPl_iff (PP : Pl D.host.E) (N : ℕ) :
    ((N : 𝓞 D.host.E)) ∈ (Formalism.L2.DIV.conjPl PP).asIdeal ↔ ((N : 𝓞 D.host.E)) ∈ PP.asIdeal := by
  show Formalism.L2.DIV.starOHom (N : 𝓞 D.host.E) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem absNorm_conjPl (PP : Pl D.host.E) :
    Ideal.absNorm (Formalism.L2.DIV.conjPl PP).asIdeal = Ideal.absNorm PP.asIdeal := by
  have h : (Formalism.L2.DIV.conjPl PP).asIdeal = PP.asIdeal.map (starOEquiv (D := D)) := by
    rw [← Ideal.comap_symm]; rfl
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv PP.asIdeal (Formalism.L2.DIV.conjPl PP).asIdeal (starOEquiv (D := D)) h).toEquiv).symm

theorem fixBase_split_conj {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (PP : Pl D.host.E) :
    FixBase T R i τ → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal →
      τ ((((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)) =
        (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) := by
  intro hF hN
  have hN' : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    rwa [natCast_mem_conjPl_iff]
  have := hF.split (Formalism.L2.DIV.conjPl PP) hN'
  rwa [absNorm_conjPl] at this

end GlobalTheory.ConjFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlOrbitalIntegralUnitLiftLastBasisReduceStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glOrbitalIntegral_unit_liftLastBasis_reduce : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (M' : Meas r F E) (Z : Gl r F) (μ l : F), ‖μ‖ = 1 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → orbG M (unitG (r + 1) F) (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * orbG M' (unitG r F) Z := by
  first | exact @GlobalTheory.JR.GLift.orbG_lift | exact GlobalTheory.JR.GLift.orbG_lift | (intros; apply GlobalTheory.JR.GLift.orbG_lift <;> assumption)
end

