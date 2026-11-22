import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0649
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChain
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeformationComplex
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstLift

theorem isGrpPullback_of_eq_id {S : Scheme.{0}} (G : Over S) [GrpObj G] {f : S ⟶ S} {φ : G.left ⟶ G.left}
    (hf : f = 𝟙 S) (hφ : φ = 𝟙 _) : IsGrpPullback G G f φ := by
  subst hf hφ
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (Category.comp_id T.hom) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

theorem exists_constLift : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ →
    SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ),
    (∀ a : ℂ, π (algebraMap ℂ D a) = a) →
    ∃ (A' : Over (Sp D)) (_ : GrpObj A') (q : A'.left ⟶ A₀.left) (i : A₀.left ⟶ A'.left),
      IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ IsGrpPullback A' A₀ (spMap (algebraMap ℂ D)) q ∧
        IsGrpPullback A₀ A' (spMap π) i ∧ i ≫ q = 𝟙 _ := by
  intro A₀ _ g h hg D _ _ π hπ
  have e : spMap π ≫ spMap (algebraMap ℂ D) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, show π.comp (algebraMap ℂ D) = RingHom.id ℂ from RingHom.ext hπ,
      CommRingCat.ofHom_id, Spec.map_id]
  have w : 𝟙 A₀.left ≫ A₀.hom = (A₀.hom ≫ spMap π) ≫ spMap (algebraMap ℂ D) := by
    rw [Category.assoc, e, Category.id_comp, Category.comp_id]
  have hq := isGrpPullback_pullback A₀ (spMap (algebraMap ℂ D))
  refine ⟨(Over.pullback (spMap (algebraMap ℂ D))).obj A₀, inferInstance,
    pullback.fst A₀.hom (spMap (algebraMap ℂ D)), pullback.lift _ _ w, ?_, ?_, hq, ?_, pullback.lift_fst _ _ w⟩
  · exact
      { comm := by have := h.comm; infer_instance
        smooth := by have := h.smooth; change Smooth (pullback.snd A₀.hom _); infer_instance
        proper := by have := h.proper; change IsProper (pullback.snd A₀.hom _); infer_instance
        geomConnected := by
          have := h.geomConnected; change GeometricallyConnected (pullback.snd A₀.hom _); infer_instance }
  · change SmoothOfRelativeDimension g (pullback.snd A₀.hom _)
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback
      (IsPullback.of_hasPullback A₀.hom _) hg
  · exact hq.cancel (isGrpPullback_of_eq_id A₀ e (pullback.lift_fst _ _ w)) (pullback.lift_snd _ _ w)

end GlobalTheory.ConstLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomAgreeLocusClosedSubscheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem agreeLocus_factors_closedSubscheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → (φ' ≫ u.left = φ' ≫ v.left ↔ ∃ z : T ⟶ Z, z ≫ i = t) :=
  GlobalTheory.EndLoc.eqLocus_isClosedImmersion

end GlobalTheory.EndLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcycFOfPiShStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acycF_of_pi_sh' : ∀ (R : Type) [CommRing R] (F : Shv R) (ι : Type) [Finite ι] (T : ι → Type) [∀ i, CommRing (T i)] (B : Type) [CommRing B], Nonempty (B ≃+* (∀ i, T i)) → (∀ i, SH (T i)) → AcycF R (sp B) F := by
  first | exact @GlobalTheory.EtC.acycF_of_pi_sh | exact GlobalTheory.EtC.acycF_of_pi_sh | (intros; apply GlobalTheory.EtC.acycF_of_pi_sh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddMulLeOfPowLeOfLargeStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.add_mul_le_of_pow_le_of_large : ∀ (p L m : ℕ), 2 ≤ p → ∃ M0 : ℕ, ∀ n v : ℕ, M0 ≤ n → p ^ v ≤ n → (v + m) * L ≤ n := by
  first | exact @GlobalTheory.VSubArith.add_mul_le_of_pow_le | exact GlobalTheory.VSubArith.add_mul_le_of_pow_le | (intros; apply GlobalTheory.VSubArith.add_mul_le_of_pow_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveTwoCocycleCoeffRelationsOnePairStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveTwoCocycle_coeff_relations_one_pair : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R), cob2 (addLaw R d) c = 0 → ∀ m : Fin d, (∀ n, 0 < n → coeff (Finsupp.single (Sum.inl m) n) c = 0) ∧ ∀ i j l, 0 < i → 0 < j → 0 < l → coeff (Finsupp.single (Sum.inl m) (i + j) + Finsupp.single (Sum.inr m) l) c * ((i + j).choose i : R) = coeff (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (j + l)) c * ((j + l).choose j : R) := by
  first | exact @GlobalTheory.Katz.CocRel.relations | exact GlobalTheory.Katz.CocRel.relations | (intros; apply GlobalTheory.Katz.CocRel.relations <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrobeniusSemilinearEquationExistsUniqueStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (M : Matrix ι ι (Ainf p O)), IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) M → (∀ c : ι → Ainf p O, ∃ v : ι → Ainf p O, ∀ i, v i - M.mulVec (fun j => WittVector.frobenius (v j)) i = c i) ∧ ∀ v : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ v i - M.mulVec (fun j => WittVector.frobenius (v j)) i) → ∀ i, Sandwich.mu ε ∣ v i := by
  first | exact @GlobalTheory.WSolve.main | exact GlobalTheory.WSolve.main | (intros; apply GlobalTheory.WSolve.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChainStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfSquareZeroFrame_reflTransGen_cyclic_chain : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, Relation.ReflTransGen (fun N N' : Ideal F.B => IsStep p F.θ N' N) ⊤ (Ideal.span {(p : F.B)}) := by
  first | exact @GlobalTheory.BChain.reflTransGen_isStep | exact GlobalTheory.BChain.reflTransGen_isStep | (intros; apply GlobalTheory.BChain.reflTransGen_isStep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderiv
section
open Filter Topology

namespace GlobalTheory

open Filter Topology in
private lemma iteratedFDeriv_slice_eq_compContinuousLinearMap_inl {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (H : E × F → ℂ) {w : F}
    (hH : AnalyticAt ℂ H (0, w)) (k : ℕ) :
    iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 =
      (iteratedFDeriv ℂ k H (0, w)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inl ℂ E F) := by
  obtain ⟨U, hU, hUo, hwU⟩ := eventually_nhds_iff.1 hH.eventually_analyticAt
  set s : Set (E × F) := (fun q ↦ q + (0, w)) ⁻¹' U with hs
  have hso : IsOpen s := hUo.preimage (continuous_id.add continuous_const)
  have h0s : (0 : E × F) ∈ s := by simpa [hs] using hwU
  have hf : AnalyticOnNhd ℂ (fun q : E × F ↦ H (q + (0, w))) s := fun q hq ↦
    (hU _ hq).comp (f := fun q : E × F ↦ q + (0, w)) (analyticAt_id.add analyticAt_const)
  have hslice : (fun z : E ↦ H (z, w)) =
      (fun q : E × F ↦ H (q + (0, w))) ∘ ContinuousLinearMap.inl ℂ E F := by
    ext z; simp
  have hpre : IsOpen (ContinuousLinearMap.inl ℂ E F ⁻¹' s) :=
    hso.preimage (ContinuousLinearMap.continuous _)
  have h0s' : ContinuousLinearMap.inl ℂ E F 0 ∈ s := by rw [map_zero]; exact h0s
  have h0pre : (0 : E) ∈ ContinuousLinearMap.inl ℂ E F ⁻¹' s := h0s'
  rw [hslice, ← iteratedFDerivWithin_of_isOpen k hpre h0pre,
    ContinuousLinearMap.iteratedFDerivWithin_comp_right _ (hf.contDiffOn (n := k) hso.uniqueDiffOn)
      hso.uniqueDiffOn hpre.uniqueDiffOn h0s' le_rfl,
    iteratedFDerivWithin_of_isOpen k hso h0s', iteratedFDeriv_comp_add_right]
  simp

open Filter Topology in
private lemma fin_snoc_eq_cons_comp_finRotate {X : Type} {k : ℕ} (u : Fin k → X) (a : X) :
    (Fin.snoc u a : Fin (k + 1) → X) = Fin.cons a u ∘ finRotate (k + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp
  · simp

open Filter Topology in

theorem _root_.GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv :
    ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (H : E × F → ℂ) (w₀ : F) (k : ℕ) (v : Fin k → E), AnalyticAt ℂ H (0, w₀) → AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ ∧ ∀ e : F, fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ e = iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ H (z, w₀) (0, e)) 0 v := by
  intro E F _ _ _ _ _ _ H w₀ k v hH
  set u : Fin k → E × F := fun i ↦ (v i, 0) with hu
  have hev : ∀ᶠ w in 𝓝 w₀, AnalyticAt ℂ H (0, w) :=
    ((continuous_const.prodMk continuous_id).tendsto w₀).eventually hH.eventually_analyticAt
  have heq : (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) =ᶠ[𝓝 w₀]
      fun w ↦ iteratedFDeriv ℂ k H (0, w) u :=
    hev.mono fun w hw ↦ by dsimp only; rw [iteratedFDeriv_slice_eq_compContinuousLinearMap_inl H hw k]; rfl
  obtain ⟨U, hU, hUo, hwU⟩ := eventually_nhds_iff.1 hH.eventually_analyticAt
  have hiter : AnalyticAt ℂ (iteratedFDeriv ℂ k H) (0, w₀) :=
    (AnalyticOnNhd.iteratedFDeriv_of_isOpen hU hUo k) _ hwU
  have hA : AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k H (0, w) u) w₀ :=
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).analyticAt _).comp
      (hiter.comp (f := fun w : F ↦ ((0 : E), w)) (analyticAt_const.prod analyticAt_id))
  refine ⟨hA.congr heq.symm, fun e ↦ ?_⟩
  have hD : HasFDerivAt (fun w ↦ iteratedFDeriv ℂ k H (0, w) u)
      ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).comp
        ((fderiv ℂ (iteratedFDeriv ℂ k H) (0, w₀)).comp (ContinuousLinearMap.inr ℂ E F))) w₀ :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).hasFDerivAt.comp w₀
      (hiter.differentiableAt.hasFDerivAt.comp w₀ (hasFDerivAt_prodMk_right (0 : E) w₀))
  have hG : AnalyticAt ℂ (fun y ↦ fderiv ℂ H y (0, e)) (0, w₀) :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0 : E), e)).analyticAt _).comp hH.fderiv
  rw [heq.fderiv_eq, hD.fderiv, iteratedFDeriv_slice_eq_compContinuousLinearMap_inl _ hG k]
  have hcomp : (fun y ↦ fderiv ℂ H y (0, e)) =
      (ContinuousLinearMap.apply ℂ ℂ ((0 : E), e)) ∘ fderiv ℂ H := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ (hH.fderiv.contDiffAt (n := k)) le_rfl]
  have hperm := (hH.contDiffAt (n := ⊤)).iteratedFDeriv_comp_perm (Fin.cons ((0 : E), e) u)
    (finRotate (k + 1))
  rw [← fin_snoc_eq_cons_comp_finRotate, iteratedFDeriv_succ_apply_right,
    iteratedFDeriv_succ_apply_left] at hperm
  simpa [u] using hperm.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtlasSectionsMulDivNonvanishingIsOpenStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlasSections_mul_div_nonvanishing_isOpen : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), (∀ (la mu : La) (a b : ι → Y → ℂ), A.IsSec la a → A.IsSec mu b → A.IsSec (la + mu) (fun i y => a i y * b i y) ∧ ∀ y, A.nsq (la + mu) (fun i y => a i y * b i y) y = A.nsq la a y * A.nsq mu b y) ∧ (∀ (la : La) (a : ι → Y → ℂ), A.IsSec la a → IsOpen (nz A a)) ∧ (∀ (B la : La) (a b : ι → Y → ℂ) (U : Set Y), A.IsSec (B + la) a → A.IsSec B b → (∀ y ∈ U, a (A.pick y) y ≠ 0 ∧ b (A.pick y) y ≠ 0) → A.IsFrameOn la U (fun i y => a i y / b i y)) := by
  first | exact @GlobalTheory.OTY.sections_prod_quot_open | exact GlobalTheory.OTY.sections_prod_quot_open | (intros; apply GlobalTheory.OTY.sections_prod_quot_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BallExistsEtaleSteinExhaustionStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_exists_etaleStein_exhaustion : ∀ (n : ℕ) (c : V n) (r : ℝ), ∃ X : EtaleStein n (ball c r), X.z = Subtype.val := by
  first | exact @GlobalTheory.BallStein.ball_etaleStein | exact GlobalTheory.BallStein.ball_etaleStein | (intros; apply GlobalTheory.BallStein.ball_etaleStein <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIntegralClosureEtaleHeightOneStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_integralClosure_etale_height_one : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective f → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
      (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁)),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      (∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
        GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
        GlobalTheory.KeyOriginEnlarge.PointAtZero A₁ (Localization.AtPrime QA₁) DA₁ ρ₁) ∧
      (∀ (P₁ : Ideal (Localization.AtPrime QA₁)) [P₁.IsPrime], P₁.height ≤ 1 →
        GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (Localization.AtPrime QA₁) DA₁ P₁) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β := by
  first | (exact @GlobalTheory.KeyOriginBC.etale_bc) | (exact GlobalTheory.KeyOriginBC.etale_bc) | (intros; apply GlobalTheory.KeyOriginBC.etale_bc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamPeriodsLinear
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

open Opposite in

theorem periods_linear : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ x y q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ y q' → IsPer u.ex u.Λ (x + y) (q + q') ∧ IsPer u.ex u.Λ (x - y) (q - q')) ∧ ∀ (a : ℂ) x q, IsPer u.ex u.Λ x q → IsPer u.ex u.Λ (a • x) (a • q) := by
  intro A _ g L u
  have hO : ∀ U : A.left.Opens, IsOpen (pre u.ex U) := fun U ↦ (u.hol U 0).1
  have vadd : ∀ (U : A.left.Opens) (b b' : Γ(A.left, U)) z, val u.ex U (b + b') z = val u.ex U b z + val u.ex U b' z :=
    fun U b b' z ↦ valAt'_add _ _ _ _
  have vsub : ∀ (U : A.left.Opens) (b b' : Γ(A.left, U)) z, val u.ex U (b - b') z = val u.ex U b z - val u.ex U b' z :=
    fun U b b' z ↦ valAt'_sub _ _ _ _
  have vsmul : ∀ (U : A.left.Opens) (a : ℂ) (b : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (a • b) z = a * val u.ex U b z := by
    intro U a b z hz
    have e : (u.ex z).left ≫ str A = 𝟙 (Sp ℂ) := by
      rw [str, Category.comp_id]; exact Over.w (u.ex z)
    have k : valAt' (u.ex z).left U ((secMap (str A) U).hom a) = a :=
      (valAt'_appLE (u.ex z).left (str A) ⊤ U le_top _ hz).trans
        ((congrArg (fun p ↦ valAt' p ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) e).trans (valAt'_id_top a))
    exact (valAt'_mul (u.ex z).left U ((secMap (str A) U).hom a) b).trans (congrArg (· * val u.ex U b z) k)
  have dA : ∀ (k : A.left.affineOpens → (Fin g → ℂ) → ℂ) (U : A.left.affineOpens),
      DifferentiableOn ℂ (k U) (pre u.ex U.1) → ∀ z ∈ pre u.ex U.1, DifferentiableAt ℂ (k U) z :=
    fun k U hk z hz ↦ hk.differentiableAt ((hO _).mem_nhds hz)
  refine ⟨fun x y q q' hx hy ↦ ?_, fun a x q hx ↦ ?_⟩
  · obtain ⟨c, h, rfl, ⟨h1, h2, h3⟩, hp⟩ := hx
    obtain ⟨c', h', rfl, ⟨h1', h2', h3'⟩, hp'⟩ := hy
    constructor
    · refine ⟨c + c', fun U z ↦ h U z + h' U z, map_add _ _ _,
        ⟨fun U ↦ (h1 U).add (h1' U), fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
      · change h V z + h' V z = (h U z + h' U z) + val u.ex V.1 (c.1.1 (op U) (op V) f + c'.1.1 (op U) (op V) f) z
        refine Eq.trans ?_ (congrArg _ (vadd V.1 _ _ z).symm)
        rw [h2 U V f z hz, h2' U V f z hz]; ring
      · change fderiv ℂ (fun z ↦ h U z + h' U z) z = evForm u.ex U.1 z (c.1.2 (op U) + c'.1.2 (op U))
        rw [fderiv_fun_add (dA h U (h1 U) z hz) (dA h' U (h1' U) z hz), map_add, h3 U z hz, h3' U z hz]
      · simp only [Pi.add_apply]
        rw [hp U l z hz, hp' U l z hz]; ring
    · refine ⟨c - c', fun U z ↦ h U z - h' U z, map_sub _ _ _,
        ⟨fun U ↦ (h1 U).sub (h1' U), fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
      · change h V z - h' V z = (h U z - h' U z) + val u.ex V.1 (c.1.1 (op U) (op V) f - c'.1.1 (op U) (op V) f) z
        refine Eq.trans ?_ (congrArg _ (vsub V.1 _ _ z).symm)
        rw [h2 U V f z hz, h2' U V f z hz]; ring
      · change fderiv ℂ (fun z ↦ h U z - h' U z) z = evForm u.ex U.1 z (c.1.2 (op U) - c'.1.2 (op U))
        rw [fderiv_fun_sub (dA h U (h1 U) z hz) (dA h' U (h1' U) z hz), map_sub, h3 U z hz, h3' U z hz]
      · simp only [Pi.sub_apply]
        rw [hp U l z hz, hp' U l z hz]; ring
  · obtain ⟨c, h, rfl, ⟨h1, h2, h3⟩, hp⟩ := hx
    refine ⟨a • c, fun U z ↦ a * h U z, map_smul _ _ _,
      ⟨fun U ↦ (h1 U).const_mul a, fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
    · change a * h V z = a * h U z + val u.ex V.1 (a • c.1.1 (op U) (op V) f) z
      refine Eq.trans ?_ (congrArg _ (vsmul V.1 a _ z hz).symm)
      rw [h2 U V f z hz]; ring
    · change fderiv ℂ (fun z ↦ a * h U z) z = evForm u.ex U.1 z (a • c.1.2 (op U))
      rw [fderiv_const_mul (dA h U (h1 U) z hz), map_smul, h3 U z hz]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hp U l z hz]; ring

end GlobalTheory.CechPer
end

