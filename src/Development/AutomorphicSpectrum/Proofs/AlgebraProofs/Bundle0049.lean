import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0047
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0046
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0034
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0042
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0022

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NonFundamentalEigenLeSquareAugmentationStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_fundamental_eigen_le_square_augmentation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ χ : MulChar F R, ¬ IsFund p χ → eig AA.carrier χ ≤ sqIdeal (augIdeal AA.carrier) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation | exact GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation | (intros; apply GlobalTheory.CompanionTheory.Relay.non_fundamental_eigen_le_square_augmentation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NumericalSegreClosed
section
namespace GlobalTheory.CompanionTheory.Segre

theorem numericalSegre_closed : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.full

end GlobalTheory.CompanionTheory.Segre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegree
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.FieldNumbers

open GroundTheory.Heights₂.Heights.FieldNumbers GroundTheory.Heights₂.Heights.NumbersDVR

theorem projectionFormulaDegree :
    GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{0} :=
  ProjectionFormulaDegree.of_divPushForward
    (DivPushForward.proof ContractRelDimLe.proof DivPushForwardLocalZero)

end GlobalTheory.CompanionTheory.FieldNumbers
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientZarhinHodgeTateSubquotient
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem subquotientStatement_of_quotient_zarhin_hodgeTate
    (hQ : QuotientByFiniteFlatStatement) (hZ : ZarhinStatement) (hH : HodgeTateDatumStatement) :
    SubquotientStatement := by
  intro p _ C _ _ _ v R _ _ hv hp hc N _ M hM K
  obtain ⟨A, _, L, hA, hL, hamp, T, N', _, pt, hpt, i, π, hiπ, hst, rfl⟩ := hM
  classical
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : IsCommMonObj A := hA.comm
  haveI : Finite N' := GlobalTheory.T.torsion_points_finite R p A T N' pt hpt
  letI : Fintype N' := Fintype.ofFinite N'
  have hi : Function.Injective i := Function.LeftInverse.injective (g := π) hiπ
  haveI : Finite N := Finite.of_injective i hi
  letI : Fintype N := Fintype.ofFinite N
  obtain ⟨⟨AA, hAA⟩, -⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hv hp A T N' pt hpt
  have hgen := GlobalTheory.T.abelian_scheme_torsion_augmentation hQ hZ hH p C v R hv hp hc A L hA hL hamp T N' pt hpt (K.map i)
  have hret := GlobalTheory.T.hopf_order_retract_restriction p C v R hv hp N' AA N i π hiπ (by rw [hAA]; exact hst)
  rw [← hAA]
  exact hret.2.2 K (by rw [hAA]; exact hgen)

example : QuotientByFiniteFlatStatement → ZarhinStatement → HodgeTateDatumStatement →
    SubquotientStatement := subquotientStatement_of_quotient_zarhin_hodgeTate

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitCharactersUnramified
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc

open Module

theorem injective_of_charZero (E : Type) [Field E] [NumberField E] {L : Type} [Field L] [CharZero L]
    (g : 𝓞 E →+* L) : Function.Injective g := by
  refine (injective_iff_map_eq_zero g).2 fun x hx => ?_
  by_contra h
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := RingHom.ker g) h
    (RingHom.mem_ker.2 hx) (Algebra.IsIntegral.isIntegral x)
  apply hne
  rw [eq_bot_iff]
  intro n hn
  have h0 : g (algebraMap ℤ (𝓞 E) n) = 0 := RingHom.mem_ker.1 (Ideal.mem_comap.1 hn)
  have h1 : (n : L) = 0 := by simpa using h0
  simpa using h1

theorem det_sq_eq_discr (E : Type) [Field E] [NumberField E] (R S : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Fintype S] [DecidableEq S] (σ : S → (𝓞 E →+* R)) (hσ : Function.Injective σ)
    (hc : Fintype.card S = finrank ℚ E) (e : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ S) :
    (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).det ^ 2 = (NumberField.discr E : R) := by
  let F := FractionRing R
  let Ω := AlgebraicClosure F
  let i₀ : R →+* Ω := (algebraMap F Ω).comp (algebraMap R F)
  have hi₀ : Function.Injective i₀ :=
    (algebraMap F Ω).injective.comp (IsFractionRing.injective R F)
  have : CharZero Ω := charZero_of_injective_ringHom hi₀
  let ρ : S → (𝓞 E →+* Ω) := fun s => i₀.comp (σ s)
  have hρ : ∀ s, Function.Injective (ρ s) := fun s => injective_of_charZero E (ρ s)
  let τ : S → (E →ₐ[ℚ] Ω) := fun s => (IsFractionRing.lift (hρ s)).toRatAlgHom
  have hτ : ∀ s (a : 𝓞 E), τ s (algebraMap (𝓞 E) E a) = i₀ (σ s a) := fun s a => by
    change IsFractionRing.lift (hρ s) (algebraMap (𝓞 E) E a) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hinj : Function.Injective τ := by
    intro s t hst
    apply hσ
    ext a
    apply hi₀
    rw [← hτ, ← hτ, hst]
  have hbij : Function.Bijective τ :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by rw [AlgHom.card, hc]⟩
  let e' : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] Ω) := e.trans (Equiv.ofBijective τ hbij)
  have key := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω (integralBasis E) e'
  rw [← coe_discr] at key
  have hm : Algebra.embeddingsMatrixReindex ℚ Ω (integralBasis E) e' =
      (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).map i₀ := by
    ext i j
    simp only [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.of_apply, Matrix.map_apply, integralBasis_apply]
    exact hτ _ _
  rw [hm, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_pow] at key
  apply hi₀
  rw [← key]
  simp

theorem isSplit_of_det {O k S ι : Type} [CommRing O] [Field k] [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι]
    (χ : S → (O →+* k)) (b : Basis ι ℤ O) (e : ι ≃ S)
    (h : (Matrix.of fun i j => χ (e j) (b i)).det ≠ 0) : IsSplit χ := by
  unfold IsSplit
  let B := Algebra.TensorProduct.basis k b
  let B' := (Pi.basisFun k S).reindex e.symm
  let f := (Algebra.TensorProduct.lift (Algebra.ofId k (S → k)) (AlgHom.pi fun s => (χ s).toIntAlgHom)
    (fun _ _ => Commute.all _ _))
  have hm : LinearMap.toMatrix B B' f.toLinearMap = (Matrix.of fun i j => χ (e j) (b i)).transpose := by
    ext i j
    simp [LinearMap.toMatrix_apply, B, B', f]
  have hu : IsUnit (LinearMap.toMatrix B B' f.toLinearMap).det := by
    rw [hm, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 h
  exact (LinearEquiv.ofIsUnitDet hu).bijective

theorem exists_isSplit (E : Type) [Field E] [NumberField E] (R K S : Type) [CommRing R] [IsDomain R] [CharZero R]
    [Field K] [Fintype S] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K] (σ : S → (𝓞 E →+* R)) (π : R →+* K)
    (hσ : Function.Injective σ) (hc : Fintype.card S = finrank ℚ E) (hp : ¬ (p : ℤ) ∣ NumberField.discr E) :
    ∃ χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K), IsSplit χ ∧
      ∀ s a, ((χ s a : algebraicClosure (ZMod p) K) : K) = π (σ s a) := by
  classical
  have hchar : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hmem : ∀ s a, (π.comp (σ s)) a ∈ algebraicClosure (ZMod p) K := fun s a => by
    have h1 : IsIntegral ℤ ((π.comp (σ s)) a) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (π.comp (σ s)).toIntAlgHom
    exact mem_algebraicClosure_iff'.2 (h1.tower_top)
  let χ : S → (𝓞 E →+* algebraicClosure (ZMod p) K) := fun s =>
    (π.comp (σ s)).codRestrict (algebraicClosure (ZMod p) K) (hmem s)
  refine ⟨χ, ?_, fun s a => rfl⟩
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card S := by
    rw [hc, finrank_eq_card_basis (integralBasis E)]
  let e : Free.ChooseBasisIndex ℤ (𝓞 E) ≃ S := Fintype.equivOfCardEq hcard
  refine isSplit_of_det χ (RingOfIntegers.basis E) e fun h0 => hp ?_
  have hsq := congrArg π (det_sq_eq_discr E R S σ hσ hc e)
  have hmap : (algebraMap (algebraicClosure (ZMod p) K) K).mapMatrix
      (Matrix.of fun i j => χ (e j) (RingOfIntegers.basis E i)) =
      π.mapMatrix (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)) := by
    ext i j
    rfl
  have hdet : π (Matrix.of fun i j => σ (e j) (RingOfIntegers.basis E i)).det = 0 := by
    rw [RingHom.map_det, ← hmap, ← RingHom.map_det]
    simp [h0]
  rw [map_pow, hdet] at hsq
  have hz : ((NumberField.discr E : ℤ) : K) = 0 := by
    simpa using hsq.symm
  exact (CharP.intCast_eq_zero_iff K p _).1 hz

end GlobalTheory.CompanionTheory.Ar.Conj.SplitDisc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisColength
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_colength : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) := by
  first | exact @PositivityTheory.HtPt.Rd.gr_partial | exact PositivityTheory.HtPt.Rd.gr_partial
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderBasisLengths
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.stable_hopf_order_basis_lengths : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r := by
  first | exact @PositivityTheory.HtPt.Rd.flag_om | exact PositivityTheory.HtPt.Rd.flag_om
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TrivialFlagAtPrime
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.TrivFlagAtRelay

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (b : Fin N → K → ℤ), TrivFlagMod O ϖ x N b → ∀ (W : Ideal (MRing ι O)), IsMultiProjPrime W → (pointIdeal O x) ≤ W → (C ϖ : MRing ι O) ∈ W → TrivFlagAt W b :=
  @PositivityTheory.Xgn.t_trivflagmod_at

end GlobalTheory.CompanionTheory.Ar.Num.TrivFlagAtRelay
end

