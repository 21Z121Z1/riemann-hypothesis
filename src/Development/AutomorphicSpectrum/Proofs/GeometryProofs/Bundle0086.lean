import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0017
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0018
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0082
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPairingTorsionFree
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem gram_invertible_of_unramified : ∀ (E : Type) [Field E] [NumberField E] (cc : E ≃+* E) (p R N : ℕ) [Fact p.Prime], 1 ≤ R → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)), (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv cc a • y)) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → ∀ (O Ω : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ¬ IsUnit (p : O) → ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) → ∃ C : Matrix (Fin N) (Fin N) Ω, (∀ i j, C i j ∈ (algebraMap O Ω).range) ∧ (Matrix.of fun i j => ∑ k, σ (HT.dualInt E k) * ((e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : Ω)) * C = 1 :=
  @PositivityTheory.Xgn.gram_determinant_unit_mod_p

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralPointsEqOfGeneric
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem coordTie_points_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B Ω], Function.Injective (algebraMap B Ω) → (∀ c', x c' / x c ∈ (algebraMap B Ω).range) → ∀ z z' : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z = ξ → Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z' = ξ → z = z' :=
  @PositivityTheory.Xgn.same_generic_point_charts

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerAtOneCompEndo
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem isDerAtOne_comp_endo : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (i : Γ.G.left ⟶ G.left) (N : ℕ), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (B : L →ₗ[R] L), M.IsDiffOf a B → ∀ (α : T →* T), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → ∀ (f : T → R) (w : Module.Dual R L), Γ.IsDerAtOne i M N f w → Γ.IsDerAtOne i M N (fun t => f (α t)) (w ∘ₗ B) :=
  @PositivityTheory.Xgn.isDerAtOne_comp_of_isDiffOf

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOfSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Nonempty (Module.Basis (Fin g) R E) := by
  first | exact @PositivityTheory.UnitarySelfGeneration.lie_free | exact PositivityTheory.UnitarySelfGeneration.lie_free
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleSectionDivisible
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue

theorem sc_res {R : Type} [CommRing R] {X : Scheme.{0}} (π : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (d : R) :
    (X.presheaf.map (homOfLE h).op).hom (sc π U d) = sc π V d := by
  have e := Scheme.Hom.appLE_map π (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op
  simp only [sc, RingHom.comp_apply]
  exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) e

theorem sc_ne_zero {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (π : X ⟶ Sp R) {V : X.Opens}
    [Nonempty V] {d : R} (hd : sc π ⊤ d ≠ 0) : sc π V d ≠ 0 := by
  intro h
  apply hd
  have hi := map_injective_of_isIntegral X (homOfLE (le_top : V ≤ ⊤))
  apply hi
  have := sc_res π (le_top : V ≤ ⊤) d
  rw [map_zero]
  exact this.trans h

theorem sc_cancel {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (π : X ⟶ Sp R) (V : X.Opens)
    {d : R} (hd : sc π ⊤ d ≠ 0) {a b : Γ(X, V)} (h : sc π V d * a = sc π V d * b) : a = b := by
  by_cases hV : Nonempty V
  · exact mul_left_cancel₀ (sc_ne_zero π hd) h
  · have : V = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hV ⟨⟨x, hx⟩⟩
    subst this
    exact Subsingleton.elim _ _

theorem exists_div {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (π : X ⟶ Sp R) (V : X.Opens)
    {d : R} (hd : sc π ⊤ d ≠ 0) (x : Γ(X, V))
    (h : ∀ (W : X.Opens) (hW : W ≤ V), IsAffineOpen W →
      ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom x = sc π W d * a) :
    ∃ y : Γ(X, V), x = sc π V d * y := by
  let I := {W : X.affineOpens // (W : X.Opens) ≤ V}
  let U : I → X.Opens := fun i => (i.1 : X.Opens)
  choose g hg using fun i : I => h (U i) i.2 i.1.2
  have hcover : V ≤ iSup U := by
    intro y hy
    obtain ⟨W, hW, hyW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWV⟩, hyW⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U g := by
    intro i j
    show (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (g i) =
      (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (g j)
    apply sc_cancel π _ hd
    have e1 := congrArg (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (hg i)
    have e2 := congrArg (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (hg j)
    rw [map_mul, sc_res, ← CommRingCat.comp_apply, ← Functor.map_comp] at e1 e2
    exact e1.symm.trans e2
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U V (fun i => homOfLE i.2) hcover g hcompat
  refine ⟨s, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf U V (fun i => homOfLE i.2) hcover
  intro i
  show (X.presheaf.map (homOfLE i.2).op).hom x = (X.presheaf.map (homOfLE i.2).op).hom (sc π V d * (show Γ(X, V) from s))
  rw [hg i, map_mul, sc_res]
  exact congrArg _ (hs i).symm

theorem exists_sec_of_local {X : Scheme.{0}} [IsIntegral X] (R : Type) [CommRing R] (π : X ⟶ Sp R) (M : LB X)
    (s : LB.Sec M) (δ : R) (hδ : sc π ⊤ δ ≠ 0)
    (h : ∀ i (W : X.Opens) (hW : W ≤ M.U i), IsAffineOpen W →
      ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom (s.f i) = sc π W δ * a) :
    ∃ s' : LB.Sec M, ∀ i, s.f i = sc π (M.U i) δ * s'.f i := by
  choose y hy using fun i => exists_div π (M.U i) hδ (s.f i) (h i)
  refine ⟨⟨y, fun i j => ?_⟩, hy⟩
  apply sc_cancel π _ hδ
  have e := s.compat i j
  rw [hy i, hy j, map_mul, map_mul, sc_res, sc_res] at e
  rw [e]
  ring

theorem sec_eq_smul_of_local : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (π : X ⟶ Sp R) (M : LB X) (s : LB.Sec M) (δ : R), sc π ⊤ δ ≠ 0 → (∀ i (W : X.Opens) (hW : W ≤ M.U i), IsAffineOpen W → ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom (s.f i) = sc π W δ * a) → ∃ s' : LB.Sec M, ∀ i, s.f i = sc π (M.U i) δ * s'.f i := by
  intro X _ R _ π M s δ hδ h
  exact exists_sec_of_local R π M s δ hδ h

end GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalizationsEqualBasicOpensStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localizations_equal_basic_opens : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A B : Subalgebra ℚ Ω) (q : Ideal A) (q' : Ideal B) (R : Subring Ω), A.FG → B.FG → q.IsPrime → q'.IsPrime → IsLocAt A q R → IsLocAt B q' R → ∃ (g : A) (h : B), g ∉ q ∧ h ∉ q' ∧ Mdl.invAdj A g = Mdl.invAdj B h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.CommonLoc.exists_common_loc | exact GlobalTheory.CompanionTheory.Ar.SncBase.CommonLoc.exists_common_loc | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.CommonLoc.exists_common_loc <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentIntegralClosure
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.ModelDescentAlt

noncomputable section

open GroundTheory.Heights₂.Heights.NumbersDVR (classList classNum cycEval ratDiv IsVerticalDivisor pairNum psumExpansion isHomogeneous_psumExpansion)

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
  {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)]

def Scales (P : Ideal (MvPolynomial (Σ k, J k) O)) (P' : Ideal (MvPolynomial (Σ k, J k) O')) (d e : ℕ) : Prop :=
  ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P →
    ∀ l : List (K → ℤ), l.length = d →
      cycList (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P' (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) l

theorem support_divCycle_finite {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (P : Ideal (MvPolynomial (Σ k, J k) R))
    (f : MvPolynomial (Σ k, J k) R) : (Function.support (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f)).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  simp [GroundTheory.Heights₂.Heights.NumbersDVR.divCycle, h]

theorem length_classList {σ : Type} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) {m : ℕ} {H : MvPolynomial σ ℝ}
    (hH : H.IsHomogeneous m) (hμ : μ ∈ H.support) : (classList cls μ).length = m := by
  have h := hH (mem_support_iff.mp hμ)
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  rw [← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem cycNum_scale {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ} (hs : Scales P P' d e)
    {a : K → ℕ} {f : MvPolynomial (Σ k, J k) O} (hf : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a) (hfP : f ∉ P)
    {σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {m : ℕ} (hH : H.IsHomogeneous m)
    (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    cycNum (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P' (MvPolynomial.map (algebraMap O O') f)) cls H Q =
      e * cycNum (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) cls H Q := by
  unfold cycNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [hs a f hf hfP _ (by rw [List.length_append, length_classList cls μ hH hμ, hQ])]
  push_cast
  ring

theorem cycEval_scale {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ} (hs : Scales P P' d e)
    {a : K → ℕ} {f : MvPolynomial (Σ k, J k) O} (hf : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a) (hfP : f ∉ P)
    {σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {m : ℕ} (hH : H.IsHomogeneous m)
    (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    cycEval (fun W => classNum cls H Q W) (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P' (MvPolynomial.map (algebraMap O O') f)) =
      e * cycEval (fun W => classNum cls H Q W) (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) := by
  have h1 := (cycNum_int_and_comb O K J σ cls Q).1 (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) (support_divCycle_finite P f) H
  have h2 := (cycNum_int_and_comb O' K J σ cls Q).1 _
    (support_divCycle_finite P' (MvPolynomial.map (algebraMap O O') f)) H
  have hH' : (MvPolynomial.map (Int.castRingHom ℝ) H).IsHomogeneous m := hH.map _
  have h3 := cycNum_scale hs hf hfP cls hH' Q hQ
  rw [h1, h2] at h3
  exact_mod_cast h3

theorem cycEval_ratDiv {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (n : Ideal (MvPolynomial (Σ k, J k) R) → ℤ) (P : Ideal (MvPolynomial (Σ k, J k) R)) (f g : MvPolynomial (Σ k, J k) R) :
    cycEval n (ratDiv P f g) = cycEval n (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f) - cycEval n (GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P g) := by
  unfold cycEval ratDiv
  simp only [sub_mul]
  refine finsum_sub_distrib ?_ ?_
  · exact (support_divCycle_finite P f).subset fun W hW h => hW (by simp [show GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P f W = 0 from h])
  · exact (support_divCycle_finite P g).subset fun W hW h => hW (by simp [show GroundTheory.Heights₂.Heights.NumbersDVR.divCycle P g W = 0 from h])

theorem ck_scale {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ} (hs : Scales P P' d e) {ϖ : O}
    {r : ℕ} (T : LocPair J O (Fin r)) (hT : T.IsVert P ϖ) {k : ℕ} (hk : 1 ≤ k) (Q : List (K → ℤ))
    (hQ : Q.length + k = d + 1) :
    (T.map (algebraMap O O')).ck P' k Q = e * T.ck P k Q := by
  unfold LocPair.ck pairNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨bf, bg, hf, hg, -⟩, hfP, hgP, -, -⟩ := hT i
  have hm : k - 1 + Q.length = d := by omega
  have hH := isHomogeneous_psumExpansion r k i
  show cycEval _ (ratDiv P' (MvPolynomial.map (algebraMap O O') (T.f i))
    (MvPolynomial.map (algebraMap O O') (T.g i))) = _
  rw [cycEval_ratDiv, cycEval_ratDiv, mul_sub]
  exact congrArg₂ _ (cycEval_scale hs hf hfP _ hH Q hm) (cycEval_scale hs hg hgP _ hH Q hm)

theorem laNum_scale {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ} (hs : Scales P P' d e)
    {p : ℕ} (hp : (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ P) {r : ℕ} (x : Fin r → K → ℤ) {k : ℕ} (hk : 1 ≤ k)
    (Q : List (K → ℤ)) (hQ : Q.length + k = d + 1) :
    laNum P' (p : O') x k Q = e * laNum P (p : O) x k Q := by
  unfold laNum
  have hc : (C (p : O') : MvPolynomial (Σ k, J k) O') = MvPolynomial.map (algebraMap O O') (C (p : O)) := by simp
  have hH : (MvPolynomial.psum (Fin r) ℤ (k - 1)).IsHomogeneous (k - 1) := by
    unfold MvPolynomial.psum
    exact IsHomogeneous.sum _ _ _ fun i _ => by simpa using (isHomogeneous_X ℤ i).pow (k - 1)
  have hC : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (C (p : O) : MvPolynomial (Σ k, J k) O) (0 : K → ℕ) :=
    isWeightedHomogeneous_C _ _
  rw [hc, cycEval_scale hs hC hp x hH Q (by omega)]
  ring

theorem isHomogeneous_liePs {Ψ : Type} {N : ℕ} (j m : ℕ) (τ : Ψ ⊕ Ψ) :
    (liePs (N := N) j m τ : MvPolynomial (Ψ × Fin N) ℝ).IsHomogeneous m := by
  rcases τ with τ | τ
  · exact IsHomogeneous.sum _ _ _ fun i _ => by simpa using (isHomogeneous_X ℝ (τ, i)).pow m
  · exact IsHomogeneous.sum _ _ _ fun i _ => by simpa using ((isHomogeneous_X ℝ (τ, i)).neg).pow m

theorem isHomogeneous_bracket {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ))
    (p k : ℕ) (τ : Ψ) : (bracket (N := N) j φ p k τ).IsHomogeneous (k - 1) := by
  unfold bracket
  have h : (∑ τ', C (GroundTheory.Heights₂.Heights.ModelLeaves.co φ p k (Sum.inl τ) τ') *
      (liePs (N := N) j (k - 1) τ' : MvPolynomial (Ψ × Fin N) ℝ)).IsHomogeneous (k - 1) :=
    IsHomogeneous.sum _ _ _ fun τ' _ => by
      simpa using (isHomogeneous_C _ _).mul (isHomogeneous_liePs j (k - 1) τ')
  have h2 := (isHomogeneous_C (Ψ × Fin N) (k : ℝ)).mul h
  rwa [zero_add] at h2

end

end GlobalTheory.CompanionTheory.Ar.Num.ModelDescentAlt

namespace GlobalTheory.CompanionTheory.Ar.Num.ModelDescentAlt

noncomputable section

open GroundTheory.Heights₂.Heights.NumbersDVR (classList classNum cycEval ratDiv IsVerticalDivisor pairNum psumExpansion isHomogeneous_psumExpansion)

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
  {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)]

theorem flag_descends {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ}
    (hs : Scales P P' d e) (he : 0 < e) {ϖ : O} {p : ℕ} (hp : (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ P)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ))
    (T : LocPair J O (Ψ × Fin N)) (hT : T.IsVert P ϖ)
    (h : FlagChernComparison P' d p j φ (T.map (algebraMap O O'))) : FlagChernComparison P d p j φ T := by
  intro τ k hk Q hQ
  have h0 := h τ k hk Q hQ
  have e1 : ((T.map (algebraMap O O')).comp fun i : Fin N => (τ, i)) =
      (T.comp fun i : Fin N => (τ, i)).map (algebraMap O O') := rfl
  have hTc : (T.comp fun i : Fin N => (τ, i)).IsVert P ϖ := fun i => hT (τ, i)
  have hc : (C (p : O') : MvPolynomial (Σ k, J k) O') = MvPolynomial.map (algebraMap O O') (C (p : O)) := by simp
  have hC : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (C (p : O) : MvPolynomial (Σ k, J k) O) (0 : K → ℕ) :=
    isWeightedHomogeneous_C _ _
  rw [e1, ck_scale hs _ hTc hk Q hQ, show (T.map (algebraMap O O')).x = T.x from rfl, hc,
    cycNum_scale hs hC hp T.x (isHomogeneous_bracket j φ p k τ) Q (by omega)] at h0
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  push_cast at h0
  exact mul_left_cancel₀ he' h0

theorem whole_descends {P : Ideal (MvPolynomial (Σ k, J k) O)} {P' : Ideal (MvPolynomial (Σ k, J k) O')} {d e : ℕ}
    (hs : Scales P P' d e) (he : 0 < e) {ϖ : O} {p : ℕ}
    (hp : p ≠ 0 → (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ P) {r s : ℕ}
    (lie : LocPair J O (Fin r)) (om : LocPair J O (Fin s)) (hl : lie.IsVert P ϖ) (ho : om.IsVert P ϖ)
    (h : BundleChernComparison P' d p (lie.map (algebraMap O O')) (om.map (algebraMap O O'))) : BundleChernComparison P d p lie om := by
  intro k hk Q hQ
  have h0 := h k hk Q hQ
  have he' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  rw [ck_scale hs _ hl hk Q hQ, ck_scale hs _ ho hk Q hQ] at h0
  by_cases hp0 : p = 0
  · subst hp0
    have hz : (1 / (((0 : ℕ) : ℝ) ^ k - 1) - 1 / (((0 : ℕ) : ℝ) - 1)) = 0 := by
      have : k ≠ 0 := by omega
      simp [this]
    rw [hz, zero_mul] at h0 ⊢
    push_cast at h0
    have h1 : (e : ℝ) * (((lie.ck P k Q : ℤ) : ℝ) + ((om.ck P k Q : ℤ) : ℝ)) = 0 := by linarith
    exact (mul_eq_zero.1 h1).resolve_left he'
  · rw [show (lie.map (algebraMap O O')).x = lie.x from rfl, laNum_scale hs (hp hp0) lie.x hk Q hQ] at h0
    push_cast at h0
    refine mul_left_cancel₀ he' ?_
    linarith

end

end GlobalTheory.CompanionTheory.Ar.Num.ModelDescentAlt

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem model_descends_from_dvr_ext : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → ∀ (ϖ : O), Irreducible ϖ → ∀ p : ℕ, (p ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair J O (Ψ × Fin N)), T.IsVert (pointIdeal O y) ϖ → FlagChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p j φ (T.map (algebraMap O O')) → FlagChernComparison (pointIdeal O y) d p j φ T) ∧ ∀ (r s : ℕ) (lie : LocPair J O (Fin r)) (om : LocPair J O (Fin s)), lie.IsVert (pointIdeal O y) ϖ → om.IsVert (pointIdeal O y) ϖ → BundleChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p (lie.map (algebraMap O O')) (om.map (algebraMap O O')) → BundleChernComparison (pointIdeal O y) d p lie om := by
  intro O _ _ _ Ω _ _ _ K _ _ J _ y d hM hI O' _ _ _ _ _ _ Ω' _ _ _ _ _ _ hinj ϖ hϖ p
  obtain ⟨hEq, hM'⟩ := GlobalTheory.T.model_over_dvr_extension O Ω K J y d hM hI O' Ω' hinj
  have hCmem : ∀ a : O, (C a : MvPolynomial (Σ k, J k) O) ∈ pointIdeal O y → a = 0 := fun a ha => by
    have h' : a ∈ (pointIdeal O y).comap (C : O →+* MvPolynomial (Σ k, J k) O) := ha
    rw [hM.noTorsion] at h'
    simpa using h'
  have hΩ : Function.Injective (algebraMap O Ω) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => hCmem a ?_
    show GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap O y (C a) = 0
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap, ha]
  have hOO : Function.Injective (algebraMap O O') := by
    have h2 : Function.Injective (algebraMap O' Ω' ∘ algebraMap O O') := by
      have e : (algebraMap O' Ω' ∘ algebraMap O O' : O → Ω') = algebraMap Ω Ω' ∘ algebraMap O Ω := by
        funext a
        simp only [Function.comp]
        rw [← IsScalarTower.algebraMap_apply O O' Ω', ← IsScalarTower.algebraMap_apply O Ω Ω']
      rw [e]
      exact (algebraMap Ω Ω').injective.comp hΩ
    exact h2.of_comp
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hne : algebraMap O O' ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hOO (by simpa using h0))
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hϖ'
  have hrel : algebraMap O O' ϖ = ((u⁻¹ : O'ˣ) : O') * ϖ' ^ e := by
    rw [← hu]
    simp [mul_comm]
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · exfalso
      have hU : IsUnit (algebraMap O O' ϖ) := by
        rw [hrel]
        simp
      exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap O O') ϖ).1 hU)
    · exact h
  have hs : ModelDescentAlt.Scales (pointIdeal O y) ((pointIdeal O y).map (MvPolynomial.map (algebraMap O O'))) d e :=
    fun a f hf hfP l hl => GlobalTheory.T.model_over_ramified_extension O O' ϖ ϖ' u⁻¹ e hϖ hϖ' he hrel K J (pointIdeal O y) d hM (hEq ▸ hM') a f hf hfP l hl
  have hp : p ≠ 0 → (C (p : O) : MvPolynomial (Σ k, J k) O) ∉ pointIdeal O y := fun h0 hmem => by
    have h1 := hCmem _ hmem
    have h2 : ((p : ℕ) : Ω) = 0 := by
      have := congrArg (algebraMap O Ω) h1
      simpa using this
    exact h0 (by exact_mod_cast h2)
  rw [hEq]
  exact ⟨fun h0 Ψ _ _ N j φ T hT h => ModelDescentAlt.flag_descends hs he (hp h0) j φ T hT h,
    fun r s lie om hl ho h => ModelDescentAlt.whole_descends hs he hp lie om hl ho h⟩

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ObjMapComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem objMap_exists_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (S' S'' : Scheme.{0}) (s' : S' ⟶ Sp B) (s'' : S'' ⟶ Sp B) (o : Obj D l b s) (o' : Obj D l b s') (o'' : Obj D l b s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f) (m' : ObjMap o'' o' f'), ∃ n : ObjMap o'' o (f' ≫ f), n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  intro E _ _ _ H D l B _ b S s S' S'' s' s'' o o' o'' f f' m m'
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H S S' S'' o.t o'.t o''.t f f' m.toSABMap m'.toSABMap
  have hn' : n.cm.F = m'.cm.F ≫ m.cm.F := hn
  refine ⟨{ toSABMap := n, eta := fun x => ?_, etaA := fun x => ?_ }, hn⟩
  · rw [hn', ← Category.assoc, m'.eta, Category.assoc, m.eta, Category.assoc]
  · rw [hn', ← Category.assoc, m'.etaA, Category.assoc, m.etaA, Category.assoc]

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeDivisorsOfOmegaBundleStatement
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_divisors_of_omega_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx), Or.𝔐.OmVB → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → AlgOver (Or.Re.comap some) → ∃ T : HodgeTie Y S (Module.finrank ℚ c.F) RM, T.A = Or.𝔐 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.hodgeTie_of_rootOrigin | exact GlobalTheory.CompanionTheory.Ar.hodgeTie_of_rootOrigin | (intros; apply GlobalTheory.CompanionTheory.Ar.hodgeTie_of_rootOrigin <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothAdjoinInverseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_adjoin_inverse : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 → Algebra.Smooth ℚ A → Algebra.Smooth ℚ (Mdl.invAdj A g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.smooth_invAdj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelFromLocalPatchesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_model_from_local_patches : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (B : Set (Cpt ξ)) (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1)))), (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → ∃ h ∈ Mdl.chartQ x c, unitAt ξ p h ∧ ∃ (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (n : ℕ), IsSncPatch (Pts ξ) (regAt ξ '' B) e (Mdl.invAdj (Mdl.chartQ x c) h) z n) → (∀ c, x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ ∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) → (∀ c h, x c ≠ 0 → h ∈ Mdl.chartQ x c → h ≠ 0 → ∀ q : Ideal (Mdl.invAdj (Mdl.chartQ x c) h), q.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.invAdj (Mdl.chartQ x c) h, s ∉ q ↔ unitAt ξ p (s : Ω)) ∧ ∀ (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (n : ℕ), IsSncPatch (Pts ξ) (regAt ξ '' B) e (Mdl.invAdj (Mdl.chartQ x c) h) z n → (p ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)) → (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → (p ∈ B ↔ ∀ g ∈ bd, ¬ unitAt ξ p (Mdl.ratEval x c g))) → Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.isSncModel_of_chart_patches | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.isSncModel_of_chart_patches | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.isSncModel_of_chart_patches <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPatchBoundaryUnitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_patch_boundary_units : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ) (B : Set (Cpt ξ)) (h : Ω) (e n : ℕ) (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (p : Cpt ξ), IsCptGen ξ → (∀ q ∈ B, Char0 ξ q) → h ∈ Mdl.chartQ x c → h ≠ 0 → (∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → unitAt ξ q h → (q ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ ¬ unitAt ξ q (z i : Ω))) → Char0 ξ p → InChart ξ x c p → unitAt ξ p h → p ∉ B → ∃ a ∈ Mdl.chartQ x c, unitAt ξ p a ∧ ∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_chartQ_unit_sep | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_chartQ_unit_sep | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_chartQ_unit_sep <;> assumption)
end

