import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.AppendIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SmoothDivisorReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.Bundle0001
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LevelwiseIso
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem strictTransform_top_eq_top {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    Blowup.strictTransform f Z ⊤ = ⊤ := by
  have h := comap_le_strictTransform f Z (⊤ : X.IdealSheafData)
  have h2 : (⊤ : X'.IdealSheafData) ≤ Blowup.strictTransform f Z ⊤ := by
    refine le_trans ?_ h
    simp
  exact top_le_iff.mp h2

theorem BlowupSequenceData.iteratedStrictTransform_top {X : Scheme.{u}} (d : BlowupSequenceData X) (i : ℕ) :
    d.iteratedStrictTransform i ⊤ = ⊤ := by
  induction i with
  | zero =>
      rw [BlowupSequenceData.iteratedStrictTransform_zero]
      simp
  | succ i ih =>
      rw [BlowupSequenceData.iteratedStrictTransform_succ, ih, strictTransform_top_eq_top]

structure BlowupSequenceData.LevelwiseIso {X : Scheme.{u}} (s₁ s₂ : BlowupSequenceData X) where
  iso : ∀ i : ℕ, i ≤ s₁.length → (s₁.obj i ≅ s₂.obj i)
  length_eq : s₁.length = s₂.length
  zero_compat : (iso 0 (Nat.zero_le _)).hom ≫ s₂.isoZero.hom = s₁.isoZero.hom
  map_compat : ∀ (i : ℕ) (hi : i < s₁.length),
    (iso (i + 1) hi).hom ≫ s₂.map i = s₁.map i ≫ (iso i hi.le).hom
  center_compat : ∀ (i : ℕ) (hi : i < s₁.length),
    (s₂.center i).comap (iso i hi.le).hom = s₁.center i

structure BlowupSequenceData.LevelwiseIsoOver {Y₁ Y₂ : Scheme.{u}} (φ : Y₁ ≅ Y₂)
    (t₁ : BlowupSequenceData Y₁) (t₂ : BlowupSequenceData Y₂) where
  iso : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i)
  length_eq : t₁.length = t₂.length
  zero_compat : (iso 0 (Nat.zero_le _)).hom ≫ t₂.isoZero.hom = t₁.isoZero.hom ≫ φ.hom
  map_compat : ∀ (i : ℕ) (hi : i < t₁.length),
    (iso (i + 1) hi).hom ≫ t₂.map i = t₁.map i ≫ (iso i hi.le).hom
  center_compat : ∀ (i : ℕ) (hi : i < t₁.length),
    (t₂.center i).comap (iso i hi.le).hom = t₁.center i

private theorem nontrivialPart_nil {X : Scheme.{u}} :
    MarkedIdealWithBoundary.nontrivialPart ([] : List X.IdealSheafData) = [] := rfl

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactOrderReduction
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactFunctoriality

theorem isOrderReduction_maxContact_of_descentHypotheses
    (hinv : ComapIsoInvariance.{u}) (P Q : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (L L' : PrincipalizationAssignment.{u})
    (hdimlink : ∀ a b : ℕ, a < b → P b → Q a)
    (hlow : IsMaxOrderReduction Q L L')
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) L)
    (hstar : CoverSequenceProperties hinv P A)
    (hdes : DescentHypotheses hinv P A L) :
    IsOrderReduction P (maxContactPrincipalization hinv A) L := by
  refine
    { cert := ?_, base_change := ?_, base_change_strict := ?_, pushforward := ?_,
      order_le := ?_, center_nonempty := ?_, resolves := ?_, smooth_pullback := ?_,
      smooth_pullback_strict := ?_, trivial_of_coSupport_empty := ?_ }
  · intro T hv hdim hO i hi
    exact orderCertificate_of_orderAt_le_mult hinv P A L hstar hdes T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) i hi
  · intro T hv hdim hO K _ _ f E' hBE hV' hP' hO'
    have hord : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
        orderAt ((T.baseChange K f).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.baseChange K f).withBoundary E')).mp hO' x
      rwa [MarkedIdealWithBoundary.withBoundary_mult, MarkedIdealWithBoundary.baseChange_mult] at h
    exact hdes.base_change T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) K f E' hBE hV'
      hP' hord
  · intro T hv hdim hO K _ _ f E' hBE hV' hP' hO'
    have hord : ∀ x : ↥((T.baseChange K f).withBoundary E').scheme,
        orderAt ((T.baseChange K f).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.baseChange K f).withBoundary E')).mp hO' x
      rwa [MarkedIdealWithBoundary.withBoundary_mult, MarkedIdealWithBoundary.baseChange_mult] at h
    exact hdes.base_change_strict T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) K f E' hBE
      hV' hP' hord
  · intro T hv hdim hO hbdry hmult Y q e _ hq hsm J hJv hJd hJi
    exact isPushforward_of_isSmoothDivisor hinv P Q A L L' hstar hdes hdiv hlow hdimlink T hv hdim hO
      hbdry hmult Y q e hq hsm J hJv hJd hJi
  · intro T hv hdim hO i hi x
    exact orderAt_ideal_le_mult hinv P A L hdes T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) i hi x
  · intro T hv hdim hO i hi
    exact center_support_nonempty hinv P A L hstar hdes T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) i hi
  · intro T hv hdim hO
    exact isResolution_of_orderAt_le_mult hinv P A L hstar hdes T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO)
  · intro T hv hdim hO Y q g _ hq E' hBE hV' hP' hO'
    have hm : ((T.pullbackAlong Y q g).withBoundary E').mult = T.mult :=
      (MarkedIdealWithBoundary.withBoundary_mult (T.pullbackAlong Y q g) E').trans
        (T.pullbackAlong_mult Y q g)
    have hord : ∀ x : ↥((T.pullbackAlong Y q g).withBoundary E').scheme,
        orderAt ((T.pullbackAlong Y q g).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.pullbackAlong Y q g).withBoundary E')).mp hO' x
      rwa [hm] at h
    exact hdes.smooth_pullback T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) Y q g hq E' hBE
      hV' hP' hord
  · intro T hv hdim hO Y q g _ _ hq E' hBE hV' hP' hO'
    have hm : ((T.pullbackAlong Y q g).withBoundary E').mult = T.mult :=
      (MarkedIdealWithBoundary.withBoundary_mult (T.pullbackAlong Y q g) E').trans
        (T.pullbackAlong_mult Y q g)
    have hord : ∀ x : ↥((T.pullbackAlong Y q g).withBoundary E').scheme,
        orderAt ((T.pullbackAlong Y q g).withBoundary E').ideal x ≤ (T.mult : ℕ∞) := by
      intro x
      have h := (MarkedIdealWithBoundary.isOrderBoundedByMult_iff ((T.pullbackAlong Y q g).withBoundary E')).mp hO' x
      rwa [hm] at h
    exact hdes.smooth_pullback_strict T hv hdim ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) Y q g hq
      E' hBE hV' hP' hord
  · intro T hv hdim hO hemp
    exact length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hdim
      ((MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).mp hO) hemp

theorem isOrderReduction_maxContact_dim_le_of_descentHypotheses
    (hinv : ComapIsoInvariance.{u}) (n : ℕ) (A : ℕ → PrincipalizationAssignment.{u})
    (L L' : PrincipalizationAssignment.{u})
    (hlow : IsMaxOrderReduction (fun d => d < n) L L')
    (hdiv : ∀ j : ℕ, IsBoundaryDivisorReduction (fun d => d ≤ n) j (A j) L)
    (hstar : CoverSequenceProperties hinv (fun d => d ≤ n) A)
    (hdes : DescentHypotheses hinv (fun d => d ≤ n) A L) :
    IsOrderReduction (fun d => d ≤ n) (maxContactPrincipalization hinv A) L :=
  isOrderReduction_maxContact_of_descentHypotheses hinv (fun d => d ≤ n) (fun d => d < n) A L L'
    (fun _ _ hab hb => lt_of_lt_of_le hab hb) hlow hdiv hstar hdes

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
end

