import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0680
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierOfOrders
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Poinc.TraitGlue

theorem dvd_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] {a b : A}
    (ha : a ≠ 0) (h : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      algebraMap A (Localization.AtPrime P) a ∣ algebraMap A (Localization.AtPrime P) b) : a ∣ b := by
  have ha' : algebraMap A (FractionRing A) a ≠ 0 := fun e =>
    ha (IsFractionRing.injective A (FractionRing A) (e.trans (map_zero _).symm))
  obtain ⟨c, hc⟩ := KrullAlg.mem_range_of_forall_height_one (A := A)
    (algebraMap A (FractionRing A) b / algebraMap A (FractionRing A) a) (fun P hP h1 => by
      obtain ⟨c, hc⟩ := h P h1
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
      have e : algebraMap A (Localization.AtPrime P) (s * b) = algebraMap A (Localization.AtPrime P) (a * r) := by
        rw [map_mul, map_mul, hc, mul_left_comm, IsLocalization.mk'_spec']
      have e' : s * b = a * r := IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors e
      refine ⟨s, s.2, r, ?_⟩
      rw [← mul_div_assoc, ← map_mul, e', map_mul, mul_div_cancel_left₀ _ ha'])
  refine ⟨c, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, hc, mul_div_cancel₀ _ ha']

theorem dvd_of_generisations {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (x : X)
    {a b : X.presheaf.stalk x} (ha : a ≠ 0)
    (h : ∀ (η : X) (hη : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
      (X.presheaf.stalkSpecializes hη).hom a ∣ (X.presheaf.stalkSpecializes hη).hom b) : a ∣ b := by
  have := (hX x).2
  refine dvd_of_height_one ha fun q _ hq => ?_
  let y : PrimeSpectrum (X.presheaf.stalk x) := ⟨q, inferInstance⟩
  obtain ⟨e, he⟩ := LocalRingGeneralisation.stalk_fromSpecStalk_equiv X x q
  have hs : X.fromSpecStalk x y ⤳ x := by
    have : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hcomp : ∀ t, e ((X.presheaf.stalkSpecializes hs).hom t) = algebraMap _ (Localization.AtPrime q) t := by
    intro t
    obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq t
    have h3 := congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hs)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
    erw [h3]
    exact he U _ hxU s
  rw [← hcomp, ← hcomp]
  refine map_dvd e (h _ hs ?_)
  rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
  rfl

theorem finite_dim_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {W : X.Opens} (hW : IsAffineOpen W)
    (V : X.Opens) {z : X} (hzW : z ∈ W) (hzV : z ∈ V) :
    {η : X | η ∈ W ∧ ringKrullDim (X.presheaf.stalk η) = 1 ∧ η ∉ V}.Finite := by
  obtain ⟨a, haV, hza⟩ := hW.exists_basicOpen_le ⟨z, hzV⟩ hzW
  have : Nonempty W := ⟨⟨z, hzW⟩⟩
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hza
  have hfin := (KrullAlg.finite_height_one ha).preimage
    (f := fun p : PrimeSpectrum Γ(X, W) => p.asIdeal) (fun _ _ _ _ e => PrimeSpectrum.ext e)
  refine (hfin.image (fun p => hW.fromSpec p)).subset ?_
  rintro η ⟨h1, h2, h3⟩
  letI : Algebra Γ(X, W) (X.presheaf.stalk η) := X.presheaf.algebra_section_stalk ⟨η, h1⟩
  haveI := hW.isLocalization_stalk ⟨η, h1⟩
  refine ⟨hW.primeIdealOf ⟨η, h1⟩, ⟨inferInstance, ?_, ?_⟩, hW.fromSpec_primeIdealOf ⟨η, h1⟩⟩
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hW.primeIdealOf ⟨η, h1⟩).asIdeal] at h2
    exact_mod_cast h2
  · by_contra hn
    refine h3 (haV ((X.mem_basicOpen a η h1).2 ?_))
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk η) (hW.primeIdealOf ⟨η, h1⟩).asIdeal a).2 hn

theorem associated_of_map {A V : Type} [CommRing A] [IsDomain A] [ValuationRing A] [CommRing V] [IsDomain V]
    (φ : A →+* V) [IsLocalHom φ] {a b : A} (h : Associated (φ a) (φ b)) (ha : φ a ≠ 0) : Associated a b := by
  have key : ∀ {a c : A}, Associated (φ a) (φ (a * c)) → φ a ≠ 0 → Associated a (a * c) := by
    intro a c h ha
    rw [map_mul] at h
    have : IsUnit (φ c) := isUnit_of_associated_mul h.symm ha
    exact (associated_mul_unit_left _ _ (isUnit_of_map_unit φ c this)).symm
  rcases ValuationRing.dvd_total a b with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact key h ha
  · exact (key h.symm (h.ne_zero_iff.1 ha)).symm

theorem valuationRing_stalk {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (η : X)
    (h : ringKrullDim (X.presheaf.stalk η) = 1) : ValuationRing (X.presheaf.stalk η) := by
  have := (hX η).2
  have hle : Ring.KrullDimLE 1 (X.presheaf.stalk η) := by
    rw [Ring.krullDimLE_iff, h]
    norm_num
  have : Ring.DimensionLEOne (X.presheaf.stalk η) := by
    refine ⟨fun {p} hp hprime => ?_⟩
    rcases Ring.krullDimLE_one_iff.mp hle p hprime with h | h
    · rw [IsDomain.minimalPrimes_eq_singleton_bot] at h
      exact absurd h hp
    · exact h
  have : IsDedekindDomain (X.presheaf.stalk η) :=
    (isDedekindDomain_iff _ (FractionRing (X.presheaf.stalk η))).mpr
      ⟨inferInstance, inferInstance, inferInstance, fun {y} hy => IsIntegrallyClosed.isIntegral_iff.mp hy⟩
  have h2 := (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk η)).out 2 1
  exact h2.1 this

theorem specializes_germ {X : Scheme.{0}} {W : X.Opens} {x η : X} (h : η ⤳ x) (hx : x ∈ W) (hη : η ∈ W) (s : Γ(X, W)) :
    (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ W x hx).hom s) = (X.presheaf.germ W η hη).hom s :=
  congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hx h)

theorem exists_spread {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
    (f : ∀ x : X, X.presheaf.stalk x) (hU : ∀ η ∈ U, ringKrullDim (X.presheaf.stalk η) = 1 → IsUnit (f η))
    (hne : ∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → genericPoint X ∈ U) (x : X) (h0 : f x ≠ 0)
    (hc : ∀ (η : X) (h : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
      Associated ((X.presheaf.stalkSpecializes h).hom (f x)) (f η)) :
    ∃ (W : X.Opens) (hx : x ∈ W) (s : Γ(X, W)), (X.presheaf.germ W x hx).hom s = f x ∧
      ∀ (η : X) (hη : η ∈ W), ringKrullDim (X.presheaf.stalk η) = 1 →
        Associated ((X.presheaf.germ W η hη).hom s) (f η) := by
  obtain ⟨W₀, hx₀, s₀, hs₀⟩ := X.presheaf.exists_germ_eq (f x)
  obtain ⟨⟨W, hW⟩, hx, hle⟩ := EffCartierData.exists_affine_le hx₀
  let s : Γ(X, W) := resG X hle s₀
  have hs : (X.presheaf.germ W x hx).hom s = f x := (Cartier.germ_resG hle _ hx _).trans hs₀
  let B : Set X := {η | ∃ hη : η ∈ W, ringKrullDim (X.presheaf.stalk η) = 1 ∧
    ¬ Associated ((X.presheaf.germ W η hη).hom s) (f η)}
  have hgen : ∀ {V : X.Opens} {y : X}, y ∈ V → genericPoint X ∈ V := fun {V y} hy =>
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨y, trivial, hy⟩
  have hB : B.Finite := by
    rcases B.eq_empty_or_nonempty with h | ⟨η₀, -, h₀, -⟩
    · rw [h]; exact Set.finite_empty
    have hs0 : s ≠ 0 := fun e => h0 (by rw [← hs, e, map_zero])
    have hb : genericPoint X ∈ X.basicOpen s := by
      rw [X.mem_basicOpen s _ (hgen hx)]
      have : (X.presheaf.germ W _ (hgen hx)).hom s ≠ 0 := fun e =>
        hs0 (germ_injective_of_isIntegral X _ (hgen hx) (e.trans (map_zero _).symm))
      exact (IsUnit.mk0 (G₀ := X.functionField) _ this)
    refine (finite_dim_one hW (U ⊓ X.basicOpen s) (hgen hx) ⟨hne η₀ h₀, hb⟩).subset ?_
    rintro η ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun h4 => h3 ?_⟩
    exact (associated_one_iff_isUnit.2 ((X.mem_basicOpen s η h1).1 h4.2)).trans
      (associated_one_iff_isUnit.2 (hU η h4.1 h2)).symm
  have hcl : IsClosed (⋃ η ∈ B, closure ({η} : Set X)) := hB.isClosed_biUnion fun _ _ => isClosed_closure
  let W' : X.Opens := W ⊓ ⟨_, hcl.isOpen_compl⟩
  have hx' : x ∈ W' := by
    refine ⟨hx, fun hm => ?_⟩
    obtain ⟨η, ⟨h1, h2, h3⟩, h4⟩ := Set.mem_iUnion₂.1 hm
    have h5 : η ⤳ x := specializes_iff_mem_closure.2 h4
    refine h3 ?_
    rw [← specializes_germ h5 hx h1, hs]
    exact hc η h5 h2
  refine ⟨W', hx', resG X inf_le_left s, (Cartier.germ_resG _ _ hx' _).trans hs, fun η hη h1 => ?_⟩
  rw [Cartier.germ_resG]
  by_contra hn
  exact hη.2 (Set.mem_iUnion₂.2 ⟨η, ⟨hη.1, h1, hn⟩, subset_closure rfl⟩)

theorem exists_of_germs {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (U : X.Opens)
    (f : ∀ x : X, X.presheaf.stalk x) (hU : ∀ η ∈ U, ringKrullDim (X.presheaf.stalk η) = 1 → IsUnit (f η))
    (hne : ∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → genericPoint X ∈ U) (h0 : ∀ x, f x ≠ 0)
    (hc : ∀ (x η : X) (h : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
      Associated ((X.presheaf.stalkSpecializes h).hom (f x)) (f η)) :
    ∃ D : EffCartierData X, (∀ x ∈ D.idealSheaf.support, x ∉ U) ∧
      ∀ x, FinalTheorems.stalkId D.idealSheaf x = Ideal.span {f x} := by
  choose W hx s hs hW using fun x => exists_spread U f hU hne x (h0 x) (hc x)
  have hs0 : ∀ x, s x ≠ 0 := fun x e => h0 x (by rw [← hs x, e, map_zero])
  have hreg : ∀ x, Cartier.IsRegularFn (s x) := fun x => Cartier.isRegularFn_of_ne_zero (hs0 x)
  have hdvd : ∀ (i j y : X) (hi : y ∈ W i) (hj : y ∈ W j),
      (X.presheaf.germ _ y hi).hom (s i) ∣ (X.presheaf.germ _ y hj).hom (s j) := by
    intro i j y hi hj
    refine dvd_of_generisations hX y (fun e =>
      hs0 i (germ_injective_of_isIntegral X _ hi (e.trans (map_zero _).symm))) fun η hη h1 => ?_
    have hi' : η ∈ W i := hη.mem_open (W i).isOpen hi
    have hj' : η ∈ W j := hη.mem_open (W j).isOpen hj
    rw [specializes_germ hη hi hi', specializes_germ hη hj hj']
    exact ((hW i η hi' h1).trans (hW j η hj' h1).symm).dvd
  let D : EffCartierData X :=
    { ι := X
      U := W
      f := s
      cover := eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩
      regular := hreg
      assoc := fun i j => ((hreg i).resG _).associated_of_germ ((hreg j).resG _) fun y hy => by
        rw [Cartier.germ_resG, Cartier.germ_resG]
        exact le_antisymm (Ideal.span_singleton_le_span_singleton.2 (hdvd j i y hy.2 hy.1))
          (Ideal.span_singleton_le_span_singleton.2 (hdvd i j y hy.1 hy.2)) }
  refine ⟨D, fun x hxD hxU => ?_, fun x => (D.stalkId_idealSheaf x x (hx x)).trans (congrArg (fun t => Ideal.span {t}) (hs x))⟩
  refine (D.mem_support_iff x (hx x)).1 hxD ((X.mem_basicOpen (s x) x (hx x)).2 ?_)
  change IsUnit ((X.presheaf.germ _ x (hx x)).hom (s x))
  rw [hs x]
  refine isUnit_of_dvd_one (dvd_of_generisations hX x (h0 x) fun η hη h1 => ?_)
  exact ((hc x η hη h1).symm.isUnit (hU η (hη.mem_open U.isOpen hxU) h1)).dvd

theorem exists_effCartier_of_orders : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (U : X.Opens) (R : ATrait X → ℕ → Prop), (∀ (T : ATrait X) (a : ℕ), Set.range T.ξ ⊆ U → R T a → a = 0) → (∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → ∃ (T : ATrait X) (a e : ℕ), T.CentredAt η e ∧ T.GenIn U ∧ R T a) → (∀ x : X, ∃ f : X.presheaf.stalk x, ∀ (T : ATrait X) (h : T.ξ (closedPoint T.V) ⤳ x) (a : ℕ), T.GenIn U → R T a → T.HasOrd h f a) → ∃ D : EffCartierData X, (∀ x ∈ D.idealSheaf.support, x ∉ U) ∧ ∀ (T : ATrait X) (a : ℕ), T.GenIn U → R T a → idlAlong D.idealSheaf T.ξ = Ideal.span {T.ϖ ^ a} := by
  intro X _ _ hX U R hR hT hf
  have hf' : ∀ x : X, ∃ f : X.presheaf.stalk x, f ≠ 0 ∧ ∀ (T : ATrait X) (h : T.ξ (closedPoint T.V) ⤳ x) (a : ℕ),
      T.GenIn U → R T a → T.HasOrd h f a := by
    intro x
    obtain ⟨f, hf⟩ := hf x
    by_cases h0 : f = 0
    · refine ⟨1, one_ne_zero, fun T h a h1 h2 => ?_⟩
      have := hf T h a h1 h2
      rw [h0, ATrait.HasOrd, map_zero, map_zero, Ideal.span_singleton_eq_span_singleton] at this
      exact absurd (this.eq_zero_iff.1 rfl) (pow_ne_zero _ T.irr.ne_zero)
    · exact ⟨f, h0, hf⟩
  choose f h0 hf using hf'
  have hself : ∀ (T : ATrait X) (a : ℕ), T.GenIn U → R T a →
      Ideal.span {(Scheme.stalkClosedPointTo T.ξ).hom (f _)} = Ideal.span {T.ϖ ^ a} := by
    intro T a h1 h2
    have := hf _ T specializes_rfl a h1 h2
    rwa [ATrait.HasOrd, TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, RingHom.id_apply] at this
  obtain ⟨D, hD, hD'⟩ := exists_of_germs hX U f (fun η hη h1 => by
      obtain ⟨T, a, e, ⟨rfl, -⟩, h2, h3⟩ := hT η h1
      have ha : a = 0 := hR T a (by
        rintro _ ⟨p, rfl⟩
        exact ((IsLocalRing.specializes_closedPoint p).map T.ξ.continuous).mem_open U.isOpen hη) h3
      have := hself T a h2 h3
      rw [ha, pow_zero, Ideal.span_singleton_one, Ideal.span_singleton_eq_top] at this
      exact isUnit_of_map_unit _ _ this)
    (fun η h1 => by
      obtain ⟨T, a, e, -, h2, -⟩ := hT η h1
      obtain ⟨p⟩ : Nonempty (Sp (FractionRing T.V)) := inferInstanceAs (Nonempty (PrimeSpectrum _))
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨_, trivial, h2 ⟨p, rfl⟩⟩) h0
    (fun x η h h1 => by
      obtain ⟨T, a, e, ⟨rfl, -⟩, h2, h3⟩ := hT η h1
      have := valuationRing_stalk hX _ h1
      have e1 := Ideal.span_singleton_eq_span_singleton.1 (hf x T h a h2 h3)
      have e2 := Ideal.span_singleton_eq_span_singleton.1 (hself T a h2 h3)
      exact associated_of_map (Scheme.stalkClosedPointTo T.ξ).hom (e1.trans e2.symm)
        (e1.ne_zero_iff.2 (pow_ne_zero _ T.irr.ne_zero)))
  refine ⟨D, hD, fun T a h1 h2 => ?_⟩
  rw [idlAlong, hD', Ideal.map_span, Set.image_singleton]
  exact hself T a h1 h2

end GlobalTheory.Poinc.TraitGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEltPrescribedValuationsBalancedArchimedean
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt

open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped nonZeroDivisors

theorem sum_embeddings_eq_sum_places {K : Type} [Field K] [NumberField K] (g : (K →+* ℂ) → ℝ)
    (hg : ∀ σ, g ((starRingEnd ℂ).comp σ) = g σ) :
    ∑ σ, g σ = ∑ w : InfinitePlace K, (w.mult : ℝ) * g w.embedding := by
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : K →+* ℂ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w), g σ = g w.embedding := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [← hσ.2]
    rcases embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun x => ComplexEmbedding.conjugate_coe_eq σ x
      rw [this, hg]
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]

theorem t_embedding_mk {K : Type} [Field K] (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (σ : K →+* ℂ) : t (InfinitePlace.mk σ).embedding = t σ := by
  rcases embedding_mk_eq σ with h | h
  · rw [h]
  · have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
      RingHom.ext fun x => ComplexEmbedding.conjugate_coe_eq σ x
    rw [h, this, ht]

theorem minkowskiBound_eq_absNorm_mul {K : Type} [Field K] [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    minkowskiBound K I = ENNReal.ofReal (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
      minkowskiBound K 1 := by
  unfold minkowskiBound
  rw [volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_fractionalIdealLatticeBasis]
  simp [mul_assoc]

end GlobalTheory.CovHt

namespace GlobalTheory.CovHt

open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped nonZeroDivisors

theorem exists_elt_balanced : ∀ (K : Type) [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ)
    (t : (K →+* ℂ) → ℝ), (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → ∃ C : ℝ, ∀ τ : ℕ, ∃ α : K, α ≠ 0 ∧
      (∀ la, (τ : ℝ) * e la ≤ (vLa la α : ℝ)) ∧ ∀ σ : K →+* ℂ, Real.log ‖σ α‖ ≤ τ * (cost e t - t σ) + C := by
  intro K _ _ e t ht

  have hNpos : ∀ la : HeightOneSpectrum (𝓞 K), (0 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by
    intro la
    have : Ideal.absNorm la.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have hNone : ∀ la : HeightOneSpectrum (𝓞 K), (1 : ℝ) ≤ (Ideal.absNorm la.asIdeal : ℝ) := by
    intro la
    have h := hNpos la
    have : (1 : ℕ) ≤ Ideal.absNorm la.asIdeal := by exact_mod_cast h
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  set S : ℝ := e.sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ) with hS
  set A : ℝ := ∑ la ∈ e.support, Real.log (Ideal.absNorm la.asIdeal : ℝ) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun la _ => Real.log_nonneg (hNone la)
  set V0 : ℝ := (minkowskiBound K 1).toReal with hV0
  have hV0nn : 0 ≤ V0 := ENNReal.toReal_nonneg
  set c : ℝ := |Real.log V0| + A + 1 with hc
  refine ⟨c, fun τ => ?_⟩
  set m : HeightOneSpectrum (𝓞 K) → ℤ := fun la => ⌈(τ : ℝ) * e la⌉ with hm
  have hm0 : ∀ la, la ∉ e.support → m la = 0 := by
    intro la hla
    rw [Finsupp.notMem_support_iff] at hla
    simp [hm, hla]
  have hmfin : ∀ᶠ v in Filter.cofinite, m v = 0 := by
    rw [Filter.eventually_cofinite]
    refine e.support.finite_toSet.subset fun v hv => ?_
    by_contra h
    exact hv (hm0 v h)
  set I : (FractionalIdeal (𝓞 K)⁰ K)ˣ := ∏ᶠ v, GroundTheory.Global.primeIdealUnit v ^ m v with hI
  have hcount : ∀ v, FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = m v :=
    GroundTheory.Global.count_finprod_primeIdealUnit_zpow m hmfin

  have hnorm : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) =
      ∏ la ∈ e.support, (Ideal.absNorm la.asIdeal : ℝ) ^ m la := by
    rw [hI, GroundTheory.Global.coe_finprod_primeIdealUnit_zpow m hmfin,
      finprod_eq_prod_of_mulSupport_subset (s := e.support)]
    · rw [map_prod, Rat.cast_prod]
      refine Finset.prod_congr rfl fun la _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    · intro v hv
      by_contra h
      exact hv (by simp [hm0 v h])
  have hnormle : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) ≤ Real.exp (τ * S + A) := by
    rw [hnorm]
    have hS' : S = ∑ la ∈ e.support, e la * Real.log (Ideal.absNorm la.asIdeal : ℝ) := rfl
    rw [hS', hA, Finset.mul_sum, ← Finset.sum_add_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun la _ => by positivity) fun la _ => ?_
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (hNpos la)]
    refine Real.exp_le_exp.2 ?_
    have h1 : ((m la : ℤ) : ℝ) ≤ τ * e la + 1 := (Int.ceil_lt_add_one _).le
    have h2 := Real.log_nonneg (hNone la)
    nlinarith

  set g : InfinitePlace K → ℝ := fun w => (τ : ℝ) * (cost e t - t w.embedding) + c with hg
  set f : InfinitePlace K → NNReal := fun w => ⟨Real.exp (g w), (Real.exp_pos _).le⟩ with hf
  have hsum : ∑ w : InfinitePlace K, (w.mult : ℝ) * g w = τ * S + (Module.finrank ℚ K : ℝ) * c := by
    have h := sum_embeddings_eq_sum_places (K := K) (fun σ => (τ : ℝ) * (cost e t - t σ) + c)
      (fun σ => by simp only [ht])
    rw [show (∑ w : InfinitePlace K, (w.mult : ℝ) * g w) =
        ∑ w : InfinitePlace K, (w.mult : ℝ) * ((τ : ℝ) * (cost e t - t w.embedding) + c) from rfl, ← h]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul, nsmul_eq_mul]
    have hn0 : (Module.finrank ℚ K : ℝ) ≠ 0 := by positivity
    have hcost : (Module.finrank ℚ K : ℝ) * cost e t = S + ∑ σ, t σ := by
      rw [cost, mul_div_cancel₀ _ hn0]
    rw [hcost]; ring
  have hprod : ((∏ w, f w ^ w.mult : NNReal) : ℝ) = Real.exp (τ * S + (Module.finrank ℚ K : ℝ) * c) := by
    rw [NNReal.coe_prod, ← hsum, Real.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [NNReal.coe_pow, Real.exp_nat_mul]
    rfl
  have hmink : minkowskiBound K I < MeasureTheory.volume (convexBodyLT K f) := by
    rw [convexBodyLT_volume, minkowskiBound_eq_absNorm_mul]
    have h1 : minkowskiBound K 1 = ENNReal.ofReal V0 := (ENNReal.ofReal_toReal (minkowskiBound_lt_top K 1).ne).symm
    rw [h1, ← ENNReal.ofReal_mul (by
      rw [hnorm]; exact Finset.prod_nonneg fun la _ => by positivity)]
    refine lt_of_lt_of_le ?_ (le_mul_of_one_le_left zero_le' (by exact_mod_cast one_le_convexBodyLTFactor K))
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (by rw [hprod]; positivity), hprod]
    have hV : V0 ≤ Real.exp |Real.log V0| := by
      rcases hV0nn.eq_or_lt with h | h
      · rw [← h]; positivity
      · calc V0 = Real.exp (Real.log V0) := (Real.exp_log h).symm
          _ ≤ Real.exp |Real.log V0| := Real.exp_le_exp.2 (le_abs_self _)
    calc ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) * V0
        ≤ Real.exp (τ * S + A) * Real.exp |Real.log V0| :=
          mul_le_mul hnormle hV hV0nn (Real.exp_pos _).le
      _ = Real.exp (τ * S + (A + |Real.log V0|)) := by rw [← Real.exp_add]; ring_nf
      _ < Real.exp (τ * S + (Module.finrank ℚ K : ℝ) * c) := by
          refine Real.exp_lt_exp.2 ?_
          have hc0 : 0 ≤ c := by positivity
          nlinarith
  obtain ⟨α, hαI, hα0, hlt⟩ := exists_ne_zero_mem_ideal_lt K I hmink
  refine ⟨α, hα0, fun la => ?_, fun σ => ?_⟩
  · have hsp : FractionalIdeal.spanSingleton (𝓞 K)⁰ α ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hα0
    have hle := FractionalIdeal.count_mono K la hsp (FractionalIdeal.spanSingleton_le_iff_mem.2 hαI)
    rw [hcount, GroundTheory.Global.count_spanSingleton la hα0] at hle
    have hv : vLa la α = -WithZero.log (la.valuation K α) := rfl
    calc (τ : ℝ) * e la ≤ (m la : ℝ) := Int.le_ceil _
      _ ≤ (vLa la α : ℝ) := by rw [hv]; exact_mod_cast hle
  · have h := hlt (InfinitePlace.mk σ)
    rw [InfinitePlace.apply] at h
    have hpos : 0 < ‖σ α‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hα0)
    have : Real.log ‖σ α‖ ≤ Real.log (f (InfinitePlace.mk σ) : ℝ) := Real.log_le_log hpos h.le
    rw [show ((f (InfinitePlace.mk σ)) : ℝ) = Real.exp (g (InfinitePlace.mk σ)) from rfl, Real.log_exp] at this
    rw [hg] at this
    simp only [t_embedding_mk t ht σ] at this
    exact this

end GlobalTheory.CovHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatPowEq
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtCover

theorem exists_faithfullyFlat_pow_eq : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 0 < n → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D') (ψ : D →ₐ[R] D') (z : Pt A D'), (ψ : D →+* D').FaithfullyFlat ∧ z ^ n = spOver ψ ≫ x := by
  intro R _ A _ hA n hn D _ _ x
  obtain ⟨hf, hfl⟩ := AbTorsionAnyBase.isFinite_and_flat_mulA _ A hA n hn
  have hs := AbelianLimit.surjective_pow A hA n hn
  let m : A.left ⟶ A.left := ((𝟙 A) ^ n : A ⟶ A).left
  have : IsFinite m := hf
  have : Flat m := hfl
  have : Surjective m := hs
  let x₀ : Spec (CommRingCat.of D) ⟶ A.left := x.left
  let Y := Limits.pullback x₀ m
  have : IsAffine Y := isAffine_of_isAffineHom (Limits.pullback.fst x₀ m)
  let q : Spec Γ(Y, ⊤) ⟶ Spec (CommRingCat.of D) := Y.isoSpec.inv ≫ Limits.pullback.fst x₀ m
  let φ : CommRingCat.of D ⟶ Γ(Y, ⊤) := Spec.preimage q
  have hφ : Spec.map φ = q := Spec.map_preimage q
  have hff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 (by
    rw [hφ]; exact ⟨inferInstance, inferInstance⟩)
  letI : Algebra R Γ(Y, ⊤) := (φ.hom.comp (algebraMap R D)).toAlgebra
  let ψ : D →ₐ[R] Γ(Y, ⊤) := { φ.hom with commutes' := fun _ ↦ rfl }
  have hψ : (spOver ψ).left = q := hφ
  have hc : (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) ≫ m = (spOver ψ ≫ x).left := by
    rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc, Over.comp_left, hψ]
  let z : Pt A Γ(Y, ⊤) := Over.homMk (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) (by
    rw [← Over.w (spOver ψ ≫ x), ← hc]
    simp only [Category.assoc]
    rw [Over.w ((𝟙 A) ^ n : A ⟶ A)])
  refine ⟨Γ(Y, ⊤), inferInstance, inferInstance, ψ, z, hff, ?_⟩
  rw [← Category.comp_id z, ← MonObj.comp_pow]
  exact Over.OverMorphism.ext hc

end GlobalTheory.PtCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFieldEmbeddingStalkOfFiniteStalkMap
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.StalkField

theorem exists_stalk_field_hom : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (p : Sp Ω ⟶ X), (p.stalkMap (genericPoint (Sp Ω))).hom.Finite → ∃ φ : X.presheaf.stalk (p.base (genericPoint (Sp Ω))) →+* Ω, φ.Finite ∧ ∀ (K : Type) [Field K] (τ₁ τ₂ : Ω →+* K), spMap τ₁ ≫ p = spMap τ₂ ≫ p → τ₁.comp φ = τ₂.comp φ := by
  intro Ω _ X p hfin
  have hpt : genericPoint (Sp Ω) = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
  rw [hpt] at hfin ⊢
  refine ⟨(Scheme.stalkClosedPointTo p).hom, ?_, ?_⟩
  · have e : Scheme.stalkClosedPointTo p = p.stalkMap _ ≫ (stalkClosedPointIso (CommRingCat.of Ω)).hom := rfl
    rw [e, CommRingCat.hom_comp]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of Ω)).hom).2) hfin
  · intro K _ τ₁ τ₂ h
    have hs : ∀ τ : Ω →+* K, (spMap τ ≫ p) (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω) := by
      intro τ
      apply specializes_of_eq
      exact congrArg p (Subsingleton.elim ((spMap τ).base (IsLocalRing.closedPoint K)) (IsLocalRing.closedPoint Ω))
    have H : ∀ (q₁ q₂ : Sp K ⟶ X), q₁ = q₂ → ∀ (h₁ : q₁ (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω))
        (h₂ : q₂ (IsLocalRing.closedPoint K) ⤳ p (IsLocalRing.closedPoint Ω)) a,
        (Scheme.stalkClosedPointTo q₁).hom ((X.presheaf.stalkSpecializes h₁).hom a) =
          (Scheme.stalkClosedPointTo q₂).hom ((X.presheaf.stalkSpecializes h₂).hom a) := by
      rintro _ _ rfl _ _ _; rfl
    ext a
    simp only [RingHom.comp_apply]
    rw [← GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes X p τ₁ (hs τ₁) a,
      ← GlobalTheory.TorRef.stalkClosedPointTo_comp_spMap_specializes X p τ₂ (hs τ₂) a]
    exact H _ _ h _ _ a

end GlobalTheory.StalkField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteGroupLevelStatement
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_group_level : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → ∃ (G : Type) (_ : Group G) (_ : Finite G) (lev : G → ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La) × ((dat p i).La →ₗ[𝓞 D.host.E] (dat p i).La)) (χ : G →* (p.T.Q.c.F)ˣ), ActLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c lev ∧ slope_sq (normW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)) (eigLat (p.T.U ((i : ℕ) + 1)) lev χ (Gk p i)) ≤ muCore p i := by
  first | exact @GlobalTheory.DefEig.eig_slope_le | exact GlobalTheory.DefEig.eig_slope_le | (intros; apply GlobalTheory.DefEig.eig_slope_le <;> assumption)
end

