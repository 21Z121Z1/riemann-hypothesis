import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0058
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0056
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSJoinright
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0025
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0059
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodHermitianTypeCompatibility
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupGeneration
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRestrictPreimageOpenStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_restrict_preimage_open : ∀ {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}, IsChart a b V q → ∀ D : Y.Opens, ∃ (hle : V.ι ''ᵁ (q ⁻¹ᵁ D) ≤ V) (q' : (V.ι ''ᵁ (q ⁻¹ᵁ D)).toScheme ⟶ D.toScheme), IsChart a b (V.ι ''ᵁ (q ⁻¹ᵁ D)) q' ∧ q' ≫ D.ι = X.homOfLE hle ≫ q := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open | exact GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.isChart_restrict_quotient_open <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsTransitionMatrixGramStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transition_matrix_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → ∃ T : Matrix I I E, IsTransition D x e T ∧ gramE D x = T * gramE D e * (T.map (IsCMField.complexConj E)).transpose ∧ (LinearIndependent (𝓞 E) x → T.det ≠ 0) ∧ ∃ (n : ℕ) (S : Matrix I I (𝓞 E)), 0 < n ∧ (∀ a, n • x a = ∑ b, S a b • e b) ∧ ∀ a b, (S a b : E) = n * T a b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.transition_matrix_exists | exact GlobalTheory.CompanionTheory.Ar.Fl.transition_matrix_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.transition_matrix_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinLeftStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_join_left : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft.main | exact GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinRight
section
namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement :=
  PositivityTheory.Xgn.A_s_joinright.of_pullback GlobalTheory.T.pair_number_pullback

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GlueQuotientChartsCoverStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_quotient_charts_cover : ∀ {X : Scheme.{0}} (R : X → X → Prop) (𝒰 : Set X.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → (∀ x : X, ∃ U : 𝒰, x ∈ U.1) → ∀ (Y : 𝒰 → Scheme.{0}) (q : ∀ U : 𝒰, U.1.toScheme ⟶ Y U), (∀ U, Epi (q U)) → (∀ U, Function.Surjective (q U)) → (∀ (U : 𝒰) (u v : U.1.toScheme), q U u = q U v ↔ R (U.1.ι u) (U.1.ι v)) → (∀ (U : 𝒰) (x y : X), R x y → x ∈ U.1 → y ∈ U.1) → ∀ (k : ∀ U V : 𝒰, U.1 ≤ V.1 → (Y U ⟶ Y V)), (∀ U V h, IsOpenImmersion (k U V h)) → (∀ U V h, q U ≫ k U V h = X.homOfLE h ≫ q V) → ∃ (Y' : Scheme.{0}) (π : X ⟶ Y') (em : ∀ U, Y U ⟶ Y') (_ : ∀ U, IsOpenImmersion (em U)), (∀ U, U.1.ι ≫ π = q U ≫ em U) ∧ (∀ U, π ⁻¹ᵁ (em U).opensRange = U.1) ∧ ∀ y : Y', ∃ U, ∃ z : Y U, em U z = y := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.exists_colimit_of_quotient_charts | exact GlobalTheory.CompanionTheory.FreeQuotGlue.exists_colimit_of_quotient_charts | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.exists_colimit_of_quotient_charts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GramDetNeZeroLocalBasisCofinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → (gramE D e).det ≠ 0 ∧ {ℓ : Nat.Primes | ¬ IsLocBasis (𝓞 E) ℓ e}.Finite := by
  classical
  intro E _ _ _ H D I _ _ e hcard hli
  haveI := D.fin
  have T : ∀ (c : 𝓞 E) (x y : D.La), Algebra.trace ℚ E (algebraMap (𝓞 E) E c * sesq D x y) = ((D.EF (c • x) y : ℤ) : ℚ) := by
    intro c x y
    have key : ∀ j, Algebra.trace ℚ E (algebraMap (𝓞 E) E (RingOfIntegers.basis E j) * sesq D x y) = ((D.EF (RingOfIntegers.basis E j • x) y : ℤ) : ℚ) := by
      intro j
      have hterm : ∀ k, Algebra.trace ℚ E (algebraMap (𝓞 E) E (RingOfIntegers.basis E j) * (((D.EF (RingOfIntegers.basis E k • x) y : ℤ) : E) * HT.dualInt E k)) = ((D.EF (RingOfIntegers.basis E k • x) y : ℤ) : ℚ) * (if j = k then 1 else 0) := by
        intro k
        rw [← HT.LatBasic.trace_dualInt k j, ← map_intCast (algebraMap ℚ E), mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm (algebraMap (𝓞 E) E _), ← NumberField.integralBasis_apply]
      simp only [sesq, Finset.mul_sum, map_sum, hterm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact mul_one _
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr c]
    conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr c]
    simp only [map_sum, Finset.sum_mul, Finset.sum_smul, LinearMap.sum_apply, Int.cast_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_zsmul, smul_mul_assoc, map_zsmul, key j, smul_assoc, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul]
    norm_cast
  have hy : ∀ y : D.La, ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
    intro y
    by_contra hne
    push_neg at hne
    have hli' : LinearIndependent (𝓞 E) (fun o : Option I => Option.elim o y e) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fintype.sum_option] at hg
      simp only [Option.elim] at hg
      have hnone : g none = 0 := by
        by_contra h0
        apply hne (g none) h0
        have : g none • y = -∑ i, g (some i) • e i := eq_neg_of_add_eq_zero_left hg
        rw [this]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)))
      rw [hnone, zero_smul, zero_add] at hg
      intro o
      cases o with
      | none => exact hnone
      | some i => exact (Fintype.linearIndependent_iff.mp hli) _ hg i
    have := hli'.fintype_card_le_finrank
    rw [Fintype.card_option, hcard, D.rank] at this
    omega
  have hfin : ∃ c : 𝓞 E, c ≠ 0 ∧ ∀ y : D.La, c • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule (𝓞 E) D.La).FG)
    choose f hf0 hfm using hy
    refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.mpr (fun y _ => hf0 y), ?_⟩
    intro y
    have hy' : y ∈ Submodule.span (𝓞 E) (s : Set D.La) := hs ▸ Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy'
    · intro z hz
      rw [← Finset.mul_prod_erase s f hz, mul_comm (f z), mul_smul]
      exact Submodule.smul_mem _ _ (hfm z)
    · simp
    · intro a b _ _ ha hb
      rw [smul_add]
      exact Submodule.add_mem _ ha hb
    · intro r a _ ha
      rw [smul_comm]
      exact Submodule.smul_mem _ _ ha
  obtain ⟨c, hc0, hc⟩ := hfin
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {c}))
  have hN0 : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  have hNy : ∀ y : D.La, Ideal.absNorm (Ideal.span {c}) • y ∈ Submodule.span (𝓞 E) (Set.range e) := by
    intro y
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← ht, mul_smul]
    exact Submodule.smul_mem _ _ (hc y)
  constructor
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ v
    choose a ha using fun i => RingHom.mem_rangeS.mp (hb i (Finset.mem_univ i))
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hv0
    have hai0 : a i0 ≠ 0 := by
      intro h0
      have := ha i0
      rw [h0, map_zero, Algebra.smul_def, eq_comm, mul_eq_zero] at this
      rcases this with h | h
      · exact nonZeroDivisors.coe_ne_zero b ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mp h)
      · exact hi0 h
    have hx0 : (∑ i, a i • e i) ≠ 0 := fun h => hai0 ((Fintype.linearIndependent_iff.mp hli) a h i0)
    have hEFc : ∀ (c : 𝓞 E) (n : I), D.EF (c • ∑ i, a i • e i) (e n) = 0 := by
      intro c n
      have h1 : c • ∑ i, a i • e i = ∑ m, (c * a m) • e m := by simp only [Finset.smul_sum, mul_smul]
      apply Int.cast_injective (α := ℚ)
      rw [h1, map_sum, LinearMap.sum_apply, Int.cast_sum, Int.cast_zero]
      simp only [← T]
      rw [← map_sum]
      have h2 : ∑ m, algebraMap (𝓞 E) E (c * a m) * sesq D (e m) (e n) = algebraMap (𝓞 E) E c * (algebraMap (𝓞 E) E b * (v ᵥ* gramE D e) n) := by
        simp only [Matrix.vecMul, dotProduct, gramE, Matrix.of_apply, map_mul, ha, Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => by ring)
      rw [h2, hv, Pi.zero_apply, mul_zero, mul_zero, map_zero]
    have hEF : ∀ y, D.EF (∑ i, a i • e i) y = 0 := by
      intro y
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp (hNy y)
      have h2 : D.EF (∑ i, a i • e i) (Ideal.absNorm (Ideal.span {c}) • y) = 0 := by
        rw [← hg, map_sum]
        refine Finset.sum_eq_zero (fun n _ => ?_)
        have := D.adj (H.bar.symm (g n)) (∑ i, a i • e i) (e n)
        rw [RingEquiv.apply_symm_apply] at this
        rw [← this]
        exact hEFc _ n
      rw [map_nsmul] at h2
      exact (smul_eq_zero.mp h2).resolve_left hN0
    apply hx0
    apply D.unimod.1
    rw [map_zero]
    exact LinearMap.ext hEF
  · apply Set.Finite.subset ((Nat.divisors (Ideal.absNorm (Ideal.span {c}))).finite_toSet.preimage (f := ((↑) : Nat.Primes → ℕ)) (Set.injOn_of_injective Subtype.val_injective))
    intro ℓ hℓ
    simp only [Set.mem_preimage, Finset.mem_coe, Nat.mem_divisors]
    refine ⟨?_, hN0⟩
    by_contra hd
    exact hℓ (by unfold IsLocBasis; exact ⟨hli, _, hd, hNy⟩)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphStatementHolds
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem graphStatement : GraphStatement := by
  intro K _ ι _ K₂ _ ι₂ _ P d g δ hP hg hne
  obtain ⟨h1, h2⟩ := GlobalTheory.T.graph_ideal_arithmetic_variety_image K ι K₂ ι₂ P d g δ hP hg hne
  refine ⟨h1, h2, ?_⟩
  intro G J hJ
  have hP' : IsArithVar (imageZ inlV (graphIdeal P g)) d := by rw [h2]; exact hP
  have hF : IsProjVarF (fibreIdeal Sum.inl G) 0 :=
    GlobalTheory.CompanionTheory.Ar.Giv.fibreDim K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV (graphIdeal P g) d 0 G
      isBlockMap_inl h1 hP'
  have hrel := hF.1.2.2
  let i : ∀ k, fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂) k := fun k => (hrel k).choose
  have hi : IsChart (fibreIdeal Sum.inl G) i := fun k => (hrel k).choose_spec
  rw [hJ.1 _ _ i hF hi]
  exact_mod_cast GlobalTheory.T.graph_ideal_fibre_chart_degree K ι K₂ ι₂ P g hP.2.1.1 hne h2 G i hi

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.InvariantOpenChartPreimageStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_open_chart_preimage : ∀ {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}, IsChart a b V q → ∀ (V' : X.Opens), V' ≤ V → a ⁻¹ᵁ V' = b ⁻¹ᵁ V' → ∃ D : Y.Opens, V.ι ''ᵁ (q ⁻¹ᵁ D) = V' := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage | exact GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.IsChart.exists_opens_image_preimage <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KodairaGenericOfAmpleSectionCountStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_generic_of_ample_section_count : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count | exact GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count | (intros; apply GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PeriodGramHermitianSignature
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.SignTau

open GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_type {g n : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (e : Fin n ≃ {i // ty i = σ}) (f : Fin g → ℂ)
    (hf : ∀ j, ty j ≠ σ → f j = 0) : ∑ j, f j = ∑ a, f (e a) := by
  classical
  have h1 : ∑ a, f (e a) = ∑ i : {i // ty i = σ}, f i := Equiv.sum_comp e (fun i : {i // ty i = σ} => f i)
  rw [h1, ← Finset.sum_subtype (p := fun j => ty j = σ) (Finset.univ.filter fun j => ty j = σ) (by simp) f,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rfl
  · exact hf j h

theorem hermForm_tyPart {g n : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (e : Fin n ≃ {i // ty i = σ})
    (M : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (tyPart ty σ z) (tyPart ty σ w) =
      ∑ a, ∑ b, z (e a) * M (e a) (e b) * star (w (e b)) := by
  classical
  rw [hermForm_eq_sum]
  have h1 : ∀ j, ty j ≠ σ → ∑ k, tyPart ty σ z j * M j k * star (tyPart ty σ w k) = 0 := by
    intro j hj
    apply Finset.sum_eq_zero
    intro k _
    simp [tyPart, hj]
  rw [sum_type ty σ e _ h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : ∀ k, ty k ≠ σ → tyPart ty σ z (e a) * M (e a) k * star (tyPart ty σ w k) = 0 := by
    intro k hk
    simp [tyPart, hk]
  rw [sum_type ty σ e _ h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [tyPart, (e a).2, (e b).2]

theorem star_hermForm {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) (z w : Fin g → ℂ) :
    star (hermForm M z w) = hermForm M w z := by
  rw [hermForm_eq_sum, hermForm_eq_sum]
  simp only [star_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul', star_mul', star_star, hM.apply]
  ring

theorem posDef_of_hermForm {g : ℕ} {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) : M.PosDef := by
  refine ⟨hM, fun x hx => ?_⟩
  have hx' : star (⇑x) ≠ 0 := by
    intro h0
    apply hx
    ext i
    simpa using congrFun h0 i
  have h1 := hpos (star ⇑x) hx'
  have h2 : (starRingEnd ℂ) (hermForm M (star ⇑x) (star ⇑x)) = hermForm M (star ⇑x) (star ⇑x) :=
    star_hermForm hM _ _
  have h3 : (x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj) =
      ∑ i, ∑ j, star (x i) * M i j * x j := by
    rw [Finsupp.sum_fintype x (fun i xi => x.sum fun j xj => star xi * M i j * xj)
      (fun i => by simp [Finsupp.sum])]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.sum_fintype x (fun j xj => star (x i) * M i j * xj) (fun j => by simp)
  have h4 : ∑ i, ∑ j, star (x i) * M i j * x j = hermForm M (star ⇑x) (star ⇑x) := by
    rw [hermForm_eq_sum]
    simp
  rw [h3, h4, Complex.lt_def]
  exact ⟨by simpa using h1, by simp [Complex.conj_eq_iff_im.mp h2]⟩

theorem fromCols_block {I : Type} [Fintype I] {p q : ℕ} (A : Matrix I (Fin p) ℂ) (B : Matrix I (Fin q) ℂ)
    (G₁ : Matrix (Fin p) (Fin p) ℂ) (G₂ : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.fromCols A B * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Matrix.fromCols A B)ᴴ =
      A * G₁ * Aᴴ - B * G₂ * Bᴴ := by
  rw [Matrix.fromCols_mul_fromBlocks, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows]
  simp [sub_eq_add_neg]

private theorem add_mul_mul_conjTranspose_add_eq_of_two_smul {r p q : ℕ} (C : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (V M N : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (key : V * ((2 : ℂ) • M) * Vᴴ = N) :
    (C * V + C * V) * M * (C * V + C * V)ᴴ = C * N * Cᴴ + C * N * Cᴴ := by
  rw [← key]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_smul, Matrix.smul_mul, two_smul, Matrix.mul_assoc]

theorem signature_of_factor {p q : ℕ} (M W : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (G₁ : Matrix (Fin p) (Fin p) ℂ) (G₂ : Matrix (Fin q) (Fin q) ℂ) (h₁ : G₁.PosDef) (h₂ : G₂.PosDef)
    (hM : (2 : ℂ) • M = W * Matrix.fromBlocks G₁ 0 0 (-G₂) * Wᴴ) (hdet : M.det ≠ 0) :
    M.IsHermitian ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (C * M * Cᴴ).PosDef) ∧
      ∃ C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ, (-(C * M * Cᴴ)).PosDef := by
  have hN : (Matrix.fromBlocks G₁ 0 0 (-G₂))ᴴ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by
    rw [Matrix.fromBlocks_conjTranspose, h₁.1.eq, Matrix.conjTranspose_neg, h₂.1.eq,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_zero]
  have hMh : M.IsHermitian := by
    have h2 : ((2 : ℂ) • M)ᴴ = (2 : ℂ) • M := by
      rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hN,
        Matrix.mul_assoc]
    rw [Matrix.conjTranspose_smul] at h2
    have h3 : (2 : ℂ) • Mᴴ = (2 : ℂ) • M := by simpa using h2
    exact smul_right_injective _ two_ne_zero h3
  have hW : IsUnit W.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h4 := congrArg Matrix.det hM
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, h0] at h4
    simp [hdet] at h4
  have hVW : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hW
  have hWV : Wᴴ * (W⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hVW, Matrix.conjTranspose_one]
  have key : W⁻¹ * ((2 : ℂ) • M) * (W⁻¹)ᴴ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by
    rw [hM]
    calc W⁻¹ * (W * Matrix.fromBlocks G₁ 0 0 (-G₂) * Wᴴ) * (W⁻¹)ᴴ
        = (W⁻¹ * W) * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Wᴴ * (W⁻¹)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.fromBlocks G₁ 0 0 (-G₂) := by rw [hVW, hWV, Matrix.one_mul, Matrix.mul_one]
  refine ⟨hMh, ⟨Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (0 : Matrix (Fin p) (Fin q) ℂ) * W⁻¹ +
      Matrix.fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (0 : Matrix (Fin p) (Fin q) ℂ) * W⁻¹, ?_⟩,
    ⟨Matrix.fromCols (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin q) (Fin q) ℂ) * W⁻¹ +
      Matrix.fromCols (0 : Matrix (Fin q) (Fin p) ℂ) (1 : Matrix (Fin q) (Fin q) ℂ) * W⁻¹, ?_⟩⟩
  · rw [add_mul_mul_conjTranspose_add_eq_of_two_smul _ _ _ _ key, fromCols_block]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.zero_mul, sub_zero]
    exact h₁.add h₁
  · rw [add_mul_mul_conjTranspose_add_eq_of_two_smul _ _ _ _ key, fromCols_block]
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.zero_mul, zero_sub,
      neg_add_rev, neg_neg]
    exact h₂.add h₂

theorem conj_cmHostRoot_ne_self (H : Host E) : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp h
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [sq, Complex.mul_re, him] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

end GlobalTheory.CompanionTheory.Ar.Fl.SignTau

private theorem posDef_reindex_of_hermForm_re_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {g n : ℕ}
    (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (e : Fin n ≃ {i // ty i = σ})
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    (Matrix.of fun a b => Hm (e a) (e b)).PosDef := by
  classical
  apply GlobalTheory.CompanionTheory.Ar.Fl.SignTau.posDef_of_hermForm
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    exact hH.apply _ _
  · intro z hz
    let w : Fin g → ℂ := fun i => if h : ty i = σ then z (e.symm ⟨i, h⟩) else 0
    have hw : ∀ a, w (e a) = z a := fun a => by simp [w, (e a).2]
    have hw0 : ∀ i, ty i ≠ σ → w i = 0 := fun i hi => by simp [w, hi]
    have hwz : w ≠ 0 := by
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hz
      exact fun h => ha (by simpa [h] using (hw a).symm)
    have key : hermForm Hm w w = hermForm (Matrix.of fun a b => Hm (e a) (e b)) z z := by
      rw [GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau.hermForm_eq_sum, GlobalTheory.CompanionTheory.Ar.Flat.RiemannTau.hermForm_eq_sum]
      have h1 : ∀ j, ty j ≠ σ → ∑ k, w j * Hm j k * star (w k) = 0 := fun j hj => by
        simp [hw0 j hj]
      rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.sum_type ty σ e _ h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 : ∀ k, ty k ≠ σ → w (e a) * Hm (e a) k * star (w k) = 0 := fun k hk => by
        simp [hw0 k hk]
      rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.sum_type ty σ e _ h2]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [hw]
    rw [← key]
    exact hpos w hwz

theorem GlobalTheory.CompanionTheory.Ar.Fl.signature_tau_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (p q : ℕ) (X : Fin p ⊕ Fin q → D.La) (τ : E →+* ℂ), IsPeriod D ty P → IsTypeFn H p q ty → LinearIndependent (𝓞 E) X → p + q = D.p + D.q → τ (H.rt : E) = H.rt0 → ((gramE D X).map fun a => Complex.I * τ a).IsHermitian ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ).PosDef) ∧ ∃ C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ, (-(C * ((gramE D X).map fun a => Complex.I * τ a) * Cᴴ)).PosDef := by
  intro E _ _ _ H D g ty P p q X τ hP hT hX hpq hτ
  obtain ⟨-, -, -, -, Hm, hH, hpos, hEF⟩ := id hP
  obtain ⟨-, hcomp, hC⟩ := GlobalTheory.CompanionTheory.Ar.Flat.riemann_tau_component E H D g ty P Hm hP hH hEF
  have hτc : ComplexEmbedding.conjugate τ (H.rt : E) ≠ H.rt0 := by
    rw [ComplexEmbedding.conjugate_coe_eq, hτ]
    exact GlobalTheory.CompanionTheory.Ar.Fl.SignTau.conj_cmHostRoot_ne_self H
  let e₁ : Fin p ≃ {i // ty i = τ} := (Finite.equivFinOfCardEq ((hT τ).1 hτ)).symm
  let e₂ : Fin q ≃ {i // ty i = ComplexEmbedding.conjugate τ} :=
    (Finite.equivFinOfCardEq ((hT (ComplexEmbedding.conjugate τ)).2 hτc)).symm
  let G₁ : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun a b => Hm (e₁ a) (e₁ b)
  let G₂ : Matrix (Fin q) (Fin q) ℂ := (Matrix.of fun a b => Hm (e₂ a) (e₂ b))ᵀ
  let A : Matrix (Fin p ⊕ Fin q) (Fin p) ℂ := Matrix.of fun m a => P (X m) (e₁ a)
  let B : Matrix (Fin p ⊕ Fin q) (Fin q) ℂ := Matrix.of fun m b => star (P (X m) (e₂ b))
  have h₁ : G₁.PosDef := posDef_reindex_of_hermForm_re_pos ty τ e₁ Hm hH hpos
  have h₂ : G₂.PosDef := (posDef_reindex_of_hermForm_re_pos ty (ComplexEmbedding.conjugate τ) e₂ Hm hH hpos).transpose
  have hfac : (2 : ℂ) • ((gramE D X).map fun a => Complex.I * τ a) =
      Matrix.fromCols A B * Matrix.fromBlocks G₁ 0 0 (-G₂) * (Matrix.fromCols A B)ᴴ := by
    rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.fromCols_block]
    ext m n
    have key := hcomp τ (X m) (X n)
    rw [GlobalTheory.CompanionTheory.Ar.Fl.SignTau.hermForm_tyPart ty τ e₁,
      GlobalTheory.CompanionTheory.Ar.Fl.SignTau.hermForm_tyPart ty (ComplexEmbedding.conjugate τ) e₂] at key
    have hA : (A * G₁ * Aᴴ) m n =
        ∑ a, ∑ b, P (X m) (e₁ a) * Hm (e₁ a) (e₁ b) * star (P (X n) (e₁ b)) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, A, G₁, Finset.sum_mul]
      rw [Finset.sum_comm]
    have hB : (B * G₂ * Bᴴ) m n =
        star (∑ a, ∑ b, P (X m) (e₂ a) * Hm (e₂ a) (e₂ b) * star (P (X n) (e₂ b))) := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply, B, G₂,
        Finset.sum_mul, star_sum, star_mul', star_star]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hH.apply]
    rw [Matrix.sub_apply, hA, hB, key]
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [show gramE D X m n = sesq D (X m) (X n) from rfl]
    ring
  have hdetA : (gramE D X).det ≠ 0 := hC 0 (Fin p ⊕ Fin q) X (by simp [hpq]) hX
  have hdetM : ((gramE D X).map fun a => Complex.I * τ a).det ≠ 0 := by
    have hM' : ((gramE D X).map fun a => Complex.I * τ a) = Complex.I • (τ.mapMatrix (gramE D X)) := by
      ext m n
      simp [Matrix.map_apply]
    rw [hM', Matrix.det_smul, ← RingHom.map_det]
    exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) ((map_ne_zero τ).mpr hdetA)
  exact GlobalTheory.CompanionTheory.Ar.Fl.SignTau.signature_of_factor _ (Matrix.fromCols A B) G₁ G₂ h₁ h₂ hfac hdetM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackOfGluedChartsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_of_glued_charts : ∀ {P X Y' : Scheme.{0}} (a b : P ⟶ X) (π : X ⟶ Y') {J : Type} (V : J → X.Opens) (Y : J → Scheme.{0}) (q : ∀ j, (V j).toScheme ⟶ Y j) (em : ∀ j, Y j ⟶ Y') [∀ j, IsOpenImmersion (em j)], (∀ j, IsChart a b (V j) (q j)) → (∀ j, (V j).ι ≫ π = q j ≫ em j) → (∀ j, π ⁻¹ᵁ (em j).opensRange = V j) → (∀ y : Y', ∃ j, ∃ z : Y j, em j z = y) → IsPullback a b π π := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_isChart | exact GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_isChart | (intros; apply GlobalTheory.CompanionTheory.FreeQuotGlue.isPullback_of_isChart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StableHopfOrderSubgroupGenerationStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_hopf_order_subgroup_generation : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → idealX AA.carrier K t τ ≤ idealD p AA.carrier K t τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.idealX_le_idealD | exact GlobalTheory.CompanionTheory.Ar.GR.idealX_le_idealD | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.idealX_le_idealD <;> assumption)
end

