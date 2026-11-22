import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalitySubgroupMeasureOne
section
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.SchurOrthOnSubgroup

theorem setIntegral_subgroup_mul_left {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Ω : Subgroup G) (hΩ : MeasurableSet (Ω : Set G))
    (f : G → ℂ) {h : G} (hh : h ∈ Ω) :
    ∫ g in (Ω : Set G), f (h * g) ∂ν = ∫ g in (Ω : Set G), f g ∂ν := by
  rw [← integral_indicator hΩ, ← integral_indicator hΩ]
  have : (Ω : Set G).indicator (fun g => f (h * g)) = fun g => (Ω : Set G).indicator f (h * g) := by
    funext g
    by_cases hg : g ∈ Ω
    · have hg' : h * g ∈ Ω := Ω.mul_mem hh hg
      simp [Set.indicator_of_mem, hg, hg']
    · have hg' : h * g ∉ Ω := fun H => hg ((Ω.mul_mem_cancel_left hh).1 H)
      simp [Set.indicator_of_notMem, hg, hg']
  rw [this, integral_mul_left_eq_self]

variable {G : Type} [Group G] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem rep_apply_inv_apply (ρ : G →* Module.End ℂ W) (g : G) (v : W) : ρ g (ρ g⁻¹ v) = v := by
  show (ρ g * ρ g⁻¹) v = v
  rw [← map_mul, mul_inv_cancel, map_one]; rfl

theorem inner_rep_inv (ρ : G →* Module.End ℂ W) (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) (x y : W) : ⟪ρ g⁻¹ x, y⟫_ℂ = ⟪x, ρ g y⟫_ℂ := by
  rw [← hU g (ρ g⁻¹ x) y, rep_apply_inv_apply]

theorem inner_rep_inv' (ρ : G →* Module.End ℂ W) (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) (x y : W) : ⟪x, ρ g⁻¹ y⟫_ℂ = ⟪ρ g x, y⟫_ℂ := by
  rw [← hU g x (ρ g⁻¹ y), rep_apply_inv_apply]

theorem norm_rep (ρ : G →* Module.End ℂ W) (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) (v : W) : ‖ρ g v‖ = ‖v‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hU]

end GlobalTheory.SchurOrthOnSubgroup

namespace GlobalTheory.SchurOrthOnSubgroup

theorem schur_orthogonality {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Ω : Subgroup G) (hΩ : MeasurableSet (Ω : Set G))
    (hν : ν (Ω : Set G) = 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : G →* Module.End ℂ W)
    (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hM : ∀ x y : W, Measurable fun g => ⟪x, ρ g y⟫_ℂ)
    (hirr : ∀ U : Submodule ℂ W, (∀ g ∈ Ω, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤)
    (a a' x x' : W) :
    IntegrableOn (fun g => star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ) Ω ν ∧
      (Module.finrank ℂ W : ℂ) * ∫ g in (Ω : Set G), star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ ∂ν
        = ⟪a', a⟫_ℂ * ⟪x, x'⟫_ℂ := by

  set F : W → W → G → ℂ := fun y y' g => star ⟪a, ρ g⁻¹ y⟫_ℂ * ⟪a', ρ g⁻¹ y'⟫_ℂ with hF
  have hfin : ν (Ω : Set G) < ⊤ := by rw [hν]; exact ENNReal.one_lt_top
  have hint : ∀ y y', IntegrableOn (F y y') Ω ν := by
    intro y y'
    have hmeas : Measurable (F y y') := by
      have h1 : Measurable fun g : G => ⟪a, ρ g⁻¹ y⟫_ℂ := (hM a y).comp measurable_inv
      have h2 : Measurable fun g : G => ⟪a', ρ g⁻¹ y'⟫_ℂ := (hM a' y').comp measurable_inv
      exact (continuous_star.measurable.comp h1).mul h2
    refine Integrable.mono' (g := fun _ => (‖a‖ * ‖y‖) * (‖a'‖ * ‖y'‖)) ?_
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    · exact integrableOn_const hfin.ne
    · simp only [hF, norm_mul, norm_star]
      gcongr
      · exact (norm_inner_le_norm _ _).trans (by rw [norm_rep ρ hU])
      · exact (norm_inner_le_norm _ _).trans (by rw [norm_rep ρ hU])
  refine ⟨hint x x', ?_⟩

  set B : W → W → ℂ := fun y y' => ∫ g in (Ω : Set G), F y y' g ∂ν with hB
  let b := stdOrthonormalBasis ℂ W
  have hBadd : ∀ y y1 y2, B y (y1 + y2) = B y y1 + B y y2 := by
    intro y y1 y2
    simp only [hB]
    rw [← integral_add (hint y y1) (hint y y2)]
    congr 1; funext g
    simp only [hF, map_add, inner_add_right, mul_add]
  have hBsmul : ∀ y (c : ℂ) y', B y (c • y') = c * B y y' := by
    intro y c y'
    simp only [hB]
    rw [← integral_const_mul]
    congr 1; funext g
    simp only [hF, map_smul, inner_smul_right]; ring
  have hBexp : ∀ y y', B y y' = ∑ i, ⟪y, b i⟫_ℂ * B (b i) y' := by
    intro y y'
    simp only [hB]
    simp_rw [← integral_const_mul]
    rw [← integral_finset_sum _ (fun i _ => (hint (b i) y').const_mul _)]
    congr 1; funext g
    simp only [hF]
    have hs : ∀ z, star ⟪a, ρ g⁻¹ z⟫_ℂ = ⟪z, ρ g a⟫_ℂ := by
      intro z
      rw [inner_rep_inv' ρ hU]
      exact inner_conj_symm _ _
    simp_rw [hs, ← mul_assoc, ← Finset.sum_mul]
    rw [b.sum_inner_mul_inner]
  have hBinv : ∀ h ∈ Ω, ∀ y y', B (ρ h y) (ρ h y') = B y y' := by
    intro h hh y y'
    simp only [hB]
    rw [← setIntegral_subgroup_mul_left ν Ω hΩ (F y y') (Ω.inv_mem hh)]
    congr 1; funext g
    have hg : ∀ z, ρ g⁻¹ (ρ h z) = ρ (h⁻¹ * g)⁻¹ z := by
      intro z
      rw [mul_inv_rev, inv_inv, map_mul]; rfl
    simp only [hF, hg]

  let T : W →ₗ[ℂ] W :=
    { toFun := fun y' => ∑ i, B (b i) y' • b i
      map_add' := by
        intro y1 y2
        simp only [hBadd, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c y'
        simp only [hBsmul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
  have hT : ∀ y y', ⟪y, T y'⟫_ℂ = B y y' := by
    intro y y'
    rw [hBexp y y']
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right]
    congr 1; funext i; ring
  have hcomm : ∀ h ∈ Ω, ∀ v, T (ρ h v) = ρ h (T v) := by
    intro h hh v
    apply ext_inner_left ℂ
    intro y
    rw [hT, ← inner_rep_inv ρ hU, hT]
    conv_lhs => rw [← rep_apply_inv_apply ρ h y]
    exact hBinv h hh _ _
  have hsum : ∑ i, B (b i) (b i) = ⟪a', a⟫_ℂ := by
    simp only [hB]
    rw [← integral_finset_sum _ (fun i _ => hint (b i) (b i))]
    have : ∀ g, ∑ i, F (b i) (b i) g = ⟪a', a⟫_ℂ := by
      intro g
      simp only [hF]
      have hs : ∀ z, star ⟪a, ρ g⁻¹ z⟫_ℂ = ⟪z, ρ g a⟫_ℂ := by
        intro z
        rw [inner_rep_inv' ρ hU]
        exact inner_conj_symm _ _
      simp_rw [hs, inner_rep_inv' ρ hU]
      simp_rw [mul_comm (⟪b _, ρ g a⟫_ℂ)]
      rw [b.sum_inner_mul_inner, hU]
    simp_rw [this]
    rw [setIntegral_const, Measure.real, hν]
    simp
  rcases subsingleton_or_nontrivial W with hW | hW
  · have ha : a = 0 := Subsingleton.elim _ _
    simp [Module.finrank_zero_of_subsingleton, ha]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T : Module.End ℂ W)
  have hU' : Module.End.eigenspace (T : Module.End ℂ W) c = ⊤ := by
    rcases hirr (Module.End.eigenspace (T : Module.End ℂ W) c) (by
      intro g hg
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
      rw [Module.End.mem_eigenspace_iff, hcomm g hg, hv, map_smul]) with h0 | h0
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have : v ∈ Module.End.eigenspace (T : Module.End ℂ W) c := hv.1
      rw [h0, Submodule.mem_bot] at this
      exact hv.2 this
    · exact h0
  have hTc : ∀ v, T v = c • v := fun v =>
    Module.End.mem_eigenspace_iff.1 (hU' ▸ Submodule.mem_top)
  have hBc : ∀ y y', B y y' = c * ⟪y, y'⟫_ℂ := by
    intro y y'
    rw [← hT, hTc, inner_smul_right]
  have hnc : (Module.finrank ℂ W : ℂ) * c = ⟪a', a⟫_ℂ := by
    rw [← hsum]
    have h1 : ∀ i, ⟪b i, b i⟫_ℂ = 1 := fun i => by
      simpa using orthonormal_iff_ite.1 b.orthonormal i i
    simp only [hBc, h1, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  show (Module.finrank ℂ W : ℂ) * B x x' = _
  rw [hBc, ← mul_assoc, hnc]

end GlobalTheory.SchurOrthOnSubgroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanValuationLe
section
namespace GlobalTheory.SpanValuationBound

open IsDedekindDomain

theorem span_valuation_le {L : Type} [Field L] [NumberField L] {S : Set L}
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) {γ : WithZero (Multiplicative ℤ)}
    (hS : ∀ x ∈ S, (HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ) :
    ∀ x ∈ Submodule.span (NumberField.RingOfIntegers L) S,
      (HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => simp
  | add y z _ _ hy hz =>
    exact le_trans (Valuation.map_add _ y z) (max_le hy hz)
  | smul a y _ hy =>
    rw [Algebra.smul_def, map_mul]
    calc (HeightOneSpectrum.valuation L w) (algebraMap _ L a) * (HeightOneSpectrum.valuation L w) y
        ≤ 1 * γ := mul_le_mul' (HeightOneSpectrum.valuation_le_one w a) hy
      _ = γ := one_mul γ

theorem main : ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {S : Set L} (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {γ : WithZero (Multiplicative ℤ)}, (∀ x ∈ S, (IsDedekindDomain.HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ) → ∀ x ∈ Submodule.span (NumberField.RingOfIntegers L) S, (IsDedekindDomain.HeightOneSpectrum.valuation L w : L → WithZero (Multiplicative ℤ)) x ≤ γ :=
  @fun _ _ _ _ w _ h => span_valuation_le w h

end GlobalTheory.SpanValuationBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace GlobalTheory.LocalRingGeneralisation

theorem flat_fromSpecStalk (X : Scheme.{0}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU]
  change Flat (Spec.map (X.presheaf.germ U x hxU) ≫ hU.fromSpec)
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have h₂ : IsOpenImmersion (IsAffineOpen.fromSpec hU) := IsAffineOpen.isOpenImmersion_fromSpec hU
  have h₃ : Flat (IsAffineOpen.fromSpec hU) := inferInstance
  exact MorphismProperty.comp_mem @Flat _ _ this h₃

theorem isIso_stalkMap_fromSpecStalk (X : Scheme.{0}) (x : X) (y : Spec (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap y) := by
  have := flat_fromSpecStalk X x
  have hs : SurjectiveOnStalks (X.fromSpecStalk x) := inferInstance
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, (X.fromSpecStalk x).stalkMap_surjective y⟩
  have hl : IsLocalHom ((X.fromSpecStalk x).stalkMap y).hom := inferInstance
  have h := Flat.stalkMap (X.fromSpecStalk x) y
  algebraize [((X.fromSpecStalk x).stalkMap y).hom]
  have : IsLocalHom (algebraMap (X.presheaf.stalk ((X.fromSpecStalk x) y))
    ((Spec (X.presheaf.stalk x)).presheaf.stalk y)) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk ((X.fromSpecStalk x) y)) (B := (Spec (X.presheaf.stalk x)).presheaf.stalk y)
  exact FaithfulSMul.algebraMap_injective _ _

theorem exists_stalk_equiv_localization : ∀ {X : Scheme.{0}} (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime], ∃ (q : X) (e : X.presheaf.stalk q ≃+* Localization.AtPrime p), q ⤳ x ∧ ∀ (U : X.Opens) (hq : q ∈ U) (hx : x ∈ U) (s : Γ(X, U)), e ((X.presheaf.germ U q hq).hom s) = algebraMap (X.presheaf.stalk x) (Localization.AtPrime p) ((X.presheaf.germ U x hx).hom s) := by
  intro X x p _
  let y : Spec (X.presheaf.stalk x) := (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))
  have := isIso_stalkMap_fromSpecStalk X x y
  refine ⟨X.fromSpecStalk x y,
    (asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_, ?_⟩
  · have : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  · intro U hq hx s
    have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
    show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
    rw [h1, Scheme.fromSpecStalk_app hx]
    have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
      (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
      Iso.inv_hom_id, CommRingCat.id_apply] at h2
    rw [← h2]
    simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
    erw [TopCat.Presheaf.germ_res]

end GlobalTheory.LocalRingGeneralisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubrepTopToSubmodule
section
namespace GlobalTheory.SubrepTopBot

open Representation

theorem subrep_bot_toSubmodule {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

theorem subrep_top_toSubmodule {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

theorem main : ∀ {G : Type} [inst : Group G] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] (ρ : Representation ℂ G V), Representation.IsIrreducible ρ ↔ Nontrivial V ∧ ∀ (U : Submodule ℂ V), (∀ (g : G), ∀ v ∈ U, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro G _ V _ _ ρ
  have hbot := subrep_bot_toSubmodule ρ
  have htop := subrep_top_toSubmodule ρ
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
      rw [← Submodule.nontrivial_iff ℂ]
      refine ⟨⟨⊥, ⊤, fun e => hne ?_⟩⟩
      apply Subrepresentation.toSubmodule_injective
      rw [hbot, htop]; exact e
    · intro U hU
      let S : Subrepresentation ρ := ⟨U, fun g v hv => hU g v hv⟩
      rcases h.eq_bot_or_eq_top S with e | e
      · left
        have := congrArg Subrepresentation.toSubmodule e
        rw [hbot] at this; exact this
      · right
        have := congrArg Subrepresentation.toSubmodule e
        rw [htop] at this; exact this
  · rintro ⟨hV, hU⟩
    haveI : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⟨⊥, ⊤, fun e => ?_⟩⟩
      have := congrArg Subrepresentation.toSubmodule e
      rw [hbot, htop] at this
      exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) this
    refine { eq_bot_or_eq_top := ?_ }
    intro S
    rcases hU S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e
    · left; apply Subrepresentation.toSubmodule_injective; rw [hbot]; exact e
    · right; apply Subrepresentation.toSubmodule_injective; rw [htop]; exact e

end GlobalTheory.SubrepTopBot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem sum_log_embedding_add_finsum_log_adicAbv_eq_zero
    (F : Type) [Field F] [NumberField F] (N : F) (hN : N ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
        Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)).Finite ∧
      (∑ σ : F →+* ℂ, Real.log ‖σ N‖) +
        ∑ᶠ v : HeightOneSpectrum (𝓞 F),
          Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) = 0 := by
  have hfun : (fun v : HeightOneSpectrum (𝓞 F) => NumberField.HeightOneSpectrum.adicAbv F v N) =
      (fun w : FinitePlace F => w N) ∘ (FinitePlace.equivHeightOneSpectrum (K := F)).symm := by
    funext v
    simp only [Function.comp, FinitePlace.equivHeightOneSpectrum_symm_apply,
      FinitePlace.norm_embedding]
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      NumberField.HeightOneSpectrum.adicAbv F v N).Finite := by
    rw [hfun, Function.mulSupport_comp_eq_preimage]
    exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
      (FinitePlace.hasFiniteMulSupport hN)
  have hpos : ∀ v : HeightOneSpectrum (𝓞 F), 0 < NumberField.HeightOneSpectrum.adicAbv F v N :=
    fun v => (NumberField.HeightOneSpectrum.adicAbv F v).pos hN
  have hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v N =
      ((|Algebra.norm ℚ N|⁻¹ : ℚ) : ℝ) := by
    rw [← FinitePlace.prod_eq_inv_abs_norm hN,
      ← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm]
    exact congrArg finprod hfun
  have hsub : (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v N)) ⊆ hfin.toFinset := by
    intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h
    exact hv (by simp only [h, Real.log_one])
  refine ⟨hfin.toFinset.finite_toSet.subset hsub, ?_⟩
  have h1 : ∑ᶠ v : HeightOneSpectrum (𝓞 F),
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v N) =
      - Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
    rw [finsum_eq_sum_of_support_subset _ hsub, ← Real.log_prod (fun v _ => (hpos v).ne'),
      ← finprod_eq_prod_of_mulSupport_subset _ (by simp), hprod, Rat.cast_inv, Real.log_inv]
  have h2 : ∑ σ : F →+* ℂ, Real.log ‖σ N‖ = Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
    have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ N)
    simp only [norm_prod] at h
    rw [← Real.log_prod (fun σ _ => by simpa using hN)]
    congr 1
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun σ : F →+* ℂ => ‖σ N‖)
      (fun σ : F →ₐ[ℚ] ℂ => ‖σ N‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]
    simp [← Complex.norm_ratCast]
  rw [h1, h2, add_neg_cancel]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoOfForallIntegral
section
namespace GlobalTheory.TendstoOfIntegrals

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Topology

theorem tendsto_of_forall_integral {L : Type} [Field L] [NumberField L] {ι : Type} {l : Filter ι}
    (f : ι → FiniteAdeleRing (NumberField.RingOfIntegers L) L)
    (b : FiniteAdeleRing (NumberField.RingOfIntegers L) L)
    (hf : ∀ (i : ι) (v : HeightOneSpectrum (NumberField.RingOfIntegers L)),
      (f i : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v ∈
        v.adicCompletionIntegers L)
    (hb : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers L),
      (b : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v ∈
        v.adicCompletionIntegers L)
    (hl : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers L),
      Tendsto (fun i ↦ (f i : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) →
        a.adicCompletion L) v) l
        (𝓝 ((b : (a : HeightOneSpectrum (NumberField.RingOfIntegers L)) → a.adicCompletion L) v))) :
    Tendsto f l (𝓝 b) := by

  let A : (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → Set (v.adicCompletion L) :=
    fun v ↦ (v.adicCompletionIntegers L : Set (v.adicCompletion L))
  let g : ι → (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → A v :=
    fun i v ↦ ⟨_, hf i v⟩
  let c : (v : HeightOneSpectrum (NumberField.RingOfIntegers L)) → A v := fun v ↦ ⟨_, hb v⟩
  have hg : Tendsto g l (𝓝 c) :=
    tendsto_pi_nhds.2 fun v ↦ tendsto_subtype_rng.2 (hl v)
  have hemb := RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (NumberField.RingOfIntegers L) ↦ v.adicCompletion L)
    (A := A) (𝓕 := cofinite)
  exact (hemb.continuous.tendsto c).comp hg

end GlobalTheory.TendstoOfIntegrals

theorem GlobalTheory.TendstoOfIntegrals.target_check : ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {ι : Type} {l : Filter ι} (f : ι → IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers L) L) (b : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers L) L), (∀ (i : ι) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), (f i : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers L v) → (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), (b : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers L v) → (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)), Filter.Tendsto (fun (i : ι) ↦ (f i : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v) l (nhds ((b : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion L a) v))) → Filter.Tendsto f l (nhds b) := by
  intro L _ _ ι l f b hf hb hl
  exact GlobalTheory.TendstoOfIntegrals.tendsto_of_forall_integral f b hf hb hl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorDomainBirational
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem flat_baseChange_birational_isDomain_and_includeRight_injective
    (A B R : Type) [CommRing A] [CommRing B] [IsDomain B] [CommRing R] [IsDomain R]
    [Algebra A B] [Algebra A R] [Module.Flat A R]
    (_hAB : Function.Injective (algebraMap A B))
    (hfrac : ∀ b : B, ∃ a s : A, algebraMap A B s ≠ 0 ∧ algebraMap A B s * b = algebraMap A B a) :
    IsDomain (TensorProduct A B R) ∧
      Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by

  have hinc : Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by
    have hcomp : ∀ r : R, (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) r =
        (LinearMap.rTensor R (Algebra.linearMap A B)) ((TensorProduct.lid A R).symm r) := by
      intro r
      simp [Algebra.TensorProduct.includeRight_apply]
    intro r r' h
    rw [hcomp, hcomp] at h
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := R) (Algebra.linearMap A B) _hAB h
    exact (TensorProduct.lid A R).symm.injective h1

  have hmove : ∀ (a : A) (r : R), (algebraMap A B a) ⊗ₜ[A] r = (1 : B) ⊗ₜ[A] (algebraMap A R a * r) := by
    intro a r
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]

  have hmulInj : ∀ c : B, c ≠ 0 → ∀ x : TensorProduct A B R, (c ⊗ₜ[A] (1 : R)) * x = 0 → x = 0 := by
    intro c hc x hx
    have heq : ∀ y : TensorProduct A B R, (c ⊗ₜ[A] (1 : R)) * y =
        (LinearMap.rTensor R (LinearMap.mulLeft A c)) y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b r => simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add y z hy hz => rw [mul_add, map_add, hy, hz]
    have hinjc : Function.Injective (LinearMap.mulLeft A c) := by
      intro u v huv
      exact mul_left_cancel₀ hc huv
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := R) _ hinjc
    apply this
    rw [← heq, hx, map_zero]

  have hden : ∀ x : TensorProduct A B R, ∃ s : A, algebraMap A B s ≠ 0 ∧
      ∃ r : R, (algebraMap A B s ⊗ₜ[A] (1 : R)) * x = (1 : B) ⊗ₜ[A] r := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨1, by simp, 0, by simp⟩
    | tmul b r =>
      obtain ⟨a, s, hs, hsb⟩ := hfrac b
      refine ⟨s, hs, algebraMap A R a * r, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul, hsb, one_mul, hmove]
    | add x y hx hy =>
      obtain ⟨s, hs, r, hr⟩ := hx
      obtain ⟨s', hs', r', hr'⟩ := hy
      refine ⟨s * s', by rw [map_mul]; exact mul_ne_zero hs hs',
        algebraMap A R s' * r + algebraMap A R s * r', ?_⟩
      have e1 : (algebraMap A B (s * s') ⊗ₜ[A] (1 : R)) =
          (algebraMap A B s' ⊗ₜ[A] (1 : R)) * (algebraMap A B s ⊗ₜ[A] (1 : R)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul, mul_comm]
      have e2 : (algebraMap A B (s * s') ⊗ₜ[A] (1 : R)) =
          (algebraMap A B s ⊗ₜ[A] (1 : R)) * (algebraMap A B s' ⊗ₜ[A] (1 : R)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
      rw [mul_add]
      conv_lhs => arg 1; rw [e1, mul_assoc, hr]
      conv_lhs => arg 2; rw [e2, mul_assoc, hr']
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one,
        hmove, hmove, one_mul, one_mul, ← TensorProduct.tmul_add]

  haveI : Nontrivial (TensorProduct A B R) := by
    refine ⟨⟨Algebra.TensorProduct.includeRight (1 : R), Algebra.TensorProduct.includeRight (0 : R), ?_⟩⟩
    intro h
    exact one_ne_zero (hinc h)
  haveI : NoZeroDivisors (TensorProduct A B R) := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨s, hs, r, hr⟩ := hden x
    obtain ⟨s', hs', r', hr'⟩ := hden y
    have hprod : (1 : B) ⊗ₜ[A] (r * r') = 0 := by
      have : ((algebraMap A B s ⊗ₜ[A] (1 : R)) * x) * ((algebraMap A B s' ⊗ₜ[A] (1 : R)) * y) = 0 := by
        rw [mul_mul_mul_comm, hxy, mul_zero]
      rw [hr, hr', Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
      exact this
    have hrr : r * r' = 0 := by
      apply hinc
      rw [map_zero, Algebra.TensorProduct.includeRight_apply]
      exact hprod
    rcases mul_eq_zero.mp hrr with h0 | h0
    · left
      apply hmulInj _ hs
      rw [hr, h0, TensorProduct.tmul_zero]
    · right
      apply hmulInj _ hs'
      rw [hr', h0, TensorProduct.tmul_zero]
  exact ⟨NoZeroDivisors.to_isDomain _, hinc⟩

end GlobalTheory
end

