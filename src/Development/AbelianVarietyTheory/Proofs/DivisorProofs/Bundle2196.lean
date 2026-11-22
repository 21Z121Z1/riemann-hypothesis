import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0107
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0115
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0165
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0121
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0046
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0018
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveField
section
noncomputable section

namespace GlobalTheory.FixedPoint

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompRat GlobalTheory.CompRat.FixedConst
  GlobalTheory.AllWt GlobalTheory.FlatLine

theorem exists_descent {Y : Scheme.{0}} (K : IntermediateField ℚ ℂ) (x : Sp ℂ ⟶ Y)
    (hx : ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ K, τ a = a) → spMap (τ : ℂ →+* ℂ) ≫ x = x) :
    ∃ g : Sp K ⟶ Y, spMap (algebraMap K ℂ) ≫ g = x := by
  classical
  obtain ⟨⟨y, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField ℂ Y).symm.surjective x
  have hfix : ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ K, τ a = a) → φ ≫ CommRingCat.ofHom (τ : ℂ →+* ℂ) = φ := by
    intro τ hτ
    have e : spMap (τ : ℂ →+* ℂ) ≫ (Scheme.SpecToEquivOfField ℂ Y).symm ⟨y, φ⟩ =
        (Scheme.SpecToEquivOfField ℂ Y).symm ⟨y, φ ≫ CommRingCat.ofHom (τ : ℂ →+* ℂ)⟩ := by
      change Spec.map _ ≫ Spec.map φ ≫ _ = Spec.map (φ ≫ _) ≫ _
      rw [Spec.map_comp, Category.assoc]
    have h2 := (Scheme.SpecToEquivOfField ℂ Y).symm.injective (e.symm.trans (hx τ hτ))
    exact eq_of_heq (Sigma.mk.inj_iff.mp h2).2
  have hmem : ∀ r, φ.hom r ∈ K := by
    intro r
    obtain ⟨a, ha⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := K) (φ.hom r) (fun σ => by
      have h := hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩)
      exact congrArg (fun f => f.hom r) h)
    rw [← ha]
    exact a.2
  let ψ : Y.residueField y →+* K := φ.hom.codRestrict K hmem
  refine ⟨Spec.map (CommRingCat.ofHom ψ : Y.residueField y ⟶ CommRingCat.of K) ≫ Y.fromSpecResidueField y, ?_⟩
  have hc : (CommRingCat.ofHom ψ : Y.residueField y ⟶ CommRingCat.of K) ≫ CommRingCat.ofHom (algebraMap K ℂ) = φ := by
    ext r
    rfl
  exact (Spec.map_comp_assoc _ _ _).symm.trans (congrArg (· ≫ Y.fromSpecResidueField y) (congrArg Spec.map hc))

theorem ev_eq_of_restrict {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (W : Y.Opens) (p : Sp ℂ) (hp : x p ∈ W) (f : Γ(Y, ⊤))
    (n : ℕ) (hf : Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op f = n) : ev x f = n := by
  have hr : Set.range x ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q p]
  have hf' : (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom f = n := hf
  have hle : W.ι ''ᵁ ⊤ ≤ W := (Scheme.Opens.ι_image_top W).le
  have e : (homOfLE (le_top : W.ι ''ᵁ ⊤ ≤ ⊤)).op = (homOfLE (le_top : W ≤ ⊤)).op ≫ (homOfLE hle).op := rfl
  have key : (Y.presheaf.map (homOfLE (le_top : W.ι ''ᵁ ⊤ ≤ ⊤)).op).hom f = n := by
    rw [e, Functor.map_comp]
    exact (congrArg (Y.presheaf.map (homOfLE hle).op).hom hf').trans (map_natCast _ n)
  rw [← IsOpenImmersion.lift_fac W.ι x hr, ev_comp, Scheme.Opens.ι_appTop]
  exact (congrArg _ key).trans (map_natCast _ n)

theorem exists_indicator {Y : Scheme.{0}} {Z : Set Y} (hZ : IsClopen Z) :
    ∃ f : Γ(Y, ⊤), ∀ (x : Sp ℂ ⟶ Y) (p : Sp ℂ), (x p ∈ Z → ev x f = 1) ∧ (x p ∉ Z → ev x f = 0) := by
  let V : Y.Opens := ⟨Z, hZ.isOpen⟩
  let W : Y.Opens := ⟨Zᶜ, hZ.isClosed.isOpen_compl⟩
  have hVW : V ⊔ W = ⊤ := by
    apply TopologicalSpace.Opens.ext
    simp [V, W, Set.union_compl_self]
  have hdis : Disjoint V W := by
    rw [disjoint_iff]
    apply TopologicalSpace.Opens.ext
    simp [V, W]
  obtain ⟨f, hfV, hfW⟩ := exists_extension_zero V W hVW hdis 1
  refine ⟨f, fun x p => ⟨fun hp => ?_, fun hp => ?_⟩⟩
  · have h := ev_eq_of_restrict x V p hp f 1 (by rw [hfV, Nat.cast_one])
    simpa using h
  · have h := ev_eq_of_restrict x W p hp f 0 (by rw [hfW, Nat.cast_zero])
    simpa using h

private theorem exists_isTypeFn' {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q : ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))
  refine ⟨_, fun i => (e.symm i).1, fun τ => ?_⟩
  have hcard : Nat.card {i // (e.symm i).1 = τ} = m τ := by
    rw [Nat.card_congr (e.symm.subtypeEquiv (p := fun i => (e.symm i).1 = τ) (q := fun s => s.1 = τ)
      (fun _ => Iff.rfl)), Nat.card_congr (Equiv.sigmaSubtype τ), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]; simp [m, h]
  · rw [hcard]; simp [m, h]

private theorem spMap_comp_spMap_divisor {R₀ R R' : Type} [CommRing R₀] [CommRing R] [CommRing R'] (f : R →+* R')
    (g : R₀ →+* R) : spMap f ≫ spMap g = spMap (f.comp g) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_fixed_point (hD : 1 ≤ Dw.p + Dw.q)
    (hsig : Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) (Z : Comp Xo c) :
    ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ strK = spMap (algebraMap c.F ℂ) ∧ (∀ p, x p ∈ (Z : Set (Xo.XF c))) ∧
      ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ c.F, τ a = a) → FixesCurve H τ l.M' → spMap (τ : ℂ →+* ℂ) ≫ x = x := by
  classical
  obtain ⟨g, ty, hty⟩ := exists_isTypeFn' H Dw.p Dw.q
  let σ₀ : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  have hσ₀ : σ₀ (baseKA l).ρ = H.rt0 := rfl
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H Dw l Xo σ₀ g ty hD hσ₀ hty

  obtain ⟨L, _, _, j, g₀, hg₀, hZ₀⟩ := GlobalTheory.FlatLine.exists_numberField_point Z
  letI : Algebra c.F L := j.toAlgebra
  haveI : IsScalarTower ℚ c.F L := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ c.F), eq_ratCast (algebraMap ℚ L), map_ratCast])
  haveI : Algebra.IsAlgebraic c.F L := Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let φ : L →ₐ[c.F] ℂ := IsAlgClosed.lift
  have hφ : (φ : L →+* ℂ).comp j = algebraMap c.F ℂ := RingHom.ext fun a => φ.commutes a
  obtain ⟨hx₀, hZx₀⟩ := GlobalTheory.FlatLine.point_ext hg₀ hZ₀ (φ : L →+* ℂ)
  rw [hφ] at hx₀
  set x₀ : Sp ℂ ⟶ Xo.XF c := spMap (φ : L →+* ℂ) ≫ g₀ with hx₀def
  have hover : x₀ ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap σ₀ := by
    rw [pullback.condition, ← Category.assoc]
    erw [hx₀]
    rw [spMap_comp_spMap_divisor]
  obtain ⟨i, P, hP, hPx⟩ := F.onto _ (by rw [Category.assoc]; exact hover)
  obtain ⟨P', hP', hs⟩ := GlobalTheory.CompRat.exists_isSplit_period_anyLevel E H Dw l Xo σ₀ g ty F hD hσ₀ hty hsig i
  have hcond : F.u i P' ≫ Xo.s = spMap (algebraMap c.F ℂ) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [F.over_σ i P' hP', spMap_comp_spMap_divisor]
  let xs : Sp ℂ ⟶ Xo.XF c := pullback.lift (F.u i P') (spMap (algebraMap c.F ℂ)) hcond
  have hxs₁ : xs ≫ pullback.fst _ _ = F.u i P' := pullback.lift_fst _ _ _
  have hxs₂ : xs ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) := pullback.lift_snd _ _ _

  obtain ⟨f, hf⟩ := exists_indicator (GlobalTheory.TrivOrderTieCompare.isClopen_comp Z)
  have hvals : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      valAt' x ⊤ f ∈ ({0, 1} : Set ℂ) := by
    intro x _
    rw [valAt'_top]
    by_cases hx : x default ∈ (Z : Set (Xo.XF c))
    · simp [(hf x default).1 hx]
    · simp [(hf x default).2 hx]
  have heq := GlobalTheory.CompRat.valAt_eq_of_finite_values_anyLevel E H Dw l Xo σ₀ g ty F hD hσ₀ hty c
    (algebraMap c.F ℂ) f _ (Set.toFinite _) hvals i P P' hP hP' x₀ xs hPx.symm hx₀ hxs₁ hxs₂
  rw [valAt'_top, valAt'_top, (hf x₀ default).1 (hZx₀ default)] at heq
  refine ⟨xs, hxs₂, fun p => ?_, fun τ hτ hfix => ?_⟩
  · by_contra hp
    rw [(hf xs p).2 hp] at heq
    exact one_ne_zero heq
  · have hτσ : (τ : ℂ →+* ℂ).comp σ₀ = σ₀ := RingHom.ext fun a => hτ _ (IntermediateField.inclusion c.le a).2
    have hfixed := GlobalTheory.CompRat.AnyLevel.conj_point_eq_of_isSplit F hD hσ₀ hty τ hτσ hfix i P' hP' hs
    apply pullback.hom_ext
    · rw [Category.assoc, hxs₁, hfixed]
    · rw [Category.assoc, hxs₂, spMap_comp_spMap_divisor]
      congr 1
      exact RingHom.ext fun a => hτ a a.2

end GlobalTheory.FixedPoint

namespace GlobalTheory.FixedPoint

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
open AlgebraicGeometry CategoryTheory

theorem exists_frPt_liesOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ (K : IntermediateField ℚ ℂ) [NumberField K] (hle : c.F ≤ K), GlobalTheory.CompRat.CurveOver H K l.M' → ∀ Z : Comp Xo c, (letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra; ∃ y : FrPt Xo c K, LiesOn Z y) := by
  intro E _ _ _ H Dw l Xo c hD hsig K _ hle hK Z
  letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  obtain ⟨x, _, hxZ, hxfix⟩ := exists_fixed_point (H := H) (Xo := Xo) (c := c) hD hsig Z
  obtain ⟨g, hg⟩ := exists_descent K x (fun τ hτ => hxfix τ (fun a ha => hτ a (hle ha)) (hK τ hτ))
  have hcancel : ∀ a b : Sp K ⟶ Sp c.F, spMap (algebraMap K ℂ) ≫ a = spMap (algebraMap K ℂ) ≫ b → a = b := by
    intro a b hab
    rw [← Spec.map_preimage a, ← Spec.map_preimage b] at hab ⊢
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at hab
    congr 1
    ext r
    exact congrArg (fun f => f.hom r) hab
  have hgK : g ≫ strK = spMap (algebraMap c.F K) := by
    apply hcancel
    rw [← Category.assoc, hg, ‹x ≫ strK = spMap (algebraMap c.F ℂ)›, spMap_comp_spMap_divisor]
    rfl
  obtain ⟨y, hy⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (g ≫ GlobalTheory.FlatLine.prX Xo c) (GlobalTheory.FlatLine.prX_over hgK)
  refine ⟨y, fun s => ?_⟩
  rw [GlobalTheory.FlatLine.ptF_eq hgK hy]
  have hs : s = spMap (algebraMap K ℂ) default := Subsingleton.elim _ _
  have h1 := hxZ default
  rw [← hg] at h1
  rw [hs]
  exact h1

end GlobalTheory.FixedPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCoverOverSizedField
section
set_option autoImplicit false

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
open GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.CovTop.SizedCover

theorem stable_of_normal (R : IntermediateField ℚ ℂ) [hN : Normal ℚ R] (s : ℂ ≃+* ℂ) (a : ℂ) (ha : a ∈ R) : s a ∈ R := by
  have h := @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ R (by convert hN; exact Subsingleton.elim _ _)
    (s.toRingHom.toRatAlgHom.comp R.val)
  exact h.le ⟨⟨a, ha⟩, rfl⟩

theorem exists_ray (hRF : GlobalTheory.NT.RayField) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n : ℕ) (hn : 3 ≤ n) :
    ∃ (R : IntermediateField ℚ ℂ) (a b : ℝ), Sz R a b ∧ a + b ≤ 20 * (Real.log n + Real.log H.d + 1) ∧
      (∀ s : ℂ ≃+* ℂ, ∀ z ∈ R, s z ∈ R) ∧ H.rt0 ∈ R ∧ zeta n ∈ R ∧ ∀ F, R ≤ F → GlobalTheory.FinalJoin.WeberIn H F n := by
  have hdm := H.d_mod
  have hd0 : 0 < H.d := H.d_prime.pos
  obtain ⟨hfin, h2⟩ := RayExistCurve.finrank_adjoin hd0 H.sqrt_neg_disc_sq
  have hr0 : H.rt0 ∈ ℚ⟮H.rt0⟯ := IntermediateField.mem_adjoin_simple_self ℚ H.rt0
  generalize ℚ⟮H.rt0⟯ = K₀ at hfin h2 hr0
  have hNF : NumberField K₀ := NumberField.mk
  have hr : (⟨H.rt0, hr0⟩ : K₀) ^ 2 = -(H.d : K₀) := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  have hD : discr K₀ = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 H.d_prime.squarefree (by omega) hr
  have hTC : IsTotallyComplex K₀ := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h1 : InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩ ^ 2 = -(H.d : ℝ) := by
      rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd0
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩)]
  have hQ : Algebra.IsQuadraticExtension ℚ K₀ := ⟨h2⟩
  have hG : IsGalois ℚ K₀ := inferInstance
  obtain ⟨w, hw, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 H.d_prime.squarefree (by omega) hr
  let φ : K₀ →+* ℂ := algebraMap K₀ ℂ
  have hw' : φ w = (1 + H.rt0) / 2 := by
    have := congrArg φ hw
    rw [map_mul, map_add, map_one, map_ofNat] at this
    change _ = 1 + H.rt0 at this
    linear_combination this / 2
  have hc : ∀ a b : ℤ, φ ((a : 𝓞 K₀) + b * w : 𝓞 K₀) = a + b * ((1 + H.rt0) / 2) := fun a b => by
    rw [← hw']
    simp
  have hn0 : (n : 𝓞 K₀) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨L, _, _, _, hL⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hRF K₀ (Ideal.span {(n : 𝓞 K₀)})
    (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let ψ : L →ₐ[K₀] ℂ := IsAlgClosed.lift
  let e₀ : L ≃ₐ[K₀] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  have hfR : FiniteDimensional K₀ ψ.fieldRange := e₀.toLinearEquiv.finiteDimensional
  have hLR := fun (_ : NumberField ψ.fieldRange) => hL.of_algEquiv e₀
  generalize ψ.fieldRange = R at hfR hLR
  have hNR : NumberField R := NumberField.of_module_finite K₀ R
  have hin := (hLR hNR).isRayFieldIn_restrictScalars
  obtain ⟨hab, hR⟩ := hLR hNR
  change IsRay R (Ideal.span {(n : 𝓞 K₀)}) at hR
  have hGR : IsGalois ℚ R := GlobalTheory.RayNatGalois.isGalois_of_isRay_nat ℚ (L := K₀) (by omega) hR
  have hGR' : Normal ℚ (R.restrictScalars ℚ) := hGR.to_normal
  obtain ⟨hdeg, hsz⟩ := GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz K₀ _ n _ hin (by omega)
  have hNR' : NumberField (R.restrictScalars ℚ) := hNR
  have hdpos := GlobalTheory.Mem.Fld.degOver_pos _ _ hin.emb_mem
  refine ⟨R.restrictScalars ℚ, _, _, hsz, ?_, stable_of_normal _, R.algebraMap_mem (⟨H.rt0, hr0⟩ : K₀),
    GlobalTheory.Mem.RayRoots.rootOne_mem_of_isRayFieldIn K₀ _ n n _ (by omega) dvd_rfl hin, fun F hRle P hP => ?_⟩
  · have hcl := classNumber_le_abs_discr_of_finrank_eq_two K₀ h2
    generalize GlobalTheory.Mem.Fld.degOver _ _ hin.emb_mem = m at hdeg hdpos
    rw [h2] at hdeg
    rw [hD] at hcl
    rw [h2, hD]
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, Nat.cast_ofNat] at hcl ⊢
    have hd1 : (1 : ℝ) ≤ H.d := by exact_mod_cast hd0
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hm : (0 : ℝ) < m := by exact_mod_cast hdpos
    have hm' : (m : ℝ) ≤ H.d * (n : ℝ) ^ 2 := by
      have : (m : ℝ) ≤ classNumber K₀ * (n : ℝ) ^ 2 := by exact_mod_cast hdeg
      exact this.trans (by gcongr)
    have h1 := Real.log_le_log hm hm'
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    have h3 := Real.log_nonneg hd1
    have h4 := Real.log_nonneg hn1
    have h5 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    push_cast at h1
    linarith
  · have hW := GlobalTheory.T.weberInvariantTorsionValues_subset_rayClassField K₀ h2 (by omega) P (fun z => ?_) n hn R hR
    · exact ⟨hRle (hW (Set.mem_insert _ _)), fun s hs => hRle (hW (Set.mem_insert_of_mem _
        ⟨_, (hP _).2 ⟨s, rfl⟩, hs, rfl⟩))⟩
    · rw [hP]
      constructor
      · rintro ⟨s, rfl⟩
        exact ⟨_, hc s.1 s.2⟩
      · rintro ⟨a, rfl⟩
        obtain ⟨a, b, rfl⟩ := hgen a
        exact ⟨(a, b), hc a b⟩

set_option maxHeartbeats 1000000 in

theorem exists_good_sized : GlobalTheory.Published.RayClassFieldSt → ∀ (D : D7) (T : Core D), T.Q.Pins → ∀ j : ℕ, InR D j → 5 ≤ D.host.splitBound → Nat.Coprime 15 (D.host.g 0 * D.host.g 1) → ∀ e : ℕ, ∃ Y : Deep T j, Y.Good e (fieldSz T.Q.c.F + 20 * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ e) + Real.log D.host.d + 1)) := by
  intro hRF D T hQ j hj h5 h15 e
  obtain ⟨s, hs⟩ := Inhab.exists_root h5
  have hpos := Inhab.rank_pos T hQ j hj
  obtain ⟨I, hK, hp, hI⟩ := Inhab.exists_half T.Q.H s (by rw [hQ.1.1]; exact hs) e
  obtain ⟨l₂, l1, l2, l3, l4, l5, l6⟩ := GlobalTheory.CoverHalf.exists_coverLevel T.Q.l hQ.2.1.2 (15 ^ e) I (Odd.pow (by decide))
    (by rw [hQ.2.1.1]; exact h15.pow_left e) hK hp hI
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ _ (T.Q.Dw j) l₂ hpos
  have hM' : l₂.M' = l₂.M := by
    show Nat.lcm l₂.M l₂.A = l₂.M
    rw [l6, Nat.lcm_one_right]
  obtain ⟨R, a, b, hsz, hab, hst, hrt, hz, hW⟩ := exists_ray hRF T.Q.H l₂.M l₂.three_le
  haveI := T.Q.c.fin
  have hsz0 : Sz T.Q.c.F (Real.log (Module.finrank ℚ T.Q.c.F))
      (Real.log |(discr T.Q.c.F : ℝ)| / (Module.finrank ℚ T.Q.c.F : ℝ)) := ⟨T.Q.c.fin, le_rfl, le_rfl⟩
  obtain ⟨hN, hN1, hN2⟩ := GlobalTheory.FieldSize.sz_sup _ _ _ _ _ _ hsz0 hsz
  have h1 : T.Q.c.F ≤ T.Q.c.F ⊔ R := le_sup_left
  have h2 : R ≤ T.Q.c.F ⊔ R := le_sup_right
  have hst' : ∀ s : ℂ ≃+* ℂ, (∀ a ∈ T.Q.c.F, s a = a) → ∀ a ∈ T.Q.c.F ⊔ R, s a ∈ T.Q.c.F ⊔ R := fun s hs a ha => by
    have : T.Q.c.F ⊔ R ≤ (T.Q.c.F ⊔ R).comap s.toRingHom.toRatAlgHom :=
      sup_le (fun x hx => show s x ∈ T.Q.c.F ⊔ R from (hs x hx).symm ▸ h1 hx) fun x hx => h2 (hst s x hx)
    exact this ha
  have hKA : KA l₂ ≤ T.Q.c.F ⊔ R := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro x (rfl | rfl)
    · exact h2 hrt
    · rw [l6]
      simpa [zeta] using one_mem (T.Q.c.F ⊔ R)
  generalize T.Q.c.F ⊔ R = N at hN hN1 hN2 h1 h2 hst' hKA
  haveI : NumberField N := NumberField.mk
  let c' : Coeff T.Q.l := ⟨N, hN, fun τ a => h1 (T.Q.c.conj τ a), h1 T.Q.c.zeta_mem, T.Q.c.le.trans h1⟩
  let c₂ : Coeff l₂ := ⟨N, hN, fun τ a => h1 (T.Q.c.conj τ a), hM' ▸ h2 hz, hKA⟩
  have hfa : FnAlgClosed Xo₂ c₂ := GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn D T.Q hQ j hj l₂ Xo₂ c₂ l₂.M
    (by have := l₂.three_le; omega) hM'.dvd (Or.inl (hW N h2))
  have hsize : fieldSz c₂.F ≤ fieldSz T.Q.c.F + 20 * (Real.log ((D.host.g 0 : ℝ) * D.host.g 1 * 15 ^ e) +
      Real.log D.host.d + 1) := by
    rw [l2, hQ.2.1.1, hQ.1.1] at hab
    push_cast at hab
    unfold fieldSz
    have h3 : Real.log (Module.finrank ℚ c₂.F : ℝ) ≤ _ := hN1
    have h4 : Real.log |(discr c₂.F : ℝ)| / (Module.finrank ℚ c₂.F : ℝ) ≤ _ := hN2
    linarith
  obtain ⟨⟨pd', I', l₂', Xo₂', c₂', hF, r, mm, nab, cδ, φ₀⟩, a1, a2, a3, e₁, e₂, -, a4, a5⟩ :=
    GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo j) c' hpos 0 (15 ^ e) I l₂ Xo₂ c₂ rfl l1 l2 l3 l4 l5
  dsimp only at a3 e₁ e₂
  subst a3
  obtain rfl := eq_of_heq e₁
  obtain rfl := eq_of_heq e₂
  obtain ⟨U, dict, Kf, h⟩ := Inhab.exists_good_of_cover T hQ j hj c' h1 _ e a1 a4 l6 hfa hst'
  exact ⟨_, h.mono hsize⟩

end GlobalTheory.CovTop.SizedCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicQuotientAlongArcStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_quotient_along_arc : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (m : H0 p B O) (W : Y.Opens) (hW : IsAffineOpen W) (i : B.ι), W ≤ B.U i → ∀ (ψ : ℂ → (Γ(Y, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) → ∃ (ρ : ℝ) (a b : Γ(Y, W)), 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → ψ u b ≠ 0 ∧ ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ B.U i), H0.val (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) i hO hi m * ψ u b = ψ u a := by
  first | exact @GlobalTheory.Vanishing.exists_quot_along_arc | exact GlobalTheory.Vanishing.exists_quot_along_arc | (intros; apply GlobalTheory.Vanishing.exists_quot_along_arc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrBelow
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverDown

section Integral

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem integral_below (T : CDVR) (io : c.F →+* T.Fr) (io₂ : d.c₂.F →+* T.Fr) (hio : ∀ a : c.F, io₂ (d.eF a) = io a)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (y₂ : letI := io₂.toAlgebra; FrPt d.Xo₂ d.c₂ T.Fr)
    (hy : letI := io.toAlgebra; letI := io₂.toAlgebra; FrOver d y₂ y) (h : Integral T io₂ y₂) : Integral T io y := by
  letI := io.toAlgebra
  letI := io₂.toAlgebra
  obtain ⟨G, t', m1, m2, ⟨ub, b1, b2, b3, b4⟩, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, p2, hg⟩ := h
  obtain ⟨e, hu, w, p, hw, p₁, p₂, R⟩ := (FrameLift.frOver_iff d y₂ y).1 hy
  obtain ⟨m', e₁⟩ := LiftBaseChange.exists_comp' d.m m1 y.x e.symm
  have eig : ∀ τ v, Formalism.L2.Pj.IsEigV d.c₂ io₂ G τ v ↔ Formalism.L2.Pj.IsEigV c io G τ v := fun τ v =>
    forall_congr' fun a => forall_congr' fun z => by rw [← FrameLift.embK_eF d τ a, hio]
  obtain ⟨w', r', tri⟩ := LiftBaseChange.rigIso_comp d.m m1 m' e.symm e₁ (w := w) hw r1
  obtain ⟨s', hs'⟩ := thf_secUp ((isGen_iff w').1 r'.1) Xo.univ.t.PP.isLB t'.PP.isLB σ
  refine ⟨G, t', m', m2, ⟨ub, b1, fun τ i => (eig τ _).1 (b2 τ i), fun τ v h1 h2 => b3 τ v h1 ((eig τ v).2 h2),
    fun τ i => ?_⟩, θ, hθ, w', w2, σ, s', θ2, r', r2,
    (ArcQ.FrUniq.isoMaps_iff w' σ s').2 fun Z r z j k hj hk => hs' Z r z (fun _ => j) k (mem_pull.2 hj) hk,
    i2, p2, ?_⟩
  · obtain ⟨q, h2, h3⟩ := b4 τ i
    exact ⟨q, by rw [e₁, ← Category.assoc, h2, hu], h3⟩
  · intro g g₁ g₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    obtain ⟨g', a₁, a₂⟩ := FrameLift.exists_pm (G := d.Xo₂.univ.t.G) (x := y₂.x) t'.G.hom m1.φ m1.cart.1.w.symm
    have eg : g' ≫ p = g := by
      refine FrameLift.pm_ext ?_ ?_
      · rw [Category.assoc, p₁, ← Category.assoc, a₁, g₁, e₁]
      · rw [Category.assoc, p₂, a₂, g₂]
    refine fn_ext fun z hz => ?_
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB z
    obtain ⟨i, hi⟩ := exists_chart d.Xo₂.univ.t.PP.isLB (m1.φ z)
    have hj : m'.φ z ∈ Xo.univ.t.PP.L.U (J PUnit.unit) := mem_pull.1 hz
    have hj' : d.m.φ (m1.φ z) ∈ Xo.univ.t.PP.L.U (J PUnit.unit) :=
      (congrArg (· ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) (FrameLift.pt_eq e₁ z)).mp hj
    have le : (d.Xo₂.univ.t.PP.L.pull m1.φ).U (fun _ => i) ≤ g' ⁻¹ᵁ (PPx y₂.x).U (fun _ => i) := fun q hq =>
      Set.mem_iInter.2 fun _ => (congrArg (· ∈ d.Xo₂.univ.t.PP.L.U i) (FrameLift.pt_eq a₁ q)).mpr (mem_pull.1 hq)
    have u₁ := (ArcQ.FrUniq.isoMaps_iff w1 σ s1).1 i1 _ (𝟙 _) z i k hi hk
    rw [hg g' a₁ a₂ (fun _ => i) le, gs_appLE g' _ _ le (𝟙 _) z (mem_pull.2 hi), Category.id_comp] at u₁
    have u₂ := R _ g' z (J PUnit.unit) i
      ((congrArg (fun t => d.m.φ t ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) (FrameLift.pt_eq a₁ z)).mpr hj')
      ((congrArg (· ∈ d.Xo₂.univ.t.PP.L.U i) (FrameLift.pt_eq a₁ z)).mpr hi)
    rw [a₁, eg] at u₂
    have u₃ := tri _ (𝟙 _) z (J PUnit.unit) i k hj' hi hk
    rw [Category.id_comp] at u₃
    rw [hs' _ (𝟙 _) z J k hz hk, gs_appLE _ _ _ hJ (𝟙 _) z hz, Category.id_comp]
    refine Eq.trans ?_ (u₂.trans (congrArg _ u₁)).symm
    rw [← _root_.mul_assoc, ← Units.val_mul, ← u₃]

theorem evR_eq_of_pull {d : DeltaDat Xo c 0} {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂}
    (hf : f ∈ sec Xo c a m) (hg : g ∈ sec d.Xo₂ d.c₂ a m) (h : GlobalTheory.LevPull.Pull d f g) {K : Type} [Field K]
    [Algebra c.F K] [Algebra d.c₂.F K] (hc : ∀ a : c.F, algebraMap d.c₂.F K (d.eF a) = algebraMap c.F K a)
    {y₂ : FrPt d.Xo₂ d.c₂ K} {y : FrPt Xo c K} (hy : FrOver d y₂ y) : evR d.Xo₂ d.c₂ g y₂ = evR Xo c f y := by
  let j : K →+* AlgebraicClosure K := algebraMap _ _
  letI : Algebra c.F (AlgebraicClosure K) := (j.comp (algebraMap c.F K)).toAlgebra
  letI : Algebra d.c₂.F (AlgebraicClosure K) := (j.comp (algebraMap d.c₂.F K)).toAlgebra
  let ψ : K →ₐ[c.F] AlgebraicClosure K := ⟨j, fun _ => rfl⟩
  let ψ₂ : K →ₐ[d.c₂.F] AlgebraicClosure K := ⟨j, fun _ => rfl⟩
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c K _ ψ y
  obtain ⟨z₂, hz₂⟩ := GlobalTheory.TransferCompare.frBC_framed d.Xo₂ d.c₂ K _ ψ₂ y₂
  have e := h (AlgebraicClosure K) (fun a => congrArg j (hc a)) z₂ z
    (GlobalTheory.FrameLift.frOver_map d (ψ := ψ) (ψ₂ := ψ₂) rfl hy hz hz₂)
  rw [GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 ψ y
      (GlobalTheory.TransferCompare.allTest_framed Xo c K y) z hz,
    GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed d.Xo₂ d.c₂) g hg.1 ψ₂ y₂
      (GlobalTheory.TransferCompare.allTest_framed d.Xo₂ d.c₂ K y₂) z₂ hz₂] at e
  exact j.injective e

end Integral

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem exists_intFr_below : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ((Dw.p ≠ Dw.q ∧ l.A = 1) ∨ GlobalTheory.ClsVal.Cmp.OverBase d) → ∀ (T : CDVR) (io₂ : d.c₂.F →+* T.Fr) (y₂ : IntFr d.Xo₂ d.c₂ T io₂), y₂.IsAlg → ∃ y : IntFr Xo c T (io₂.comp (d.eF : c.F →+* d.c₂.F)), y.IsAlg ∧ (∀ φ : ℝ, HasPhi y₂ φ → HasPhi y φ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, GlobalTheory.LevPull.Pull d f g → evI y₂ g = evI y f := by
  intro E _ _ _ H Dw l Xo c d _ hlev hO T io₂ y₂ halg
  have hO' : GlobalTheory.ClsVal.Cmp.OverBase d := hO.elim (fun h => GlobalTheory.ClsVal.Cmp.overBase_of_ne h.1 h.2 d) id
  letI := io₂.toAlgebra
  letI := (io₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  obtain ⟨y, hy⟩ := GlobalTheory.CovPull.below_exists d hO' (GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm.KA_le hlev.1) (S := T.Fr) (fun _ => rfl) y₂.1
  refine ⟨⟨y, GlobalTheory.TransferCompare.allTest_framed Xo c T.Fr y,
    integral_below d T _ io₂ (fun _ => rfl) y y₂.1 hy y₂.2.2⟩, halg, ?_, fun a n f hf g hg h => ?_⟩
  · rintro φ ⟨G, t', m1, m2, h⟩
    obtain ⟨m', -⟩ := LiftBaseChange.exists_comp' d.m m1 y.x hy.1.symm
    exact ⟨G, t', m', m2, h⟩
  · exact evR_eq_of_pull hf hg h (fun _ => rfl) hy

end GlobalTheory.CoverDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointsOverComponentOpenSetStatement
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePointsOverComponent_open_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ), IsUnf (U σ) → ∀ (Z : Comp Xo c) (k : (U σ).Comp) (y y' : Frame ((U σ).X k).Ψ r), y' ∈ ((U σ).X k).dom → (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z → (⟨k, y'⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z := by
  first | exact @GlobalTheory.FramesUnion.framesOn_of_mem | exact GlobalTheory.FramesUnion.framesOn_of_mem | (intros; apply GlobalTheory.FramesUnion.framesOn_of_mem <;> assumption)
end

