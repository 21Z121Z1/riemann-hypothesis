import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3082
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureNegEqZeroSemiPosiStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_neg_eq_zero_semiPositive : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ), (∀ i, (L i).φ.SemiPosReg D) → part L (-1) = 0 := by
  first | exact @GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg | exact GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg | (intros; apply GlobalTheory.Mix.part_neg_eq_zero_of_semiPosReg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularRuleExtOfLevelTwelve
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem Rule.eq_of_eq_on_level_twelve : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k),
    (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((6 : ℕ) : R)), Nonempty (X.Level 12) →
      ∀ δ : X.DetGen, s.val R X h δ = t.val R X h δ) → s = t := by
  intro F _ _ _ 𝔠 R₀ _ k s t H
  apply Rule.ext
  funext R _ _ X h δ
  have h2 : IsUnit ((2 : ℕ) : R) :=
    isUnit_of_dvd_unit ⟨((3 : ℕ) : R), by rw [← Nat.cast_mul]⟩ h
  have h12 : IsUnit ((12 : ℕ) : R) := by
    have : ((12 : ℕ) : R) = ((6 : ℕ) : R) * ((2 : ℕ) : R) := by rw [← Nat.cast_mul]
    rw [this]; exact h.mul h2
  obtain ⟨R', _, σ, X', φ, hff, hpull, hlev⟩ := GlobalTheory.RealMult.exists_faithfullyFlat_level F 𝔠 12 (by norm_num) R h12 X
  letI : Algebra R₀ R' := (σ.comp (algebraMap R₀ R)).toAlgebra
  let σa : R →ₐ[R₀] R' := { σ with commutes' := fun _ ↦ rfl }
  have h' : IsUnit ((6 : ℕ) : R') := by
    have := h.map σ
    rwa [map_natCast] at this
  obtain ⟨δ', hδ', -⟩ := hpull.existsUnique_detGen σ δ
  have e1 := s.baseChange R R' σa X h X' h' φ δ δ' hpull hδ'
  have e2 := t.baseChange R R' σa X h X' h' φ δ δ' hpull hδ'
  have e3 := H R' X' h' hlev δ'
  apply hff.injective
  change σa (s.val R X h δ) = σa (t.val R X h δ)
  rw [← e1, ← e2, e3]

end GlobalTheory.RealMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulipointLiftToFinerLevelCompleteDVR
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

namespace GlobalTheory.LevelLift

open scoped TensorProduct

theorem exists_field_over (K F M : Type) [Field K] [Field F] [Field M] [Algebra K F] [FiniteDimensional K F]
    (io : K →+* M) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : Algebra M L₀) (_ : FiniteDimensional M L₀) (io' : F →+* L₀),
      io'.comp (algebraMap K F) = (algebraMap M L₀).comp io := by
  letI : Algebra K M := io.toAlgebra
  haveI : Nontrivial (M ⊗[K] F) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain K M F io.injective
      (algebraMap K F).injective
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (M ⊗[K] F)
  letI : Field (M ⊗[K] F ⧸ I) := Ideal.Quotient.field I
  refine ⟨M ⊗[K] F ⧸ I, inferInstance, inferInstance, inferInstance,
    (Ideal.Quotient.mk I).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext k
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply K M (M ⊗[K] F), Ideal.Quotient.mk_algebraMap]
  rfl

theorem exists_point_finite_surjective {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : IsFinite f) (hs : Surjective f)
    (L₀ : Type) [Field L₀] (y : Sp L₀ ⟶ Y) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra L₀ L) (_ : FiniteDimensional L₀ L) (x : Sp L ⟶ X),
      x ≫ f = spMap (algebraMap L₀ L) ≫ y := by
  haveI := hf
  haveI := hs
  haveI : Surjective (pullback.snd f y) := inferInstance
  haveI : IsAffine (pullback f y) := isAffine_of_isAffineHom (pullback.snd f y)
  let P := pullback f y
  let g' : Spec Γ(P, ⊤) ⟶ Sp L₀ := P.isoSpec.inv ≫ pullback.snd f y
  haveI : IsFinite g' := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g'
  have hφf : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  haveI : Nonempty (Sp L₀) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨p, -⟩ := (pullback.snd f y).surjective (Classical.arbitrary (Sp L₀))
  haveI : Nontrivial Γ(P, ⊤) := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨P.isoSpec.hom p⟩
  obtain ⟨I, hI⟩ := Ideal.exists_maximal Γ(P, ⊤)
  letI : Field (Γ(P, ⊤) ⧸ I) := Ideal.Quotient.field I
  letI : Algebra L₀ (Γ(P, ⊤) ⧸ I) := ((Ideal.Quotient.mk I).comp φ.hom).toAlgebra
  have hfin : ((Ideal.Quotient.mk I).comp φ.hom).Finite :=
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hφf
  refine ⟨Γ(P, ⊤) ⧸ I, inferInstance, inferInstance, hfin,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ P.isoSpec.inv ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc P.isoSpec.inv]
  change _ ≫ g' ≫ y = _
  rw [← hφ, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem lift_to_finer_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l₂ : Level H) (Xo : Moduli Dw l) (Xo₂ : Moduli Dw l₂) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.Dvd l₂ → l₂.A = l.A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∃ (c₂ : Coeff l₂) (la₂ : HeightOneSpectrum (𝓞 c₂.F)) (T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V) (e' : ℕ) (io₂ : c₂.F →+* T'.Fr) (e₂ : ℕ) (x₂ : Sp T'.Fr ⟶ Xo₂.X) (r : Xo₂.X ⟶ Xo.X) (_ : SABMap Xo₂.univ.t Xo.univ.t r), 0 < e' ∧ (∀ a : T.Fr, vV T'.V (iT a) = (e' : ℤ) * vV T.V a) ∧ (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) ∧ OverLa la₂ T'.V io₂ e₂ ∧ x₂ ≫ Xo₂.s = spMap (io₂.comp (IntermediateField.inclusion c₂.le).toRingHom) ∧ x₂ ≫ r = spMap iT ≫ x := by
  intro E _ _ _ H Dw l l₂ Xo Xo₂ c hpq hd hA la T io e ho x hx
  obtain ⟨r, jK, m, -, -, -, -, -, hrF⟩ :=
    ((GlobalTheory.moduliScheme_levelMaps_heckePoints).2 E H Dw hpq).1 l l₂ Xo Xo₂ hd
  let F₂ : IntermediateField ℚ ℂ := c.F ⊔ IntermediateField.adjoin ℚ {zeta l₂.M'}
  have hle : c.F ≤ F₂ := le_sup_left
  have hpos : 0 < l₂.M' := Nat.lcm_pos (by have := l₂.three_le; omega) l₂.A_pos
  have hint : IsIntegral ℚ (zeta l₂.M') :=
    ((Complex.isPrimitiveRoot_exp l₂.M' hpos.ne').isIntegral hpos).tower_top
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta l₂.M'}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hfin : FiniteDimensional ℚ F₂ := IntermediateField.finiteDimensional_sup _ _
  have hKA : KA l₂ = KA l := by unfold KA; rw [hA]
  let c₂ : Coeff l₂ :=
    { F := F₂, fin := hfin, conj := fun τ a => hle (c.conj τ a),
      zeta_mem := le_sup_right (a := c.F) (IntermediateField.subset_adjoin ℚ _ rfl),
      le := hKA ▸ c.le.trans hle }
  let c' : Coeff l :=
    { F := F₂, fin := hfin, conj := fun τ a => hle (c.conj τ a), zeta_mem := hle c.zeta_mem,
      le := c.le.trans hle }
  obtain ⟨rF, hr1, hr2, hfinr, -, hsurj, -⟩ := hrF c' c₂ rfl
  letI : Algebra c.F F₂ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ c.F F₂ := IsScalarTower.of_algebraMap_eq fun q => by
    simp
  haveI : FiniteDimensional c.F F₂ := Module.Finite.of_restrictScalars_finite ℚ c.F F₂
  obtain ⟨L₀, _, _, _, io', hio'⟩ := exists_field_over c.F F₂ T.Fr io
  have cond : (spMap (algebraMap T.Fr L₀) ≫ x) ≫ Xo.s =
      spMap io' ≫ spMap (IntermediateField.inclusion c'.le).toRingHom := by
    rw [Category.assoc, hx, Formalism.L2.PjFree.spMap_comp', Formalism.L2.PjFree.spMap_comp']
    congr 1
    ext a
    have h := RingHom.congr_fun hio' (IntermediateField.inclusion c.le a)
    exact h.symm
  let z' : Sp L₀ ⟶ Xo.XF c' := pullback.lift (spMap (algebraMap T.Fr L₀) ≫ x) (spMap io') cond
  obtain ⟨L, _, _, _, x', hx'⟩ := exists_point_finite_surjective rF hfinr hsurj L₀ z'
  letI : Algebra T.Fr L := ((algebraMap L₀ L).comp (algebraMap T.Fr L₀)).toAlgebra
  haveI : IsScalarTower T.Fr L₀ L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional T.Fr L := Module.Finite.trans L₀ L
  obtain ⟨T', iT, e', ψ, φ, he', hv, hψ, hφ, -⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T L
  let io₂ : c₂.F →+* T'.Fr := ψ.toRingHom.comp ((algebraMap L₀ L).comp io')
  haveI : NumberField c₂.F := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨la₂, e₂, ho₂⟩ := GlobalTheory.LocalDepthCompare.exists_overLa_of_not_charZero (V := T'.V) io₂
    (GlobalTheory.LocalDepthCompare.not_charZero_of_overLa (ho.bc iT he' hv))
  have hid : spMap (IntermediateField.inclusion (le_of_eq (rfl : c'.F = c₂.F))).toRingHom = 𝟙 (Sp c₂.F) := by
    have : (IntermediateField.inclusion (le_of_eq (rfl : c'.F = c₂.F))).toRingHom = RingHom.id _ :=
      RingHom.ext fun _ => rfl
    rw [this]
    exact (congrArg Spec.map (CommRingCat.ofHom_id)).trans (Spec.map_id _)
  have hs : x' ≫ pullback.snd _ _ = spMap ((algebraMap L₀ L).comp io') := by
    have h := congrArg (· ≫ pullback.snd _ _) hx'
    simp only [Category.assoc, hr2, pullback.lift_snd, z'] at h
    rw [hid, Category.comp_id] at h
    rw [h, Formalism.L2.PjFree.spMap_comp']
  have hf : x' ≫ pullback.fst _ _ ≫ r = spMap (algebraMap T.Fr L) ≫ x := by
    have h := congrArg (· ≫ pullback.fst _ _) hx'
    simp only [Category.assoc, hr1, pullback.lift_fst, z'] at h
    rw [h, ← Category.assoc, Formalism.L2.PjFree.spMap_comp']
  refine ⟨c₂, la₂, T', iT, φ, e', io₂, e₂, spMap ψ.toRingHom ≫ x' ≫ pullback.fst _ _, r, m, he', hv, hφ, ho₂,
    ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc x', hs, ← Category.assoc,
      Formalism.L2.PjFree.spMap_comp', Formalism.L2.PjFree.spMap_comp']
  · rw [Category.assoc, Category.assoc, hf, ← Category.assoc, Formalism.L2.PjFree.spMap_comp']
    have hc : ψ.toRingHom.comp (algebraMap T.Fr L) = iT := RingHom.ext fun a => hψ a
    rw [hc]

end GlobalTheory.LevelLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoritaSpreadStableSummandLieDecompositionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moritaSpread_stableSummand_lieDecomposition : ∀ {C : Type} [CommRing C] (I : Ideal C) {H : Type u} [AddCommGroup H] [Module C H]
  (m : ℕ) [NeZero m] (E : Fin m → Fin m → Module.End C H),
  (∀ i j k l, E i j * E k l = if j = k then E i l else 0) → ∑ i, E i i = 1 →
  ∀ {A : Type} [CommRing A] (σ : A →+* Module.End C H), (∀ i j c, E i j * σ c = σ c * E i j) →
  ∀ {O : Type} [Ring O] (ρ : O →+* Module.End C H),
  (∀ (c : O) i j (N : Submodule C H), (∀ c', ∀ x ∈ N, σ c' x ∈ N) → ∀ x ∈ N, E 0 0 x = x → E 0 i (ρ c (E j 0 x)) ∈ N) →
  ∀ (e : Module.End C H), e * e = e → (∀ i j, E i j * e = e * E i j) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ i j, ∀ x ∈ F, E i j x ∈ F) → (∀ x ∈ F, e x ∈ F) →
  ∀ (a : ℕ) (χ : Fin a → A →+* C) (G₀ M₀ : Submodule C H), G₀ ⊓ M₀ = ⊥ → G₀ ⊔ M₀ = LinearMap.range (E 0 0 * e) →
    (∀ c, ∀ x ∈ G₀, σ c x ∈ G₀) → G₀ ⊔ I • LinearMap.range (E 0 0 * e) = F ⊓ LinearMap.range (E 0 0 * e) →
    (∀ d ∈ LinearMap.range (E 0 0 * e), ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G₀) ∧ d - ∑ i, w i ∈ G₀) →
  ∃ G M : Submodule C H, G ⊓ M = ⊥ ∧ G ⊔ M = LinearMap.range e ∧ (∀ (c : O), ∀ x ∈ G, ρ c x ∈ G) ∧
    G ⊔ (I • ⊤ ⊓ LinearMap.range e) = F ⊓ LinearMap.range e ∧
    ∀ d ∈ LinearMap.range e, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ G) ∧ d - ∑ i, w i ∈ G := by
  first | (exact @GlobalTheory.morita_spread_stable_summand_lie) | (exact GlobalTheory.morita_spread_stable_summand_lie) | (intros; apply GlobalTheory.morita_spread_stable_summand_lie  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismLocalDescentsGlueUnionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.morphism_local_descents_glue_union : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (I : Type) (V : I → Y.Opens) (hV : ∀ i, p ⁻¹ᵁ V i ≤ O) (h₀ : ∀ i, (V i).toScheme ⟶ W), (∀ i, (p ∣_ V i) ≫ h₀ i = Z.homOfLE (hV i) ≫ h) → ∃ (hV' : p ⁻¹ᵁ (⨆ i, V i) ≤ O) (m : (⨆ i, V i).toScheme ⟶ W), (p ∣_ (⨆ i, V i)) ≫ m = Z.homOfLE hV' ≫ h ∧ ∀ (W' : Scheme.{0}) (g g' : (⨆ i, V i).toScheme ⟶ W'), (p ∣_ (⨆ i, V i)) ≫ g = (p ∣_ (⨆ i, V i)) ≫ g' → g = g' := by
  first | exact @GlobalTheory.MorDescent.descend_glue | exact GlobalTheory.MorDescent.descend_glue | (intros; apply GlobalTheory.MorDescent.descend_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZero
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDivGroup

theorem mulP_mem_kerIdeal_of_verschiebung_eq_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (a : G.A 1) (ha : (verschiebung h G).app 1 a = 0) :
    G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) := by
  set K := kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) with hK
  let x := Ideal.Quotient.mkₐ R K
  have hx := (kerIdeal_le_ker_iff ((G.mulP 1).comp ((relFrob h G).app 1)) x).1
    fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
  let y := x.comp ((relFrob h G).app 2 : (frobTwist h G).A 2 →ₐ[R] G.A 2)
  have hy : torsionIdeal R ((frobTwist h G).A 2) p ≤ RingHom.ker y :=
    (kerIdeal_le_ker_iff _ y).2 fun z => by
      have e : (relFrob h G).app 2 (mulBy R _ p z) =
          G.mulP 1 ((relFrob h G).app 1 ((frobTwist h G).res 1 z)) := by
        rw [map_mulBy, ← PDivGroup.res_app, mulP_res]
      have := hx ((frobTwist h G).res 1 z)
      rw [CoalgHomClass.counit_comp_apply] at this
      exact (congrArg x e).trans this
  obtain ⟨b, rfl⟩ := G.res_surjective 1 a
  rw [← PDivGroup.res_app] at ha
  have hb : (verschiebung h G).app 2 b ∈ torsionIdeal R ((frobTwist h G).A 2) p := by
    have : (verschiebung h G).app 2 b ∈ torsionIdeal R ((frobTwist h G).A 2) (p ^ 1) := by
      rw [← (frobTwist h G).ker_res 1]
      exact ha
    rwa [pow_one] at this
  have h1 : x ((relFrob h G).app 2 ((verschiebung h G).app 2 b)) = 0 := hy hb
  rw [relFrob_app_verschiebung_app] at h1
  rw [mulP_res]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (y : Z ⟶ D.P.A) (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (1 : Z ⟶ D.P.A) y).left z J J' = 1 ∧ lamVal w (lift y (1 : Z ⟶ D.P.A)).left z J J' = 1 := by
  first | exact @GlobalTheory.TInj.lamVal_axes_one | exact GlobalTheory.TInj.lamVal_axes_one | (intros; apply GlobalTheory.TInj.lamVal_axes_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomIsNilpotentOfConstantCoeffZer
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_isNilpotent_of_constantCoeff_zero :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        ∀ a : MvPowerSeries σ k, constantCoeff a = 0 → IsNilpotent (φ a) := by
  intro k _ σ _ A _ _ φ hφ a ha
  classical
  haveI := Fintype.ofFinite σ
  have hc : ∀ α : σ →₀ ℕ, ∃ o : Option σ, (α = 0 ∧ o = none) ∨ ∃ i, o = some i ∧ α i ≠ 0 := by
    intro α
    by_cases h : α = 0
    · exact ⟨none, Or.inl ⟨h, rfl⟩⟩
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h
      exact ⟨some i, Or.inr ⟨i, rfl, by simpa using hi⟩⟩
  choose c hc using hc
  let g : σ → MvPowerSeries σ k := fun i α => if c α = some i then coeff α a else 0
  have hg : ∀ i α, coeff α (g i) = if c α = some i then coeff α a else 0 := fun _ _ => rfl
  have hsum : a = ∑ i, g i := by
    ext α
    rw [map_sum]
    simp only [hg]
    rcases hc α with ⟨h0, h1⟩ | ⟨i, h1, -⟩
    · rw [h1, h0]
      simpa using ha
    · rw [h1]
      simp
  rw [hsum, map_sum]
  refine isNilpotent_sum fun i _ => ?_
  have hd : (X i : MvPowerSeries σ k) ∣ g i := by
    rw [X_dvd_iff]
    intro m hm
    rw [hg, if_neg]
    intro h
    rcases hc m with ⟨-, h1⟩ | ⟨j, h1, h2⟩
    · rw [h1] at h; cases h
    · rw [h1] at h
      cases h
      exact h2 hm
  obtain ⟨b, hb⟩ := hd
  rw [hb, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right (hφ i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomKillHighOrder
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_kill_high_order :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        ∃ N : ℕ, ∀ f : MvPowerSeries σ k,
          (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → φ f = 0 := by
  intro k _ σ _ A _ _ φ hφ
  classical
  haveI := Fintype.ofFinite σ
  choose m hm using hφ
  set M := Finset.univ.sup m with hMdef
  have hM : ∀ i, φ (X i) ^ M = 0 := fun i =>
    pow_eq_zero_of_le (Finset.le_sup (Finset.mem_univ i)) (hm i)
  refine ⟨Fintype.card σ * M + 1, fun f hf => ?_⟩

  let fi : σ → MvPowerSeries σ k := fun i α =>
    if h : ∃ j, M ≤ α j then (if h.choose = i then coeff α f else 0) else 0
  have hcoeff : ∀ i α, coeff α (fi i) =
      if h : ∃ j, M ≤ α j then (if h.choose = i then coeff α f else 0) else 0 :=
    fun i α => rfl
  have hsum : f = ∑ i, fi i := by
    ext α
    rw [map_sum]
    simp only [hcoeff]
    by_cases h : ∃ j, M ≤ α j
    · simp only [dif_pos h]
      rw [Finset.sum_ite_eq]
      simp
    · simp only [dif_neg h, Finset.sum_const_zero]
      apply hf
      push_neg at h
      rw [Finsupp.degree_eq_sum]
      calc ∑ i, α i ≤ ∑ _i : σ, M := Finset.sum_le_sum fun i _ => (h i).le
        _ = Fintype.card σ * M := by simp
        _ < Fintype.card σ * M + 1 := Nat.lt_succ_self _
  have hdvd : ∀ i, (X i : MvPowerSeries σ k) ^ M ∣ fi i := by
    intro i
    rw [MvPowerSeries.X_pow_dvd_iff]
    intro α hα
    rw [hcoeff]
    split_ifs with h h'
    · exact absurd (h'.symm ▸ h.choose_spec) (not_le.mpr hα)
    · rfl
    · rfl
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨g, hg⟩ := hdvd i
  rw [hg, map_mul, map_pow, hM i, zero_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeatLevelActionUnipotentStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neat_level_action_unipotent : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → FnAlgClosed Xo c → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), (∀ γ, UnipAt I (ι γ)) → ActsBy ι ρ → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ℓ : V₀ TF.Y Z ⟶ X') (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → IsOpenImmersion ℓ → ℓ ≫ φ = j₀ TF.Y Z → (∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom) → ∃ (G' : Over X') (_ : GrpObj G') (ψ : G'.left ⟶ TF.Y.t.G.left) (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)), GlobalTheory.HodgeLin.EqvLin TF.Y.t (φ ≫ (barComp TF.Y Z).ι) ρ' G' ψ act' m := by
  first | exact @GlobalTheory.EqvAct.eqvLin_pull | exact GlobalTheory.EqvAct.eqvLin_pull | (intros; apply GlobalTheory.EqvAct.eqvLin_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaModelPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_mem_dividing_labels_theta_model_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → -a ∈ X₁.S.supI X₁.M z₁ := by
  first | exact @GlobalTheory.Poinc.Sep.neg_mem_supI | exact GlobalTheory.Poinc.Sep.neg_mem_supI | (intros; apply GlobalTheory.Poinc.Sep.neg_mem_supI <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyGaloisActionPulledBackUniformisation
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem galAct_nonempty : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), Nonempty (GalAct ρ hD U') := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hgal D D' hD A' G' _ _ hG U'
  have hex : ∀ σ : Gal ρ, ∃ a, GalMap hD U' σ a := GlobalTheory.T.exists_uniformisedGroup_galoisAutomorphism_map R hR R' ρ hfin D D' hD A' G' hG U'
  choose act hact using hex
  exact ⟨{ act := act
           cart := fun σ => (hact σ).1
           act_one := GlobalTheory.T.uniformisedGroup_galoisMap_unique R hR R' ρ hfin D D' hD A' G' hG U' 1 _ _ (hact 1) (GlobalTheory.T.uniformisedGroup_galoisMap_one R hR R' ρ hfin D D' hD A' G' hG U')
           act_mul := fun σ τ => GlobalTheory.T.uniformisedGroup_galoisMap_unique R hR R' ρ hfin D D' hD A' G' hG U' (σ * τ) _ _ (hact (σ * τ))
             (GlobalTheory.T.uniformisedGroup_galoisMap_mul R hR R' ρ hfin D D' hD A' G' hG U' σ τ _ _ (hact σ) (hact τ))
           unif := fun σ => (hact σ).2 }⟩

end GlobalTheory.Mum
end
end

