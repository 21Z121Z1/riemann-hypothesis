import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0103
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalRootReZeroImSq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0105

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.FixedConst

open Polynomial

theorem exists_section_of_isIntegral {Y : Scheme.{0}} [GlobalTheory.IsNormalScheme Y] [IsIntegral Y] (p : Γ(Y, ⊤)[X])
    (hp : p.Monic) (r : Y.residueField (genericPoint Y))
    (hr : p.eval₂ (Y.evaluation ⊤ (genericPoint Y) trivial).hom r = 0) :
    ∃ s : Γ(Y, ⊤), (Y.evaluation ⊤ (genericPoint Y) trivial).hom s = r ∧ p.eval s = 0 := by
  haveI : Nonempty (⊤ : Y.Opens) := ⟨Nonempty.some inferInstance, trivial⟩
  obtain ⟨t, rfl⟩ := Y.residue_surjective (genericPoint Y) r
  let ρ : Y.functionField →+* Y.residueField (genericPoint Y) := (Y.residue (genericPoint Y)).hom
  have e : (Y.evaluation ⊤ (genericPoint Y) trivial).hom = ρ.comp (algebraMap Γ(Y, ⊤) Y.functionField) := rfl
  have ht : p.eval₂ (algebraMap Γ(Y, ⊤) Y.functionField) t = 0 := by
    apply ρ.injective
    rw [hom_eval₂, ← e, map_zero]
    exact hr
  obtain ⟨s, hs⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral (R := Γ(Y, ⊤)) (A := Y.functionField)
    (x := t) ⟨p, hp, ht⟩
  refine ⟨s, by rw [e, RingHom.comp_apply, hs], ?_⟩
  apply Y.germToFunctionField_injective ⊤
  rw [← hs, eval₂_at_apply] at ht
  exact ht.trans (map_zero _).symm

theorem exists_extension_zero {Y : Scheme.{0}} (V W : Y.Opens) (hU : V ⊔ W = ⊤) (hVW : Disjoint V W) (s : Γ(Y, V)) :
    ∃ f : Γ(Y, ⊤), Y.presheaf.map (homOfLE le_top).op f = s ∧
      Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op f = 0 := by
  have hs : ∀ T : Y.Opens, T = ⊥ → Subsingleton Γ(Y, T) := fun T hT ↦
    CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty hT)
  obtain ⟨e, he, -⟩ := Y.sheaf.existsUnique_gluing' (fun b : Bool ↦ cond b V W) ⊤
    (fun b ↦ homOfLE le_top)
    (by rw [iSup_bool_eq]; exact hU.ge)
    (fun b ↦ match b with | true => s | false => (0 : Γ(Y, W))) (by
      rintro (_ | _) (_ | _)
      · rfl
      · exact (hs _ (hVW.symm.eq_bot)).elim _ _
      · exact (hs _ (hVW.eq_bot)).elim _ _
      · rfl)
  exact ⟨e, he true, he false⟩

theorem exists_section {Y : Scheme.{0}} [GlobalTheory.IsNormalScheme Y] [IsLocallyNoetherian Y] (Z : irreducibleComponents Y)
    (ξ : Y) (hξ : IsGenericPoint ξ Z.1) (p : Γ(Y, ⊤)[X]) (hp : p.Monic) (r : Y.residueField ξ)
    (hr : p.eval₂ (Y.evaluation ⊤ ξ trivial).hom r = 0) :
    ∃ f : Γ(Y, ⊤), (Y.evaluation ⊤ ξ trivial).hom f = r ∧ f * p.eval f = 0 := by
  let V : Y.Opens := IsNormalScheme.component Z
  let W : Y.Opens := ⟨Z.1ᶜ, (IsNormalScheme.isClosed_component Z).isOpen_compl⟩
  have hU : V ⊔ W = ⊤ := by
    refine le_antisymm le_top fun x _ ↦ ?_
    by_cases h : x ∈ Z.1
    exacts [Or.inl h, Or.inr h]
  have hVW : Disjoint V W := by
    rw [← TopologicalSpace.Opens.coe_disjoint]
    exact Set.disjoint_left.mpr fun x hx hx' ↦ hx' hx
  obtain rfl : V.ι (genericPoint V.toScheme) = ξ := by
    refine IsGenericPoint.eq ?_ hξ
    have h := (genericPoint_spec V.toScheme).image V.ι.continuous
    rwa [Set.image_univ, Scheme.Opens.range_ι, (IsNormalScheme.isClosed_component Z).closure_eq] at h
  let φ := (V.ι.residueFieldMap (genericPoint V.toScheme)).hom
  have e : ∀ f : Γ(Y, ⊤), φ ((Y.evaluation ⊤ (V.ι (genericPoint V.toScheme)) trivial).hom f) =
      (V.toScheme.evaluation ⊤ (genericPoint V.toScheme) trivial).hom (V.ι.appTop.hom f) := fun f =>
    Scheme.evaluation_naturality_apply V.ι (genericPoint V.toScheme) (V := ⊤) trivial f
  obtain ⟨s, hs, hps⟩ := exists_section_of_isIntegral (p.map V.ι.appTop.hom) (hp.map _) (φ r) (by
    have e' : φ.comp (Y.evaluation ⊤ (V.ι (genericPoint V.toScheme)) trivial).hom =
        (V.toScheme.evaluation ⊤ (genericPoint V.toScheme) trivial).hom.comp V.ι.appTop.hom := RingHom.ext e
    rw [eval₂_map, ← e', ← hom_eval₂, hr, map_zero])
  obtain ⟨f, h1, h0⟩ := exists_extension_zero V W hU hVW (V.topIso.hom.hom s)
  have e2 : V.ι.appTop ≫ V.topIso.hom = Y.presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
    exact (Y.presheaf.map_comp _ _).symm
  have hf : V.ι.appTop.hom f = s := by
    apply V.topIso.commRingCatIsoToRingEquiv.injective
    exact (congrArg (fun g => g.hom f) e2).trans h1
  refine ⟨f, φ.injective (by rw [e, hf, hs]), ?_⟩
  refine Y.sheaf.eq_of_locally_eq₂ (homOfLE (le_top : V ≤ ⊤)) (homOfLE (le_top : W ≤ ⊤)) hU.ge _ _ ?_ ?_
  · change Y.presheaf.map (homOfLE le_top).op (f * p.eval f) = Y.presheaf.map (homOfLE le_top).op 0
    rw [← e2]
    change V.topIso.hom.hom (V.ι.appTop.hom _) = V.topIso.hom.hom (V.ι.appTop.hom _)
    rw [map_mul, ← eval₂_at_apply, hf, ← Polynomial.eval_map, hps, mul_zero, map_zero V.ι.appTop.hom]
  · change Y.presheaf.map (homOfLE le_top).op (f * p.eval f) = Y.presheaf.map (homOfLE le_top).op 0
    rw [map_mul, h0, zero_mul, map_zero]

theorem mem_range_of_fixed {K L : Type} [Field K] [Field L] [Countable L] [Algebra K L] [Algebra K ℂ] [CharZero K]
    (φ : L →ₐ[K] ℂ) {r : L} (hr : IsIntegral K r)
    (h : ∀ τ : ℂ ≃+* ℂ, (∀ x : K, τ (algebraMap K ℂ x) = algebraMap K ℂ x) → τ (φ r) = φ r) :
    r ∈ (algebraMap K L).range := by
  let M := IntermediateField.adjoin K {r}
  haveI : FiniteDimensional K M := IntermediateField.adjoin.finiteDimensional hr
  have key : ∀ ψ : M →ₐ[K] ℂ, ψ = φ.comp M.val := by
    intro ψ
    obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq M (φ.comp M.val).toRingHom ψ.toRingHom
    refine IntermediateField.algHom_ext_of_eq_adjoin K (S := M) rfl fun x hx => ?_
    obtain rfl : x = r := hx
    refine (hτ _).symm.trans (h τ fun y => ?_)
    have := hτ (algebraMap K M y)
    simpa using this
  have hc : Module.finrank K M ≤ 1 := by
    rw [← AlgHom.card K M ℂ]
    exact Fintype.card_le_one_iff.2 fun a b => (key a).trans (key b).symm
  have h1 : Module.finrank K M = 1 := le_antisymm hc Module.finrank_pos
  exact IntermediateField.mem_bot.1 (IntermediateField.finrank_adjoin_simple_eq_one_iff.1 h1)

noncomputable def ev {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) : Γ(Y, ⊤) →+* ℂ :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

theorem valAt'_top {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (f : Γ(Y, ⊤)) : valAt' x ⊤ f = ev x f := by
  have h : ⊤ ≤ x ⁻¹ᵁ ⊤ := le_rfl
  rw [valAt', dif_pos h, valAt, ev]
  exact congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (g.hom f)) (x.appLE_eq_app (U := ⊤))

theorem ev_comp {Y Y' : Scheme.{0}} (x : Sp ℂ ⟶ Y) (g : Y ⟶ Y') (f : Γ(Y', ⊤)) :
    ev (x ≫ g) f = ev x (g.appTop.hom f) := by
  rw [ev, ev, Scheme.Hom.comp_appTop]; rfl

theorem ev_spec {R : CommRingCat.{0}} (j : R ⟶ CommRingCat.of ℂ) (a : Γ(Spec R, ⊤)) :
    ev (Spec.map j) a = j.hom ((Scheme.ΓSpecIso R).hom.hom a) := by
  rw [ev, Scheme.ΓSpecIso_naturality]; rfl

theorem ev_conj {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (τ : ℂ →+* ℂ) (f : Γ(Y, ⊤)) : ev (spMap τ ≫ x) f = τ (ev x f) := by
  rw [ev_comp, ev_spec]; rfl

theorem ΓSpecIso_fromSpecResidueField {Y : Scheme.{0}} (ξ : Y) :
    (Y.fromSpecResidueField ξ).appTop ≫ (Scheme.ΓSpecIso _).hom = Y.evaluation ⊤ ξ trivial := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    Scheme.fromSpecStalk_appTop]
  simp [Scheme.evaluation]

theorem ev_residue {Y : Scheme.{0}} (ξ : Y) (φ : Y.residueField ξ →+* ℂ) (f : Γ(Y, ⊤)) :
    ev (Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecResidueField ξ) f = φ ((Y.evaluation ⊤ ξ trivial).hom f) := by
  rw [ev_comp, ev_spec, ← ΓSpecIso_fromSpecResidueField]; rfl

theorem emb_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) (σ : KA l →+* ℂ)
    (hσ : σ (baseKA l).ρ = H.rt0) (hA : l.A = 1) : σ = algebraMap (KA l) ℂ := by
  have h : σ.toRatAlgHom = (KA l).val := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := KA l) rfl fun x hx => ?_
    rcases hx with rfl | rfl
    · exact hσ
    · have e : zeta l.A = 1 := by simp [zeta, hA]
      have e' : ∀ h, (⟨zeta l.A, h⟩ : KA l) = 1 := fun _ => Subtype.ext e
      exact (congrArg _ (e' _)).trans ((map_one _).trans e.symm)
  exact RingHom.ext fun x => DFunLike.congr_fun h x

theorem fnAlgClosed_of_permutes_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed Xo c := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty hA c hperm Z a ha
  obtain ⟨r, rfl⟩ := GlobalTheory.GeomIrr.mem_range_of_isAlgebraic_ratFun a (ha.tower_top (kap Z))
  have hr : IsIntegral c.F r := (isIntegral_algebraMap_iff (algebraMap (kap Z) (Om Z)).injective).1 ha.isIntegral
  suffices h : r ∈ (algebraMap c.F (kap Z)).range by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← hk, ← IsScalarTower.algebraMap_apply]⟩
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  have hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H D l Xo c).1 Z)
  obtain ⟨φ⟩ : Nonempty (kap Z →ₐ[c.F] ℂ) := GlobalTheory.nonempty_algHom_complex_of_countable c.F (kap Z)
  refine mem_range_of_fixed φ hr fun τ hτ => ?_
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := (GlobalTheory.isNormalScheme_iff _).2
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strK (Xo := Xo) (c := c))
      ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))
  let κ : c.F →+* Γ(Xo.XF c, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ (strK (Xo := Xo) (c := c)).appTop).hom
  let j : c.F →+* ℂ := algebraMap c.F ℂ
  have hκ : ∀ (x : Sp ℂ ⟶ Xo.XF c) (i : c.F →+* ℂ), x ≫ strK = spMap i → (ev x).comp κ = i := by
    intro x i hx
    ext k
    change ev x ((strK (Xo := Xo) (c := c)).appTop.hom _) = _
    rw [← ev_comp, hx, ev_spec]
    exact congrArg i ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv_hom_id_apply k)
  let x : Sp ℂ ⟶ Xo.XF c := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ genSp Z
  have hx : x ≫ strK = spMap j := by
    rw [Category.assoc, ← Spec.map_preimage (genSp Z ≫ strK), ← Spec.map_comp]
    congr 1
    ext k
    exact φ.commutes k
  have hev : ∀ f, ev x f = φ (((Xo.XF c).evaluation ⊤ (genPt Z) trivial).hom f) := ev_residue _ φ.toRingHom
  have hm := minpoly.monic hr
  obtain ⟨f, hf, hf0⟩ := exists_section Z (genPt Z)
    ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)) ((minpoly c.F r).map κ) (hm.map _) r (by
    apply φ.toRingHom.injective
    rw [hom_eval₂, ← (RingHom.ext hev : ev x = φ.toRingHom.comp _), eval₂_map, hκ x j hx, map_zero]
    exact (aeval_algHom_apply φ r _).trans (by rw [minpoly.aeval, map_zero]))
  have hS : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap j →
      valAt' y ⊤ f ∈ insert 0 ((minpoly c.F r).rootSet ℂ) := by
    intro y hy
    have h := congrArg (ev y) hf0
    rw [map_mul, ← eval₂_at_apply, eval₂_map, hκ y j hy, map_zero, mul_eq_zero] at h
    rw [valAt'_top]
    exact h.imp id fun h => mem_rootSet.2 ⟨hm.ne_zero, h⟩
  obtain ⟨i, P, hP, hu⟩ := F.onto (x ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, emb_eq l σ hσ hA, ← Spec.map_comp]
    rfl)
  obtain ⟨P', hP', hu'⟩ := hperm τ (fun z hz => hτ ⟨z, hz⟩) i P hP
  have key := GlobalTheory.T.regularFunction_const_of_finite_values_on_period_space E H D l Xo σ g ty F h1 hσ hty hA c j f _ ((rootSet_finite _ _).insert 0) hS i P' P hP' hP
    (spMap (τ : ℂ →+* ℂ) ≫ x) x (by rw [Category.assoc, ← hu]; exact hu') (by
      rw [Category.assoc, hx, ← Spec.map_comp]
      congr 1
      ext k
      exact hτ k) hu.symm hx
  rwa [valAt'_top, valAt'_top, ev_conj, hev, hf] at key

end GlobalTheory.CompRat.FixedConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicCharacter_eq_cmMultiplier_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (io : C.P.A.left ⟶ C.P.A.left) (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → τ (zeta n) = zeta n ^ (s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4)) := by
  first | exact @GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm | exact GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm | (intros; apply GlobalTheory.MultiplierNorm.map_zeta_eq_zpow_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmCurveHomOfPureTypeVectorAnyLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmCurve_hom_of_pureType_vector_anyLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (ε : ℤˣ), ∀ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ φ : C.P.A.left ⟶ Xo.univ.t.G.left, φ ≫ Xo.univ.t.G.hom = C.P.A.hom ≫ F.u i P ∧ ∀ z : ℂ, C.pt z ≫ φ = (F.ex i P (z • P a)).left := by
  first | exact @GlobalTheory.CompRat.exists_hom_of_pureType_of_level | exact GlobalTheory.CompRat.exists_hom_of_pureType_of_level | (intros; apply GlobalTheory.CompRat.exists_hom_of_pureType_of_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmCurveHomOfPureTypeVectorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmCurve_hom_of_pureType_vector : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (ε : ℤˣ), ∀ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ φ : C.P.A.left ⟶ Xo.univ.t.G.left, φ ≫ Xo.univ.t.G.hom = C.P.A.hom ≫ F.u i P ∧ ∀ z : ℂ, C.pt z ≫ φ = (F.ex i P (z • P a)).left := by
  first | exact @GlobalTheory.CompRat.exists_hom_of_pureType | exact GlobalTheory.CompRat.exists_hom_of_pureType | (intros; apply GlobalTheory.CompRat.exists_hom_of_pureType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffCurveOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveField

open GlobalTheory.Ex.UnifModel GlobalTheory.Ex.TorsionField

theorem exists_finset_fixed (hM : Out.MulNSt) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (P : Out.PolAV (Sp M)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset ℂ, (∀ z ∈ s, IsIntegral ℚ z) ∧ ∀ τ : ℂ →+* ℂ, (∀ x ∈ M, τ x = x) → (∀ z ∈ s, τ z = z) →
      ∀ x : Over.mk (spMap (algebraMap M ℂ)) ⟶ P.A, x ^ n = 1 → spMap τ ≫ x.left = x.left := by
  classical
  let F := algebraicClosure M ℂ
  have : IsAlgClosed F := (algebraicClosure.isAlgClosure M ℂ).isAlgClosed
  obtain ⟨s, hs⟩ := exists_finset (F := F) hM P hn
  refine ⟨s.image Subtype.val, fun z hz => ?_, fun τ h₁ h₂ x hx => ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
    exact isIntegral_trans (A := M) _ (mem_algebraicClosure_iff'.1 y.2)
  · let k : Subfield F := RingHom.eqLocusField (τ.comp (algebraMap F ℂ)) (algebraMap F ℂ)
    obtain ⟨y, hy, hy'⟩ := exists_descend_algClosed hM P (algebraMap M F) (algebraMap F ℂ) (algebraMap M ℂ)
      (fun _ => rfl) hn x hx
    obtain ⟨z, hz⟩ := hs k k.subtype (fun c => ⟨⟨algebraMap M F c, h₁ c c.2⟩, rfl⟩)
      (fun c hc => ⟨⟨c, h₂ c (Finset.mem_image_of_mem _ hc)⟩, rfl⟩) y hy
    have e₁ : spMap (algebraMap F ℂ) ≫ spMap k.subtype = spMap ((algebraMap F ℂ).comp k.subtype) :=
      spMap_comp fun _ => rfl
    have e₂ : spMap τ ≫ spMap ((algebraMap F ℂ).comp k.subtype) = spMap ((algebraMap F ℂ).comp k.subtype) :=
      spMap_comp fun c => c.2
    rw [← hy', ← hz, reassoc_of% e₁, reassoc_of% e₂]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_wC_eq (H : Host E) (a : ℤ × ℤ) :
    ∃ m k : ℤ, wC H a = (m : ℂ) + k * ((1 + Complex.I * Real.sqrt H.d) / 2) := by
  have h : H.rt0 ^ 2 = (Complex.I * Real.sqrt H.d) ^ 2 := by
    rw [H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact ⟨a.1, a.2, by rw [wC, h]⟩
  · exact ⟨a.1 + a.2, -a.2, by rw [wC, h]; push_cast; ring⟩

theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z : Fin g → ℂ) (n : ℕ) :
    u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_pow_eq_one (C : Curve H) {n : ℕ} (hn : 0 < n) (a : ℤ × ℤ) :
    (C.u.ex fun _ => C.c * (wC H a / n)) ^ n = 1 := by
  obtain ⟨m, k, h⟩ := exists_wC_eq H a
  rw [← ex_nsmul, C.u.ker]
  refine (C.lat _).2 ⟨m, k, funext fun _ => ?_⟩
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [← h, Pi.smul_apply, nsmul_eq_mul]
  field_simp

theorem exists_model (H : Host E) : ∃ (M : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ M)
    (P : Out.PolAV (Sp M)) (C : Curve H) (ψ : C.P.A.left ⟶ P.A.left),
    IsGrpPullback C.P.A P.A (spMap (algebraMap M ℂ)) ψ := by
  have hd := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) H.d_prime.pos
  obtain ⟨M, _, w, P, v, hw, hg, -, ⟨P₀, π, -, -, ⟨hg₀, hπ, hL₀⟩, -⟩, hcm, -⟩ :=
    cmCurve_closed H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  obtain ⟨PC, ψ, hgC, hψ, hLC⟩ := exists_baseChange firstFiveLaws.1.polBaseChange (spMap (algebraMap M ℂ)) P₀
  obtain ⟨u, hu⟩ := exists_isThetaUnif thetaUnifAV_all PC
  have hL : LBIso PC.L (P.L.pull (ψ ≫ π)) :=
    LBIso.trans PC.isLB (pull_isLB P₀.isLB ψ) (pull_isLB P.isLB _) hLC
      (LBIso.chartPull (Geo.Tor.chartPullPull P₀.L ψ ψ rfl) (Geo.Tor.chartPullSame P.L _ _ _ ψ fun _ => rfl) hL₀.symm)
  obtain ⟨c, hc, hΛ⟩ := hcm PC (ψ ≫ π)
    ⟨hgC.trans hg₀, (hψ.comp hπ).congr (spMap_comp fun _ => rfl) rfl, hL.symm⟩ u
  rw [hw] at hΛ
  exact ⟨M, inferInstance, P₀, ⟨PC, hgC.trans (hg₀.trans hg), u, hu, c, hc, hΛ⟩, ψ, hψ⟩

theorem exists_curveOver (H : Host E) {n : ℕ} (hn : 0 < n) :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ CurveOver H F n := by
  obtain ⟨M, _, P, C, ψ, hψ⟩ := exists_model H
  obtain ⟨s, hs, hfix⟩ := exists_finset_fixed firstFiveLaws.1.mulN M P hn
  have := IntermediateField.finiteDimensional_adjoin (K := ℚ) (S := (s : Set ℂ)) hs
  refine ⟨M ⊔ IntermediateField.adjoin ℚ (s : Set ℂ), inferInstance, fun τ hτ => ?_⟩
  have h₁ : ∀ x ∈ M, (τ : ℂ →+* ℂ) x = x := fun x hx => hτ x (le_sup_left (a := M) hx)
  have h₂ : ∀ z ∈ s, (τ : ℂ →+* ℂ) z = z := fun z hz =>
    hτ z (le_sup_right (a := M) (IntermediateField.subset_adjoin ℚ _ hz))
  have e : spMap (τ : ℂ →+* ℂ) ≫ spMap (algebraMap M ℂ) = spMap (algebraMap M ℂ) :=
    spMap_comp fun c => h₁ c c.2
  have w : ψ ≫ P.A.hom = (C.P.A.hom ≫ spMap (τ : ℂ →+* ℂ)) ≫ spMap (algebraMap M ℂ) := by
    rw [Category.assoc, e, hψ.1.w]
  refine ⟨C, hψ.1.lift _ _ w, hψ.cancel (hψ.congr e.symm (hψ.1.lift_fst _ _ w).symm) (hψ.1.lift_snd _ _ w),
    fun a => ?_⟩
  have h1 : wC H (1, 0) = 1 := by simp [wC]
  rw [h1, _root_.one_mul]
  obtain ⟨ε, hε⟩ := exists_mulEquiv_of_isGrpPullback hψ (𝟙 (Sp ℂ)) (spMap (algebraMap M ℂ)) (Category.id_comp _).symm
  have hx := hfix τ h₁ h₂ (ε (C.u.ex fun _ => C.c * (wC H a / n))) (by
    rw [← map_pow]
    exact (congrArg ε (ex_pow_eq_one C hn a)).trans (map_one ε))
  rw [hε] at hx
  have ho : C.pt (wC H a / n) ≫ C.P.A.hom = 𝟙 _ := Over.w (C.u.ex fun _ => C.c * (wC H a / n))
  refine hψ.1.hom_ext ?_ ?_
  · rw [Category.assoc, hψ.1.lift_fst, Category.assoc]
    exact hx.symm
  · rw [Category.assoc, hψ.1.lift_snd, Category.assoc, ho, reassoc_of% ho, Category.comp_id]

theorem exists_coeff_curveOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (n : ℕ), 0 < n → ∃ c' : Coeff l, c.F ≤ c'.F ∧ ∀ c'' : Coeff l, c'.F ≤ c''.F → CurveOver H c''.F n := by
  intro E _ _ _ H l c n hn
  obtain ⟨F, _, hF⟩ := exists_curveOver H hn
  have := c.fin
  exact ⟨⟨c.F ⊔ F, inferInstance, fun τ a => le_sup_left (b := F) (c.conj τ a), le_sup_left (b := F) c.zeta_mem,
    c.le.trans le_sup_left⟩, le_sup_left, fun c'' h τ hτ => hF τ fun x hx => hτ x (h (le_sup_right (a := c.F) hx))⟩

end GlobalTheory.CurveField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentsPeriodSpacesAnyLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeffField_idempotents_periodSpaces_anyLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  first | exact @GlobalTheory.CompRat.exists_coeff_idempotents_any_level | exact GlobalTheory.CompRat.exists_coeff_idempotents_any_level | (intros; apply GlobalTheory.CompRat.exists_coeff_idempotents_any_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComplexFrobeniusPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_frobenius_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] [Algebra c.F k] (y y' : FrPt Xo c k), ∃ z z' : FrPt Xo c (CAt c.F.val.toRingHom), (∀ ρ : Xo.X ⟶ Xo.X, y'.x = y.x ≫ ρ → z'.x = z.x ≫ ρ) ∧ (∀ f ∈ sec Xo c 0 0, evR Xo c f y = 0 → evR Xo c f z = 0) ∧ ∀ f ∈ sec Xo c 0 0, ∀ a : c.F, evR Xo c f z' = algebraMap c.F (CAt c.F.val.toRingHom) a * evR Xo c f z → evR Xo c f y' = algebraMap c.F k a * evR Xo c f y := by
  first | exact @GlobalTheory.Frames.exists_complex_framed_pair | exact GlobalTheory.Frames.exists_complex_framed_pair | (intros; apply GlobalTheory.Frames.exists_complex_framed_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFiniteAdelicElementMarkingComponentStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelic_element_marking_component : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ k, ∃ h ∈ GfC V, C.Mark h k 1 := by
  first | exact @GlobalTheory.Member.exists_finite_mark | exact GlobalTheory.Member.exists_finite_mark | (intros; apply GlobalTheory.Member.exists_finite_mark <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPureTypePeriodOfSignatureSplit
section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureType

namespace GlobalTheory.CompRat

theorem exists_isSplit_of_splitLat (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (g : ℕ) (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty) (hD : SplitLat D) :
    ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsSplit hP := by
  obtain ⟨Lp, Lm, hs, ho, -, -, hp, hm⟩ := hD
  have two : ∀ m, (D.EF (H.rt • m) m : ℝ) = 2 * D.EF (H.w0 • m) m := fun m => by
    have : D.EF ((2 * H.w0) • m) m = D.EF ((1 + H.rt) • m) m := by rw [H.two_weight_eq_one_add_root]
    rw [two_mul, add_smul, add_smul, one_smul, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      D.alt] at this
    have h : D.EF (H.rt • m) m = 2 * D.EF (H.w0 • m) m := by linarith
    exact_mod_cast h
  obtain ⟨P, hP, k₁, k₂⟩ := GlobalTheory.CM.FamCompare.exists_period D Lp Lm
    (fun z => ⟨1, one_pos, hs ▸ Submodule.mem_top⟩) ho
    (fun x hx => by
      by_cases h : x = 0
      · simp [h]
      · have := hp x hx h
        rw [two] at this
        linarith)
    (fun x hx => by
      by_cases h : x = 0
      · simp [h]
      · have := hm x hx h
        rw [two] at this
        linarith) hty
  exact ⟨P, hP, top_le_iff.1 (hs ▸ sup_le_sup k₁ k₂)⟩

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDataNonemptyComponentStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisationData_nonempty_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ σ : c.F →+* ℂ, ∃ U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q), Nonempty U.Comp := by
  first | exact @GlobalTheory.exists_unf_nonempty_comp | exact GlobalTheory.exists_unf_nonempty_comp | (intros; apply GlobalTheory.exists_unf_nonempty_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationWithComponentAtEveryEmbeddin
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory

theorem exists_unf_nonempty_comp_all : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) → ∀ j (σ : Q.c.F →+* ℂ), ∃ U : Unf (Q.Xo j) Q.c σ D.R.r, Nonempty U.Comp := by
  intro D Q _ h j σ
  obtain ⟨X⟩ := DefiniteData.nonempty_data D.host.E D.R.r
  obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws
    GlobalTheory.firstFiveLaws.2.1.secTwist _ _ _ _ (Q.Xo j) Q.c (h j) σ
  exact ⟨{ Comp := Unit, X := fun _ => X, un := fun _ _ => y }, ⟨()⟩⟩

end GlobalTheory
end

