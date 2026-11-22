import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0040
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem isPullback_overPullback_map_left {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (q : X ⟶ Y) :
    IsPullback (pullback.fst X.hom f) ((Over.pullback f).map q).left q.left (pullback.fst Y.hom f) := by
  refine IsPullback.of_bot (h₃₁ := f) (v₂₁ := pullback.snd Y.hom f) (v₂₂ := Y.hom) ?_ ?_
    (IsPullback.of_hasPullback Y.hom f)
  · have h₁ : ((Over.pullback f).map q).left ≫ pullback.snd Y.hom f = pullback.snd X.hom f :=
      Over.w ((Over.pullback f).map q)
    have h₂ : q.left ≫ Y.hom = X.hom := Over.w q
    rw [h₁, h₂]
    exact IsPullback.of_hasPullback X.hom f
  · exact (pullback.lift_fst _ _ _).symm

theorem nonempty_torusExtension_pullback {k Ω : Type} [Field k] [Field Ω] (f : Sp Ω ⟶ Sp k)
    (G : Over (Sp k)) [GrpObj G] (h : Nonempty (TorusExtension G)) :
    Nonempty (TorusExtension ((Over.pullback f).obj G)) := by
  obtain ⟨T⟩ := h
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange (Sp k) (Sp Ω) f T.X
  have hq := isPullback_overPullback_map_left f T.q
  refine ⟨{ X := T.X
            addCommGroup := T.addCommGroup
            free := T.free
            finite := T.finite
            B := (Over.pullback f).obj T.B
            grpB := inferInstance
            isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
            q := (Over.pullback f).map T.q
            q_hom := inferInstance
            q_flat := MorphismProperty.of_isPullback (P := @Flat) hq T.q_flat
            q_surjective := MorphismProperty.of_isPullback (P := @Surjective) hq T.q_surjective
            q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) hq T.q_quasiCompact
            i := e.hom ≫ (Over.pullback f).map T.i
            i_hom := inferInstance
            isKernel := ?_ }⟩
  have hk := T.isKernel.map (Over.pullback f)
  refine IsPullback.of_iso hk e.symm (Iso.refl _) (Functor.Monoidal.εIso (Over.pullback f)).symm (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · exact toUnit_unique _ _
  · simp
  · simp

theorem exists_ringHom_comp_eq_of_isIntegral {W k Ω : Type} [CommRing W] [IsLocalRing W] [Field k] [Field Ω]
    [IsAlgClosed Ω] (ρ : W →+* k) (hρ : RingHom.ker ρ = IsLocalRing.maximalIdeal W) (hi : ρ.IsIntegral)
    (φ : W →+* Ω) (hφ : RingHom.ker φ = IsLocalRing.maximalIdeal W) : ∃ ψ : k →+* Ω, ψ.comp ρ = φ := by
  let ρ' : IsLocalRing.ResidueField W →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) ρ fun a ha => (RingHom.mem_ker).1 (hρ ▸ ha)
  let φ' : IsLocalRing.ResidueField W →+* Ω :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) φ fun a ha => (RingHom.mem_ker).1 (hφ ▸ ha)
  letI := ρ'.toAlgebra
  letI := φ'.toAlgebra
  have hi' : ρ'.IsIntegral := RingHom.IsIntegral.tower_top (IsLocalRing.residue W) ρ' hi
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField W) k := ⟨hi'⟩
  let ψ : k →ₐ[IsLocalRing.ResidueField W] Ω := IsAlgClosed.lift
  refine ⟨ψ.toRingHom, RingHom.ext fun x => ?_⟩
  exact ψ.commutes (IsLocalRing.residue W x)

theorem isSemiAbelian_of_proper_generic_of_torusExtension : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], SmConn G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ (k : Type) [Field k] (ρ : W →+* k), RingHom.ker ρ = IsLocalRing.maximalIdeal W → ρ.IsIntegral → Nonempty (TorusExtension ((Over.pullback (spMap ρ)).obj G)) → IsSemiAbelian G := by
  intro W L _ _ _ _ _ _ G _ hG hp k _ ρ hρ hi hT
  obtain ⟨hc, hs, hsep, hqc, hgc⟩ := hG
  have key : ∀ (Ω F : Type) [Field Ω] [Field F] (a : W →+* F) (ψ : F →+* Ω),
      Nonempty (TorusExtension ((Over.pullback (spMap a)).obj G)) →
      Nonempty (TorusExtension ((Over.pullback (spMap (ψ.comp a))).obj G)) := by
    intro Ω F _ _ a ψ h
    obtain ⟨E⟩ := nonempty_torusExtension_pullback (spMap ψ) _ h
    have e : spMap (ψ.comp a) = spMap ψ ≫ spMap a := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e]
    have : IsMonHom (pullCompIso (spMap ψ) (spMap a) G).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso (spMap ψ) (spMap a) G).inv)
    exact ⟨torusExtOfIso (pullCompIso (spMap ψ) (spMap a) G).symm E⟩
  have hA : IsAbelianScheme ((Over.pullback (spMap (algebraMap W L))).obj G) :=
    { comm := inferInstance
      smooth := by change Smooth (pullback.snd G.hom _); infer_instance
      proper := hp
      geomConnected := by change GeometricallyConnected (pullback.snd G.hom _); infer_instance }
  refine ⟨hc, hs, hsep, hqc, hgc, fun Ω _ _ q => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  change Nonempty (TorusExtension ((Over.pullback (spMap φ.hom)).obj G))
  by_cases h : RingHom.ker φ.hom = ⊥
  · have hinj := (RingHom.injective_iff_ker_eq_bot _).2 h
    have e : (IsFractionRing.lift (K := L) hinj).comp (algebraMap W L) = φ.hom :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    rw [← e]
    exact key Ω L _ _ ⟨GlobalTheory.torusExtensionOfAbelian _ hA⟩
  · have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ.hom).isMaximal h)
    obtain ⟨ψ, e⟩ := exists_ringHom_comp_eq_of_isIntegral ρ hρ hi φ.hom hm
    rw [← e]
    exact key Ω k _ _ hT

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemRangeAppLEChartIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ

open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs

def wtZeroSubring {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ H) (V : H.left.Opens) : Subring Γ(H.left, V) where
  carrier := {u | HasWt i V u 0}
  one_mem' := hasWt_one i V
  zero_mem' := fun Y t g h h' => by rw [map_zero, map_zero, mul_zero]
  mul_mem' := fun {a b} ha hb Y t g h h' => by
    have h₁ := ha Y t g h h'
    have h₂ := hb Y t g h h'
    rw [charUnit_zero_val, map_one, _root_.one_mul] at h₁ h₂ ⊢
    rw [map_mul, map_mul, h₁, h₂]
  add_mem' := fun {a b} ha hb Y t g h h' => by
    rw [map_add, map_add, ha Y t g h h', hb Y t g h h', mul_add]
  neg_mem' := fun {a} ha Y t g h h' => by
    rw [map_neg, map_neg, ha Y t g h h', mul_neg]

theorem hasWt_zero_appLE_base {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ H) (V : H.left.Opens) (a : Γ(S, ⊤)) :
    HasWt i V ((H.hom.appLE ⊤ V le_top).hom a) 0 := by
  intro Y t g h h'
  rw [charUnit_zero_val, map_one, _root_.one_mul]
  refine (appLE_appLE _ H.hom (U := ⊤) le_top h' a).trans (Eq.trans ?_ (appLE_appLE _ H.hom (U := ⊤) le_top h a).symm)
  exact congrArg (fun ψ : Γ(S, ⊤) ⟶ Γ(Y.left, ⊤) => ψ.hom a)
    (appLE_of_eq ((Over.w _).trans (Over.w _).symm) _ _ _ _)

theorem mem_range_appLE_chart_iff {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N)
    (W : Y.Opens) (a : Fin (N + 1)) (h : W ≤ φ ⁻¹ᵁ chart R N a) (u : Γ(Y, W)) :
    u ∈ Set.range (φ.appLE (chart R N a) W h).hom ↔
      u ∈ Subring.closure (Set.range ((φ ≫ PSpace.str R N).appLE ⊤ W le_top).hom ∪
        Set.range (pullRatio φ W a h)) := by
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨p, rfl⟩ := aeval_ratio_surjective R N a v
    have e := congrArg (fun t => t p) (appLE_comp_aeval_ratio (φ := φ) (hi := h))
    refine (show _ = _ from e) ▸ ?_
    clear e
    induction p using MvPolynomial.induction_on with
    | C r =>
      rw [MvPolynomial.eval₂Hom_C]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (Subring.subset_closure (Or.inr ⟨j, rfl⟩))
  · intro hu
    have : Subring.closure (Set.range ((φ ≫ PSpace.str R N).appLE ⊤ W le_top).hom ∪
        Set.range (pullRatio φ W a h)) ≤ (φ.appLE (chart R N a) W h).hom.range := by
      rw [Subring.closure_le]
      rintro _ (⟨v, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨_, appLE_appLE φ (PSpace.str R N) (le_top : chart R N a ≤ _) h v⟩
      · exact ⟨_, rfl⟩
    exact this hu

theorem Charts.exists_proper_image {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) (C : Charts Y)
    [Nonempty Y] : ∃ (B : Scheme.{0}) (p : B ⟶ Sp R) (q : Y ⟶ B), q ≫ p = f ∧ IsProper p ∧ IsAffineHom q ∧
      ∃ V : {i // C.wt i = C.c₀} → B.Opens, ⨆ a, V a = ⊤ ∧ ∀ a, IsAffineOpen (V a) ∧ ∃ h : C.W a = q ⁻¹ᵁ V a,
        Function.Injective (q.appLE (V a) (C.W a) h.le).hom ∧ ∀ u,
          u ∈ Set.range (q.appLE (V a) (C.W a) h.le).hom ↔
          u ∈ Subring.closure (Set.range (f.appLE ⊤ (C.W a) le_top).hom ∪
            {v | ∃ j, C.wt j = C.c₀ ∧ v = C.r a j}) := by
  have hne : Nonempty {i // C.wt i = C.c₀} := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    obtain ⟨a, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (C.cover.ge (Set.mem_univ y))
    exact ⟨a⟩
  obtain ⟨n, ⟨e₀⟩⟩ := Finite.exists_equiv_fin {i // C.wt i = C.c₀}
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := by
    cases n with
    | zero => exact (e₀ hne.some).elim0
    | succ N => exact ⟨N, rfl⟩
  let e := e₀.symm
  have hC : IsCoordFamily (fun i : Fin (N + 1) => C.W (e i)) (fun i j => C.r (e i) (e j).1) :=
    { cover := (e.iSup_comp (g := C.W)).trans C.cover
      self := fun i => C.r_self _
      mul := fun i j k => (C.trans _ _ _).symm
      basicOpen_le := fun i j => (C.inter _ _).ge.trans inf_le_right }
  obtain ⟨φ, hφ, hpre, hr⟩ : ∃ φ : Y ⟶ PSpace R N, φ ≫ PSpace.str R N = f ∧
      ∃ hpre : ∀ i, φ ⁻¹ᵁ chart R N i = C.W (e i), ∀ i j,
        pullRatio φ (C.W (e i)) i (hpre i).ge j = C.r (e i) (e j).1 :=
    ⟨hC.toHom f, hC.toHom_str f, hC.toHom_preimage f, hC.pullRatio_toHom f⟩
  have haff : IsAffineHom φ := isAffineHom_of_forall_exists_isAffineOpen φ fun x => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 ((iSup_chart R N).ge (Set.mem_univ x))
    exact ⟨_, hi, isAffineOpen_chart R N i, (hpre i).symm ▸ C.aff _⟩
  have hq : ∀ i, C.W (e i) = φ.toImage ⁻¹ᵁ φ.imageι ⁻¹ᵁ chart R N i := fun i => by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toImage_imageι, hpre]
  have hV : ∀ i, IsAffineOpen (φ.imageι ⁻¹ᵁ chart R N i) := fun i => (isAffineOpen_chart R N i).preimage _
  have hcov : ⨆ i, φ.imageι ⁻¹ᵁ chart R N i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, iSup_chart, Scheme.Hom.preimage_top]
  have := isProper_str R N
  refine ⟨φ.image, φ.imageι ≫ PSpace.str R N, φ.toImage, by rw [Scheme.Hom.toImage_imageι_assoc, hφ],
    inferInstance, ?_, fun a => φ.imageι ⁻¹ᵁ chart R N (e₀ a),
    (e₀.iSup_comp (g := fun i => φ.imageι ⁻¹ᵁ chart R N i)).trans hcov, fun a => ?_⟩
  · refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ x))
    exact ⟨_, hi, hV i, hq i ▸ C.aff _⟩
  · obtain ⟨i, rfl⟩ := e.surjective a
    have hi : e₀ (e i) = i := e₀.apply_symm_apply i
    beta_reduce
    rw [hi]
    refine ⟨hV i, hq i, ?_, fun u => ?_⟩
    · have key : ∀ (W : Y.Opens) (h : W = φ.toImage ⁻¹ᵁ φ.imageι ⁻¹ᵁ chart R N i),
          Function.Injective (φ.toImage.appLE _ W h.le).hom := by
        rintro _ rfl
        rw [Scheme.Hom.appLE_eq_app]
        exact φ.toImage_app_injective ⟨_, isAffineOpen_chart R N i⟩
      exact key _ (hq i)
    · have hs : {v | ∃ j, C.wt j = C.c₀ ∧ v = C.r (e i) j} =
          Set.range (pullRatio φ (C.W (e i)) i (hpre i).ge) := by
        ext v
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨e₀ ⟨j, hj⟩, (hr i _).trans (by rw [show e (e₀ ⟨j, hj⟩) = ⟨j, hj⟩ from e₀.symm_apply_apply _])⟩
        · rintro ⟨j, rfl⟩
          exact ⟨_, (e j).2, hr i j⟩
      rw [hs, ← hφ, ← mem_range_appLE_chart_iff]
      have hc : ∀ v, (φ.toImage.appLE _ _ (hq i).le).hom ((φ.imageι.app (chart R N i)).hom v) =
          (φ.appLE (chart R N i) _ (hpre i).ge).hom v := fun v => by
        rw [Scheme.Hom.app_eq_appLE, appLE_appLE]
        exact congrArg (fun ψ : _ ⟶ Γ(Y, C.W (e i)) => ψ.hom v) (appLE_of_eq φ.toImage_imageι _ _ _ _)
      constructor
      · rintro ⟨w, rfl⟩
        obtain ⟨v, rfl⟩ := φ.imageι.app_surjective _ (isAffineOpen_chart R N i) w
        exact ⟨v, (hc v).symm⟩
      · rintro ⟨v, rfl⟩
        exact ⟨_, hc v⟩

theorem Charts.Torus.exists_proper_quotient :
    ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), C.Torus c i → ∃ (B : Over (Sp K)) (q : H ⟶ B), IsProper B.hom ∧ IsAffineHom q.left ∧ ∃ V : {i // C.wt i = C.c₀} → B.left.Opens, ⨆ a, V a = ⊤ ∧ ∀ a, IsAffineOpen (V a) ∧ ∃ h : C.W a = q.left ⁻¹ᵁ V a, Function.Injective (q.left.appLE (V a) (C.W a) h.le).hom ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE (V a) (C.W a) h.le).hom := by
  intro K _ H _ _ _ _ _ C d c i hT
  have : Nonempty H.left := ⟨(η : 𝟙_ (Over (Sp K)) ⟶ H).left (⊥ : PrimeSpectrum K)⟩
  obtain ⟨B, p, q, hq, hp, ha, V, hV, h⟩ := C.exists_proper_image H.hom
  refine ⟨Over.mk p, Over.homMk q hq, hp, ha, V, hV, fun a => ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h a
  refine ⟨h₁, h₂, h₃, fun u => ⟨fun hu => (h₄ u).2 (hT.gen a u hu), fun hu => ?_⟩⟩
  refine (Subring.closure_le (t := wtZeroSubring i (C.W a))).2 ?_ ((h₄ u).1 hu)
  rintro _ (⟨v, rfl⟩ | ⟨j, hj, rfl⟩)
  · exact hasWt_zero_appLE_base i _ v
  · exact hT.inv a j hj

end GlobalTheory.ZJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisingFactor
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.SymLift

theorem odd_root_iff {U : Type} [CommGroup U] (j : ℕ) (E P w : U) (h : E ^ (2 * j + 1) = P ^ 2) :
    w = P / E ^ j ↔ (w ^ 2 = E ∧ w ^ (2 * j + 1) = P) := by
  constructor
  · rintro rfl
    have h' := congrArg Additive.ofMul h
    simp only [ofMul_pow] at h'
    constructor
    · apply Additive.ofMul.injective
      simp only [ofMul_pow, ofMul_div]
      linear_combination (norm := module) -h'
    · apply Additive.ofMul.injective
      simp only [ofMul_pow, ofMul_div]
      linear_combination (norm := module) -(j • h')
  · rintro ⟨rfl, rfl⟩
    rw [← pow_mul, pow_succ, mul_div_cancel_left]

variable {O : Type} [CommRing O] (N : NumD O)

theorem tk_pow {k : ℕ} (p p' : N.QT k) :
    N.tk p p' ^ k = N.τ p.1.1.toAdd p'.1.1.toAdd *
      (cubN N.θ k 1 p.1.2.b (p'.1.2.b ^ k) * cubN N.θ k 1 p'.1.2.b p.1.2.b ^ k) := by
  have a := NumD.Gt.pow_s p.1.2 k p'.1.1.toAdd
  rw [N.mem_QT.1 p.2, NumD.io_s, ← N.QT_pow_b p'] at a
  rw [NumD.tk, mul_pow, ← a, mul_assoc]

theorem tk_mul_left {k : ℕ} (p p' p'' : N.QT k) :
    N.tk (p * p') p'' * N.θ p''.1.2.b p.1.2.b p'.1.2.b ^ k = N.tk p p'' * N.tk p' p'' := by
  have a := N.cub.N_add k 1 p''.1.2.b p.1.2.b p'.1.2.b
  rw [N.cub.face, mul_one, one_mul, N.QT_pow_b p''] at a
  change p.1.2.s p''.1.1.toAdd * p'.1.2.s p''.1.1.toAdd / N.θ (N.c p''.1.1.toAdd) p.1.2.b p'.1.2.b *
    cubN N.θ k 1 p''.1.2.b (p.1.2.b * p'.1.2.b) * _ = _
  replace a := congrArg Additive.ofMul a
  apply Additive.ofMul.injective
  simp only [NumD.tk, ofMul_mul, ofMul_div] at a ⊢
  linear_combination (norm := abel) a

theorem tk_one_left {k : ℕ} (p : N.QT k) : N.tk 1 p = 1 := by
  change 1 * cubN N.θ k 1 p.1.2.b 1 = 1
  rw [N.cub.N_one, one_mul]

theorem wQ_iff {k : ℕ} (hk : Odd k) (p : N.QT k) (w : Oˣ) :
    w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧
      w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b) := by
  obtain ⟨j, rfl⟩ := hk
  have e : N.wQ p = N.ψ p.1.1.toAdd * mulq N.θ N.σ (2 * j + 1) p.1.2.b /
      (N.tk p p / dbl N.θ N.σ p.1.2.b ^ (2 * j + 1)) ^ j := by
    have : (2 * j + 1 - 1) / 2 = j := by omega
    simp only [NumD.wQ, NumB.wS, NumD.tk, this]
  rw [e, odd_root_iff, eq_div_iff_mul_eq']
  have a := tk_pow N p p
  have b := (GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N 0 p.1.1.toAdd).1
  have c := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB (2 * j + 1) 0 p.1.2.b 1).2.2.1
  rw [← N.QT_pow_b p] at b
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b c ⊢
  linear_combination (norm := module) a + b + c

theorem dbl_mul (x y : N.A) :
    dbl N.θ N.σ (x * y) * (N.θ (x * y) x y * N.θ x x y * N.θ y x y) = dbl N.θ N.σ x * dbl N.θ N.σ y := by
  have a := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB 2 0 x y).2.1
  have c := N.cub.coc x y y x
  rw [N.cub.s12 (x * y), N.cub.s12 x y x, N.cub.s12 x (y * y), N.cub.s12 y y x] at c
  simp only [mulq, cubN, Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, one_mul, mul_one,
    N.cub.face, div_one, sq] at a
  rw [N.cub.s12 y y x] at a
  replace a := congrArg Additive.ofMul a
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_one] at a c ⊢
  linear_combination (norm := abel) c - a

theorem wQ_mul {k : ℕ} (hk : Odd k) (p p' : N.QT k) :
    N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') := by
  obtain ⟨a₁, a₂⟩ := (wQ_iff N hk p _).1 rfl
  obtain ⟨b₁, b₂⟩ := (wQ_iff N hk p' _).1 rfl
  rw [← div_eq_iff_eq_mul', wQ_iff N hk]
  have k₁ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p).2.2.2.1
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  constructor
  · have t₁ := tk_mul_left N p p' (p * p')
    have t₂ := tk_mul_left N p p' p
    have t₃ := tk_mul_left N p p' p'
    have w₂ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p).1
    have w₃ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p').1
    have d := dbl_mul N p.1.2.b p'.1.2.b
    have e : (p * p').1.2.b = p.1.2.b * p'.1.2.b := rfl
    rw [e] at t₁ ⊢
    obtain ⟨j, rfl⟩ := hk
    have : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [this]
    have a₁ := E a₁; have b₁ := E b₁; have k₁ := E k₁; have t₁ := E t₁; have t₂ := E t₂; have t₃ := E t₃
    have w₂ := E w₂; have w₃ := E w₃; have d := E d
    apply Additive.ofMul.injective
    simp only [NumD.wp, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₁ b₁ k₁ t₁ t₂ t₃ w₂ w₃ d ⊢
    linear_combination (norm := module) a₁ + b₁ - k₁ - t₁ - t₂ - t₃ + w₂ + w₃ + (2 * j + 1) • d
  · have t := tk_pow N p p'
    have m := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB k 0 p.1.2.b p'.1.2.b).2.1
    have s := N.ψ_add p.1.1.toAdd p'.1.1.toAdd
    change _ = N.ψ (p.1.1.toAdd + p'.1.1.toAdd) * mulq N.θ N.σ k (p.1.2.b * p'.1.2.b)
    have a₂ := E a₂; have b₂ := E b₂; have k₁ := E k₁; have t := E t; have m := E m; have s := E s
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₂ b₂ k₁ t m s ⊢
    linear_combination (norm := module) a₂ + b₂ - ((k + 1) / 2) • k₁ + t - m - s

theorem wQ_inv {k : ℕ} (hk : Odd k) (p : N.QT k) : N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p := by
  obtain ⟨a₁, a₂⟩ := (wQ_iff N hk p _).1 rfl
  rw [← eq_div_iff_mul_eq', eq_comm, wQ_iff N hk]
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  have e : (p⁻¹).1.2.b = p.1.2.b⁻¹ := rfl
  constructor
  · have t₁ := tk_mul_left N p p⁻¹ p⁻¹
    have t₂ := tk_mul_left N p p⁻¹ p
    have w₁ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p⁻¹ p).1
    have w₂ := (GlobalTheory.T.degenerationWeilPairing_properties O N k 1 1 p).1
    have s := N.σ_inv p.1.2.b
    rw [mul_inv_cancel] at t₁ t₂ w₁
    rw [mul_one, left_eq_mul] at w₂
    rw [w₂] at w₁
    rw [tk_one_left, e] at t₁ t₂
    rw [N.cub.s01 p.1.2.b p.1.2.b p.1.2.b⁻¹, N.cub.s12 p.1.2.b p.1.2.b p.1.2.b⁻¹] at t₂
    rw [e]
    have a₁ := E a₁; have t₁ := E t₁; have t₂ := E t₂; have w₁ := E w₁; have s := E s
    apply Additive.ofMul.injective
    simp only [NumD.wp, dbl, inv_inv, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₁ t₁ t₂ w₁ s ⊢
    linear_combination (norm := module) a₁ + t₁ - t₂ + w₁ - k • s
  · have m := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB k 0 p.1.2.b 1).2.2.2
    have s := N.even p.1.1.toAdd
    rw [← N.QT_pow_b p] at s
    change _ = N.ψ (-p.1.1.toAdd) * mulq N.θ N.σ k p.1.2.b⁻¹
    have a₂ := E a₂; have m := E m; have s := E s
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at a₂ m s ⊢
    linear_combination (norm := module) a₂ - m - s

theorem normalising_factor : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ), Odd k → ∀ p p' : N.QT k, (∀ w : Oˣ, w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧ w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b)) ∧ N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') ∧ N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p :=
  fun _ _ N _ hk p p' => ⟨wQ_iff N hk p, wQ_mul N hk p p', wQ_inv N hk p⟩

end GlobalTheory.Ex.SymLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfSmoothThickeningsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_of_smooth_thickenings' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (B : Over (Spec (CommRingCat.of R))), IsProper B.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ B.left), (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, Smooth (Y e).hom) → Smooth B.hom := by
  first | exact @GlobalTheory.SmoothThickenings.smooth_of_smooth_thickenings | exact GlobalTheory.SmoothThickenings.smooth_of_smooth_thickenings | (intros; apply GlobalTheory.SmoothThickenings.smooth_of_smooth_thickenings <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusExtensionDescendsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.splitTorus_extension_descends_alt : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [GrpObj B₀] (X : Type) [AddCommGroup X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap β) φG → IsGrpPullback B B₀ (spMap β) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G) (q₀ : G₀ ⟶ B₀) (i₀ : splitTorus (Sp k) X ⟶ G₀), φG ≫ q₀.left = q.left ≫ φ → GlobalTheory.SplitTorus.bcMap (spMap β) X ≫ i₀.left = i.left ≫ φG → IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → IsMonHom q₀ ∧ Flat q₀.left ∧ Surjective q₀.left ∧ QuasiCompact q₀.left ∧ IsMonHom i₀ ∧ IsPullback i₀ (toUnit _) q₀ (η[B₀] : 𝟙_ _ ⟶ B₀) := by
  first | exact @GlobalTheory.splitTorus_extension_descends | exact GlobalTheory.splitTorus_extension_descends | (intros; apply GlobalTheory.splitTorus_extension_descends <;> assumption)
end

