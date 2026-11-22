import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0006
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGenerators
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompatStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominating_model_chart_compat : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] {κ' : Type} [Finite κ'] {y : κ' → Ω'} (M' : PModel o y) (f : M'.X ⟶ M.X) (e : κ → κ'), Dominates M'.ξ M.ξ f (algebraMap Ω Ω') → (∀ c, x c ≠ 0 → y (e c) ≠ 0) → (∀ c, x c ≠ 0 → ∀ p' : Cpt M'.ξ, InChart M'.ξ y (e c) p' ↔ ∃ p : Cpt M.ξ, p.1 = f p'.1 ∧ InChart M.ξ x c p) → (∀ c, x c ≠ 0 → ∃ s : Finset Ω', ∀ a : Ω', a ∈ chRing o y (e c) ↔ a ∈ Submodule.span (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (s : Set Ω')) → IsFinite f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartFin.isFinite_of_charts | exact GlobalTheory.CompanionTheory.Ar.ChartFin.isFinite_of_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartFin.isFinite_of_charts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingPiecesSmooth
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem val_appLE_of_dominates {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}
    (hd : Dominates ξ' ξ f i) {U : X.Opens} {W : X'.Opens} (e : W ≤ f ⁻¹ᵁ U) (hW : genPt ξ' ∈ W)
    (hU : genPt ξ ∈ U) (t : Γ(X, U)) :
    (X'.presheaf.germ W (genPt ξ') hW ≫ Scheme.stalkClosedPointTo ξ').hom ((f.appLE U W e).hom t) =
      i ((X.presheaf.germ U (genPt ξ) hU ≫ Scheme.stalkClosedPointTo ξ).hom t) := by
  have hfq : f (genPt ξ') ∈ U := e hW
  have hp : genPt ξ ⤳ f (genPt ξ') := by rw [RegAtDom.map_genPt hd]
  have h := RegAtDom.genMap_stalkMap hd (genPt ξ') specializes_rfl hp
    ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t)
  have l1 : X.presheaf.germ U (f (genPt ξ')) hfq ≫ f.stalkMap (genPt ξ') =
      f.appLE U W e ≫ X'.presheaf.germ W (genPt ξ') hW := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have l2 : X'.presheaf.germ W (genPt ξ') hW ≫ X'.presheaf.stalkSpecializes specializes_rfl =
      X'.presheaf.germ W (genPt ξ') hW := TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have l3 : X.presheaf.germ U (f (genPt ξ')) hfq ≫ X.presheaf.stalkSpecializes hp =
      X.presheaf.germ U (genPt ξ) hU := TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have a1 : (f.stalkMap (genPt ξ')).hom ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X'.presheaf.germ W (genPt ξ') hW).hom ((f.appLE U W e).hom t) :=
    congrArg (fun g => g.hom t) l1
  have a2 : ∀ s, (X'.presheaf.stalkSpecializes specializes_rfl).hom
      ((X'.presheaf.germ W (genPt ξ') hW).hom s) = (X'.presheaf.germ W (genPt ξ') hW).hom s :=
    fun s => congrArg (fun g => g.hom s) l2
  have a3 : (X.presheaf.stalkSpecializes hp).hom ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X.presheaf.germ U (genPt ξ) hU).hom t := congrArg (fun g => g.hom t) l3
  rw [a1] at h
  have b1 : genMap ξ' ⟨genPt ξ', specializes_rfl⟩ ((X'.presheaf.germ W (genPt ξ') hW).hom ((f.appLE U W e).hom t)) =
      (X'.presheaf.germ W (genPt ξ') hW ≫ Scheme.stalkClosedPointTo ξ').hom ((f.appLE U W e).hom t) := by
    exact congrArg (Scheme.stalkClosedPointTo ξ').hom (a2 _)
  have b2 : genMap ξ ⟨f (genPt ξ'), hp⟩ ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X.presheaf.germ U (genPt ξ) hU ≫ Scheme.stalkClosedPointTo ξ).hom t := by
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom a3
  rw [← b1, h, b2]

theorem smooth_of_pieces : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'),
    IsCptGen ξ → IsCptGen ξ' → Dominates ξ' ξ f i →
    (∀ p' : X', ∃ (U : X.Opens) (W : X'.Opens) (R : Subring Ω) (C : Subring Ω') (h : ∀ a ∈ R, i a ∈ C),
      IsPiece ξ U R ∧ IsPiece ξ' W C ∧ W ≤ f ⁻¹ᵁ U ∧ p' ∈ W ∧
      ((i.comp R.subtype).codRestrict C (fun a => h a a.2)).Smooth) → Smooth f := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hg hg' hd h
  refine (HasRingHomProperty.iff_exists_appLE (P := @Smooth) (Q := RingHom.Smooth)
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).1).2 fun p' => ?_
  obtain ⟨U, W, R, C, hRC, hU, hW, e, hp, hs⟩ := h p'
  refine ⟨⟨U, hU.affine⟩, ⟨W, hW.affine⟩, hp, e, ?_⟩
  have hWg : genPt ξ' ∈ W := (hW.spec p' hp).mem_open W.isOpen hp
  have hUg : genPt ξ ∈ U := by
    have h1 : f (genPt ξ') ∈ U := e hWg
    rwa [RegAtDom.map_genPt hd] at h1
  obtain ⟨injU, ranU⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hg U hUg hU.spec
  obtain ⟨injW, ranW⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X' Ω' ξ' hg' W hWg hW.spec
  have memR : ∀ t, (X.presheaf.germ U (genPt ξ) hUg ≫ Scheme.stalkClosedPointTo ξ).hom t ∈ R :=
    fun t => (hU.ring _).2 ((ranU _).1 ⟨t, rfl⟩)
  have memC : ∀ t, (X'.presheaf.germ W (genPt ξ') hWg ≫ Scheme.stalkClosedPointTo ξ').hom t ∈ C :=
    fun t => (hW.ring _).2 ((ranW _).1 ⟨t, rfl⟩)
  let eU : Γ(X, U) ≃+* R := RingEquiv.ofBijective
    ((X.presheaf.germ U (genPt ξ) hUg ≫ Scheme.stalkClosedPointTo ξ).hom.codRestrict R memR)
    ⟨fun a b hab => injU (congrArg Subtype.val hab), fun r => by
      obtain ⟨t, ht⟩ := (ranU r.1).2 ((hU.ring r.1).1 r.2)
      exact ⟨t, Subtype.ext ht⟩⟩
  let eW : Γ(X', W) ≃+* C := RingEquiv.ofBijective
    ((X'.presheaf.germ W (genPt ξ') hWg ≫ Scheme.stalkClosedPointTo ξ').hom.codRestrict C memC)
    ⟨fun a b hab => injW (congrArg Subtype.val hab), fun r => by
      obtain ⟨t, ht⟩ := (ranW r.1).2 ((hW.ring r.1).1 r.2)
      exact ⟨t, Subtype.ext ht⟩⟩
  have hval : ∀ t, eW ((f.appLE U W e).hom t) =
      ((i.comp R.subtype).codRestrict C (fun a => hRC a a.2)) (eU t) :=
    fun t => Subtype.ext (val_appLE_of_dominates hd e hWg hUg t)
  have key : (f.appLE U W e).hom = (eW.symm : C →+* Γ(X', W)).comp
      (((i.comp R.subtype).codRestrict C (fun a => hRC a a.2)).comp (eU : Γ(X, U) →+* R)) :=
    RingHom.ext fun t => (eW.symm_apply_eq.2 (hval t).symm).symm
  show RingHom.Smooth (f.appLE U W e).hom
  rw [key]
  exact RingHom.Smooth.comp (RingHom.Smooth.comp (RingHom.Smooth.of_bijective eU.bijective) hs)
    (RingHom.Smooth.of_bijective eW.symm.bijective)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsComplexPointNonvanishing
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_ptOver_ne : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (g : MRing ι) (d : K → ℕ), OverInt y φ → IsMultiHomog g d → g ∉ mCoordIdeal y → ∃ z, PtOver y φ σ z ∧ evC z g ≠ 0 :=
  @PositivityTheory.Xgn.exists_point_over_nonvanishing

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin
section
namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]

def latOn (D : HTChart A K c p R N (Module.Dual K Li)) (V : Submodule K Li) (t : K) (B : Subring K) : Set Li :=
  {e | e ∈ V ∧ ∀ w ∈ D.om', t * w e ∈ B}

def IsLocIn (A : Type) {K : Type} [CommRing A] [Field K] [Algebra A K] (B : Subring K) : Prop :=
  (∀ a : A, algebraMap A K a ∈ B) ∧
    ∀ b ∈ B, ∃ u a : A, algebraMap A K u ≠ 0 ∧ (algebraMap A K u)⁻¹ ∈ B ∧ algebraMap A K u * b = algebraMap A K a

end
end GlobalTheory.CompanionTheory.Ar.Flat.HTL

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

theorem exists_extend_lin {A K V W : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower A K W]
    (M : Submodule A V) (g : M →ₗ[A] W) : ∃ G : V →ₗ[K] W, ∀ z : M, G z = g z := by
  classical
  obtain ⟨b, hbM, -, hsp, hli⟩ := exists_linearIndepOn_id_extension (K := K) (s := ∅) (t := (M : Set V)) (by simp) (by simp)
  let bb := Basis.extend hli
  let f : V → W := fun x => if h : x ∈ M then g ⟨x, h⟩ else 0
  let G : V →ₗ[K] W := bb.constr K fun i => f i.1
  have hGb : ∀ x ∈ b, G x = f x := fun x hx => by
    have hx' : x ∈ hli.extend (Set.subset_univ b) := hli.subset_extend _ hx
    have := bb.constr_basis K (fun i => f i.1) ⟨x, hx'⟩
    simpa [bb, G, Basis.extend_apply_self] using this
  have hG : ∀ x (hx : x ∈ Submodule.span A b) (h : x ∈ M), G x = g ⟨x, h⟩ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro h
      rw [hGb x hx]
      simp [f, h]
    | zero =>
      intro h
      have : (⟨0, h⟩ : M) = 0 := rfl
      rw [this, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro h
      have h1 : x ∈ M := Submodule.span_le.2 hbM hx
      have h2 : y ∈ M := Submodule.span_le.2 hbM hy
      have : (⟨x + y, h⟩ : M) = ⟨x, h1⟩ + ⟨y, h2⟩ := rfl
      rw [map_add, ihx h1, ihy h2, this, map_add]
    | smul a x hx ih =>
      intro h
      have h1 : x ∈ M := Submodule.span_le.2 hbM hx
      have : (⟨a • x, h⟩ : M) = a • ⟨x, h1⟩ := rfl
      rw [this, g.map_smul, ← ih h1, LinearMap.map_smul_of_tower]
  have hden : ∀ v ∈ Submodule.span K b, ∃ a : A, algebraMap A K a ≠ 0 ∧ a • v ∈ Submodule.span A b := by
    intro v hv
    have hinj := IsFractionRing.injective A K
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, by simp, by simpa using Submodule.subset_span hx⟩
    | zero => exact ⟨1, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨a', ha', hy⟩ := hy
      refine ⟨a * a', by rw [map_mul]; exact mul_ne_zero ha ha', ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul r x _ hx =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := A) r
      have hv0 : algebraMap A K v ≠ 0 := (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hv)
      refine ⟨v * a, by rw [map_mul]; exact mul_ne_zero hv0 ha, ?_⟩
      have : (v * a) • (algebraMap A K u / algebraMap A K v) • x = u • a • x := by
        rw [← algebraMap_smul K (v * a), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul, map_mul]
        congr 1
        field_simp
      rw [this]
      exact Submodule.smul_mem _ _ hx
  refine ⟨G, fun z => ?_⟩
  obtain ⟨a, ha, haz⟩ := hden z (hsp z.2)
  have h1 := hG _ haz (M.smul_mem a z.2)
  have h2 : (⟨a • (z : V), M.smul_mem a z.2⟩ : M) = a • z := rfl
  rw [h2, g.map_smul, LinearMap.map_smul_of_tower, ← algebraMap_smul K a (G (z : V)), ← algebraMap_smul K a (g z)] at h1
  exact smul_right_injective W ha h1

section Chart

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ} {Li : Type} [AddCommGroup Li] [Module K Li]
  (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li)

theorem eigProj_dual (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) (w : Module.Dual K Li) :
    eigProj D.ρΩ σ w = w ∘ₗ eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ := by
  ext v
  simp [eigProj, LinearMap.sum_apply, hact]

theorem eigProj_apply (hc : ∀ x, c (c x) = x)
    (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) {e : Li} (he : e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom)) (w : Module.Dual K Li) :
    eigProj D.ρΩ σ w e = w e := by
  rw [eigProj_dual D ρ hact, LinearMap.comp_apply]
  congr 1
  have h1 : ∀ a : 𝓞 E, ρ (RingOfIntegers.mapRingEquiv c a) e = σ (a : E) • e := fun a => by
    rw [LatBasic.mem_eigSp.1 he]
    simp [hc]
  have h2 : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ e = e := by
    apply LatBasic.eigProj_of_mem
    rw [LatBasic.mem_eigSp]
    exact fun a => h1 a
  exact h2

theorem exists_vec [IsDomain A] [IsFractionRing A K] (hc : ∀ x, c (c x) = x)
    (hact : ∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a))
    (σ : E →+* K) (g : Module.Dual A (D.omHT σ)) :
    ∃ e ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom), ∀ z : D.omHT σ,
      (z : Module.Dual K Li) e = algebraMap A K (g z) := by
  haveI : Module.Finite K (Module.Dual K Li) := by
    obtain ⟨S, hS⟩ := D.om_lat.fg
    refine ⟨⟨S, ?_⟩⟩
    rw [← D.om_lat.span_eq_top, ← hS, Submodule.span_span_of_tower]
  haveI : Module.Finite K Li := (Module.finite_dual_iff K).1 inferInstance
  obtain ⟨G, hG⟩ := exists_extend_lin (K := K) (D.omHT σ) ((Algebra.linearMap A K) ∘ₗ g)
  let v : Li := (Module.evalEquiv K Li).symm G
  have hv : ∀ w : Module.Dual K Li, w v = G w := fun w => by
    simpa [v] using Module.apply_evalEquiv_symm_apply w G
  refine ⟨eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v, ?_, ?_⟩
  · have h := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v
    rw [LatBasic.mem_eigSp] at h ⊢
    intro a
    have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
      apply RingOfIntegers.ext
      simp [hc]
    have := h (RingOfIntegers.mapRingEquiv c a)
    simpa [hinv] using this
  · intro z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ σ w = (z : Module.Dual K Li) := hz
    have he : eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v ∈ GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ (σ.comp c.toRingHom) := by
      have h := LatBasic.eigProj_mem (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v
      rw [LatBasic.mem_eigSp] at h ⊢
      intro a
      have hinv : RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
        apply RingOfIntegers.ext
        simp [hc]
      have := h (RingOfIntegers.mapRingEquiv c a)
      simpa [hinv] using this
    rw [← hz', eigProj_apply D ρ hc hact σ he w]
    have h2 : w (eigProj (ρ.comp (RingOfIntegers.mapRingEquiv c : 𝓞 E →+* 𝓞 E)) σ v) = (eigProj D.ρΩ σ w) v := by
      rw [eigProj_dual D ρ hact, LinearMap.comp_apply]
    rw [h2, hz', hv, hG z]
    rfl

end Chart

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGeneratorsStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → L.IsVB r V → ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω E), IsTwistGen ξ x L m φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Twist.exists_twistGen | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Twist.exists_twistGen | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Twist.exists_twistGen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueHostAutEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HostAutTrans

theorem existsUnique_hostAut_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [IsGalois ℚ E] (τ τ' : E →+* ℂ), τ (H.rt : E) = H.rt0 → τ' (H.rt : E) = H.rt0 → ∃! g : HostAut H, τ' = τ.comp g.σ.toRingHom := by
  intro E _ _ _ H _ τ τ' hτ hτ'
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) τ τ'
    (Subsingleton.elim _ _)
  have key : ∀ x, τ' x = τ (σ.symm x) := fun x => by rw [← hσ]; rfl
  refine ⟨⟨σ.symm.toRingEquiv, τ.injective ((key _).symm.trans (hτ'.trans hτ.symm))⟩, ?_, ?_⟩
  · exact RingHom.ext fun x => key x
  · rintro ⟨g₀, hfix⟩ hg
    have hx : ∀ x, g₀ x = σ.symm x := fun x =>
      τ.injective ((RingHom.congr_fun hg x).symm.trans (key x))
    have h0 : g₀ = σ.symm.toRingEquiv := RingEquiv.ext fun x => hx x
    subst h0
    rfl

end GlobalTheory.CompanionTheory.Ar.HostAutTrans
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueLatOfChartBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TieVB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

noncomputable def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (U : X.Opens) (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U) (t : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq t) = secVal ξ U h t := by
  have e : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U (genPt ξ) h :=
    TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2
  have e2 : X.presheaf.germ U q.1 hq ≫ (X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) e)
  exact congrArg (fun f => f.hom t) e2

theorem isUnit_iff_unitAt {q : Cpt ξ} (hi : Function.Injective (genMap ξ q)) (s : X.presheaf.stalk q.1) :
    IsUnit s ↔ unitAt ξ q (genMap ξ q s) := by
  constructor
  · intro hs
    have hu := hs.map (genMap ξ q)
    refine ⟨hu.ne_zero, ⟨s, rfl⟩, ?_⟩
    obtain ⟨u, rfl⟩ := hs
    refine ⟨(u⁻¹ : (X.presheaf.stalk q.1)ˣ).1, ?_⟩
    have : genMap ξ q u.1 * genMap ξ q (u⁻¹ : (X.presheaf.stalk q.1)ˣ).1 = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact eq_inv_of_mul_eq_one_right this
  · rintro ⟨h0, -, ⟨s', hs'⟩⟩
    have : s * s' = 1 := hi (by rw [map_mul, hs', map_one, mul_inv_cancel₀ h0])
    exact IsUnit.of_mul_eq_one _ this

theorem mem_basicOpen_iff (hg : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (t : Γ(X, U)) : q.1 ∈ X.basicOpen t ↔ unitAt ξ q (secVal ξ U h t) := by
  rw [Scheme.mem_basicOpen X t q.1 hq, isUnit_iff_unitAt (hg.inj q), genMap_germ U h q hq]

theorem unitAt_mul {p : Cpt ξ} {s t : Ω} (hs : unitAt ξ p s) (ht : unitAt ξ p t) : unitAt ξ p (s * t) :=
  ⟨mul_ne_zero hs.1 ht.1, mul_mem hs.2.1 ht.2.1, by rw [mul_inv]; exact mul_mem hs.2.2 ht.2.2⟩

theorem unitAt_one (p : Cpt ξ) : unitAt ξ p 1 := ⟨one_ne_zero, one_mem _, by simp [one_mem]⟩

theorem regAt_genPt (hg : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) := by
  obtain ⟨s, rfl⟩ := hg.bij.2 a
  refine ⟨s, ?_⟩
  unfold genMap
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  erw [Category.id_comp]
  rfl

section Chart

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}

theorem exists_chart (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ (U : X.Opens) (h : genPt ξ ∈ U), IsAffineOpen U ∧ (∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q) ∧
      (∀ q : X, q ∈ U → genPt ξ ⤳ q) ∧
      Function.Injective (secVal ξ U h) ∧
      ∀ a : Ω, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ a ∈ (secVal ξ U h).range := by
  obtain ⟨U, hU, hmem⟩ := hT.affine c hc
  have h : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, hc, fun c' => regAt_genPt hT.gen _⟩
  have hsp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => by
    obtain ⟨h2, _⟩ := (hmem q).1 hq
    exact h2
  have hUq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := fun q =>
    ⟨fun hq => by obtain ⟨_, h2⟩ := (hmem q.1).1 hq; exact h2, fun hq => (hmem q.1).2 ⟨q.2, hq⟩⟩
  obtain ⟨hinj, hran⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hT.gen U h hsp
  refine ⟨U, h, hU, hUq, hsp, hinj, fun a => ?_⟩
  rw [hT.ring c hc a]
  refine Iff.trans ?_ (hran a).symm
  exact forall_congr' fun q => (by rw [hUq q])

theorem exists_point (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) (P : Ideal (chartRing o x c)) (hP : P.IsPrime) :
    ∃ p : Cpt ξ, InChart ξ x c p ∧ ∀ s : chartRing o x c, s ∈ P ↔ ¬ unitAt ξ p s := by
  obtain ⟨U, h, hU, hUq, hsp, -, hran⟩ := exists_chart hT hc
  let φ : Γ(X, U) →+* chartRing o x c :=
    (secVal ξ U h).codRestrict (chartRing o x c) fun t => (hran _).2 ⟨t, rfl⟩
  let y : PrimeSpectrum Γ(X, U) := ⟨P.comap φ, inferInstance⟩
  have hyU : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this
  let q : Cpt ξ := ⟨_, hsp _ hyU⟩
  refine ⟨q, (hUq q).1 hyU, fun s => ?_⟩
  obtain ⟨t, ht⟩ := (hran s).1 s.2
  have hst : s = φ t := Subtype.ext ht.symm
  have key : q.1 ∈ X.basicOpen t ↔ t ∉ P.comap φ := by
    show y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen t ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  have h2 := mem_basicOpen_iff hT.gen U h q hyU t
  have h3 : (s : Ω) = secVal ξ U h t := ht.symm
  rw [h3, ← h2, key, hst, Ideal.mem_comap, not_not]

theorem chart_le_regAt (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ chartRing o x c) : a ∈ regAt ξ p :=
  (hT.ring c hp.1 a).1 ha p hp

theorem exists_den (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) {a : Ω}
    (ha : a ∈ regAt ξ p) : ∃ s ∈ chartRing o x c, unitAt ξ p s ∧ s * a ∈ chartRing o x c :=
  (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ x hT c p hp a).1 ha

theorem exists_pow_mul_mem (hT : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) {f a : Ω} (hf : f ∈ chartRing o x c)
    (h : ∀ p : Cpt ξ, InChart ξ x c p → unitAt ξ p f → a ∈ regAt ξ p) :
    ∃ n : ℕ, f ^ n * a ∈ chartRing o x c := by
  let I : Ideal (chartRing o x c) :=
    { carrier := {s | (s : Ω) * a ∈ chartRing o x c}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : chartRing o x c) : Ω) * a ∈ chartRing o x c
        have : ((u + v : chartRing o x c) : Ω) * a = (u : Ω) * a + (v : Ω) * a := by
          push_cast; ring
        rw [this]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : chartRing o x c) : Ω) * a ∈ chartRing o x c
        simp
      smul_mem' := fun t u hu => by
        show ((t • u : chartRing o x c) : Ω) * a ∈ chartRing o x c
        have : ((t • u : chartRing o x c) : Ω) * a = (t : Ω) * ((u : Ω) * a) := by
          simp [_root_.mul_assoc]
        rw [this]
        exact mul_mem t.2 hu }
  have hrad : (⟨f, hf⟩ : chartRing o x c) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hle, hP⟩
    by_contra hfP
    obtain ⟨p, hp, hs⟩ := exists_point hT hc P hP
    have hu : unitAt ξ p f := by
      by_contra hn
      exact hfP ((hs ⟨f, hf⟩).2 hn)
    obtain ⟨s, hsA, hsu, hsa⟩ := exists_den hT hp (h p hp hu)
    exact (hs ⟨s, hsA⟩).1 (hle hsa) hsu
  obtain ⟨n, hn⟩ := hrad
  exact ⟨n, hn⟩

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_den_span (hT : CoordTie o ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p) (M : AddSubgroup E)
    (hM : ∀ a ∈ chartRing o x c, ∀ e ∈ M, a • e ∈ M) {e : E}
    (he : e ∈ Submodule.span (regAt ξ p) (M : Set E)) :
    ∃ s ∈ chartRing o x c, unitAt ξ p s ∧ s • e ∈ M := by
  induction he using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_mem _, unitAt_one p, by simpa using hv⟩
  | zero => exact ⟨1, one_mem _, unitAt_one p, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨s, hs, hsu, hsM⟩ := hu
    obtain ⟨t, ht, htu, htM⟩ := hv
    refine ⟨s * t, mul_mem hs ht, unitAt_mul hsu htu, ?_⟩
    have h1 : (s * t) • (u + v) = t • s • u + s • t • v := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [h1]
    exact add_mem (hM t ht _ hsM) (hM s hs _ htM)
  | smul r u _ hu =>
    obtain ⟨s, hs, hsu, hsM⟩ := hu
    obtain ⟨t, ht, htu, htr⟩ := exists_den hT hp r.2
    refine ⟨t * s, mul_mem ht hs, unitAt_mul htu hsu, ?_⟩
    have h1 : (t * s) • r • u = (t * (r : Ω)) • s • u := by
      rw [Subring.smul_def, smul_smul, smul_smul]
      congr 1
      ring
    rw [h1]
    exact hM _ htr _ hsM

end Chart

section Bundle

variable {κ : Type} {x : κ → Ω} {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

noncomputable def latOf (ξ : Spec (CommRingCat.of Ω) ⟶ X) (W : ChartBundle ℤ x r E) : Lat ξ E := fun p =>
  Submodule.span (regAt ξ p) {e | ∃ c, InChart ξ x c p ∧ e ∈ W.lat c}

end Bundle

end GlobalTheory.CompanionTheory.Ar.TieVB

namespace GlobalTheory.CompanionTheory.Ar

end GlobalTheory.CompanionTheory.Ar
end

