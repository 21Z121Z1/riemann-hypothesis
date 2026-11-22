import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0162

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRepresentableFiniteFree
section
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRep

theorem exists_finite_free_rep (O : Type) [CommRing O] [HenselianLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Sp O)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [Flat f] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (j : Sp A ⟶ Y), Module.Finite O A ∧ Module.Free O A ∧
      j ≫ f = spMap (algebraMap O A) ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
        (h : Sp B ⟶ Y), h ≫ f = spMap (algebraMap O B) → ∃! φ : A →ₐ[O] B, spMap (φ : A →+* B) ≫ j = h := by
  have : HenselianLocalRing (CommRingCat.of O) := ‹_›
  have hfin : IsFinite ((finitePart f).ι ≫ f) := isFinite_finitePart f
  have : IsAffine (finitePart f).toScheme := isAffine_of_isAffineHom ((finitePart f).ι ≫ f)
  let A : CommRingCat.{0} := Γ((finitePart f).toScheme, ⊤)
  let i : Spec A ≅ (finitePart f).toScheme := (finitePart f).toScheme.isoSpec.symm
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i.hom ≫ (finitePart f).ι ≫ f)
  have h₁ : ψ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hψ]
    infer_instance
  have h₂ : ψ.hom.Flat := by
    rw [← HasRingHomProperty.Spec_iff (P := @Flat), hψ]
    infer_instance
  let _ : Algebra O A := ψ.hom.toAlgebra
  have h₃ : Module.Finite O A := h₁
  have h₄ : Module.Flat O A := h₂
  have hj : (i.hom ≫ (finitePart f).ι) ≫ f = spMap (algebraMap O A) := by
    rw [Category.assoc, ← hψ]; rfl
  refine ⟨A, inferInstance, inferInstance, i.hom ≫ (finitePart f).ι, h₃,
    Module.free_of_flat_of_isLocalRing, hj, fun B _ _ _ h hh => ?_⟩
  have : IsFinite (spMap (algebraMap O B)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 ‹_›)
  obtain ⟨l, hl, -⟩ := existsUnique_lift_finitePart f _ h hh
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (R := A) (S := .of B) (l ≫ i.inv)
  have hχ' : Spec.map χ ≫ i.hom ≫ (finitePart f).ι = h := by
    rw [hχ, Category.assoc, i.inv_hom_id_assoc, hl]
  have hc : CommRingCat.ofHom (algebraMap O A) ≫ χ = CommRingCat.ofHom (algebraMap O B) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    refine Eq.trans ?_ hh
    rw [← hχ', Category.assoc, hj]
  refine ⟨⟨χ.hom, fun r => congr(($hc).hom r)⟩, hχ', fun φ hφ => ?_⟩
  have h₅ : spMap (φ : A →+* B) = Spec.map χ := by
    rw [← cancel_mono (i.hom ≫ (finitePart f).ι)]
    exact hφ.trans hχ'.symm
  have h₆ := Spec.map_injective h₅
  exact AlgHom.ext fun a => congr(($h₆).hom a)

theorem exists_finite_free_torsion_rep : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : Type) [CommRing O] [HenselianLocalRing O] (x : Sp O ⟶ X) (q : ℕ), q ≠ 0 → ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (u : overAt x A ⟶ G), Module.Finite O A ∧ Module.Free O A ∧ u ^ q = 1 ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (g : overAt x B ⟶ G), g ^ q = 1 → ∃! φ : A →ₐ[O] B, homAt x φ ≫ u = g := by
  intro X G _ _ hG O _ _ x q hq
  obtain ⟨hf, hqf⟩ := GlobalTheory.T.pow_flat_locallyQuasiFinite X G hG q hq
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  let m : G ⟶ G := (𝟙 G) ^ q
  have hm : ∀ {T : Over X} (g : T ⟶ G), g ≫ m = g ^ q := fun g => by
    rw [MonObj.comp_pow, Category.comp_id]
  have : Flat m.left := hf
  have : LocallyQuasiFinite m.left := hqf
  have : LocallyOfFiniteType (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType m.left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact m.left := QuasiCompact.of_comp _ G.hom
  have : IsSeparated (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated m.left := IsSeparated.of_comp _ G.hom
  let e : Sp O ⟶ G.left := (1 : Over.mk x ⟶ G).left
  have he : e ≫ G.hom = x := Over.w (1 : Over.mk x ⟶ G)
  have h1 : ∀ (B : Type) [CommRing B] [Algebra O B],
      (1 : overAt x B ⟶ G).left = spMap (algebraMap O B) ≫ e := fun B _ _ => by
    let t : overAt x B ⟶ Over.mk x := Over.homMk (spMap (algebraMap O B)) rfl
    rw [← MonObj.comp_one t]
    rfl
  have : LocallyQuasiFinite (pullback.snd m.left e) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (IsPullback.of_hasPullback m.left e) hqf
  obtain ⟨A, _, _, j, hA₁, hA₂, hj, H⟩ := exists_finite_free_rep O (pullback.snd m.left e)
  have hu : (j ≫ pullback.fst m.left e) ≫ m.left = spMap (algebraMap O A) ≫ e := by
    rw [Category.assoc, pullback.condition, reassoc_of% hj]
  let u : overAt x A ⟶ G := Over.homMk (j ≫ pullback.fst m.left e) (by
    rw [← Over.w m, ← Category.assoc]
    exact (congrArg (· ≫ G.hom) hu).trans (by rw [Category.assoc, he]; rfl))
  refine ⟨A, inferInstance, inferInstance, u, hA₁, hA₂, ?_, fun B _ _ _ g hg => ?_⟩
  · rw [← hm]
    exact Over.OverMorphism.ext (hu.trans (h1 A).symm)
  have hg' : g.left ≫ m.left = spMap (algebraMap O B) ≫ e := by
    rw [← Over.comp_left, hm, hg, h1]
  obtain ⟨φ, hφ, hφ'⟩ := H B (pullback.lift g.left (spMap (algebraMap O B)) hg') (pullback.lift_snd _ _ _)
  refine ⟨φ, Over.OverMorphism.ext ?_, fun φ' h' => hφ' φ' ?_⟩
  · change spMap (φ : A →+* B) ≫ j ≫ pullback.fst m.left e = g.left
    rw [← Category.assoc, hφ]
    exact pullback.lift_fst _ _ _
  · apply pullback.hom_ext
    · rw [Category.assoc]
      exact (congrArg CommaMorphism.left h').trans (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, hj]
      refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, φ'.comp_algebraMap]

end GlobalTheory.TorsionRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingForm
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem pow_eq_one_of_toBase {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) {T : Over S'} (x : T ⟶ G') (N : ℕ)
    (hx : Out.toBase h.1.w x ^ N = 1) : x ^ N = 1 := by
  let β := GlobalTheory.UU.toBaseHom (hw := h.1.w) (GlobalTheory.TowerAlg.toBase_mul h) T
  have hinj : Function.Injective β := fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  exact hinj ((map_pow β x N).trans (hx.trans (map_one β).symm))

theorem pushEx_cubWeil (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (hP : IsPeriod (Fu.Di i) ty P) (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ)
    (hk : 0 < k) (hζ : (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k)) :
    GlobalTheory.UU.CubWeil Z.t.cub k (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P a)) (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P b))
      (unitOn ζ) := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'

  have tors : ∀ d : (Fu.Di i).La, Fu.ex i P ((k : ℂ)⁻¹ • P d) ^ k = 1 := fun d => by
    have hpow : ∀ (n : ℕ) (z : Fin g → ℂ), Fu.ex i P z ^ n = Fu.ex i P (n • z) := fun n z => by
      induction n with
      | zero => simpa using ((Fu.ex_ker i P hP 0).2 (zero_mem _)).symm
      | succ n ih => rw [pow_succ, ih, ← Fu.ex_add i P hP, succ_nsmul]
    rw [hpow, Fu.ex_ker i P hP]
    exact ⟨d, by
      ext j
      simp [hk']⟩
  have h₀ : GlobalTheory.UU.CubWeil Xo.univ.t.cub k (Fu.ex i P ((k : ℂ)⁻¹ • P a)) (Fu.ex i P ((k : ℂ)⁻¹ • P b)) (unitOn ζ) :=
    (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.SemiRigid.globalFns (GlobalTheory.ObjDim.isAbelianScheme Xo.univ) (tors a) (tors b) _).2
      (by exact_mod_cast Fu.ex_weil i P hP k a b ζ hk hζ)
  let f₀ := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let m₀ := Z.m0.toSABMap

  let σ : Over.mk (y ≫ f₀) ⟶ Over.mk (Fu.u i P) := Over.homMk (𝟙 _) ((Category.id_comp _).trans hu)
  have h₁ := h₀.comp σ
  have e₁ : Units.map σ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ := by
    ext
    simp [σ]
  rw [e₁] at h₁

  let lf : (Fin g → ℂ) → (Over.mk y ⟶ Z.oF.t.G) := fun z =>
    Over.homMk (liftEx Z Fu y i P hu z) (liftEx_snd Z Fu y i P hu z)
  have eb : ∀ z, Out.toBase m₀.cart.1.w (lf z) = σ ≫ Fu.ex i P z := fun z =>
    Over.OverMorphism.ext ((liftEx_fst Z Fu y i P hu z).trans (by simp [σ]))
  have tl : ∀ d : (Fu.Di i).La, lf ((k : ℂ)⁻¹ • P d) ^ k = 1 := fun d =>
    pow_eq_one_of_toBase m₀.cart _ k (by
      rw [eb, ← MonObj.comp_pow, tors, MonObj.comp_one])
  obtain ⟨ζ', hζ', -⟩ := GlobalTheory.UU.existsUnique_cubWeil Z.oF.t.cub (tl a) (tl b)
  have h₂ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f₀ _ _ m₀.cm m₀.cart.1.w (GlobalTheory.TowerAlg.toBase_mul m₀.cart) _ _ _ _ m₀.lin
    k _ _ _ ζ' hζ'
  rw [eb, eb] at h₂
  obtain rfl : ζ' = unitOn ζ := h₂.unique h₁
  have h₃ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ _ _ _ Z.m.cm Z.m.cart.1.w (GlobalTheory.TowerAlg.toBase_mul Z.m.cart) _ _ _ _ Z.m.lin
    k _ _ _ _ hζ'

  let τ : Over.mk p ⟶ Over.mk ((Over.mk y).hom ≫ Z.jQ ≫ pullback.fst Z.s (spMap β)) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hp)
  have h₄ := h₃.comp τ
  have e₂ : Units.map τ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ := by
    ext
    simp [τ]
  rw [e₂] at h₄
  have e₃ : ∀ z, τ ≫ Out.toBase Z.m.cart.1.w (lf z) = pushEx Z Fu y i P p hu hp z := fun z =>
    Over.OverMorphism.ext (Category.id_comp _)
  rwa [e₃, e₃] at h₄

end GlobalTheory.ShFam.Hor.LogCh
end
end

