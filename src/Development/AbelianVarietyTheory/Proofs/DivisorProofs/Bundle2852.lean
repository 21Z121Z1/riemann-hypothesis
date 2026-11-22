import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0577
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatingConstantMemTraitFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatConst

open scoped TensorProduct

theorem mem_range_of_tmul_eq {K F O : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup O] [Module K O]
    {t u : O} {c : F} (ht : t ≠ 0) (h : (1 : F) ⊗ₜ[K] t = c ⊗ₜ[K] u) : ∃ x : K, algebraMap K F x = c := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K ht
  have e := congrArg (fun v => TensorProduct.rid K F (LinearMap.lTensor F l v)) h
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hl, one_smul, Algebra.smul_def] at e
  refine ⟨(l u)⁻¹, ?_⟩
  rw [map_inv₀]
  exact inv_eq_of_mul_eq_one_right (by simpa using e.symm)

theorem gs_spec {A B : CommRingCat.{0}} (h : A ⟶ B) (y : Spec B) (x : A) :
    gs (Spec.map h) y ⊤ ((Scheme.ΓSpecIso A).inv.hom x) = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso B).inv.hom (h.hom x)) := by
  have e := congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e]
  exact ((gs_pull (𝟙 _) (Spec.map h) y ⊤ trivial _).trans (by rw [Category.id_comp])).symm

theorem mem_of_stalk {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (hz : f z ∈ U) (y : Spec (Z.presheaf.stalk z)) :
    f (Z.fromSpecStalk z y) ∈ U := by
  have : Z.fromSpecStalk z y ⤳ z := by
    have := Set.mem_range_self (f := Z.fromSpecStalk z) y
    rwa [Scheme.range_fromSpecStalk] at this
  exact (this.map f.continuous).mem_open U.isOpen hz

theorem gs_stalk {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (hz : f z ∈ U) (a : Γ(X, U)) {B : CommRingCat.{0}}
    (h : Z.presheaf.stalk z ⟶ B) (y : Spec B) :
    gs (Spec.map h ≫ Z.fromSpecStalk z ≫ f) y U a = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso B).inv.hom (h.hom (gs f z U a))) := by
  have m := mem_of_stalk f z U hz (Spec.map h y)
  rw [← gs_spec, ← Category.assoc, ← gs_pull _ f y U m, ← gs_pull _ (Z.fromSpecStalk z) y _ m,
    Scheme.fromSpecStalk_app (U := f ⁻¹ᵁ U) hz, gs_eq f z U hz]
  exact gs_res (Spec.map h) y le_top m _

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (c : F), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → (∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0) → ∃ x : FractionRing W, algebraMap (FractionRing W) F x = c := by
  intro R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s c H ⟨Z, p, p', h₁, h₂, z, J, hJ, hne⟩
  let O := Z.presheaf.stalk z
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CommRingCat.of F ⟶ O,
      Spec.map ρ = Z.fromSpecStalk z ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left := ⟨Spec.preimage _, Spec.map_preimage _⟩
  letI : Algebra (FractionRing W) O := (ρ.hom.comp (algebraMap (FractionRing W) F)).toAlgebra
  let B := CommRingCat.of (F ⊗[FractionRing W] O)
  let iL : CommRingCat.of F ⟶ B := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let iR : O ⟶ B := CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).toRingHom
  have hK : ∀ x : FractionRing W, iR.hom (ρ.hom (algebraMap _ F x)) = iL.hom (algebraMap _ F x) := fun x =>
    ((Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).commutes x).trans rfl
  let g : Spec B ⟶ Z := Spec.map iR ≫ Z.fromSpecStalk z
  have hg : g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map (ρ ≫ iR) := by
    rw [Spec.map_comp, hρ, Category.assoc]
  have w : (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.A.A.hom = Spec.map iL ≫ jFK (R := R) F := by
    have e : (snd (TFK (R := R) F) C.A.A).left ≫ C.A.A.hom = (fst (TFK (R := R) F) C.A.A).left ≫ jFK (R := R) F :=
      (Over.w _).trans (Over.w (fst (TFK (R := R) F) C.A.A)).symm
    have e' : (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.A.A.hom =
        (g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left) ≫ jFK (R := R) F := by simp only [Category.assoc, e]
    rw [e', hg]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    refine CommRingCat.hom_ext (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    exact (congrArg (fun q => iR.hom (ρ.hom q)) (hF r)).trans ((hK _).trans (congrArg iL.hom (hF r).symm))
  obtain ⟨q, q₁, q₂⟩ : ∃ q : Spec B ⟶ (TFK (R := R) F ⊗ C.A.A).left,
      q ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map iL ∧
      q ≫ (snd (TFK (R := R) F) C.A.A).left = g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left := by
    let T' : Over (Sp (FractionRing R)) := Over.mk (Spec.map iL ≫ jFK (R := R) F)
    let a : T' ⟶ TFK (R := R) F := Over.homMk (Spec.map iL) rfl
    let b : T' ⟶ C.A.A := Over.homMk (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) w
    exact ⟨(lift a b).left, congrArg (·.left) (lift_fst a b), congrArg (·.left) (lift_snd a b)⟩
  have k₁ : (g ≫ p) ≫ T.β = q ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α := by
    rw [← Category.assoc q, q₂, Category.assoc, h₁]; simp only [Category.assoc]
  have k₂ : (g ≫ p) ≫ T.G.hom = q ≫ (fst (TFK (R := R) F) C.A.A).left ≫
      spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    rw [← Category.assoc q, q₁, Category.assoc, h₂, ← Category.assoc p', ← Category.assoc g, hg]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    exact CommRingCat.hom_ext (RingHom.ext fun r => hK _)
  let u : O := sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J
  let t : O := sval σ p z J
  have key : iR.hom t = iL.hom c * iR.hom u := by
    apply (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨J', hJ', e⟩ := exists_good C.P.L.L C.P.L.isLB y (K := Unit) (fun _ => (g ≫ p) ≫ T.β) (fun _ => J (p ≫ T.β))
      (fun _ _ _ => rfl) (fun _ => mem_of_stalk (p ≫ T.β) z _ (hJ _) (Spec.map iR y))
    have e := e ()
    have := H _ (g ≫ p) q k₁ k₂ y J' hJ'
    rw [sval_of σ _ y J' (fun _ => J (p ≫ T.β)) (fun _ => e),
      sval_of s _ y J' (fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) (fun _ => by
        rw [Category.assoc, ← k₁, Category.assoc p', ← h₁]; exact e), q₁, q₂] at this
    have a₁ := gs_stalk p z _ (hJ.mem (fun _ : Fin 1 => T.β) p) (σ.f fun _ => J (p ≫ T.β)) iR y
    have a₂ := gs_stalk (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z _
      (hJ.mem (fun _ : Fin 1 => C.α) (p' ≫ (snd (TFK (R := R) F) C.A.A).left))
      (s.f fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) iR y
    have a₃ := gs_spec iL y c
    simp only [g, Category.assoc] at this a₁ a₂
    refine a₁.symm.trans (this.trans (Eq.trans (congrArg₂ (· * ·) a₃ a₂) ?_))
    refine (gs_mul _ y ⊤ trivial _ _).symm.trans (congrArg _ ?_)
    simp only [u, sval, Category.assoc]
    exact (map_mul _ _ _).symm
  refine mem_range_of_tmul_eq (O := O) (t := t) (u := u) hne (key.trans ?_)
  exact (Algebra.TensorProduct.tmul_mul_tmul c 1 1 u).trans (by rw [_root_.mul_one, _root_.one_mul])

end GlobalTheory.Mum.RatConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusOntoGen

theorem restrict_surjective : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ g : R →+* V, Function.Injective g → ¬ IsLocalHom g → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G'), LBIso U'.LG.L (U.LG.L.pull β) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsDiscreteValuationRing V₁] (ψ : R →+* V₁) [IsLocalHom ψ]
    (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁] (m₁ : G₁.left ⟶ G.left) (hm₁ : IsGrpPullback G₁ G (spMap ψ) m₁) (hG₁ : IsSemiAbelian G₁)
    (Ω : Type) [Field Ω] (α : V₁ →+* Ω) (b : V →+* Ω) (hb : ∀ x ∈ maximalIdeal V, b x = 0)
    (GΩ : Over (Sp Ω)) [GrpObj GΩ] [IsCommMonObj GΩ] (n : GΩ.left ⟶ G₁.left) (hn : IsGrpPullback GΩ G₁ (spMap α) n)
    (n' : GΩ.left ⟶ G'.left) (hn' : IsGrpPullback GΩ G' (spMap b) n') (hGΩ : IsSemiAbelian GΩ)
    (j : splitTorus (Sp V₁) D'.toPre.X ⟶ G₁) [IsMonHom j]
    (G₀ : Over (Sp (ResidueField V₁))) [GrpObj G₀] [IsCommMonObj G₀] (m₀ : G₀.left ⟶ G₁.left)
    (hm₀ : IsGrpPullback G₀ G₁ (spMap (residue V₁)) m₀) (hG₀ : IsSemiAbelian G₀)
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V₁).comp ψ x = 0) (m₀' : G₀.left ⟶ G.left)
    (hm₀' : IsGrpPullback G₀ G (spMap ((residue V₁).comp ψ)) m₀')
    (ρ : D.toPre.X →+ D'.toPre.X),
    Function.Injective α → α.comp ψ = b.comp g → n ≫ m₁ = n' ≫ β →
    GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U'.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero hb) hn' →
    m₀' = m₀ ≫ m₁ →
    GlobalTheory.TorusPart.pullTorus hm₀ j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero h₀) hm₀' → Function.Surjective ρ := by
  intro R _ _ _ _ G _ _ _ D A U V _ _ _ _ _ g _ _ G' _ _ β _ _ D' A' U' _ V₁ _ _ _ ψ _ G₁ _ _ m₁ hm₁ hG₁ Ω _ α b hb GΩ _ _ n hn n' hn' _ j _ G₀ _ _ m₀ hm₀ _ h₀ m₀' hm₀' ρ _ _ _ hΩ hφ₀ h₀j
  classical
  by_contra hρ
  have hM : ρ.range ≠ ⊤ := fun h => hρ (AddMonoidHom.range_eq_top.1 h)
  obtain ⟨F, _, _, l, hl0, hl⟩ := GlobalTheory.TorusOnto.exists_finite_quotient_ne_zero ρ.range hM
  have hlρ : l.comp ρ = 0 := AddMonoidHom.ext fun x => hl _ ⟨x, rfl⟩
  have key : GlobalTheory.SplitTorus.torusMap (Sp V₁) l ≫ j = GlobalTheory.SplitTorus.torusMap (Sp V₁) 0 ≫ j := by
    haveI : IsSeparated G₁.hom := hG₁.separated
    have hjac : maximalIdeal V₁ ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    refine GlobalTheory.hom_eq_of_thickenings_of_isProper V₁ (maximalIdeal V₁) hjac (splitTorus (Sp V₁) F) G₁ _ _ fun e => ?_
    have hψ : ∀ x ∈ maximalIdeal R, ψ x ∈ maximalIdeal V₁ := fun x hx =>
      (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hx (isUnit_of_map_unit ψ x hu)
    have hI : maximalIdeal V₁ ^ (e + 1) ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal V₁).ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
    haveI : Nontrivial (V₁ ⧸ maximalIdeal V₁ ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsLocalRing (V₁ ⧸ maximalIdeal V₁ ^ (e + 1)) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let q : V₁ →+* V₁ ⧸ maximalIdeal V₁ ^ (e + 1) := Ideal.Quotient.mk _
    have he := isGrpPullback_pullback G₁ (thick V₁ (maximalIdeal V₁) e)
    have ha : ∀ x ∈ maximalIdeal R ^ (e + 1), (q.comp ψ) x = 0 := by
      intro x hx
      refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
      have hle : Ideal.map ψ (maximalIdeal R ^ (e + 1)) ≤ maximalIdeal V₁ ^ (e + 1) := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hψ) _
      exact hle (Ideal.mem_map_of_mem ψ hx)
    have hR : IsGrpPullback (thickObj V₁ (maximalIdeal V₁) e G₁) G (spMap (q.comp ψ))
        (pullback.fst G₁.hom (thick V₁ (maximalIdeal V₁) e) ≫ m₁) :=
      (he.comp hm₁).congr (by rw [spMap, spMap, ← Spec.map_comp]; rfl) rfl
    obtain ⟨-, hfac⟩ := GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt e) ha hR
    obtain ⟨ρe, hρe⟩ := hfac D'.toPre.X (GlobalTheory.TorusPart.pullTorus he j) inferInstance
    have hres : ∀ x ∈ maximalIdeal V₁ ^ (e + 1), residue V₁ x = 0 := fun x hx =>
      (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have ke := GlobalTheory.TorusPart.isGrpPullback_thickLift hres hm₀
    have ha' : ∀ x ∈ maximalIdeal R ^ (e + 1), ((residue V₁).comp ψ) x = 0 := fun x hx =>
      h₀ x (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
    have e1 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.pullTorus he j) = GlobalTheory.TorusPart.pullTorus hm₀ j :=
      GlobalTheory.TorusPart.pullTorus_pullTorus ke he hm₀ (GlobalTheory.TorusPart.thickPt_thick hres).symm
        (GlobalTheory.TorusPart.thickLift_fst hres hm₀).symm j
    have e2 : GlobalTheory.TorusPart.pullTorus ke (GlobalTheory.TorusPart.gtTorus (U.gt e) ha hR) =
        GlobalTheory.TorusPart.gtTorus (U.gt e) ha' hm₀' :=
      GlobalTheory.TorusPart.pullTorus_gtTorus (σ := Ideal.Quotient.lift _ (residue V₁) hres) (U.gt e) ha ha' hR hm₀' ke
        (RingHom.ext fun x => rfl)
        (hφ₀.trans (by rw [← Category.assoc, GlobalTheory.TorusPart.thickLift_fst]))
    obtain ⟨hmono, hfac'⟩ := GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt e) ha' hm₀'
    obtain ⟨u, hu⟩ := hfac' D.toPre.X (GlobalTheory.TorusPart.gtTorus (U.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero h₀) hm₀') inferInstance
    have e3 := congrArg (GlobalTheory.TorusPart.pullTorus ke) hρe
    rw [e1, GlobalTheory.TorusPart.pullTorus_torusMap_comp, e2, h₀j, hu, ← Category.assoc,
      ← GlobalTheory.SplitTorus.torusMap_comp, cancel_mono] at e3
    have e4 : ρe = ρ.comp u := (GlobalTheory.SplitTorus.torusMap_injective e3).symm
    have hstep : GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ l ≫ j) =
        GlobalTheory.TorusPart.pullTorus he (GlobalTheory.SplitTorus.torusMap _ (0 : D'.toPre.X →+ F) ≫ j) := by
      rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hρe, ← Category.assoc,
        ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp, e4,
        ← AddMonoidHom.comp_assoc, hlρ, AddMonoidHom.zero_comp, AddMonoidHom.zero_comp]
    have k1 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ l ≫ j)
    have k2 := GlobalTheory.TorusPart.pullTorus_left he (GlobalTheory.SplitTorus.torusMap _ (0 : D'.toPre.X →+ F) ≫ j)
    rw [hstep] at k1
    have k3 := k1.symm.trans k2
    show pullback.fst (splitTorus (Sp V₁) F).hom (thick V₁ (maximalIdeal V₁) e) ≫ _ =
      pullback.fst (splitTorus (Sp V₁) F).hom (thick V₁ (maximalIdeal V₁) e) ≫ _
    rw [← GlobalTheory.SplitTorus.bcIso_inv_bcMap, Category.assoc, Category.assoc, k3]
  haveI : Mono (GlobalTheory.TorusPart.gtTorus (U'.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero hb) hn') :=
    (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U'.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero hb) hn').1
  have e2 := congrArg (GlobalTheory.TorusPart.pullTorus hn) key
  rw [GlobalTheory.TorusPart.pullTorus_torusMap_comp, GlobalTheory.TorusPart.pullTorus_torusMap_comp, hΩ] at e2
  have e3 : GlobalTheory.SplitTorus.torusMap (Sp Ω) l = GlobalTheory.SplitTorus.torusMap (Sp Ω) 0 := (cancel_mono _).1 e2
  exact hl0 (GlobalTheory.SplitTorus.torusMap_injective e3)

end GlobalTheory.TorusOntoGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RetractionLiftObstructionZeroOfLiftedSection
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem appLE_apply_of_eq_id {X : Scheme.{0}} {g : X ⟶ X} (hg : g = 𝟙 X) {U V : X.Opens} (e : V ≤ g ⁻¹ᵁ U)
    (e' : V ≤ U) (x : Γ(X, U)) : (g.appLE U V e).hom x = (X.presheaf.map (homOfLE e').op).hom x := by
  subst hg
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
  rfl

theorem appLE_appLE_of_retr {X₀ Z₀ : Scheme.{0}} {j₀ : X₀ ⟶ Z₀} {f₀ : Z₀ ⟶ X₀} (hjf : j₀ ≫ f₀ = 𝟙 X₀)
    (U : X₀.Opens) (U' : Z₀.Opens) (U'' : X₀.Opens) (e₁ : U' ≤ f₀ ⁻¹ᵁ U) (e₂ : U'' ≤ j₀ ⁻¹ᵁ U')
    (e : U'' ≤ U) (x : Γ(X₀, U)) :
    (j₀.appLE U' U'' e₂).hom ((f₀.appLE U U' e₁).hom x) = (X₀.presheaf.map (homOfLE e).op).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact appLE_apply_of_eq_id hjf _ e x

theorem ext_tri_res_pull1 {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁]
    {X X' X'' : Scheme.{0}} {ψ : X'' ⟶ X'} {φ : X' ⟶ X} {s' : X' ⟶ Sp R₀} {s'' : X'' ⟶ Sp R₀}
    (h' : ψ ≫ s' = s'' ≫ spMap (RingHom.id R₀)) (a : CatCoh.H1 (ext R₁ (OAff s'))) :
    (extMap R₁ (cechTriplePullbackSecond (φ := φ) h')).pull1 ((extMap R₁ (pairRes φ s')).pull1 a) =
      (extMap R₁ (cechTripleRestrictFirst ψ φ s'')).pull1 ((extMap R₁ (pairPull h')).pull1 a) := by
  rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
  refine CoefMap.pullCohomologyOne_eq_of_natTrans ((extMap R₁ (pairRes φ s')).comp (extMap R₁ (cechTriplePullbackSecond (φ := φ) h')))
    ((extMap R₁ (pairPull h')).comp (extMap R₁ (cechTripleRestrictFirst ψ φ s''))) { app U := 𝟙 _ } (fun U b ↦ ?_) a
  erw [mp_id]
  induction b using TensorProduct.induction_on with
  | zero => (erw [map_zero]) <;> rfl
  | tmul x y => rfl
  | add x y hx hy => erw [map_add, map_add, hx, hy]

theorem retractionLiftObstruction_zero_of_liftedSection_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ X Z : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (t : Z ⟶ Sp R) (i : X₀ ⟶ X) (k : Z₀ ⟶ Z) (hi : IsPullback i s₀ s (spMap π)) (hkk : IsPullback k t₀ t (spMap π)) (S : Sys I π s₀) (S' : Sys I π t₀) (P : S.Presents s i) (P' : S'.Presents t k) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (j₀ : X₀ ⟶ Z₀) (hj : j₀ ≫ t₀ = s₀ ≫ spMap (RingHom.id R₀)) (j : X ⟶ Z), j₀ ≫ f₀ = 𝟙 X₀ → j ≫ t = s → i ≫ j = j₀ ≫ k → ∀ (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T), (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l → ∀ (w : GlobForm s₀) (c : GlobalTheory.CatCoh.H1 (ext R₁ (OAff t₀))), (ofSys S).IsOb1 (pairPre S' f₀) (pairPull h) l α w ((extMap R₁ (pairRes f₀ t₀)).pull1 c) → IsExtendedPullbackDegOne R₁ hj c 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ Z₀ X Z s₀ t₀ s t i k hi hkk S S' P P' f₀ h j₀ hj j hjf hjt hij l hl w c hob
  obtain ⟨l', hl'L, hl'N⟩ := GlobalTheory.T.exists_natural_chart_lifts_of_morphism R R₀ I hI π hπ hk Z₀ X₀ Z X t₀ s₀ t s k i hkk hi S' S P' P j₀ hj j hjt hij
  have hle : ∀ T : (Triple j₀ f₀)ᵒᵖ, T.unop.1.1 ≤ T.unop.1.2.2 := fun T x hx ↦ by
    have h1 := T.unop.2.2 (T.unop.2.1 hx)
    have e := congrArg (fun g : X₀ ⟶ X₀ ↦ g.base x) hjf
    simp at e
    exact e ▸ h1
  let L'' : Pre I π (OTriple j₀ f₀ s₀) := (ofSys S).restrict (cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀))
  let u : ∀ T : (Triple j₀ f₀)ᵒᵖ, (pairPre S' f₀).B ((cechTriplePullbackSecond (φ := f₀) hj).G.obj T) →ₐ[R] L''.B T :=
    fun T ↦ l' ((cechTripleProjFirstSecond j₀ f₀).obj T)
  let v : ∀ T : (Triple j₀ f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj ((cechTriplePullbackSecond (φ := f₀) hj).G.obj T)) →ₐ[R] L''.B T :=
    fun T ↦ mp S.F (homOfLE (hle T)).op
  have hvan := GlobalTheory.T.obstructionPullback_eq_zero_of_naturalLift_alt R R₀ I hI π hπ hk R₁ α (AffOp X₀) (OAff s₀) (Pair f₀)ᵒᵖ (OPair f₀ t₀) (ofSys S)
    (pairPre S' f₀) (pairPull h) l (Triple j₀ f₀)ᵒᵖ (OTriple j₀ f₀ s₀) L'' (cechTriplePullbackSecond hj) u v hl
    (fun T b ↦ hl'L ((cechTripleProjFirstSecond j₀ f₀).obj T) b)
    (fun T T' a b ↦ by
      have e1 : (cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀)).map a = (pairFst j₀).map ((cechTripleProjFirstSecond j₀ f₀).map a) :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      have e2 : (pairFst f₀).map ((cechTripleProjSecondThird j₀ f₀).map a) = (pairSnd j₀).map ((cechTripleProjFirstSecond j₀ f₀).map a) :=
        Quiver.Hom.unop_inj (Subsingleton.elim _ _)
      change mp S.F ((cechTripleProjFirstThird j₀ f₀ ⋙ pairFst (j₀ ≫ f₀)).map a) (l' ((cechTripleProjFirstSecond j₀ f₀).obj T) b) =
        l' ((cechTripleProjFirstSecond j₀ f₀).obj T') (mp S'.F ((pairFst f₀).map ((cechTripleProjSecondThird j₀ f₀).map a)) b)
      rw [e1, e2]
      exact hl'N ((cechTripleProjFirstSecond j₀ f₀).map a) b)
    (fun T b ↦ by
      change S.p _ (mp S.F _ b) = (j₀.appLE _ _ _).hom ((f₀.appLE _ _ _).hom (S.p _ b))
      exact (S.nat _ b).trans (appLE_appLE_of_retr hjf _ _ _ _ _ (hle T) _).symm)
    (fun T T' a b ↦ by
      change mp S.F _ (mp S.F _ b) = mp S.F _ (mp S.F _ b)
      exact (mp_comp S.F _ _ b).symm.trans ((congrArg (fun q ↦ mp S.F q b)
        (Quiver.Hom.unop_inj (Subsingleton.elim _ _))).trans (mp_comp S.F _ _ b)))
    w ((extMap R₁ (pairRes f₀ t₀)).pull1 c) hob
  rw [ext_tri_res_pull1] at hvan
  have inj := (GlobalTheory.T.cechPairRestrict_baseChange_bijective R₀ R₁ Z₀ X₀ s₀ j₀).2 X₀ f₀
  unfold IsExtendedPullbackDegOne
  rw [map_zero]
  exact inj (hvan.trans (map_zero _).symm)

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLe
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.UpBall

theorem isIdent_det {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (h : IsIdent p q Ψ G x σ A e) (τ : Ψ) : (mat x τ).det ≠ 0 ∧ G.det ≠ 0 := by
  obtain ⟨h1, h2⟩ := h (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ))
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ))
  set N := Pᵀ * A (σ.symm τ)
  have hN : N * mat x τ = 1 := by rw [Matrix.mul_assoc, h2, transpose_mul_permM]
  have hN' : mat x τ * N = 1 := mul_eq_one_comm.1 hN
  refine ⟨Matrix.det_ne_zero_of_left_inverse hN, ?_⟩
  have hA : A (σ.symm τ) = P * N := by
    calc A (σ.symm τ) = A (σ.symm τ) * (mat x τ * N) := by rw [hN', Matrix.mul_one]
      _ = P * N := by rw [← Matrix.mul_assoc, h2]
  have hJ : J * J = 1 := by
    simp [J, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [P, permM, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply]
    split_ifs <;> simp
  set D := Pᵀ * J * P
  have hD : D * D = 1 := by
    calc D * D = Pᵀ * J * (P * Pᵀ) * J * P := by simp only [D, Matrix.mul_assoc]
      _ = Pᵀ * (J * J) * P := by rw [permM_mul_transpose]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hJ, Matrix.mul_one, transpose_mul_permM]
  have hDdet : D.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hD
  have hNdet : N.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hN'
  have key : -(G.map τ.1)ᵀ = Nᴴ * D * N := by
    rw [← h1, hA, Matrix.conjTranspose_mul, hPc]
    simp only [D, Matrix.mul_assoc]
  have hdet : (-(G.map τ.1)ᵀ).det ≠ 0 := by
    rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 hNdet) hDdet) hNdet
  intro hG
  apply hdet
  rw [Matrix.det_neg, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hG, map_zero, mul_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_lam (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ lam : Measure (realLie Ψ G), lam.IsAddHaarMeasure ∧ lam.map Subtype.val = riemLie Ψ G x := by
  set W := (realLie Ψ G).comap (fromFrame x)
  let Φ : W →ₗ[ℝ] realLie Ψ G :=
    ((fromFrame x).comp W.subtype).codRestrict (realLie Ψ G) (fun v => v.2)
  have key2 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      mat x τ * ((mat x τ)⁻¹ * A * mat x τ) * (mat x τ)⁻¹ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hsurj : Function.Surjective Φ := by
    intro X
    let Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r) := WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      ((mat x p.1)⁻¹ * Matrix.of (X.1 p.1) * mat x p.1) p.2.1 p.2.2)
    have hY : fromFrame x Y = X.1 := by
      funext τ
      have e : Matrix.of (fun a b => Y (τ, a, b)) = (mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ := by
        ext a b; simp [Y]
      change (mat x τ * Matrix.of _ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = X.1 τ
      rw [e, key2]; rfl
    exact ⟨⟨Y, show fromFrame x Y ∈ realLie Ψ G by rw [hY]; exact X.2⟩, Subtype.ext hY⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hinj : Function.Injective Φ := by
    intro Y Z h
    have h' : fromFrame x Y.1 = fromFrame x Z.1 := congrArg Subtype.val h
    have hτ : ∀ τ, Matrix.of (fun a b => Y.1 (τ, a, b)) = Matrix.of (fun a b => Z.1 (τ, a, b)) := by
      intro τ
      have h1 : mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ =
          mat x τ * Matrix.of (fun a b => Z.1 (τ, a, b)) * (mat x τ)⁻¹ := congrFun h' τ
      rw [← key1 τ (Matrix.of (fun a b => Y.1 (τ, a, b))), h1, key1]
    refine Subtype.ext (PiLp.ext fun p => ?_)
    obtain ⟨τ, a, b⟩ := p
    exact congrFun (congrFun (hτ τ) a) b
  let φ : W ≃L[ℝ] realLie Ψ G := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  refine ⟨(stdOrthonormalBasis ℝ W).toBasis.addHaar.map φ, φ.isAddHaarMeasure_map _, ?_⟩
  rw [Measure.map_map measurable_subtype_coe φ.continuous.measurable]
  rfl

theorem riemHaar_frBall_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → riemHaar Ψ G x (frBall Ψ G x ε) ≤ ENNReal.ofReal ((8 * ε) ^ (Ψ.card * (r ^ 2 - 1))) := by
  intro E _ _ _ r κ p q Ψ G x σ A e hr hI
  have hx : ∀ τ, (mat x τ).det ≠ 0 := fun τ => (isIdent_det hI τ).1
  by_cases hd : Ψ.card * (r ^ 2 - 1) = 0
  · refine ⟨1, one_pos, fun ε _ _ => ?_⟩
    rw [hd, pow_zero, ENNReal.ofReal_one]
    exact GlobalTheory.T.riemannianHaar_le_one_of_dim_zero E r Ψ G x hr hx hd _
  have hΨ : 0 < Ψ.card := Nat.pos_of_ne_zero fun h => hd (by rw [h, zero_mul])
  obtain ⟨τ₀, hτ₀⟩ := Finset.card_pos.1 hΨ
  have hG : G.det ≠ 0 := (isIdent_det hI ⟨τ₀, hτ₀⟩).2
  have hr2 : 3 ≤ r ^ 2 - 1 := by
    have : r ≠ 1 := fun h => hd (by rw [h]; simp)
    have : 2 ≤ r := by omega
    have : 4 ≤ r ^ 2 := by nlinarith
    omega
  have hd3 : 3 ≤ Ψ.card * (r ^ 2 - 1) := le_trans hr2 (Nat.le_mul_of_pos_left _ hΨ)
  obtain ⟨lam, hlam, hmap⟩ := exists_lam Ψ G x hx
  obtain ⟨δ, hδ, hup⟩ := GlobalTheory.T.tangentNormalizedHaar_le_two_mul_lieHaar E r Ψ G hG lam
  obtain ⟨ε₀, hε₀, hcov⟩ := GlobalTheory.T.frameBall_subset_expChart_image_frameBox E r Ψ G x hG hx δ hδ
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  set S : Set (Ψ → Fin r → Fin r → ℂ) :=
    {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < 2 * ε} with hS
  have hcont : ∀ τ a b, Continuous (fun X : Ψ → Fin r → Fin r → ℂ =>
      ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b) := by
    intro τ a b
    exact ((continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const).matrix_elem a b
  have hSm : MeasurableSet S := by
    simp only [hS, Set.setOf_forall]
    exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_lt (hcont τ a b).norm.measurable measurable_const
  set s : Set (realLie Ψ G) := {X : realLie Ψ G | ‖X‖ < δ ∧ ∀ τ a b,
    ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ < 2 * ε} with hs
  have hs' : s = Metric.ball 0 δ ∩ Subtype.val ⁻¹' S := by
    ext X; simp [hs, hS, mem_ball_zero_iff]
  have hsm : MeasurableSet s := by
    rw [hs']; exact measurableSet_ball.inter (measurable_subtype_coe hSm)
  have hsb : s ⊆ Metric.ball 0 δ := by rw [hs']; exact Set.inter_subset_left
  have h1 : riemHaar Ψ G x (frBall Ψ G x ε) ≤ 2 * lam s := by
    calc riemHaar Ψ G x (frBall Ψ G x ε)
        ≤ tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := by
          unfold riemHaar; rw [← hmap]; exact measure_mono (hcov ε hε hεε)
      _ ≤ 2 * lam s := hup s hsm hsb
  have h2 : lam s ≤ riemLie Ψ G x S := by
    rw [← hmap, Measure.map_apply measurable_subtype_coe hSm, hs']
    exact measure_mono Set.inter_subset_right
  have h3 := GlobalTheory.T.riemannianLieMeasure_frameBox_le E r κ p q Ψ G x σ A e hr hI (2 * ε) (by positivity)
  have h4 : 2 * lam s ≤ 2 * ENNReal.ofReal ((3 * (2 * ε)) ^ (Ψ.card * (r ^ 2 - 1))) := by
    gcongr; exact h2.trans h3
  refine h1.trans (h4.trans ?_)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  set d := Ψ.card * (r ^ 2 - 1)
  have e1 : (8 * ε) ^ d = (4 / 3 : ℝ) ^ d * (3 * (2 * ε)) ^ d := by rw [← mul_pow]; ring_nf
  have e2 : (2 : ℝ) ≤ (4 / 3 : ℝ) ^ d := by
    calc (2 : ℝ) ≤ (4 / 3) ^ 3 := by norm_num
      _ ≤ (4 / 3) ^ d := pow_le_pow_right₀ (by norm_num) hd3
  rw [e1]
  exact mul_le_mul_of_nonneg_right e2 (by positivity)

end GlobalTheory.CovTop.VolUp.UpBall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFiniteOfQuasiFiniteCompleteLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_finite_of_quasiFinite_complete_local : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (b : A →+* R) [IsLocalHom b], IsAdicComplete (maximalIdeal A) A → (∀ p : Ideal R, p.IsPrime → (maximalIdeal A).map b ≤ p → p = maximalIdeal R) → ((residue R).comp b).Finite → b.Finite := by
  first | exact @GlobalTheory.QuasiFiniteLocal.finite_of_quasiFinite | exact GlobalTheory.QuasiFiniteLocal.finite_of_quasiFinite | (intros; apply GlobalTheory.QuasiFiniteLocal.finite_of_quasiFinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDefStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiAdj_mumfordTensorPower_of_posDef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → ∀ (T : Tens D.toPre D'.toPre W) (a : TensO (symUnitOf W h)), RosatiAdj D'.toPre.P.A D'.toPre.P.L (T.act (TensO.mat _ a)) (T.act (TensO.mat _ (star a))) := by
  first | exact @GlobalTheory.Mum.rosatiAdj_tens | exact GlobalTheory.Mum.rosatiAdj_tens | (intros; apply GlobalTheory.Mum.rosatiAdj_tens <;> assumption)
end

