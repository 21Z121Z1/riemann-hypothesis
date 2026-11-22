import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamA
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorMapFiniteOfSplit
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0081
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0231
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle0001
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiPtsA
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLamB
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}}

section Biadd

variable {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left} (hD : IsDual A B P)
  (hD' : IsDual B A (swap P)) {Y : Over S}

include hD in
theorem evc_mul_left (a a' : Y ⟶ A) (b : Y ⟶ B) :
    evc hD.isLB (a * a') b = evc hD.isLB a b + evc hD.isLB a' b :=
  (isAdditive_iff hD.isLB).1 hD.additive Y a a' b

include hD hD' in
theorem evc_mul_right (a : Y ⟶ A) (b b' : Y ⟶ B) :
    evc hD.isLB a (b * b') = evc hD.isLB a b + evc hD.isLB a b' := by
  rw [← evc_swap hD.isLB hD'.isLB, (isAdditive_iff hD'.isLB).mp hD'.additive Y b b' a, evc_swap, evc_swap]

include hD in
theorem evc_one_l (b : Y ⟶ B) : evc hD.isLB (1 : Y ⟶ A) b = 0 := hD.additive.evc_one hD.isLB b

include hD in
theorem evc_one_r (a : Y ⟶ A) : evc hD.isLB a (1 : Y ⟶ B) = 0 := evc_one_right hD.isLB hD.zero a

include hD hD' in
theorem evc_inv_inv (a : Y ⟶ A) (b : Y ⟶ B) : evc hD.isLB a⁻¹ b⁻¹ = evc hD.isLB a b := by
  have hl : evc hD.isLB a⁻¹ b⁻¹ = - evc hD.isLB a b⁻¹ := by
    have h := evc_mul_left hD a⁻¹ a b⁻¹
    rw [_root_.inv_mul_cancel, evc_one_l hD] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hr : evc hD.isLB a b⁻¹ = - evc hD.isLB a b := by
    have h := evc_mul_right hD hD' a b⁻¹ b
    rw [_root_.inv_mul_cancel, evc_one_r hD] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  rw [hl, hr, neg_neg]

end Biadd

section abelian₂

variable {S' : Scheme.{0}} {G G' T : Over S'} [GrpObj G] [GrpObj G']

def lamHom (x y : T ⟶ G) : Pic G.left →+ Pic T.left :=
  pull (x * y).left - pull x.left - pull y.left + pull (1 : T ⟶ G).left

theorem lam_eq_lamHom (c : Pic G.left) (x y : T ⟶ G) : lam c x y = lamHom x y c := by
  simp [lam, lamHom]

theorem lam_pull_pt (φ : G ⟶ G') (c : Pic G'.left) (x y : T ⟶ G) (hm : (x * y) ≫ φ = (x ≫ φ) * (y ≫ φ))
    (h1 : (1 : T ⟶ G) ≫ φ = 1) : lam (pull φ.left c) x y = lam c (x ≫ φ) (y ≫ φ) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, hm, h1]

end abelian₂

section Fib

variable {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

theorem map_mul_pt {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f] {T : Over (Sp Ω)}
    (x y : T ⟶ (Over.pullback s).obj G) :
    (x * y) ≫ (Over.pullback s).map f = (x ≫ (Over.pullback s).map f) * (y ≫ (Over.pullback s).map f) := by
  apply toBase_injective s
  rw [toBase_map, toBase_mul, toBase_mul, toBase_map, toBase_map, MonObj.mul_comp]

theorem map_one_pt {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f] {T : Over (Sp Ω)} :
    (1 : T ⟶ (Over.pullback s).obj G) ≫ (Over.pullback s).map f = 1 := by
  apply toBase_injective s G'
  rw [toBase_map, toBase_one, toBase_one, MonObj.one_comp]

end Fib

end PositivityTheory.PrwZar
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsFiniteMapTensorHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.XB

variable {S : Scheme.{0}}

def pr8 (A : Over S) : Fin 8 → (G4 (A ⊗ A) ⟶ A)
  | 0 => prj (A ⊗ A) 0 ≫ fst A A
  | 1 => prj (A ⊗ A) 0 ≫ snd A A
  | 2 => prj (A ⊗ A) 1 ≫ fst A A
  | 3 => prj (A ⊗ A) 1 ≫ snd A A
  | 4 => prj (A ⊗ A) 2 ≫ fst A A
  | 5 => prj (A ⊗ A) 2 ≫ snd A A
  | 6 => prj (A ⊗ A) 3 ≫ fst A A
  | 7 => prj (A ⊗ A) 3 ≫ snd A A

def lim8 (A : Over S) : IsLimit (Fan.mk (G4 (A ⊗ A)) (pr8 A)) :=
  mkFanLimit _ (fun s => fourfoldProductLift ![lift (s.proj 0) (s.proj 1), lift (s.proj 2) (s.proj 3),
      lift (s.proj 4) (s.proj 5), lift (s.proj 6) (s.proj 7)])
    (fun s k => by fin_cases k <;> simp [pr8, fourfoldProductLift, prj])
    (fun s m hm => by
      have h0 : m ≫ pr8 A 0 = s.proj 0 := hm 0
      have h1 : m ≫ pr8 A 1 = s.proj 1 := hm 1
      have h2 : m ≫ pr8 A 2 = s.proj 2 := hm 2
      have h3 : m ≫ pr8 A 3 = s.proj 3 := hm 3
      have h4 : m ≫ pr8 A 4 = s.proj 4 := hm 4
      have h5 : m ≫ pr8 A 5 = s.proj 5 := hm 5
      have h6 : m ≫ pr8 A 6 = s.proj 6 := hm 6
      have h7 : m ≫ pr8 A 7 = s.proj 7 := hm 7
      simp only [pr8, prj, ← Category.assoc] at h0 h1 h2 h3 h4 h5 h6 h7
      refine CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
        (CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
          (CartesianMonoidalCategory.hom_ext _ _ (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
            (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_))) <;>
        simp [fourfoldProductLift, ← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7])

variable {T : Scheme.{0}} (s : T ⟶ S)

theorem isFinite_map_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hf : IsFinite ((Over.pullback s).map f).left) (hg : IsFinite ((Over.pullback s).map g).left) :
    IsFinite ((Over.pullback s).map (f ⊗ₘ g)).left := by
  set F := Over.pullback s
  have he : F.map (f ⊗ₘ g) =
      CartesianMonoidalCategory.prodComparison F X X' ≫ (F.map f ⊗ₘ F.map g) ≫
        inv (CartesianMonoidalCategory.prodComparison F Y Y') := by
    rw [← Category.assoc, ← CartesianMonoidalCategory.prodComparison_natural, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have ht : IsFinite (Over.Hom.left (F.map f ⊗ₘ F.map g)) :=
    GlobalTheory.TensorFinite.isFinite_tensorHom _ _ hf hg
  haveI : IsIso (CartesianMonoidalCategory.prodComparison F X X') :=
    CartesianMonoidalCategory.isIso_prodComparison_of_preservesLimit_pair F X X'
  haveI : IsIso (CartesianMonoidalCategory.prodComparison F Y Y') :=
    CartesianMonoidalCategory.isIso_prodComparison_of_preservesLimit_pair F Y Y'
  haveI : IsIso (Over.Hom.left (CartesianMonoidalCategory.prodComparison F X X')) :=
    (Over.forget T).map_isIso (CartesianMonoidalCategory.prodComparison F X X')
  haveI : IsIso (Over.Hom.left (inv (CartesianMonoidalCategory.prodComparison F Y Y'))) :=
    (Over.forget T).map_isIso (inv (CartesianMonoidalCategory.prodComparison F Y Y'))
  have h1 : IsFinite (Over.Hom.left (CartesianMonoidalCategory.prodComparison F X X')) := inferInstance
  have h2 : IsFinite (Over.Hom.left (inv (CartesianMonoidalCategory.prodComparison F Y Y'))) :=
    inferInstance
  rw [he, Over.comp_left, Over.comp_left]
  exact MorphismProperty.comp_mem @IsFinite _ _ h1 (MorphismProperty.comp_mem @IsFinite _ _ ht h2)

end PositivityTheory.PrwZar.XB
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsFiniteMuFibre
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.Z2

theorem isAbelianScheme_pb {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback f).obj A) where
  comm := by have := h.comm; infer_instance
  smooth := by have := h.smooth; show Smooth (pullback.snd A.hom f); infer_instance
  proper := by have := h.proper; show IsProper (pullback.snd A.hom f); infer_instance
  geomConnected := by
    have := h.geomConnected; show GeometricallyConnected (pullback.snd A.hom f); infer_instance

theorem pb_map_id_pow {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) [GrpObj B] (m : ℕ) :
    (Over.pullback f).map (𝟙 B ^ m) = 𝟙 ((Over.pullback f).obj B) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; exact CategoryTheory.Functor.map_one _
  | succ n ih => rw [pow_succ, pow_succ, CategoryTheory.Functor.map_mul, ih, CategoryTheory.Functor.map_id]

theorem fin_surj_core {Ω : Type} [Field Ω] {As Bs : Over (Sp Ω)} [GrpObj As] [GrpObj Bs]
    (hA : IsAbelianScheme As) (hB : IsAbelianScheme Bs) (ls : As ⟶ Bs) (mus : Bs ⟶ As) (m : ℕ) (hm : 1 ≤ m)
    (h₁ : ls ≫ mus = 𝟙 As ^ m) (h₂ : mus ≫ ls = 𝟙 Bs ^ m) {L : LB As.left} (hL : L.IsLB)
    (ha : Out.RelAmple As L) :
    IsFinite ls.left ∧ Surjective ls.left ∧ IsFinite mus.left ∧ Surjective mus.left := by
  have := hA.comm
  have := hA.proper
  have := hB.proper
  have hfin : IsFinite ((𝟙 As) ^ m : As ⟶ As).left :=
    ((GlobalTheory.T.cube_trivial_and_finite_flat_surjective_mul_abelianScheme Ω As L (L.pull (fst As As).left) hA hL ha (LB.isLB_pull hL _)).2 m hm).1
  have hsB : Surjective ((𝟙 Bs) ^ m : Bs ⟶ Bs).left := GlobalTheory.T.abelianScheme_nsmul_surjective Ω Bs hB m (by omega)
  have hsA : Surjective ((𝟙 As) ^ m : As ⟶ As).left := GlobalTheory.T.abelianScheme_nsmul_surjective Ω As hA m (by omega)
  have e₁ : ls.left ≫ mus.left = ((𝟙 As) ^ m : As ⟶ As).left := by rw [← Over.comp_left, h₁]
  have e₂ : mus.left ≫ ls.left = ((𝟙 Bs) ^ m : Bs ⟶ Bs).left := by rw [← Over.comp_left, h₂]
  have hsl : Surjective ls.left := by
    have : Surjective (mus.left ≫ ls.left) := by rw [e₂]; exact hsB
    exact AlgebraicGeometry.Surjective.of_comp (f := mus.left) (g := ls.left)
  have hsm : Surjective mus.left := by
    have : Surjective (ls.left ≫ mus.left) := by rw [e₁]; exact hsA
    exact AlgebraicGeometry.Surjective.of_comp (f := ls.left) (g := mus.left)
  have hpm : IsProper mus.left := by
    have : IsProper (mus.left ≫ As.hom) := by rw [Over.w]; infer_instance
    exact IsProper.of_comp _ As.hom
  have hfl : IsFinite ls.left := by
    have : IsFinite (ls.left ≫ mus.left) := by rw [e₁]; exact hfin
    exact MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) ls.left mus.left inferInstance this
  have hqm : LocallyQuasiFinite mus.left := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro a
    have hq : LocallyQuasiFinite (ls.left ≫ mus.left) := by rw [e₁]; infer_instance
    have h0 : ((ls.left ≫ mus.left) ⁻¹' {a}).Finite :=
      (locallyQuasiFinite_iff_finite_preimage_singleton.1 hq) a
    refine (h0.image ls.left).subset ?_
    intro x hx
    obtain ⟨y, rfl⟩ := hsl.surj x
    refine ⟨y, ?_, rfl⟩
    simpa using hx
  exact ⟨hfl, hsl, IsFinite.of_isProper_of_locallyQuasiFinite mus.left, hsm⟩

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem isFinite_mu_fibre (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (g : ℕ)
    (hgA : SmoothOfRelativeDimension g A.hom) (hgB : SmoothOfRelativeDimension g B.hom) (l : A ⟶ B) [IsMonHom l]
    (mu : B ⟶ A) [IsMonHom mu] (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (ha : Out.RelAmple ((Over.pullback s).obj A) L) : IsFinite ((Over.pullback s).map mu).left := by
  have e₁ : (Over.pullback s).map l ≫ (Over.pullback s).map mu = 𝟙 ((Over.pullback s).obj A) ^ m := by
    rw [← Functor.map_comp, h₁, pb_map_id_pow]
  have e₂ : (Over.pullback s).map mu ≫ (Over.pullback s).map l = 𝟙 ((Over.pullback s).obj B) ^ m := by
    rw [← Functor.map_comp, h₂, pb_map_id_pow]
  exact (fin_surj_core (isAbelianScheme_pb s A hA) (isAbelianScheme_pb s B hB) _ _ m hm e₁ e₂ hL ha).2.2.1

end PositivityTheory.PrwZar.Z2
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.KilledAnyOf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

open TensorProduct

namespace PositivityTheory.PrwZar.QiP

open GlobalTheory.CompanionTheory.Ar.GR

section BaseChange

variable {R : Type} [CommRing R] {C : Type} [Field C] [Algebra R C] {F : Type} [CommRing F] [Algebra R F]

def uu : F →ₐ[R] (C ⊗[R] F) := (Algebra.TensorProduct.includeRight : F →ₐ[R] C ⊗[R] F)

def lft {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T] (g : F →ₐ[R] T) :
    (C ⊗[R] F) →ₐ[C] T :=
  Algebra.TensorProduct.lift (Algebra.ofId C T) g (fun _ _ => Commute.all _ _)

theorem lft_uu {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T] (g : F →ₐ[R] T) :
    ((lft g).restrictScalars R).comp (uu (C := C)) = g := by
  ext x
  simp [lft, uu]

theorem ext_uu {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T]
    (x y : (C ⊗[R] F) →ₐ[C] T)
    (e : (x.restrictScalars R).comp (uu (C := C)) = (y.restrictScalars R).comp (uu (C := C))) : x = y := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · exact e

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {h : sp (R₀ := R) F ⟶ G}

def u1 : F →ₐ[R] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  (((Algebra.TensorProduct.includeLeft : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F))).restrictScalars R).comp (uu (R := R) (C := C) (F := F))

def u2 : F →ₐ[R] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  (((Algebra.TensorProduct.includeRight : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F))).restrictScalars R).comp (uu (R := R) (C := C) (F := F))

def dlt (hs : IsFinFlatSub G F h) : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  lft (mulPt hs (u1 (C := C)) u2)

def eps (hs : IsFinFlatSub G F h) : (C ⊗[R] F) →ₐ[C] C :=
  lft (onePt hs C)

theorem eps_uu (hs : IsFinFlatSub G F h) :
    ((((Algebra.ofId C (C ⊗[R] F)).comp (eps (C := C) hs)).restrictScalars R).comp (uu (C := C))) = onePt hs (C ⊗[R] F) := by
  rw [← comp_onePt hs ((Algebra.ofId C (C ⊗[R] F)).restrictScalars R), ← lft_uu (C := C) (onePt hs C)]
  rfl

theorem mul_dlt_uu (hs : IsFinFlatSub G F h) (f g : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F)) :
    ((((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map f g).comp (dlt (C := C) hs))).restrictScalars R).comp
      (uu (C := C))) = mulPt hs ((f.restrictScalars R).comp uu) ((g.restrictScalars R).comp uu) := by
  have e : (((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map f g).comp (dlt (C := C) hs))).restrictScalars R).comp
      (uu (C := C)) = ((((Algebra.TensorProduct.lmul' C).comp (Algebra.TensorProduct.map f g))).restrictScalars R).comp
        (((dlt (C := C) hs).restrictScalars R).comp uu) := rfl
  rw [e, dlt, lft_uu, comp_mulPt]
  congr 1
  · ext x
    simp [u1, uu]
  · ext x
    simp [u2, uu]

theorem counitL (hs : IsFinFlatSub G F h) : Qi.CounitL (dlt (C := C) hs) (eps (C := C) hs) := by
  apply ext_uu
  rw [mul_dlt_uu, eps_uu]
  exact mulPt_onePt hs _

theorem counitR (hs : IsFinFlatSub G F h) : Qi.CounitR (dlt (C := C) hs) (eps (C := C) hs) := by
  apply ext_uu
  rw [mul_dlt_uu, eps_uu]
  exact mulPt_onePt' hs _

theorem pw_uu (hs : IsFinFlatSub G F h) (n : ℕ) :
    ((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) n).restrictScalars R).comp uu = powPt hs uu n := by
  induction n with
  | zero => exact eps_uu hs
  | succ n ih =>
    change (((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) n)
      (AlgHom.id C (C ⊗[R] F))).comp (dlt (C := C) hs))).restrictScalars R).comp uu = _
    rw [mul_dlt_uu, ih]
    rfl

theorem pw_mul (hs : IsFinFlatSub G F h) (a b : ℕ) :
    Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (a * b) = (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b) := by
  apply ext_uu
  rw [pw_uu, powPt_mul]
  have hc : (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b)).restrictScalars R).comp
      (uu (C := C)) = ((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).restrictScalars R).comp
        (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b).restrictScalars R).comp uu) := rfl
  rw [hc, pw_uu, comp_powPt, pw_uu]

def ptGrp (hs : IsFinFlatSub G F h) (S : Type) [CommRing S] [Algebra R S] : Subgroup (sp (R₀ := R) S ⟶ G) where
  carrier := {g | ∃ φ : F →ₐ[R] S, spMap φ ≫ h = g}
  mul_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨φ', rfl⟩
    exact ⟨mulPt hs φ φ', mulPt_spec hs φ φ'⟩
  one_mem' := ⟨onePt hs S, onePt_spec hs S⟩
  inv_mem' := by
    rintro _ ⟨φ, rfl⟩
    obtain ⟨χ, hχ⟩ := hs.inv S φ
    exact ⟨χ, eq_inv_of_mul_eq_one_left hχ⟩

theorem pts_killed [Module.Finite R F] (hs : IsFinFlatSub G F h) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : (C ⊗[R] F) →ₐ[C] C, x.comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) m) = eps hs := by
  haveI : Finite (ptGrp hs C) :=
    Finite.of_surjective (fun φ : F →ₐ[R] C => (⟨_, φ, rfl⟩ : ptGrp hs C))
      (by rintro ⟨_, φ, rfl⟩; exact ⟨φ, rfl⟩)
  refine ⟨Nat.card (ptGrp hs C), Nat.card_pos, fun x => ?_⟩
  apply ext_uu
  have hx : ((x.comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (Nat.card (ptGrp hs C)))).restrictScalars R).comp
      (uu (C := C)) = (x.restrictScalars R).comp
        (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (Nat.card (ptGrp hs C))).restrictScalars R).comp uu) := rfl
  have he : ((eps (C := C) hs).restrictScalars R).comp uu = onePt hs C := lft_uu _
  rw [hx, pw_uu, comp_powPt, he]
  apply pt_ext hs
  rw [powPt_spec, onePt_spec]
  have h1 := pow_card_eq_one' (G := ptGrp hs C) (x := ⟨_, (x.restrictScalars R).comp uu, rfl⟩)
  exact congrArg Subtype.val h1

theorem uu_injective [Module.Flat R F] (hR : Function.Injective (algebraMap R C)) :
    Function.Injective (uu (R := R) (C := C) (F := F)) := Algebra.TensorProduct.includeRight_injective hR

end BaseChange

end PositivityTheory.PrwZar.QiP

namespace PositivityTheory.PrwZar

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR QiP

theorem killedAny_of (hc : Qi.KilledCore) : KilledAny := by
  intro C _ _ v R _ _ hv G _ _ F _ _ h hs
  haveI := hs.fin
  haveI := hs.proj
  obtain ⟨N, hN0, hN⟩ := hc C (C ⊗[R] F) (dlt (C := C) hs) (eps hs) (counitL hs) (counitR hs) (pw_mul hs)
    (pts_killed hs)
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have key : powPt hs (AlgHom.id R F) N = onePt hs F := by
    have e1 := pw_uu (C := C) hs N
    have e0 := pw_uu (C := C) hs 0
    rw [hN, e0] at e1
    have a1 : (uu (R := R) (C := C) (F := F)).comp (powPt hs (AlgHom.id R F) N) = powPt hs uu N := by
      rw [comp_powPt, AlgHom.comp_id]
    have a0 : (uu (R := R) (C := C) (F := F)).comp (onePt hs F) = powPt hs uu 0 := by
      rw [comp_onePt]
      rfl
    ext y
    apply uu_injective (C := C) hinj
    exact congrArg (fun f => f y) (a1.trans (e1.symm.trans a0.symm))
  refine ⟨N, hN0, fun S _ _ φ => ?_⟩
  rw [← powPt_spec hs, ← onePt_spec hs S]
  have e : φ.comp (powPt hs (AlgHom.id R F) N) = φ.comp (onePt hs F) := by rw [key]
  rw [comp_powPt, comp_onePt, AlgHom.comp_id] at e
  rw [e]

end PositivityTheory.PrwZar
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.RelAmpleOfLbPow
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem relAmple_of_lbPow {G : Over (Sp Ω)} [GrpObj G] (hG : IsAbelianScheme G) {M : LB G.left} (hM : M.IsLB)
    (n : ℕ) (hn : 1 ≤ n) (h : Out.RelAmple G (lbPow M n)) : Out.RelAmple G M := by
  haveI : IsProper G.hom := hG.proper
  have hP : (lbPow M n).IsLB := GlobalTheory.isLB_lbPow hM n
  exact GlobalTheory.PosDefAmple.relAmple_of_nsmul hM hP hn (cls_lbPow hM n hP).symm h

end PositivityTheory.PrwZar
end
end

