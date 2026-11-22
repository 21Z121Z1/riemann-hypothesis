import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialCharacterFiniteCommGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2528

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFiniteCommGroupSchemeCobounda
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.CharKer
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.SymCob
open TensorProduct

def pt (K : Type) [CommRing K] {B A : Type} [CommRing B] [CommRing A] [Algebra K B] [Algebra K A]
    (φ : B →ₐ[K] A) :
    (Spec (CommRingCat.of A)).asOver (Sp K) ⟶ (Spec (CommRingCat.of B)).asOver (Sp K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K A))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact φ.comp_algebraMap)

theorem pt_sharp (K : Type) [CommRing K] {B A : Type} [CommRing B] [CommRing A] [Algebra K B] [Algebra K A]
    (φ : B →ₐ[K] A) (b : B) :
    (pt K φ).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (φ b) := by
  have hn := congr(($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ.toRingHom))).hom b)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hn
  exact hn.symm

theorem specInv_injective (R : CommRingCat) : Function.Injective (Scheme.ΓSpecIso R).inv.hom := by
  intro x y h
  have := congrArg (Scheme.ΓSpecIso R).hom.hom h
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply,
    CommRingCat.id_apply] at this

theorem secMap_surj (K : Type) [CommRing K] (B D : Type) [CommRing B] [CommRing D] [Algebra K B] [Algebra K D] :
    ∃ Ψ : Γ(((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left, ⊤) →+*
      B ⊗[K] D, ∀ x, GlobalTheory.CharExists.secMap K B D (Ψ x) = x := by
  let e : ((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of D)).asOver (Sp K)).left ≅
      Spec (CommRingCat.of (B ⊗[K] D)) := pullbackSpecIso' K B D
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (B ⊗[K] D))).hom.hom.comp e.inv.appTop.hom, fun x => ?_⟩
  change e.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom ((Scheme.ΓSpecIso _).hom.hom (e.inv.appTop.hom x))) = x
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply]
  change (e.hom ≫ e.inv).appTop.hom x = x
  rw [e.hom_inv_id]; rfl

theorem key (K : Type) [CommRing K] (B A : Type) [CommRing B] [CommRing A] [Algebra K B] [Algebra K A]
    (Y : Over (Sp K)) (f h : Y ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) (φ ψ : B →ₐ[K] A)
    (j : A →+* Γ(Y.left, ⊤))
    (hf : ∀ b, f.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (φ b))
    (hh : ∀ b, h.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (ψ b))
    (z : B ⊗[K] B) :
    (lift f h).left.appTop.hom (GlobalTheory.CharExists.secMap K B B z) =
      j (Algebra.TensorProduct.lift φ ψ (fun _ _ => Commute.all _ _) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b d => rw [GlobalTheory.CharExists.secMap_lift, hf, hh, Algebra.TensorProduct.lift_tmul, map_mul]

theorem mulpt (K : Type) [CommRing K] (B A : Type) [CommRing B] [HopfAlgebra K B] [CommRing A] [Algebra K A]
    (Y : Over (Sp K)) (f h : Y ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) (φ ψ : B →ₐ[K] A)
    (j : A →+* Γ(Y.left, ⊤))
    (hf : ∀ b, f.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (φ b))
    (hh : ∀ b, h.left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = j (ψ b)) (b : B) :
    (f * h).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) =
      j (((Algebra.TensorProduct.lift φ ψ (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom K B)) b) := by
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (R := K) (Coalgebra.comul (R := K) b)
  rw [GlobalTheory.CharExists.mulsharp K B Y f h b S (fun i => i.1) (fun i => i.2) hS, hS, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.lift_tmul, map_mul, hf, hh]

theorem tensor_assoc_comul_placement_eq (K B : Type) [CommRing K] [CommRing B] [Bialgebra K B] :
    Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : B ⊗[K] B →ₐ[K] (B ⊗[K] B) ⊗[K] B).comp
        (Algebra.TensorProduct.includeLeft : B →ₐ[K] B ⊗[K] B))
      (((Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
          (Algebra.TensorProduct.includeRight : B ⊗[K] B →ₐ[K] B ⊗[K] (B ⊗[K] B))).comp
        (Bialgebra.comulAlgHom K B)) (fun _ _ => Commute.all _ _) =
      (Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id K B) (Bialgebra.comulAlgHom K B)) := by
  refine Algebra.TensorProduct.ext' fun a b => ?_
  simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply, Bialgebra.comulAlgHom_apply, AlgHom.coe_coe]
  have hab : a ⊗ₜ[K] Coalgebra.comul (R := K) b =
      (a ⊗ₜ[K] (1 : B ⊗[K] B)) * ((1 : B) ⊗ₜ[K] Coalgebra.comul (R := K) b) := by simp
  rw [hab, map_mul]
  simp [Algebra.TensorProduct.one_def]

theorem over_comp_appTop {S : Scheme.{0}} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z) (v : Γ(Z.left, ⊤)) :
    (f ≫ g).left.appTop.hom v = f.left.appTop.hom (g.left.appTop.hom v) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop]; rfl

set_option maxHeartbeats 1600000 in

theorem exists_coboundary : ∀ (K : Type) [Field K] [IsAlgClosed K] (N : Over (Sp K)) [GrpObj N] [IsCommMonObj N], IsFinite N.hom → ∀ c : Γ((N ⊗ N).left, ⊤)ˣ, (∀ (T : Over (Sp K)) (x y z : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (lift (x * y) z).left c = GlobalTheory.CharKer.pullTop (lift y z).left c * GlobalTheory.CharKer.pullTop (lift x (y * z)).left c) → (∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c = GlobalTheory.CharKer.pullTop (lift y x).left c) → ∃ u : Γ(N.left, ⊤)ˣ, ∀ (T : Over (Sp K)) (x y : T ⟶ N), GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (x * y).left u = GlobalTheory.CharKer.pullTop x.left u * GlobalTheory.CharKer.pullTop y.left u := by
  intro K _ _ N _ _ hf c hcoc hsym
  obtain ⟨B, _, _, hcc, hfin, e, he⟩ := GlobalTheory.CharExists.pres K N hf
  obtain ⟨Ψ, hΨ⟩ := secMap_surj K B B
  obtain ⟨cG, hcG⟩ : ∃ cG : Γ(((Spec (CommRingCat.of B)).asOver (Sp K) ⊗ (Spec (CommRingCat.of B)).asOver (Sp K)).left, ⊤)ˣ,
      cG = pullTop (e.hom ⊗ₘ e.hom).left c := ⟨_, rfl⟩
  have hcB : GlobalTheory.CharExists.secMap K B B (Ψ cG) = cG := hΨ _
  have hcBu : IsUnit (Ψ cG) := cG.isUnit.map Ψ
  have hpull : ∀ (T : Over (Sp K)) (x y : T ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)),
      pullTop (lift (x ≫ e.hom) (y ≫ e.hom)).left c = pullTop (lift x y).left cG := by
    intro T x y
    have : lift (x ≫ e.hom) (y ≫ e.hom) = lift x y ≫ (e.hom ⊗ₘ e.hom) := by
      rw [lift_map]
    rw [this, Over.comp_left, GlobalTheory.CharExists.pullTop_comp, hcG]
  have hmul : ∀ (T : Over (Sp K)) (x y : T ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)),
      (x ≫ e.hom) * (y ≫ e.hom) = (x * y) ≫ e.hom := by
    intro T x y
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

  let iL : B →ₐ[K] B ⊗[K] B := Algebra.TensorProduct.includeLeft
  let iR : B →ₐ[K] B ⊗[K] B := Algebra.TensorProduct.includeRight
  have hsymB : Algebra.TensorProduct.comm K B B (Ψ cG) = Ψ cG := by
    have h := congrArg Units.val (hsym _ (pt K iL ≫ e.hom) (pt K iR ≫ e.hom))
    rw [hpull, hpull] at h
    simp only [pullTop, Units.coe_map, MonoidHom.coe_coe] at h
    rw [← hcB, key K B _ _ _ _ iL iR _ (pt_sharp K iL) (pt_sharp K iR),
      key K B _ _ _ _ iR iL _ (pt_sharp K iR) (pt_sharp K iL)] at h
    have h' := specInv_injective _ h
    have e1 : Algebra.TensorProduct.lift iL iR (fun _ _ => Commute.all _ _) = AlgHom.id K (B ⊗[K] B) :=
      Algebra.TensorProduct.ext' fun a b => by simp [iL, iR]
    have e2 : Algebra.TensorProduct.lift iR iL (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.comm K B B).toAlgHom :=
      Algebra.TensorProduct.ext' fun a b => by simp [iL, iR]
    rw [e1, e2] at h'
    exact h'.symm

  let ι₁ : B →ₐ[K] (B ⊗[K] B) ⊗[K] B := Algebra.TensorProduct.includeLeft.comp iL
  let ι₂ : B →ₐ[K] (B ⊗[K] B) ⊗[K] B := Algebra.TensorProduct.includeLeft.comp iR
  let ι₃ : B →ₐ[K] (B ⊗[K] B) ⊗[K] B := Algebra.TensorProduct.includeRight
  have hcocB : Ψ cG ⊗ₜ[K] (1 : B) * Algebra.TensorProduct.map (Bialgebra.comulAlgHom K B) (AlgHom.id K B) (Ψ cG) =
      (Algebra.TensorProduct.assoc K K K B B B).symm ((1 : B) ⊗ₜ[K] Ψ cG *
        Algebra.TensorProduct.map (AlgHom.id K B) (Bialgebra.comulAlgHom K B) (Ψ cG)) := by
    have h := congrArg Units.val (hcoc _ (pt K ι₁ ≫ e.hom) (pt K ι₂ ≫ e.hom) (pt K ι₃ ≫ e.hom))
    simp only [hmul, hpull] at h
    simp only [Units.val_mul, pullTop, Units.coe_map, MonoidHom.coe_coe] at h
    have k₁ := key K B _ _ (pt K ι₁) (pt K ι₂) ι₁ ι₂ _ (pt_sharp K ι₁) (pt_sharp K ι₂) (Ψ cG)
    have k₂ := key K B _ _ (pt K ι₁ * pt K ι₂) (pt K ι₃) _ ι₃ _
      (mulpt K B _ _ (pt K ι₁) (pt K ι₂) ι₁ ι₂ _ (pt_sharp K ι₁) (pt_sharp K ι₂)) (pt_sharp K ι₃) (Ψ cG)
    have k₃ := key K B _ _ (pt K ι₂) (pt K ι₃) ι₂ ι₃ _ (pt_sharp K ι₂) (pt_sharp K ι₃) (Ψ cG)
    have k₄ := key K B _ _ (pt K ι₁) (pt K ι₂ * pt K ι₃) ι₁ _ _ (pt_sharp K ι₁)
      (mulpt K B _ _ (pt K ι₂) (pt K ι₃) ι₂ ι₃ _ (pt_sharp K ι₂) (pt_sharp K ι₃)) (Ψ cG)
    rw [hcB] at k₁ k₂ k₃ k₄
    simp only [k₁, k₂, k₃, k₄] at h
    have h' := specInv_injective _ (((map_mul _ _ _).trans h).trans (map_mul _ _ _).symm)
    have E1 : Algebra.TensorProduct.lift ι₁ ι₂ (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.includeLeft : B ⊗[K] B →ₐ[K] (B ⊗[K] B) ⊗[K] B) :=
      Algebra.TensorProduct.ext' fun a b => by simp [ι₁, ι₂, iL, iR]
    have E3 : Algebra.TensorProduct.lift ι₂ ι₃ (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
          (Algebra.TensorProduct.includeRight : B ⊗[K] B →ₐ[K] B ⊗[K] (B ⊗[K] B)) :=
      Algebra.TensorProduct.ext' fun a b => by simp [ι₂, ι₃, iL, iR]
    have E2 : Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift ι₁ ι₂ (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K B)) ι₃ (fun _ _ => Commute.all _ _) =
        Algebra.TensorProduct.map (Bialgebra.comulAlgHom K B) (AlgHom.id K B) := by
      rw [E1]
      exact Algebra.TensorProduct.ext' fun a b => by simp [ι₃]
    have E4 : Algebra.TensorProduct.lift ι₁ ((Algebra.TensorProduct.lift ι₂ ι₃ (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K B)) (fun _ _ => Commute.all _ _) =
        (Algebra.TensorProduct.assoc K K K B B B).symm.toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id K B) (Bialgebra.comulAlgHom K B)) := by
      rw [E3]
      exact tensor_assoc_comul_placement_eq K B
    rw [E2, E4, E1, E3] at h'
    simpa [map_mul] using h'
  obtain ⟨u₀, hu₀, hcu⟩ := (GlobalTheory.T.exists_twisted_groupLike') K B (Ψ cG) hcBu hcocB hsymB
  have hu := (GlobalTheory.T.isUnit_of_isUnit_mul_comul_eq_tmul) K B (Ψ cG) hcBu u₀ hu₀ hcu
  obtain ⟨w, hw⟩ : ∃ w : Γ(((Spec (CommRingCat.of B)).asOver (Sp K)).left, ⊤)ˣ,
      w = Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom hu.unit := ⟨_, rfl⟩
  have hcu' : Ψ cG * Coalgebra.comul (R := K) (hu.unit : B) = (hu.unit : B) ⊗ₜ[K] (hu.unit : B) := by
    rw [IsUnit.unit_spec]; exact hcu
  refine ⟨pullTop e.inv.left w, fun T x y => ?_⟩
  have hc : pullTop (lift x y).left c = pullTop (lift (x ≫ e.inv) (y ≫ e.inv)).left cG := by
    have h := hpull T (x ≫ e.inv) (y ≫ e.inv)
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at h
    exact h
  have hxy : (x * y) ≫ e.inv = (x ≫ e.inv) * (y ≫ e.inv) := by
    have h := hmul T (x ≫ e.inv) (y ≫ e.inv)
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at h
    simp only [h, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hval : ∀ z : T ⟶ N, ((pullTop z.left (pullTop e.inv.left w) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) =
      (z ≫ e.inv).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (hu.unit : B)) := by
    intro z
    rw [hw]
    exact (over_comp_appTop z e.inv _).symm
  letI : Algebra K Γ(T.left, ⊤) :=
    (T.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let sh : (T ⟶ (Spec (CommRingCat.of B)).asOver (Sp K)) → (B →ₐ[K] Γ(T.left, ⊤)) := fun f =>
    { toRingHom := f.left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
      commutes' := fun k => GlobalTheory.CharExists.algsharp K B T f k }
  have kc := key K B _ T (x ≫ e.inv) (y ≫ e.inv) (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (RingHom.id _)
    (fun _ => rfl) (fun _ => rfl) (Ψ cG)
  have km := mulpt K B _ T (x ≫ e.inv) (y ≫ e.inv) (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (RingHom.id _)
    (fun _ => rfl) (fun _ => rfl) (hu.unit : B)
  rw [hcB] at kc
  have fin : (Algebra.TensorProduct.lift (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (fun _ _ => Commute.all _ _)) (Ψ cG) *
      ((Algebra.TensorProduct.lift (sh (x ≫ e.inv)) (sh (y ≫ e.inv)) (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom K B)) (hu.unit : B) = sh (x ≫ e.inv) (hu.unit : B) * sh (y ≫ e.inv) (hu.unit : B) := by
    rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, ← map_mul, hcu', Algebra.TensorProduct.lift_tmul]
  simp only [hc]
  ext
  simp only [Units.val_mul, hval]
  simp only [hxy]
  simp only [pullTop, Units.coe_map, MonoidHom.coe_coe]
  simp only [kc, km, RingHom.id_apply]
  exact fin
end GlobalTheory.SymCob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeAtOriginAddTangentVector
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin.OriginCoordinatesAdd

theorem isLocalRing_tsz (S M : Type) [CommRing S] [IsLocalRing S] [AddCommGroup M] [Module S M] [Module Sᵐᵒᵖ M]
    [IsCentralScalar S M] : IsLocalRing (TrivSqZeroExt S M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst with h | h
    · exact Or.inl ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2 h)
    · exact Or.inr ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by simpa using h))

theorem isLocalHom_map {S M N : Type} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [Module Sᵐᵒᵖ M] [IsCentralScalar S M] [Module Sᵐᵒᵖ N] [IsCentralScalar S N] (L : M →ₗ[S] N) :
    IsLocalHom ((TrivSqZeroExt.map L : TrivSqZeroExt S M →ₐ[S] TrivSqZeroExt S N) : TrivSqZeroExt S M →+* TrivSqZeroExt S N) :=
  ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩

variable {X : Scheme.{0}}

def valAt {A : Type} [CommRing A] [IsLocalRing A] (x : Sp A ⟶ X) (p : X) (h : x (IsLocalRing.closedPoint A) = p) :
    X.presheaf.stalk p →+* A :=
  ((X.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of A) x).hom

theorem valAt_comp {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (g : A →+* B)
    [IsLocalHom g] (x : Sp A ⟶ X) (p : X) (hx : x (IsLocalRing.closedPoint A) = p)
    (hy : (spMap g ≫ x) (IsLocalRing.closedPoint B) = p) (f : X.presheaf.stalk p) :
    valAt (spMap g ≫ x) p hy f = g (valAt x p hx f) := by
  subst hx
  let ψ : X.presheaf.stalk (x (IsLocalRing.closedPoint A)) ⟶ CommRingCat.of B :=
    Scheme.stalkClosedPointTo (R := CommRingCat.of A) x ≫ CommRingCat.ofHom g
  have hψl : IsLocalHom ψ.hom := by
    show IsLocalHom (g.comp (Scheme.stalkClosedPointTo (R := CommRingCat.of A) x).hom)
    infer_instance
  have e1 : Spec.map ψ ≫ X.fromSpecStalk _ = spMap g ≫ x := by
    simp only [ψ, Spec.map_comp, Category.assoc]
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have e2 := congrArg (SpecToEquivOfLocalRing X (CommRingCat.of B)) e1
  have e3 : (SpecToEquivOfLocalRing X (CommRingCat.of B)) (Spec.map ψ ≫ X.fromSpecStalk _) = ⟨_, ψ, hψl⟩ :=
    (SpecToEquivOfLocalRing X (CommRingCat.of B)).apply_symm_apply ⟨_, ψ, hψl⟩
  rw [e3] at e2
  obtain ⟨h1, h2⟩ := SpecToEquivOfLocalRing_eq_iff.1 e2.symm
  dsimp only [SpecToEquivOfLocalRing, Equiv.coe_fn_mk] at h2
  have h2' : Scheme.stalkClosedPointTo (R := CommRingCat.of B) (spMap g ≫ x) =
      (X.presheaf.stalkCongr (Inseparable.of_eq hy.symm)).inv ≫ ψ := h2
  simp only [valAt, h2', Iso.hom_inv_id_assoc]
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, ψ]
  rfl

theorem valAt_congr {A : Type} [CommRing A] [IsLocalRing A] {x x' : Sp A ⟶ X} (e : x = x') (p : X)
    (h : x (IsLocalRing.closedPoint A) = p) (h' : x' (IsLocalRing.closedPoint A) = p) :
    valAt x p h = valAt x' p h' := by
  subst e; rfl

end GlobalTheory.CoordsOrigin.OriginCoordinatesAdd

namespace GlobalTheory.CoordsOrigin

open GlobalTheory.CoordsOrigin.OriginCoordinatesAdd

theorem tanDer_add : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (u v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)),
    tanDer G (u + v) f = tanDer G u f + tanDer G v f := by
  intro R _ _ G _ _ u v f
  haveI : IsLocalRing (TrivSqZeroExt R (R × R)) := isLocalRing_tsz R (R × R)
  let P : overAt (𝟙 (Sp R)) (TrivSqZeroExt R (R × R)) ⟶ G :=
    (homAt (𝟙 (Sp R)) (tm (LinearMap.inl R R R)) ≫ tv u) * (homAt (𝟙 (Sp R)) (tm (LinearMap.inr R R R)) ≫ tv v)
  have hz : (0 : R →ₗ[R] R) = (0 : R) • (LinearMap.id : R →ₗ[R] R) := by simp
  have hid : ∀ w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ G,
      homAt (𝟙 (Sp R)) (tm (LinearMap.id : R →ₗ[R] R)) ≫ w = w := by
    intro w
    simp only [tm]
    rw [TrivSqZeroExt.map_id, homAt_id, Category.id_comp]
  have hfst : homAt (𝟙 (Sp R)) (tm (LinearMap.fst R R R)) ≫ P = tv u := by
    simp only [P]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hz]
    change _ * smT (𝟙 (Sp R)) 0 (tv v) = _
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, _root_.mul_one, hid]
  have hsnd : homAt (𝟙 (Sp R)) (tm (LinearMap.snd R R R)) ≫ P = tv v := by
    simp only [P]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hz]
    change smT (𝟙 (Sp R)) 0 (tv u) * _ = _
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, _root_.one_mul, hid]
  have hsum : homAt (𝟙 (Sp R)) (tm (LinearMap.coprod (LinearMap.id : R →ₗ[R] R) LinearMap.id)) ≫ P = tv (u + v) := by
    simp only [P]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
      ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, LinearMap.coprod_inl, LinearMap.coprod_inr,
      hid, hid, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_add]
  have hP : P.left (IsLocalRing.closedPoint (TrivSqZeroExt R (R × R))) = origin G := by
    have e : spMap ((tm (LinearMap.fst R R R) : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) ≫ P.left = (tv u).left := congrArg (fun q => q.left) hfst
    haveI := isLocalHom_map (LinearMap.fst R R R)
    have e0 : spMap ((tm (LinearMap.fst R R R) : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) (IsLocalRing.closedPoint (DualNumber R)) =
        IsLocalRing.closedPoint (TrivSqZeroExt R (R × R)) :=
      Spec_closedPoint (f := CommRingCat.ofHom _)
    rw [← e0, ← tv_closedPoint G u, ← e]
    rfl
  have key : ∀ (L : R × R →ₗ[R] R) (w : TanM (𝟙 (Sp R)) G), homAt (𝟙 (Sp R)) (tm L) ≫ P = tv w →
      tanDer G w f = L (valAt P.left (origin G) hP f).snd := by
    intro L w hw
    haveI := isLocalHom_map L
    have e : (tv w).left = spMap ((tm L : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) ≫ P.left := (congrArg (fun q => q.left) hw).symm
    have hy : (spMap ((tm L : TrivSqZeroExt R (R × R) →ₐ[R] DualNumber R) :
        TrivSqZeroExt R (R × R) →+* DualNumber R) ≫ P.left) (IsLocalRing.closedPoint (DualNumber R)) = origin G :=
      e ▸ tv_closedPoint G w
    rw [tanDer_eq]
    change (valAt (tv w).left (origin G) (tv_closedPoint G w) f).snd = _
    rw [valAt_congr e (origin G) _ hy, valAt_comp _ P.left (origin G) hP hy]
    simp [tm]
  rw [key _ _ hsum, key _ _ hfst, key _ _ hsnd]
  simp

end GlobalTheory.CoordsOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeAtOriginSmulTangentVector
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin

noncomputable section

namespace GlobalTheory.CoordsOrigin

set_option backward.isDefEq.respectTransparency false in

theorem stalkClosedPointTo_localMap_comp {X : Scheme.{0}} {A B : CommRingCat.{0}} [IsLocalRing A] [IsLocalRing B]
    (x : Spec A ⟶ X) (g : A ⟶ B) [IsLocalHom g.hom] (y : Spec B ⟶ X) (hy : y = Spec.map g ≫ x) (x₀ : X)
    (h₁ : x (IsLocalRing.closedPoint A) = x₀) (h₂ : y (IsLocalRing.closedPoint B) = x₀) :
    (X.presheaf.stalkCongr (Inseparable.of_eq h₂.symm)).hom ≫ Scheme.stalkClosedPointTo y =
      ((X.presheaf.stalkCongr (Inseparable.of_eq h₁.symm)).hom ≫ Scheme.stalkClosedPointTo x) ≫ g := by
  subst h₁
  have hy' : y = Spec.map (Scheme.stalkClosedPointTo x ≫ g) ≫ X.fromSpecStalk _ := by
    rw [hy, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  clear hy
  subst hy'
  haveI : IsLocalHom (Scheme.stalkClosedPointTo x ≫ g).hom := by
    rw [CommRingCat.hom_comp]; infer_instance
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  simp only [TopCat.Presheaf.stalkCongr_hom, Category.assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc]
  exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (Scheme.stalkClosedPointTo x ≫ g) U _

theorem tanDer_smul : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (r : R) (v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)), tanDer G (r • v) f = r * tanDer G v f := by
  intro R _ _ G _ _ r v f
  have hl : IsLocalHom (CommRingCat.ofHom (epsMul r)).hom := ⟨fun a ha => (TrivSqZeroExt.isUnit_iff_isUnit_fst).2 (by
    simpa [epsMul] using (TrivSqZeroExt.isUnit_iff_isUnit_fst).1 ha)⟩
  have hy : (tv (r • v)).left = Spec.map (CommRingCat.ofHom (epsMul r)) ≫ (tv v).left := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_smul, smT_left]
  have key := stalkClosedPointTo_localMap_comp (A := CommRingCat.of (DualNumber R)) (B := CommRingCat.of (DualNumber R))
    (tv v).left (CommRingCat.ofHom (epsMul r)) (tv (r • v)).left hy (origin G) (tv_closedPoint G v)
    (tv_closedPoint G (r • v))
  rw [tanDer_eq, tanDer_eq]
  refine (congrArg (fun φ => (φ.hom f).snd) key).trans ?_
  have hs : ∀ a : DualNumber R, (epsMul r a).snd = r * a.snd := fun a => by simp [epsMul]
  exact hs _

end GlobalTheory.CoordsOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauBimultOfRefinesPolarisedData
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem exists_fracSpec {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := by
  have hu : ∀ y : nonZeroDivisors R, IsUnit ((algebraMap R' (FractionRing R')).comp ρ y) := fun y => by
    refine IsUnit.mk0 _ ?_
    rw [RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact (map_ne_zero_iff ρ hρ).2 (nonZeroDivisors.ne_zero y.2)
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hu)), ?_⟩
  simp only [jK, spMap, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsLocalization.lift_eq]

theorem toUnit_left {S : Scheme.{0}} (T : Over S) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

theorem tauBimult_of_half : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R)
    (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X), Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) →
    D.TauBimult := by
  intro R _ _ R' _ _ Q ρ D e hρ h
  obtain ⟨κ, hκ⟩ := exists_fracSpec ρ hρ
  obtain ⟨β, β₂, w, hpb, hsq, hgen, hnorm, hc, hper⟩ := h
  have per : ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' =
      lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J := by
    intro a b z J J' hJ hJ'
    have := hper κ hκ a b z J J' hJ hJ'
    rwa [show unitOn (1 : (FractionRing R')ˣ) = 1 from map_one _, map_one, _root_.mul_one] at this
  let k : Over.mk ((TK R').hom ≫ spMap ρ) ⟶ TK R := Over.homMk κ hκ
  have hQ : ∀ a a' b : Q.X, ∀ z J, Good Q.M.L z J →
      val (Q.tau (a + a') b) κ z J * @id ((TK R').left.presheaf.stalk z)ˣ
        (cubV (T := Over.mk ((TK R').hom ≫ spMap ρ)) Q.cub z J
        (k ≫ toUnit (TK R) ≫ Q.c a) (k ≫ toUnit (TK R) ≫ Q.c a') (k ≫ toUnit (TK R) ≫ Q.c b)) =
      val (Q.tau a b) κ z J * val (Q.tau a' b) κ z J := by
    intro a a' b z J hJ
    have hcorr : LB.Gen.Corr Q.M.L _ _ _ _ (LB.mulGen Q.M.L _ _ _ _ (Q.tau (a + a') b)
        (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t
          (lift (toUnit (TK R) ≫ Q.c a) (lift (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b))).left))
        (LB.mulGen Q.M.L _ _ _ _ (Q.tau a b) (Q.tau a' b)) := by
      refine corr_of_val Q.M.isLB fun y J hJ => ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
      refine (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)).trans ?_
      rw [Category.id_comp]
      exact Q.tau_add a a' b y J hJ
    have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ hcorr κ).trans (val_mul hJ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_cub Q.cub k hJ _ _ _).symm
  intro a a' b
  refine corr_of_val D.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ, -⟩ := exists_good Q.M.L Q.M.isLB y (K := PEmpty) (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim)
  refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  refine (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _)).trans ?_
  rw [Category.id_comp]
  have hx : toUnit (TK R') ≫ D.c (a + a') = (toUnit (TK R') ≫ D.c a) * (toUnit (TK R') ≫ D.c a') := by
    rw [D.c_add, padd, comp_lift_assoc, Hom.mul_def]
  have hu : ∀ χ : D.X, (k ≫ toUnit (TK R) ≫ Q.c (e χ)).left = (toUnit (TK R') ≫ D.c χ).left ≫ β := by
    intro χ
    simp only [Over.comp_left, Over.homMk_left, toUnit_left, Category.assoc, hc, k]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ Over.Hom.left (Q.c (e χ))) hκ
  obtain ⟨-, hw⟩ := GlobalTheory.T.mumfordBundleIso_normalised_respects_laws _ _ Q.B D.P.A Q.M ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ Q.cub D.cub (spMap ρ) β β₂ w
    hpb D.P.isAb hsq hgen hnorm (TK R') (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)
    y J J' hJ hJ'
  have hw' := hw _ _ _ (hu a) (hu a') (hu b)
  rw [← hx] at hw'
  have hq := hQ (e a) (e a') (e b) y J hJ
  rw [← map_add] at hq
  change val (D.tau (a + a') b) (𝟙 _) y J' * cubV D.cub y J' _ _ _ = _
  rw [per _ _ y J J' hJ hJ', per _ _ y J J' hJ hJ', per _ _ y J J' hJ hJ']
  calc _ = (lamVal w (lift (toUnit (TK R') ≫ D.c (a + a')) (toUnit (TK R') ≫ D.c b)).left y J J' *
        cubV D.cub y J' (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)) *
        val (Q.tau (e (a + a')) (e b)) κ y J := by ac_rfl
    _ = _ := by
      rw [hw']
      calc _ = lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left y J J' *
            lamVal w (lift (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)).left y J J' *
            (val (Q.tau (e (a + a')) (e b)) κ y J * @id ((TK R').left.presheaf.stalk y)ˣ
              (cubV (T := Over.mk ((TK R').hom ≫ spMap ρ)) Q.cub y J
              (k ≫ toUnit (TK R) ≫ Q.c (e a)) (k ≫ toUnit (TK R) ≫ Q.c (e a')) (k ≫ toUnit (TK R) ≫ Q.c (e b)))) := by
            ac_rfl
        _ = _ := by rw [hq]; ac_rfl

end GlobalTheory.PolDeg
end
end

