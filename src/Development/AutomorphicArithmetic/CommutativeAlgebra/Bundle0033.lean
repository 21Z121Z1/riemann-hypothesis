import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0013

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RepresentableOfAffine
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

theorem UpperTheory.representable_of_affine :
    LeafHI → B3 → C4 → ∀ (q : ℕ) [NeZero q] (i : ℤ) {P P' : PSh} (r : P' ⟶ P) (c : ∀ T : Scheme.{0}, P'.obj (op T) → Γ(T, ⊤)), (∀ {T T' : Scheme.{0}} (f : T' ⟶ T) (x : P'.obj (op T)), c T' (P'.map f.op x) = f.appTop.hom (c T x)) → (∀ T : Scheme.{0}, Function.Bijective fun x : P'.obj (op T) => (r.app (op T) x, c T x)) → ∀ Y : Scheme.{0}, IsUnit (q : Γ(Y, ⊤)) → ∀ φ : P ⟶ yoneda.obj Y, (∀ T : Scheme.{0}, IsAffine T → Function.Bijective (φ.app (op T))) → Eqv _ (disc.map r) (tw q i) := by
  intro hHI hB hC q _ i P P' r c hc hb Y hq φ hφ
  have hnat : ∀ {U V : Scheme.{0}ᵒᵖ} (f : U ⟶ V) (x : P'.obj U),
      φ.app V (r.app V (P'.map f x)) = f.unop ≫ φ.app U (r.app U x) := by
    intro U V f x
    have h1 : r.app V (P'.map f x) = P.map f (r.app U x) :=
      ConcreteCategory.congr_hom (r.naturality f) x
    have h2 : φ.app V (P.map f (r.app U x)) = f.unop ≫ φ.app U (r.app U x) :=
      ConcreteCategory.congr_hom (φ.naturality f) (r.app U x)
    rw [h1, h2]
  let φ' : P' ⟶ yoneda.obj 𝔸(Fin 1; Y) :=
    { app := fun U => TypeCat.ofHom fun x =>
        AffineSpace.homOfVector (φ.app U (r.app U x)) (fun _ => c U.unop x)
      naturality := fun U V f => by
        ext x
        change AffineSpace.homOfVector (φ.app V (r.app V (P'.map f x))) (fun _ => c V.unop (P'.map f x)) =
          f.unop ≫ AffineSpace.homOfVector (φ.app U (r.app U x)) (fun _ => c U.unop x)
        rw [AffineSpace.comp_homOfVector, hnat f x]
        congr 1
        funext _
        exact hc f.unop x }
  have hφ'v : ∀ (T : Scheme.{0}) (x : P'.obj (op T)), φ'.app (op T) x =
      AffineSpace.homOfVector (φ.app (op T) (r.app (op T) x)) (fun _ => c T x) := fun _ _ => rfl
  have hφ' : ∀ T : Scheme.{0}, IsAffine T → Function.Bijective (φ'.app (op T)) := by
    intro T hT
    constructor
    · intro x y hxy
      rw [hφ'v, hφ'v] at hxy
      have h1 := congrArg (· ≫ 𝔸(Fin 1; Y) ↘ Y) hxy
      simp only [AffineSpace.homOfVector_over] at h1
      have h2 := congrArg (fun g => g.appTop (AffineSpace.coord Y (0 : Fin 1))) hxy
      simp only [AffineSpace.homOfVector_appTop_coord] at h2
      exact (hb T).1 (Prod.ext ((hφ T hT).1 h1) h2)
    · intro g
      obtain ⟨p, hp⟩ := (hφ T hT).2 (g ≫ 𝔸(Fin 1; Y) ↘ Y)
      obtain ⟨x, hx⟩ := (hb T).2 (p, g.appTop (AffineSpace.coord Y (0 : Fin 1)))
      have hx1 : r.app (op T) x = p := congrArg Prod.fst hx
      have hx2 : c T x = g.appTop (AffineSpace.coord Y (0 : Fin 1)) := congrArg Prod.snd hx
      refine ⟨x, ?_⟩
      rw [hφ'v]
      refine AffineSpace.hom_ext ?_ ?_
      · rw [AffineSpace.homOfVector_over, hx1]
        exact hp
      · intro j
        rw [AffineSpace.homOfVector_appTop_coord, hx2, Subsingleton.elim j 0]
  have comm : φ' ≫ yoneda.map (𝔸(Fin 1; Y) ↘ Y) = r ≫ φ := by
    ext U x
    exact AffineSpace.homOfVector_over _ _
  have comm2 : disc.map φ' ≫ sch.map (𝔸(Fin 1; Y) ↘ Y) = disc.map r ≫ disc.map φ := by
    change disc.map φ' ≫ disc.map (yoneda.map (𝔸(Fin 1; Y) ↘ Y)) = _
    rw [← Functor.map_comp, ← Functor.map_comp, comm]
  have e1 := UpperTheory.equiv_of_affine_bijective _ (tw q i) φ hφ
  have e2 := UpperTheory.equiv_of_affine_bijective _ (tw q i) φ' hφ'
  have e3 := hHI hB hC q i Y hq
  intro n
  have key : pull _ (disc.map r) (tw q i) n ∘ pull _ (disc.map φ) (tw q i) n =
      pull _ (disc.map φ') (tw q i) n ∘ pull _ (sch.map (𝔸(Fin 1; Y) ↘ Y)) (tw q i) n := by
    funext x
    have a1 := pull_comp (ZMod q) (disc.map r) (disc.map φ) (tw q i) n x
    have a2 := pull_comp (ZMod q) (disc.map φ') (sch.map (𝔸(Fin 1; Y) ↘ Y)) (tw q i) n x
    exact a1.symm.trans ((congrArg (fun g => pull (ZMod q) g (tw q i) n x) comm2.symm).trans a2)
  refine (Function.Bijective.of_comp_iff (pull _ (disc.map r) (tw q i) n) (e1 n)).1 ?_
  rw [key]
  exact (e2 n).comp (e3 n)
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.UnitSectionsMultiplicativeGroupBijectiveAffine
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

namespace UpperTheory.UnitsInj
open Polynomial

private noncomputable def evalT {A : Type} [CommRing A] (a : A) : ℤ[X] →+* A :=
  Polynomial.eval₂RingHom (Int.castRingHom A) a

private noncomputable abbrev Line : Scheme.{0} := Spec (CommRingCat.of ℤ[X])

private noncomputable def toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) : V ⟶ Line :=
  V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (evalT a))

private noncomputable def ofLine {V : Scheme.{0}} (f : V ⟶ Line) : Γ(V, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom X)

private lemma line_sheaf : Presieve.IsSheaf Scheme.etaleTopology (yoneda.obj Line) :=
  Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end UpperTheory.UnitsInj

private theorem unitsInj_ofLine_toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) :
    UpperTheory.UnitsInj.ofLine (UpperTheory.UnitsInj.toLine a) = a := by
  unfold UpperTheory.UnitsInj.ofLine UpperTheory.UnitsInj.toLine
  rw [Scheme.Hom.comp_appTop]
  simp [UpperTheory.UnitsInj.evalT]

private theorem comp_unitsInj_toLine {V W : Scheme.{0}} (f : W ⟶ V) (a : Γ(V, ⊤)) :
    f ≫ UpperTheory.UnitsInj.toLine a = UpperTheory.UnitsInj.toLine (f.appTop.hom a) := by
  unfold UpperTheory.UnitsInj.toLine
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  apply Polynomial.ringHom_ext
  · intro n
    simp [UpperTheory.UnitsInj.evalT]
  · simp [UpperTheory.UnitsInj.evalT]

theorem UpperTheory.unitSections_multiplicativeGroup_bijective_affine :
    ∀ (R : Type) [CommRing R], Function.Bijective
        (unitSec : (Γ(Spec (CommRingCat.of R), ⊤))ˣ → Sec Gm (Spec (CommRingCat.of R))) := by
  intro R _
  refine ⟨?_, fun b => UpperTheory.exists_unit_eq_multiplicativeGroup_section _ b⟩
  intro u v h
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op (Spec (CommRingCat.of R)))
    (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v)) h
  have key : UpperTheory.UnitsInj.toLine (u : Γ(Spec (CommRingCat.of R), ⊤)) =
      UpperTheory.UnitsInj.toLine (v : Γ(Spec (CommRingCat.of R), ⊤)) := by
    refine (UpperTheory.UnitsInj.line_sheaf _ hS).isSeparatedFor
      (fun W f _ => f ≫ UpperTheory.UnitsInj.toLine (u : Γ(Spec (CommRingCat.of R), ⊤)))
      _ _ (fun W f hf => rfl) (fun W f hf => ?_)
    show f ≫ UpperTheory.UnitsInj.toLine _ = f ≫ UpperTheory.UnitsInj.toLine _
    rw [comp_unitsInj_toLine, comp_unitsInj_toLine]
    have h2 := congrArg (fun z : ULift (Additive (Scheme.Γ.obj (op W))ˣ) =>
      ((Additive.toMul z.down : (Scheme.Γ.obj (op W))ˣ) : Scheme.Γ.obj (op W))) hf
    have h3 : f.appTop.hom (u : Γ(Spec (CommRingCat.of R), ⊤)) = f.appTop.hom v := h2
    rw [h3]
  have h4 := congrArg UpperTheory.UnitsInj.ofLine key
  rw [unitsInj_ofLine_toLine, unitsInj_ofLine_toLine] at h4
  exact Units.ext h4
end

