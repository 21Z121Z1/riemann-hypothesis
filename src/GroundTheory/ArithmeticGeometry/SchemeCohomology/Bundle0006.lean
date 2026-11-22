import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjLaurent
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0005
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorInvertible
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0004

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjCechModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

variable (A n) in

abbrev twistAb (k : ℤ) : (Opens (projectiveSpace A n).toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (modulesAb (twistingSheaf (grading A n) k)).obj

def awayDegEquiv {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) :
    ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) k ≃+ LDeg A (Set.range i) k :=
  AddEquiv.ofBijective
    ({ toFun z := ⟨awayToLaurent i z.1, (mem_LDeg_iff i k _).2 ⟨z.1, z.2, rfl⟩⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' _ _ := Subtype.ext (map_add _ _ _) } :
      ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) k →+ LDeg A (Set.range i) k)
    ⟨fun z z' h => Subtype.ext (awayToLaurent_injective i (congrArg Subtype.val h)),
      fun ℓ => by
        obtain ⟨z, hz, h⟩ := (mem_LDeg_iff i k ℓ.1).1 ℓ.2
        exact ⟨⟨z, hz⟩, Subtype.ext h⟩⟩

@[simp] lemma awayDegEquiv_apply {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) (z) :
    (awayDegEquiv (A := A) i k z).1 = awayToLaurent i z.1 := rfl

def sectionEquiv {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) :
    ProjTwist.awayDeg (grading A n) (xprod_mem i) (Nat.succ_pos p) k ≃+
      Γ(twistingSheaf (grading A n) k, Proj.basicOpen (grading A n) (xprod i)) :=
  AddEquiv.ofBijective _ (ProjTwist.toSection_bijective (X_mem (i 0))
    (xprod_mem (i ∘ Fin.succ)) (xprod_succ i) (xprod_mem i) k)

def resEquiv {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) {V W : Opens X} (h : V = W) :
    P.obj (op W) ≃+ P.obj (op V) where
  toFun := res P h.le
  invFun := res P h.ge
  left_inv x := by rw [res_res, res_refl]
  right_inv x := by rw [res_res, res_refl]
  map_add' := map_add _

variable (A n) in

abbrev cover : Fin (n + 1) → Opens (projectiveSpace A n).toTopCat := stdOpen A n

def theta {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) :
    LDeg A (Set.range i) k ≃+ (twistAb A n k).obj (op (inter (cover A n) i)) :=
  ((awayDegEquiv i k).symm.trans (sectionEquiv i k)).trans
    (resEquiv (twistAb A n k) (inter_stdOpen i))

lemma nmem_of_mem_inter {p : ℕ} {i : Fin (p + 1) → Fin (n + 1)}
    (x : inter (cover A n) i) : xprod (A := A) i ∉ x.1.asHomogeneousIdeal := by
  have hx : x.1 ∈ Proj.basicOpen (grading A n) (xprod i) := by
    rw [← inter_stdOpen]
    exact x.2
  exact hx

lemma val_theta {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) (k : ℤ) (ℓ : LDeg A (Set.range i) k)
    (x : inter (cover A n) i) :
    ProjTwist.val (theta i k ℓ) x =
      ProjTwist.locMap x.1 (nmem_of_mem_inter x) ((awayDegEquiv i k).symm ℓ).1 := rfl

lemma res_theta {p q : ℕ} {i : Fin (p + 1) → Fin (n + 1)} {i' : Fin (q + 1) → Fin (n + 1)}
    (h : Set.range i ⊆ Set.range i') (hle : inter (cover A n) i' ≤ inter (cover A n) i) (k : ℤ)
    (ℓ : LDeg A (Set.range i) k) :
    res (twistAb A n k) hle (theta i k ℓ) = theta i' k ⟨ℓ.1, LDeg_mono h k ℓ.2⟩ := by
  apply ProjTwist.ext
  funext x
  change ProjTwist.val (theta i k ℓ) ⟨x.1, hle x.2⟩ = _
  rw [val_theta, val_theta]
  apply locMap_eq_of_awayToLaurent_eq h
  rw [← awayDegEquiv_apply, ← awayDegEquiv_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

def lval {k : ℤ} {p : ℕ} (σ : Cochain (twistAb A n k) (cover A n) p) (i : Fin (p + 1) → Fin (n + 1)) :
    Laurent A n :=
  ((theta i k).symm (σ i)).1

lemma lval_mem {k : ℤ} {p : ℕ} (σ : Cochain (twistAb A n k) (cover A n) p)
    (i : Fin (p + 1) → Fin (n + 1)) : lval σ i ∈ LDeg A (Set.range i) k :=
  ((theta i k).symm (σ i)).2

lemma theta_lval {k : ℤ} {p : ℕ} (σ : Cochain (twistAb A n k) (cover A n) p)
    (i : Fin (p + 1) → Fin (n + 1)) : theta i k ⟨lval σ i, lval_mem σ i⟩ = σ i :=
  (theta i k).apply_symm_apply _

lemma cochain_ext {k : ℤ} {p : ℕ} {σ τ : Cochain (twistAb A n k) (cover A n) p}
    (h : ∀ i, lval σ i = lval τ i) : σ = τ := by
  funext i
  rw [← theta_lval σ i, ← theta_lval τ i]
  congr 1
  exact Subtype.ext (h i)

@[simp] lemma lval_add {k : ℤ} {p : ℕ} (σ τ : Cochain (twistAb A n k) (cover A n) p) (i) :
    lval (σ + τ) i = lval σ i + lval τ i := by
  simp [lval]

@[simp] lemma lval_zero {k : ℤ} {p : ℕ} (i) :
    lval (0 : Cochain (twistAb A n k) (cover A n) p) i = 0 := by
  simp [lval]

@[simp] lemma lval_sub {k : ℤ} {p : ℕ} (σ τ : Cochain (twistAb A n k) (cover A n) p) (i) :
    lval (σ - τ) i = lval σ i - lval τ i := by
  simp [lval]

def ofL {k : ℤ} {p : ℕ} (f : ∀ i : Fin (p + 1) → Fin (n + 1), LDeg A (Set.range i) k) :
    Cochain (twistAb A n k) (cover A n) p :=
  fun i => theta i k (f i)

@[simp] lemma lval_ofL {k : ℤ} {p : ℕ} (f : ∀ i : Fin (p + 1) → Fin (n + 1), LDeg A (Set.range i) k)
    (i) : lval (ofL f) i = (f i).1 := by
  simp [lval, ofL]

lemma range_comp_subset {α β γ : Type*} (f : α → β) (g : β → γ) :
    Set.range (g ∘ f) ⊆ Set.range g := by
  rintro _ ⟨a, rfl⟩
  exact ⟨f a, rfl⟩

lemma lval_d {k : ℤ} {p : ℕ} (σ : Cochain (twistAb A n k) (cover A n) p)
    (i : Fin (p + 2) → Fin (n + 1)) :
    lval (d _ _ p σ) i = ∑ a : Fin (p + 2), ((-1 : ℤ) ^ (a : ℕ)) • lval σ (i ∘ a.succAbove) := by
  have key : d _ _ p σ i = theta i k (∑ a : Fin (p + 2), ((-1 : ℤ) ^ (a : ℕ)) •
      ⟨lval σ (i ∘ a.succAbove), LDeg_mono (range_comp_subset _ _) k (lval_mem σ _)⟩) := by
    rw [d_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_zsmul]
    congr 1
    conv_lhs => rw [← theta_lval σ (i ∘ a.succAbove)]
    exact res_theta (range_comp_subset _ _) _ k _
  rw [lval, key, AddEquiv.symm_apply_apply, AddSubgroup.val_finsetSum]
  simp

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorPicard
section
namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

noncomputable def weilDivisorToPic : WeilDivisor X →+ Additive (Pic X) where
  toFun D := Additive.ofMul (Pic.mk (divisorSheaf D) (isInvertibleSheaf_divisorSheaf D))
  map_zero' := by
    rw [ofMul_eq_zero, ← Pic.mk_unit, Pic.mk_eq_mk_iff]
    exact ⟨divisorSheafZeroIso.symm⟩
  map_add' D E := by
    rw [← ofMul_mul, ← Pic.mk_tensor]
    congr 1
    exact (Pic.mk_eq_mk_iff _ _).mpr ⟨(divisorTensorIso D E).symm⟩

lemma weilDivisorToPic_apply (D : WeilDivisor X) :
    weilDivisorToPic D =
      Additive.ofMul (Pic.mk (divisorSheaf D) (isInvertibleSheaf_divisorSheaf D)) := rfl

theorem ker_weilDivisorToPic : (weilDivisorToPic (X := X)).ker = principalDivisors X := by
  ext D
  rw [AddMonoidHom.mem_ker, weilDivisorToPic_apply, ofMul_eq_zero, Pic.mk_eq_one_iff,
    ← sub_zero D, ← nonempty_divisorSheaf_iso_iff, sub_zero]
  constructor
  · rintro ⟨e⟩
    exact ⟨e ≪≫ divisorSheafZeroIso⟩
  · rintro ⟨e⟩
    exact ⟨e ≪≫ divisorSheafZeroIso.symm⟩

theorem weilDivisorToPic_surjective : Function.Surjective (weilDivisorToPic (X := X)) := by
  intro p
  obtain ⟨L, hL, hp⟩ := Pic.exists_mk (Additive.toMul p)
  obtain ⟨D, ⟨e⟩⟩ := exists_iso_divisorSheaf hL
  refine ⟨D, ?_⟩
  rw [weilDivisorToPic_apply, ← ofMul_toMul p, ← hp]
  congr 1
  exact (Pic.mk_eq_mk_iff _ hL).mpr ⟨e.symm⟩

noncomputable def classGroupEquivPic : ClassGroup X ≃+ Additive (Pic X) :=
  (QuotientAddGroup.quotientAddEquivOfEq ker_weilDivisorToPic.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ weilDivisorToPic_surjective)

end GroundTheory.Arith.SchemeCoh
end

