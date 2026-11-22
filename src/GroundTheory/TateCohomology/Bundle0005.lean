import Mathlib
import GroundTheory.TateCohomology.TateLow
import GroundTheory.TateCohomology.Bundle0001
import GroundTheory.TateCohomology.Bundle0003

-- bundled from GroundTheory.TateCohomology.TateZeroClass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

noncomputable def tateZeroClass (M : Rep.{u} k G) : M.ρ.invariants →ₗ[k] tateCohomology M 0 :=
  ((tateCohomologyZeroIso k G).app M).inv.hom ∘ₗ (normRangeInvariants M).mkQ

lemma tateZeroClass_eq_homologyπ (M : Rep.{u} k G) (z : (tateComplex M).cycles 0)
    (x : M.ρ.invariants) (hx : (cochainsIso₀ M).inv.hom x = ((tateComplex M).iCycles 0).hom z) :
    tateZeroClass M x = ((tateComplex M).homologyπ 0).hom z :=
  tateCohomologyZeroIso_inv_mk M z x hx

lemma tateZeroClass_surjective (M : Rep.{u} k G) : Function.Surjective (tateZeroClass M) := by
  intro y
  obtain ⟨q, hq⟩ := ((ModuleCat.epi_iff_surjective ((tateCohomologyZeroIso k G).app M).inv).1
    inferInstance) y
  obtain ⟨x, rfl⟩ := (normRangeInvariants M).mkQ_surjective q
  exact ⟨x, hq⟩

lemma homologyMap_tateZeroClass {H : Type u} [Group H] [Fintype H] {M : Rep.{u} k G}
    {N : Rep.{u} k H} (f : tateComplex M ⟶ tateComplex N) (x : M.ρ.invariants)
    (y : N.ρ.invariants)
    (h : (f.f 0).hom ((cochainsIso₀ M).inv.hom x) = (cochainsIso₀ N).inv.hom y) :
    (HomologicalComplex.homologyMap f 0).hom (tateZeroClass M x) = tateZeroClass N y := by
  obtain ⟨z, hz⟩ := exists_tateComplex_cycles_zero M x
  rw [tateZeroClass_eq_homologyπ M z x hz.symm]
  have e1 := congr(($(HomologicalComplex.homologyπ_naturality f 0)).hom z)
  have e2 := congr(($(HomologicalComplex.cyclesMap_i f 0)).hom z)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  rw [e1]
  refine (tateZeroClass_eq_homologyπ N _ y ?_).symm
  rw [e2, hz, h]

lemma tateCohomologyFunctor_map_tateZeroClass {M N : Rep.{u} k G} (φ : M ⟶ N)
    (x : M.ρ.invariants) :
    ((tateCohomologyFunctor 0).map φ).hom (tateZeroClass M x) =
      tateZeroClass N (((Rep.invariantsFunctor k G).map φ).hom x) :=
  homologyMap_tateZeroClass (tateComplex.map φ) x _ (funext fun _ => rfl)

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.UniquelyDivisible
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section UniquelyDivisible

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem tateAcyclic_of_bijective_nsmul (M : Rep.{u} k G)
    (h : Function.Bijective fun m : M => Fintype.card G • m) : TateAcyclic M := by
  let f : M.V →ₗ[k] M.V := Fintype.card G • LinearMap.id
  have hf : ∀ m : M, f m = Fintype.card G • m := fun m => rfl
  have hb : Function.Bijective f := by
    have : (f : M → M) = fun m : M => Fintype.card G • m := funext hf
    rw [this]; exact h
  let e := LinearEquiv.ofBijective f hb
  have he : ∀ m : M, Fintype.card G • e.symm m = m := fun m => by
    rw [← hf]; exact e.apply_symm_apply m
  have hc : ∀ (g : G) (x : M), M.ρ g (e.symm x) = e.symm (M.ρ g x) := by
    intro g x
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    change f (M.ρ g (e.symm x)) = M.ρ g x
    rw [hf, ← map_nsmul, he]
  refine tateAcyclic_of_sum_eq M e.symm.toLinearMap fun m => ?_
  have hg : ∀ g : G, M.ρ g (e.symm.toLinearMap (M.ρ g⁻¹ m)) = e.symm m := fun g => by
    rw [LinearEquiv.coe_coe, hc, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  rw [Finset.sum_congr rfl fun g _ => hg g, Finset.sum_const, Finset.card_univ, he]

theorem isZero_groupCohomology_of_bijective_nsmul (M : Rep.{u} k G)
    (h : Function.Bijective fun m : M => Fintype.card G • m) (n : ℕ) [NeZero n] :
    IsZero (groupCohomology M n) :=
  (tateAcyclic_of_bijective_nsmul M h n).of_iso
    ((TateCohomology.isoGroupCohomology (R := k) (G := G) n).app M).symm

end UniquelyDivisible

section Rat

variable {G : Type} [Group G] [Fintype G]

theorem bijective_nsmul_of_module_rat {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (hn : n ≠ 0) : Function.Bijective fun v : V => n • v := by
  have : (fun v : V => n • v) = LinearEquiv.smulOfUnit (M := V)
      (IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ))) := by
    funext v
    change _ = IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ)) • v
    rw [Units.smul_def, IsUnit.unit_spec, Nat.cast_smul_eq_nsmul]
  rw [this]
  exact LinearEquiv.bijective _

theorem isZero_groupCohomology_trivial_rat (n : ℕ) [NeZero n] :
    IsZero (groupCohomology (Rep.trivial ℤ G ℚ) n) :=
  isZero_groupCohomology_of_bijective_nsmul _
    (bijective_nsmul_of_module_rat (V := ℚ) Fintype.card_ne_zero) n

end Rat

end GroundTheory.GroupCoh
end

