import Mathlib
import GroundTheory.ProfiniteCohomology.Procyclic
import GroundTheory.ProfiniteCohomology.Characters
import GroundTheory.ProfiniteCohomology.Bundle0004
import GroundTheory.ProfiniteCohomology.CupProducts
import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
import GroundTheory.ProfiniteCohomology.GaloisModules.Discrete

-- bundled from GroundTheory.ProfiniteCohomology.CohomologyTwoIntAddEquivQZSymmApply
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

theorem isAddTorsion_QZ : IsAddTorsion QZ := by
  intro x
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨q.den, q.den_pos, ?_⟩
  change ((q.den • q : ℚ) : AddCircle (1 : ℚ)) = 0
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨q.num, ?_⟩
  rw [nsmul_eq_mul, mul_comm, Rat.mul_den_eq_num, zsmul_one]

section Eval

variable {G : Type*} [Group G] [TopologicalSpace G]

def evalCharacter (σ : G) : (Additive G →ₜ+ QZ) →+ QZ where
  toFun χ := χ (Additive.ofMul σ)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem evalCharacter_apply (σ : G) (χ : Additive G →ₜ+ QZ) :
    evalCharacter σ χ = χ (Additive.ofMul σ) :=
  rfl

theorem evalCharacter_injective {σ : G} (hσ : IsTopologicalGenerator σ) :
    Function.Injective (evalCharacter σ) := by
  rw [injective_iff_map_eq_zero]
  intro χ hχ
  have hlc : IsLocallyConstant fun g : G => χ (Additive.ofMul g) :=
    (IsLocallyConstant.iff_continuous _).2 (χ.continuous.comp continuous_ofMul)
  have h := hσ.eq_of_forall_zpow hlc (IsLocallyConstant.const (0 : QZ)) fun n => by
    change χ (Additive.ofMul (σ ^ n)) = 0
    rw [ofMul_zpow, map_zsmul]
    change n • evalCharacter σ χ = 0
    rw [hχ, smul_zero]
  ext x
  exact congrFun h (Additive.toMul x)

theorem evalCharacter_surjective [IsTopologicalGroup G] {σ : G} (hσ : IsZHatGenerator σ) :
    Function.Surjective (evalCharacter σ) := by
  intro x
  have hn : 0 < addOrderOf x := (isAddTorsion_QZ x).addOrderOf_pos
  obtain ⟨φ, hφo, hφσ⟩ := hσ.exists_hom _ hn
  let ψ : ZMod (addOrderOf x) →+ QZ := ZMod.lift (addOrderOf x)
    ⟨zmultiplesHom QZ x, by simp [addOrderOf_nsmul_eq_zero]⟩
  let χ₀ : Additive G →+ QZ := ψ.comp (MonoidHom.toAdditive φ)
  have hlc : IsLocallyConstant fun a : Additive G => χ₀ a :=
    ((φ.isLocallyConstant_of_isOpen_ker hφo).comp fun z => ψ (Multiplicative.toAdd z)).comp_continuous
      continuous_toMul
  refine ⟨⟨χ₀, hlc.continuous⟩, ?_⟩
  change ψ (Multiplicative.toAdd (φ σ)) = x
  rw [hφσ, toAdd_ofAdd, ← Int.cast_one, ZMod.lift_coe]
  simp

noncomputable def evalCharacterEquiv [IsTopologicalGroup G] {σ : G} (hσ : IsZHatGenerator σ) :
    (Additive G →ₜ+ QZ) ≃+ QZ :=
  AddEquiv.ofBijective (evalCharacter σ) ⟨evalCharacter_injective hσ.dense, evalCharacter_surjective hσ⟩

@[simp]
theorem evalCharacterEquiv_apply [IsTopologicalGroup G] {σ : G} (hσ : IsZHatGenerator σ)
    (χ : Additive G →ₜ+ QZ) : evalCharacterEquiv hσ χ = χ (Additive.ofMul σ) :=
  rfl

end Eval

section H2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {σ : G}

noncomputable def cohomologyTwoIntIsoQZ (hσ : IsZHatGenerator σ) :
    cohomology (Rep.trivial ℤ G ℤ) 2 ≅ ModuleCat.of ℤ QZ :=
  cohomologyTwoIntIso G ≪≫ (evalCharacterEquiv hσ).toIntLinearEquiv.toModuleIso

noncomputable def cohomologyTwoIntAddEquivQZ (hσ : IsZHatGenerator σ) :
    cohomology (Rep.trivial ℤ G ℤ) 2 ≃+ QZ :=
  (cohomologyTwoIntAddEquiv G).trans (evalCharacterEquiv hσ)

theorem cohomologyTwoIntAddEquivQZ_δ (hσ : IsZHatGenerator σ) (χ : Additive G →ₜ+ QZ) :
    cohomologyTwoIntAddEquivQZ hσ
      ((δ (GroundTheory.GroupCoh.ratSES_shortExact G) 1 2 rfl).hom
        ((cohomologyOneRatModIntIso G).inv.hom χ)) = χ (Additive.ofMul σ) := by
  rw [← cohomologyTwoIntAddEquiv_symm_apply, cohomologyTwoIntAddEquivQZ, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, evalCharacterEquiv_apply]

end H2

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.CyclicCupGaloisDefs
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

section Generic

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}

noncomputable def cupRightProf (h : p + q = n) (b : cohomology B q) :
    cohomology A p ⟶ cohomology (A ⊗ B) n :=
  ModuleCat.ofHom ((cup h).flip b)

theorem cupRightProf_apply (h : p + q = n) (b : cohomology B q) (a : cohomology A p) :
    (cupRightProf h b).hom a = cup h a b :=
  rfl

end Generic

section Profinite

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

noncomputable def charClassProf (χ : Additive G →ₜ+ QZ) : cohomology (Rep.trivial ℤ G ℤ) 2 :=
  (δ (GroundTheory.GroupCoh.ratSES_shortExact G) 1 2 rfl).hom ((cohomologyOneRatModIntIso G).inv.hom χ)

noncomputable def cupCharClassProf (A : Rep ℤ G) [IsDiscreteRep A] (χ : Additive G →ₜ+ QZ) :=
  (H0Iso A).inv ≫ cupRightProf (A := A) (B := Rep.trivial ℤ G ℤ) (zero_add 2) (charClassProf χ) ≫
    cohomologyMap (A := A ⊗ Rep.trivial ℤ G ℤ) (B := A) (ρ_ A).hom 2

end Profinite

section Galois

variable (K L : Type) [Field K] [Field L] [Algebra K L]

def unitsInvariant (a : Kˣ) : (galUnitsZ K L).ρ.invariants :=
  ⟨Additive.ofMul (Units.map (algebraMap K L : K →* L) a), fun σ => by
    apply Additive.toMul.injective
    apply Units.ext
    change ((galUnitsHom K L σ (Units.map (algebraMap K L : K →* L) a) : Lˣ) : L) =
      (Units.map (algebraMap K L : K →* L) a : L)
    rw [coe_galUnitsHom_apply]
    simp⟩

@[simp]
theorem coe_unitsInvariant (a : Kˣ) :
    ((Additive.toMul (unitsInvariant K L a : Additive Lˣ) : Lˣ) : L) = algebraMap K L a :=
  rfl

variable [IsGalois K L]

noncomputable def galCupClass (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ) :
    cohomology (galUnitsZ K L) 2 :=
  (cupCharClassProf (galUnitsZ K L) χ).hom (unitsInvariant K L a)

end Galois

end GroundTheory.ProfCoh
end

