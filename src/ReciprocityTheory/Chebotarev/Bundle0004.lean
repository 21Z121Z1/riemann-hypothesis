import Mathlib
import ReciprocityTheory.Chebotarev.Bundle0001
import ReciprocityTheory.Chebotarev.Bundle0002

-- bundled from ReciprocityTheory.Chebotarev.ExistsUnitOrderOfEq
section
open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem exists_unit_orderOf_eq (l : ℕ) [Fact l.Prime] : ∃ τ : (ZMod l)ˣ, orderOf τ = l - 1 := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  refine ⟨τ, ?_⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hτ, Nat.card_eq_fintype_card, ZMod.card_units]

theorem cross : CycStatement → Statement := by
  intro hB K _ _ _ σ T
  obtain ⟨N, hN⟩ := exists_forall_isUnramifiedAt_of_liesOver K
  obtain ⟨N', hN'⟩ := exists_forall_cyclotomic_irreducible K
  have hk : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  obtain ⟨l, hlp, hlgt, hlmod⟩ := Nat.exists_prime_gt_modEq_one (max N' (T.sup id)) hk
  have : Fact l.Prime := ⟨hlp⟩
  have hσ : orderOf σ ∣ l - 1 := (Nat.modEq_iff_dvd' hlp.one_lt.le).mp hlmod.symm
  have hirr : Irreducible (cyclotomic l K) := hN' l hlp (lt_of_le_of_lt (le_max_left _ _) hlgt)
  have : NeZero l := ⟨hlp.ne_zero⟩
  have := isGalois_cyclotomicField K l
  let M := CyclotomicField l K
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta l K M) l := IsCyclotomicExtension.zeta_spec l K M
  obtain ⟨τ, hτ⟩ := exists_unit_orderOf_eq l
  obtain ⟨g, hg, hgζ⟩ := exists_lift_pow (M := M) l hirr hζ σ τ
  let E := IntermediateField.fixedField (Subgroup.zpowers g)
  have hirrE : Irreducible (cyclotomic l E) := irreducible_cyclotomic_fixedField hζ σ hσ τ hτ g hg hgζ
  obtain ⟨q, hq, hqp, hqT, hqmod⟩ := hB E l hirrE τ (T ∪ Finset.range (N + 1) ∪ {l})
  have hql : Ideal.absNorm q ≠ l := fun h => hqT (by simp [h])
  obtain ⟨P, hP, φ, hPp, hφζ, hφ⟩ := exists_frob_above E l hζ q hq hqp hql
  have hφg : φ.restrictScalars ℚ = g := eq_of_apply_eq_pow hζ σ hσ τ hτ g hg hgζ φ _ hφζ hqmod
  rw [hφg] at hφ
  obtain ⟨hQ, hQp, hQf⟩ := isArithFrobAt_restrictNormal (K := K) g _ P hP hPp hφ
  rw [hg] at hQf
  refine ⟨Ideal.absNorm q, hqp, fun h => hqT (by simp [h]), P.under (𝓞 K), hQ, hQp, ?_, hQf⟩
  have := hQ
  have := hQp
  refine hN _ hqp ?_ _
  by_contra h
  exact hqT (by simp; omega)

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.Ucoord
section
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem

namespace ReciprocityTheory.Cheb

noncomputable section

open scoped Classical

variable {E : Type} [Field E] [NumberField E]

def ucoord (x : mixedSpace E) : Fin (rank E) → ℝ :=
  fun i => ((basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E)).repr (logMap x) i

def uphi (x : mixedSpace E) : ℝ :=
  if mixedEmbedding.norm x = 0 then 0 else Tent (ucoord x)

def rsgn (x : mixedSpace E) : ℤ :=
  ∏ w : {w : InfinitePlace E // w.IsReal}, ((SignType.sign (x.1 w) : SignType) : ℤ)

def Gs {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) : ℂ :=
  χ (rsgn x : ZMod l) * (uphi x : ℂ) * ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (-(s : ℂ))

def embZ : 𝓞 E →ₗ[ℤ] mixedSpace E :=
  ((mixedEmbedding E).comp (algebraMap (𝓞 E) E)).toIntAlgHom.toLinearMap

def latOf (I : Ideal (𝓞 E)) : Submodule ℤ (mixedSpace E) :=
  Submodule.map (embZ (E := E)) (I.restrictScalars ℤ)

def mbc (l : ℕ) (b c : Ideal (𝓞 E)) : Ideal (𝓞 E) :=
  Ideal.span {((l * Ideal.absNorm b : ℕ) : 𝓞 E)} * b * c

def cls (a : NZIdeal E) : ClassGroup (𝓞 E) :=
  ClassGroup.mk0 ⟨a.1, mem_nonZeroDivisors_of_ne_zero a.2⟩

def preZ (x : mixedSpace E) : 𝓞 E := Function.invFun (embZ (E := E)) x

def cfun {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : Ideal (𝓞 E)) (x : mixedSpace E) : ℂ :=
  χ (((Algebra.norm ℤ (preZ x) / (Ideal.absNorm b : ℤ) : ℤ)) : ZMod l) *
    (1 - (Ideal.absNorm c : ℂ) * (if preZ x ∈ b * c then 1 else 0))

end

end ReciprocityTheory.Cheb
end

