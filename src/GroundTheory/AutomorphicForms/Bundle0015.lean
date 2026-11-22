import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.Projection
import GroundTheory.AutomorphicForms.HarishChandraCentre.Bundle0002
import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
import GroundTheory.AutomorphicForms.HarishChandraCentre.LeadingTerm
import GroundTheory.AutomorphicForms.HarishChandraCentre.Bundle0001
import GroundTheory.AutomorphicForms.HarishChandraCentre.Capelli
import GroundTheory.AutomorphicForms.Bundle0013
import GroundTheory.AutomorphicForms.MeasuresParabolic
import GroundTheory.AutomorphicForms.WhittakerDistribution
import GroundTheory.AutomorphicForms.WhittakerCriterion
import GroundTheory.AutomorphicForms.MeasuresGL

-- bundled from GroundTheory.AutomorphicForms.HarishChandraCentre
section
namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

theorem harishChandraHom_mem_symmetricSubalgebra (z : Subalgebra.center ℂ (U n)) :
    harishChandraHom z ∈ symmetricSubalgebra (Fin n) ℂ :=
  harishChandraHom_isSymmetric z

noncomputable def capelliCenter (k : ℕ) : Subalgebra.center ℂ (U n) :=
  ⟨capelli (k + 1), capelli_mem_center _⟩

theorem adjoin_harishChandraHom_capelli :
    Algebra.adjoin ℂ (Set.range fun k : Fin n => harishChandraHom (capelliCenter (n := n) k)) =
      symmetricSubalgebra (Fin n) ℂ :=
  adjoin_eq_symmetricSubalgebra _ (fun _ => harishChandraHom_isSymmetric _)
    (fun k => totalDegree_harishChandraHom_capelli_sub k)

theorem range_harishChandraHom :
    (harishChandraHom (n := n)).range = symmetricSubalgebra (Fin n) ℂ := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact harishChandraHom_isSymmetric z
  · rw [← adjoin_harishChandraHom_capelli, Algebra.adjoin_le_iff]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩

noncomputable def harishChandraEquiv :
    Subalgebra.center ℂ (U n) ≃ₐ[ℂ] symmetricSubalgebra (Fin n) ℂ :=
  (AlgEquiv.ofInjective harishChandraHom harishChandraHom_injective).trans
    (Subalgebra.equivOfEq _ _ range_harishChandraHom)

@[simp] theorem harishChandraEquiv_apply (z : Subalgebra.center ℂ (U n)) :
    (harishChandraEquiv z : MvPolynomial (Fin n) ℂ) = harishChandraHom z := rfl

end GroundTheory.Automorphic.HarishChandra
end

-- bundled from GroundTheory.AutomorphicForms.InductionParabolicLocal
section
noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem uniformizer_ne_zero : (GLnLocal.uniformizer F : F) ≠ 0 :=
  coe_uniformizerUnit F ▸ (uniformizerUnit F).ne_zero

theorem zpow_mul_mem {x : F} {k : ℕ} (hx : (GLnLocal.uniformizer F : F) ^ k * x ∈ 𝒪[F]) {z : ℤ}
    (hz : (k : ℤ) ≤ z) : (GLnLocal.uniformizer F : F) ^ z * x ∈ 𝒪[F] := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, z = ((d + k : ℕ) : ℤ) := ⟨(z - k).toNat, by omega⟩
  rw [hd, zpow_natCast, pow_add, mul_assoc]
  exact mul_mem (pow_mem (GLnLocal.uniformizer F).2 d) hx

theorem valuation_zpow_mul_le {x : F} {k t : ℕ} (hx : (GLnLocal.uniformizer F : F) ^ k * x ∈ 𝒪[F])
    {z : ℤ} (hz : ((k + t : ℕ) : ℤ) ≤ z) :
    valuation F ((GLnLocal.uniformizer F : F) ^ z * x) ≤ valuation F (GLnLocal.uniformizer F : F) ^ t := by
  obtain ⟨d, hd⟩ : ∃ d : ℤ, z = t + d ∧ (k : ℤ) ≤ d := ⟨z - t, by omega, by omega⟩
  rw [hd.1, zpow_add₀ uniformizer_ne_zero, mul_assoc, map_mul, zpow_natCast, map_pow]
  exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (zpow_mul_mem hx hd.2))

variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)

def rankTorus (e : ℕ) : GL (Fin n) F :=
  torusPow F n fun i => -((e * blockRank β i : ℕ) : ℤ)

variable {F n β}

theorem rankTorus_mem_levi (e : ℕ) : rankTorus F n β e ∈ levi F n β :=
  diagGL_mem_levi _

theorem rankTorus_mem_blockUpper (e : ℕ) : rankTorus F n β e ∈ blockUpper F n β :=
  levi_le_blockUpper (rankTorus_mem_levi e)

theorem rankTorus_pow (e m : ℕ) : rankTorus F n β e ^ m = rankTorus F n β (e * m) := by
  rw [rankTorus, rankTorus, torusPow, torusPow, ← map_pow]
  congr 1
  funext i
  rw [Pi.pow_apply, ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast
  ring

theorem rankTorus_conj_apply (e : ℕ) (g : GL (Fin n) F) (i j : Fin n) :
    (rankTorus F n β e * g * (rankTorus F n β e)⁻¹ : GL (Fin n) F) i j =
      (GLnLocal.uniformizer F : F) ^ (((e * blockRank β j : ℕ) : ℤ) - ((e * blockRank β i : ℕ) : ℤ)) *
        g i j := by
  rw [rankTorus, torusPow, diagGL_conj_apply]
  simp only [Units.val_zpow_eq_zpow_val, coe_uniformizerUnit, Units.val_inv_eq_inv_val]
  rw [zpow_sub₀ uniformizer_ne_zero, _root_.zpow_neg, _root_.zpow_neg, inv_inv]
  ring

theorem rankTorus_inv_conj_apply (e : ℕ) (g : GL (Fin n) F) (i j : Fin n) :
    ((rankTorus F n β e)⁻¹ * g * rankTorus F n β e : GL (Fin n) F) i j =
      (GLnLocal.uniformizer F : F) ^ (((e * blockRank β i : ℕ) : ℤ) - ((e * blockRank β j : ℕ) : ℤ)) *
        g i j := by
  rw [rankTorus, torusPow, diagGL_inv_conj_apply]
  simp only [Units.val_zpow_eq_zpow_val, coe_uniformizerUnit, Units.val_inv_eq_inv_val]
  rw [zpow_sub₀ uniformizer_ne_zero, _root_.zpow_neg, _root_.zpow_neg, inv_inv]
  ring

theorem isClosed_unipotentRadical :
    IsClosed (unipotentRadical F n β : Set (GL (Fin n) F)) := by
  have : (unipotentRadical F n β : Set (GL (Fin n) F)) =
      (⋂ i, ⋂ j, ⋂ (_ : β j < β i), (fun g : GL (Fin n) F => g i j) ⁻¹' {0}) ∩
      ⋂ i, ⋂ j, ⋂ (_ : β i = β j),
        (fun g : GL (Fin n) F => g i j) ⁻¹' {(1 : Matrix (Fin n) (Fin n) F) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipotentRadical, mem_blockUpper, Set.mem_inter_iff,
      Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 hij, h2⟩,
      fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 i j hij, h2⟩⟩
  rw [this]
  refine IsClosed.inter ?_ ?_ <;>
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_singleton.preimage (continuous_entry F n i j)

theorem rankTorus_conj_apply_mem {e : ℕ} {u : GL (Fin n) F} (hu : u ∈ unipotentRadical F n β)
    (hb : ∀ i j, (GLnLocal.uniformizer F : F) ^ e * u i j ∈ 𝒪[F]) (i j : Fin n) :
    (rankTorus F n β e * u * (rankTorus F n β e)⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F] := by
  obtain ⟨hP, h1⟩ := mem_unipotentRadical.1 hu
  rw [rankTorus_conj_apply]
  rcases lt_trichotomy (β i) (β j) with h | h | h
  · refine zpow_mul_mem (hb i j) ?_
    have := blockRank_lt h
    have : e * blockRank β i + e ≤ e * blockRank β j := by nlinarith
    push_cast
    omega
  · rw [h1 i j h, blockRank_eq h, sub_self, zpow_zero, one_mul]
    by_cases hij : i = j
    · rw [hij, one_apply_eq]
      exact one_mem _
    · rw [one_apply_ne hij]
      exact zero_mem _
  · rw [hP h, mul_zero]
    exact zero_mem _

variable (F n β) in

def unipotentCompact (e : ℕ) : Subgroup (unipotentRadical F n β) :=
  ((integralGL F n).comap (MulAut.conj (rankTorus F n β e)).toMonoidHom).subgroupOf
    (unipotentRadical F n β)

theorem mem_unipotentCompact {e : ℕ} {u : unipotentRadical F n β} :
    u ∈ unipotentCompact F n β e ↔
      rankTorus F n β e * u * (rankTorus F n β e)⁻¹ ∈ integralGL F n := by
  rw [unipotentCompact, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  rfl

def conjHomeomorph (t : GL (Fin n) F) : GL (Fin n) F ≃ₜ GL (Fin n) F :=
  (Homeomorph.mulLeft t).trans (Homeomorph.mulRight t⁻¹)

theorem coe_unipotentCompact (e : ℕ) :
    (unipotentCompact F n β e : Set (unipotentRadical F n β)) =
      Subtype.val ⁻¹' (conjHomeomorph (rankTorus F n β e) ⁻¹' (integralGL F n : Set _)) := by
  ext u
  simp only [SetLike.mem_coe, mem_unipotentCompact, Set.mem_preimage]
  rfl

theorem isOpen_unipotentCompact (e : ℕ) :
    IsOpen (unipotentCompact F n β e : Set (unipotentRadical F n β)) := by
  rw [coe_unipotentCompact]
  exact ((isOpen_integralGL F n).preimage (conjHomeomorph _).continuous).preimage
    continuous_subtype_val

theorem isCompact_unipotentCompact (e : ℕ) :
    IsCompact (unipotentCompact F n β e : Set (unipotentRadical F n β)) := by
  rw [coe_unipotentCompact]
  exact isClosed_unipotentRadical.isClosedEmbedding_subtypeVal.isCompact_preimage
    ((conjHomeomorph _).isCompact_preimage.2 (isCompact_integralGL F n))

theorem mem_unipotentCompact_of_bound {e : ℕ} {u : unipotentRadical F n β}
    (hb : ∀ i j, (GLnLocal.uniformizer F : F) ^ e * (u : GL (Fin n) F) i j ∈ 𝒪[F])
    (hb' : ∀ i j, (GLnLocal.uniformizer F : F) ^ e * ((u : GL (Fin n) F)⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F]) :
    u ∈ unipotentCompact F n β e := by
  rw [mem_unipotentCompact, mem_integralGL_iff]
  refine ⟨rankTorus_conj_apply_mem u.2 hb, fun i j => ?_⟩
  have : (rankTorus F n β e * u * (rankTorus F n β e)⁻¹)⁻¹ =
      rankTorus F n β e * (u : GL (Fin n) F)⁻¹ * (rankTorus F n β e)⁻¹ := by group
  rw [this]
  exact rankTorus_conj_apply_mem ((unipotentRadical F n β).inv_mem u.2) hb' i j

theorem exists_compactOpen_unipotentRadical (s : Finset (unipotentRadical F n β)) :
    ∃ K : Subgroup (unipotentRadical F n β), IsCompact (K : Set (unipotentRadical F n β)) ∧
      IsOpen (K : Set (unipotentRadical F n β)) ∧ ∀ x ∈ s, x ∈ K := by
  classical
  let C : Set (GL (Fin n) F) :=
    (fun x : unipotentRadical F n β => (x : GL (Fin n) F)) '' (s : Set _) ∪
      (fun x : unipotentRadical F n β => (x : GL (Fin n) F)⁻¹) '' (s : Set _)
  have hC : IsCompact C :=
    ((s.finite_toSet.image _).union (s.finite_toSet.image _)).isCompact
  obtain ⟨e, he⟩ := exists_pow_mul_mem_of_isCompact F n hC
  refine ⟨unipotentCompact F n β e, isCompact_unipotentCompact e, isOpen_unipotentCompact e,
    fun x hx => mem_unipotentCompact_of_bound (he _ ?_) (he _ ?_)⟩
  · exact Or.inl ⟨x, hx, rfl⟩
  · exact Or.inr ⟨x, hx, rfl⟩

open MeasureTheory Measure in

theorem modularCharacter_eq_one_of_mem (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ unipotentRadical F n β) : modularCharacter p = 1 := by
  classical
  let u : unipotentRadical F n β := ⟨p, hp⟩
  obtain ⟨e, he⟩ := exists_pow_mul_mem_of_isCompact F n
    (Set.toFinite ({(p : GL (Fin n) F), (p : GL (Fin n) F)⁻¹} : Set _)).isCompact
  have hmem := mem_integralGL_iff F n |>.1 <| (mem_unipotentCompact (u := u)).1
    (mem_unipotentCompact_of_bound (fun i j => he _ (by simp [u]) i j)
      (fun i j => he _ (by simp [u]) i j))
  let t : blockUpper F n β := ⟨rankTorus F n β e, rankTorus_mem_blockUpper e⟩
  have h1 : modularCharacter (t * p * t⁻¹) = 1 :=
    Measures.modularCharacter_eq_one_of_mem_integralGL (t * p * t⁻¹)
      ((mem_integralGL_iff F n).2 hmem)
  rw [map_mul, map_mul, mul_comm (modularCharacter t), mul_assoc, ← map_mul, mul_inv_cancel,
    map_one, mul_one] at h1
  exact h1

theorem rankTorus_inv_conj_apply_facts {k t m : ℕ} (hm : k + t ≤ m) {z : GL (Fin n) F}
    (hz : z ∈ oppositeUnipotentRadical F n β)
    (hb : ∀ i j, (GLnLocal.uniformizer F : F) ^ k * z i j ∈ 𝒪[F]) (i j : Fin n) :
    ((rankTorus F n β m)⁻¹ * z * rankTorus F n β m : GL (Fin n) F) i j ∈ 𝒪[F] ∧
      valuation F (((rankTorus F n β m)⁻¹ * z * rankTorus F n β m : GL (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F (GLnLocal.uniformizer F : F) ^ t := by
  obtain ⟨hlow, h1⟩ := mem_oppositeUnipotentRadical.1 hz
  rw [rankTorus_inv_conj_apply]
  rcases lt_trichotomy (β i) (β j) with h | h | h
  · rw [hlow i j h, mul_zero, one_apply_ne (fun e => h.ne (by rw [e])), sub_zero, map_zero]
    exact ⟨zero_mem _, zero_le'⟩
  · rw [h1 i j h, blockRank_eq h, sub_self, zpow_zero, one_mul, sub_self, map_zero]
    refine ⟨?_, zero_le'⟩
    by_cases hij : i = j
    · rw [hij, one_apply_eq]
      exact one_mem _
    · rw [one_apply_ne hij]
      exact zero_mem _
  · have hr := blockRank_lt h
    have hexp : ((k + t : ℕ) : ℤ) ≤
        ((m * blockRank β i : ℕ) : ℤ) - ((m * blockRank β j : ℕ) : ℤ) := by
      have : m * blockRank β j + m ≤ m * blockRank β i := by nlinarith
      push_cast
      omega
    rw [one_apply_ne (fun e => h.ne' (by rw [e])), sub_zero]
    exact ⟨zpow_mul_mem (hb i j) (by omega), valuation_zpow_mul_le (hb i j) hexp⟩

theorem exists_conj_mem_congruenceSubgroup {C : Set (GL (Fin n) F)} (hC : IsCompact C) (t : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z ∈ C, z ∈ oppositeUnipotentRadical F n β → z⁻¹ ∈ C →
      (rankTorus F n β m)⁻¹ * z * rankTorus F n β m ∈ congruenceSubgroup F n t := by
  obtain ⟨k, hk⟩ := exists_pow_mul_mem_of_isCompact F n hC
  refine ⟨k + t, fun m hm z hzC hz hz' => ?_⟩
  have hfz := rankTorus_inv_conj_apply_facts hm hz (hk z hzC)
  have hfz' := rankTorus_inv_conj_apply_facts hm
    ((oppositeUnipotentRadical F n β).inv_mem hz) (hk _ hz')
  rw [mem_congruenceSubgroup_iff, mem_integralGL_iff]
  refine ⟨⟨fun i j => (hfz i j).1, fun i j => ?_⟩, fun i j => (hfz i j).2⟩
  have : ((rankTorus F n β m)⁻¹ * z * rankTorus F n β m)⁻¹ =
      (rankTorus F n β m)⁻¹ * z⁻¹ * rankTorus F n β m := by group
  rw [this]
  exact (hfz' i j).1

end Parabolic

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.WhittakerLocal
section
namespace GroundTheory.Automorphic

namespace Whittaker

open MeasureTheory Measure ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem biEquivariantSigmaInvariant_GL (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) :
    BiEquivariantSigmaInvariant (Iwasawa.unipotent F n)
      (fun u => psiN ψ₀ (u : GL (Fin n) F)) sigmaHomeo := by
  intro D hD f
  have key := distribution_sigma_invariant ψ₀ hψ hψ₁ D (fun f u₁ u₂ hu₁ hu₂ => by
    have e : (⟨fun x => (f : GL (Fin n) F → ℂ) (u₁⁻¹ * x * u₂), twoSided_mem f.2 u₁ u₂⟩ :
        locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = biTranslL u₁ u₂ f :=
      Subtype.ext (coe_biTranslL u₁ u₂ f).symm
    rw [e]
    exact hD f ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩) f
  have e : compHomeoL sigmaHomeo f =
      (⟨fun x => (f : GL (Fin n) F → ℂ) (sigma x), comp_sigma_mem f.2⟩ :
        locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) := Subtype.ext rfl
  rw [e]
  exact key

section Measure

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

def thetaEquiv : GL (Fin n) F ≃* GL (Fin n) F where
  toFun := theta
  invFun := theta
  left_inv := theta_theta
  right_inv := theta_theta
  map_mul' := theta_mul

theorem map_sigma_eq (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] : μ.map sigma = μ := by
  have hθc : Continuous (theta : GL (Fin n) F → GL (Fin n) F) := continuous_theta
  have hθm : Measurable (theta : GL (Fin n) F → GL (Fin n) F) := hθc.measurable
  have : (μ.map theta).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ (thetaEquiv (F := F) (n := n)) hθc hθc
  set c := haarScalarFactor (μ.map theta) μ
  have e : μ.map theta = c • μ := isMulLeftInvariant_eq_smul (μ.map theta) μ
  have e2 : μ = (c * c) • μ := by
    have h1 : (μ.map theta).map theta = μ := by
      rw [Measure.map_map hθm hθm]
      have : (theta ∘ theta : GL (Fin n) F → GL (Fin n) F) = id := funext theta_theta
      rw [this, Measure.map_id]
    have h2 : (μ.map theta).map theta = (c * c) • μ := by
      rw [e, Measure.map_smul, e, smul_smul]
    exact h1.symm.trans h2
  set K := GLnLocal.integralGL F n
  have hK0 : μ K ≠ 0 := (GLnLocal.isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ⊤ := (GLnLocal.isCompact_integralGL F n).measure_lt_top.ne
  have hc : c = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e2
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    have h' := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    have hcc : (c * c : NNReal) = 1 := by exact_mod_cast h'
    have hr : ((c : ℝ) * (c : ℝ)) = 1 := by exact_mod_cast hcc
    have hc0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  have eθ : μ.map theta = μ := by rw [e, hc, one_smul]
  have hσ : (sigma : GL (Fin n) F → GL (Fin n) F) = (fun g => g⁻¹) ∘ theta := by
    funext g
    simp [theta]
  rw [hσ, ← Measure.map_map continuous_inv.measurable hθm, eθ]
  exact Measures.inv_eq_self_GL F n μ

end Measure

theorem rank_whittaker_mul_rank_whittaker_contragredient_le_one (ψ₀ : AddChar F ℂ)
    (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible] :
    Module.rank ℂ (equivariantFunctionals π
        (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F))) *
      Module.rank ℂ (equivariantFunctionals (contragredient π)
        (fun u : Iwasawa.unipotent F n => (psiN ψ₀ (u : GL (Fin n) F))⁻¹)) ≤ 1 := by
  let _ : MeasurableSpace (GL (Fin n) F) := _root_.borel _
  have : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  have : (haar : Measure (GL (Fin n) F)).IsInvInvariant := ⟨Measures.inv_eq_self_GL F n _⟩
  exact rank_mul_rank_le_one (haar : Measure (GL (Fin n) F)) (σ := sigmaHomeo)
    (fun x y => sigma_mul x y) (map_sigma_eq _) (biEquivariantSigmaInvariant_GL ψ₀ hψ hψ₁) hπ

theorem rank_whittaker_le_one_of_contragredient (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀)
    (hψ₁ : ψ₀ ≠ 1) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible]
    (hne : equivariantFunctionals (contragredient π)
      (fun u : Iwasawa.unipotent F n => (psiN ψ₀ (u : GL (Fin n) F))⁻¹) ≠ ⊥) :
    Module.rank ℂ (equivariantFunctionals π
      (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F))) ≤ 1 := by
  let _ : MeasurableSpace (GL (Fin n) F) := _root_.borel _
  have : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  have : (haar : Measure (GL (Fin n) F)).IsInvInvariant := ⟨Measures.inv_eq_self_GL F n _⟩
  exact rank_le_one_of_ne_bot (haar : Measure (GL (Fin n) F)) (σ := sigmaHomeo)
    (fun x y => sigma_mul x y) (map_sigma_eq _) (biEquivariantSigmaInvariant_GL ψ₀ hψ hψ₁) hπ hne

end Whittaker

end GroundTheory.Automorphic
end

