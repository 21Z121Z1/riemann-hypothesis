import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0030
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0039
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankCompletionSymmetry
section
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CountRank

open Module

variable {k : Type} [Field k] [Fintype k]

theorem card_injective {U V : Type} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [FiniteDimensional k U] [FiniteDimensional k V] {e n : ℕ}
    (hU : finrank k U = e) (hV : finrank k V = n) (he : e ≤ n) :
    Nat.card {g : U →ₗ[k] V // Function.Injective g} =
      ∏ j ∈ Finset.range e, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  classical
  have : Finite V := Module.finite_of_finite k
  let b : Module.Basis (Fin e) k U := Module.finBasisOfFinrankEq k U hU
  have key : ∀ g : U →ₗ[k] V, Function.Injective g ↔ LinearIndependent k (g ∘ b) := by
    intro g
    constructor
    · intro hg
      exact b.linearIndependent.map' g (LinearMap.ker_eq_bot.mpr hg)
    · intro hli
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hsum : ∑ i, (b.repr x i) • (g ∘ b) i = 0 := by
        have h0 : g (∑ i, (b.repr x i) • b i) = 0 := by rw [b.sum_repr]; exact hx
        rw [map_sum] at h0
        simpa only [Function.comp_apply, map_smul] using h0
      have hc := Fintype.linearIndependent_iff.mp hli _ hsum
      apply b.repr.injective
      ext i
      simp [hc i]
  have E : {g : U →ₗ[k] V // Function.Injective g} ≃ {s : Fin e → V // LinearIndependent k s} :=
    { toFun := fun g => ⟨g.1 ∘ b, (key g.1).mp g.2⟩
      invFun := fun s => ⟨b.constr k s.1, (key _).mpr (by
          have hs : (b.constr k s.1 : U → V) ∘ b = s.1 := by
            funext i
            simp
          rw [hs]
          exact s.2)⟩
      left_inv := fun g => Subtype.ext (b.ext fun i => by simp)
      right_inv := fun s => Subtype.ext (funext fun i => by simp) }
  rw [Nat.card_congr E, card_linearIndependent (K := k) (V := V) (k := e) (by omega), hV,
    Finset.prod_range (fun j => Fintype.card k ^ n - Fintype.card k ^ j)]

theorem card_ker_eq {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n ρ : ℕ} (hV : finrank k V = n) (hρ : ρ ≤ n) (K : Submodule k V)
    (hK : finrank k K = n - ρ) :
    Nat.card {f : V →ₗ[k] V // LinearMap.ker f = K} =
      ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  classical
  have hQ : finrank k (V ⧸ K) = ρ := by
    have := Submodule.finrank_quotient_add_finrank K
    omega
  have E : {f : V →ₗ[k] V // LinearMap.ker f = K} ≃
      {g : (V ⧸ K) →ₗ[k] V // Function.Injective g} :=
    { toFun := fun f => ⟨K.liftQ f.1 (le_of_eq f.2.symm),
        LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq f.2))⟩
      invFun := fun g => ⟨g.1.comp K.mkQ, by
        rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr g.2, Submodule.comap_bot,
          Submodule.ker_mkQ]⟩
      left_inv := fun f => Subtype.ext (Submodule.liftQ_mkQ K f.1 _)
      right_inv := fun g => Subtype.ext (Submodule.linearMap_qext K (Submodule.liftQ_mkQ K _ _)) }
  rw [Nat.card_congr E]
  exact card_injective hQ hV (by omega)

theorem card_rank_eq {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n ρ : ℕ} (hV : finrank k V = n) (hρ : ρ ≤ n) :
    Nat.card {f : V →ₗ[k] V // finrank k (LinearMap.range f) = ρ} =
      Nat.card {K : Submodule k V // finrank k K = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  classical
  have : Finite V := Module.finite_of_finite k
  have : Finite (V →ₗ[k] V) := Module.finite_of_finite k
  have : Finite (Submodule k V) :=
    Finite.of_injective (fun K : Submodule k V => (K : Set V)) SetLike.coe_injective
  letI : Fintype {K : Submodule k V // finrank k K = n - ρ} := Fintype.ofFinite _
  have E : {f : V →ₗ[k] V // finrank k (LinearMap.range f) = ρ} ≃
      Σ K : {K : Submodule k V // finrank k K = n - ρ},
        {f : V →ₗ[k] V // LinearMap.ker f = K.1} :=
    { toFun := fun f => ⟨⟨LinearMap.ker f.1, by
          have h1 := LinearMap.finrank_range_add_finrank_ker f.1
          have h2 := f.2
          omega⟩, ⟨f.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by
          have h1 := LinearMap.finrank_range_add_finrank_ker p.2.1
          have h2 := p.1.2
          have h3 := p.2.2
          rw [h3] at h1
          omega⟩
      left_inv := fun f => rfl
      right_inv := by
        rintro ⟨⟨K, hK⟩, ⟨f, hf⟩⟩
        dsimp only at hf
        subst hf
        rfl }
  rw [Nat.card_congr E, Nat.card_sigma,
    Finset.sum_congr rfl (fun a _ => card_ker_eq hV hρ a.1 a.2), Finset.sum_const,
    Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card (α := {K : Submodule k V // finrank k K = n - ρ})]

theorem card_sub_le {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n : ℕ} (hV : finrank k V = n) (d : ℕ) (hd : d ≤ n) :
    Nat.card {K : Submodule k V // finrank k K = d} ≤
      Nat.card {K : Submodule k V // finrank k K = n - d} := by
  classical
  have : Finite V := Module.finite_of_finite k
  have : Finite (Submodule k V) :=
    Finite.of_injective (fun K : Submodule k V => (K : Set V)) SetLike.coe_injective
  let eV : Module.Dual k V ≃ₗ[k] V := ((Module.finBasis k V).toDualEquiv).symm
  have hDual : ∀ K : Submodule k V,
      finrank k (K.dualAnnihilator) = finrank k V - finrank k K := by
    intro K
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq K
    omega
  let F : {K : Submodule k V // finrank k K = d} → {K : Submodule k V // finrank k K = n - d} :=
    fun K => ⟨(K.1.dualAnnihilator).map (eV : Module.Dual k V →ₗ[k] V), by
      rw [LinearEquiv.finrank_map_eq, hDual, hV, K.2]⟩
  apply Nat.card_le_card_of_injective F
  intro K₁ K₂ h
  apply Subtype.ext
  have h1 : (K₁.1.dualAnnihilator).map (eV : Module.Dual k V →ₗ[k] V) =
      (K₂.1.dualAnnihilator).map (eV : Module.Dual k V →ₗ[k] V) := congrArg Subtype.val h
  have h2 := Submodule.map_injective_of_injective eV.injective h1
  exact Subspace.dualAnnihilator_inj.mp h2

theorem card_sub_symm {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n : ℕ} (hV : finrank k V = n) (d : ℕ) (hd : d ≤ n) :
    Nat.card {K : Submodule k V // finrank k K = d} =
      Nat.card {K : Submodule k V // finrank k K = n - d} := by
  apply le_antisymm (card_sub_le hV d hd)
  have := card_sub_le hV (n - d) (Nat.sub_le n d)
  rwa [Nat.sub_sub_self hd] at this

theorem card_matrix_rank (n ρ : ℕ) :
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} =
      Nat.card {f : (Fin n → k) →ₗ[k] (Fin n → k) // finrank k (LinearMap.range f) = ρ} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquiv
    (Matrix.toLin' : Matrix (Fin n) (Fin n) k ≃ₗ[k] ((Fin n → k) →ₗ[k] (Fin n → k))).toEquiv
    (fun D => by
      show D.rank = ρ ↔ finrank k (LinearMap.range (Matrix.toLin' D)) = ρ
      rw [Matrix.toLin'_apply']
      rfl)

theorem rank_symm (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (h : ρ ≤ n) :
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  have hV : finrank k (Fin n → k) = n := Module.finrank_fin_fun k
  rw [card_matrix_rank, card_matrix_rank, card_rank_eq hV h, card_rank_eq hV (Nat.sub_le n ρ),
    Nat.sub_sub_self h, card_sub_symm hV ρ h]
  ring

end GlobalTheory.CompanionTheory.Jp.CountRank
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardTwoAffineHyperplanes
section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpCount

noncomputable def pairMap {k : Type} [Field k] {n : ℕ} (a b : Fin (n + 1) → k) :
    (Fin (n + 1) → k) →ₗ[k] k × k where
  toFun x := (a ⬝ᵥ x, b ⬝ᵥ x)
  map_add' x y := by simp [dotProduct_add]
  map_smul' c x := by simp [dotProduct_smul]

theorem pairMap_range {k : Type} [Field k] {n : ℕ} (a b : Fin (n + 1) → k)
    (ha : a ≠ 0) (hb : ∀ s : k, b ≠ s • a) : LinearMap.range (pairMap a b) = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hform : ∀ u v : k, φ (u, v) = u * φ (1, 0) + v * φ (0, 1) := by
    intro u v
    have h : ((u, v) : k × k) = u • ((1, 0) : k × k) + v • ((0, 1) : k × k) := by simp
    rw [h, map_add, map_smul, map_smul]
    simp
  have hzero : (φ (1, 0) • a + φ (0, 1) • b) = 0 := by
    apply dotProduct_eq_zero
    intro x
    have hx : φ (pairMap a b x) = 0 := hle (LinearMap.mem_range_self _ x)
    have hx' : φ (a ⬝ᵥ x, b ⬝ᵥ x) = 0 := hx
    rw [hform] at hx'
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    linear_combination hx'
  by_cases hμ : φ (0, 1) = 0
  · rw [hμ, zero_smul, add_zero] at hzero
    rcases smul_eq_zero.mp hzero with hl | h0
    · apply hφ
      ext p
      · simp [hl]
      · simp [hμ]
    · exact ha h0
  · apply hb (-(φ (0, 1))⁻¹ * φ (1, 0))
    have h1 : φ (0, 1) • b = -(φ (1, 0) • a) := eq_neg_of_add_eq_zero_right hzero
    calc b = (φ (0, 1))⁻¹ • (φ (0, 1) • b) := by rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = (-(φ (0, 1))⁻¹ * φ (1, 0)) • a := by
        rw [h1, smul_neg, smul_smul, neg_mul, neg_smul]

theorem card_two_equations (k : Type) [Field k] [Fintype k] (n : ℕ) (a b : Fin (n + 1) → k)
    (ha : a ≠ 0) (hb : ∀ s : k, b ≠ s • a) :
    Fintype.card k ^ 2 * (Finset.univ.filter
      (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card = Fintype.card k ^ (n + 1) := by
  have hr := pairMap_range a b ha hb
  obtain ⟨x0, hx0⟩ : ∃ x0, pairMap a b x0 = ((1, 1) : k × k) := by
    have : ((1, 1) : k × k) ∈ LinearMap.range (pairMap a b) := by rw [hr]; trivial
    exact this
  have hx1 : a ⬝ᵥ x0 = 1 := congrArg Prod.fst hx0
  have hx2 : b ⬝ᵥ x0 = 1 := congrArg Prod.snd hx0
  have hker : ∀ y, y ∈ LinearMap.ker (pairMap a b) ↔ a ⬝ᵥ y = 0 ∧ b ⬝ᵥ y = 0 := by
    intro y
    rw [LinearMap.mem_ker]
    exact Prod.ext_iff
  let e : LinearMap.ker (pairMap a b) ≃ {x : Fin (n + 1) → k // a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1} :=
    { toFun := fun y => ⟨y.1 + x0, by
        have h := (hker y.1).1 y.2
        simp [dotProduct_add, h.1, h.2, hx1, hx2]⟩
      invFun := fun x => ⟨x.1 - x0, by
        rw [hker]
        simp [dotProduct_sub, x.2.1, x.2.2, hx1, hx2]⟩
      left_inv := fun y => by simp
      right_inv := fun x => by simp }
  have hcard : (Finset.univ.filter
      (fun x : Fin (n + 1) → k => a ⬝ᵥ x = 1 ∧ b ⬝ᵥ x = 1)).card
      = Fintype.card k ^ Module.finrank k (LinearMap.ker (pairMap a b)) := by
    rw [← Module.card_eq_pow_finrank (K := k) (V := LinearMap.ker (pairMap a b)),
      Fintype.card_congr e, Fintype.card_subtype]
  have hrank := LinearMap.finrank_range_add_finrank_ker (pairMap a b)
  rw [hr, finrank_top] at hrank
  have h2 : Module.finrank k (k × k) = 2 := by simp
  have hV : Module.finrank k (Fin (n + 1) → k) = n + 1 := by simp
  rw [h2, hV] at hrank
  rw [hcard, ← pow_add, hrank]

end GlobalTheory.CompanionTheory.GapOpCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterAnnihilatorIntegerLattice
section
open ValuativeRel MeasureTheory Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CharLattice

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def annihilator (ψ : AddChar k Circle) (n : ℕ) (b : k) : AddSubgroup (Fin n → k) where
  carrier := {x | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1}
  zero_mem' := fun t _ => by simp
  add_mem' := fun {x y} hx hy t ht => by
    rw [dotProduct_add, mul_add, AddChar.map_add_eq_mul, hx t ht, hy t ht, one_mul]
  neg_mem' := fun {x} hx t ht => by
    rw [dotProduct_neg, mul_neg, AddChar.map_neg_eq_inv, hx t ht, inv_one]

theorem isOpen_annihilator (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (b : k) (hb : b ≠ 0) :
    IsOpen (annihilator ψ n b : Set (Fin n → k)) := by
  obtain ⟨γ, hγ0, hγ⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  apply AddSubgroup.isOpen_of_mem_nhds
  have hball : {z : k | valuation k z < γ} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ0
  have hmul : {y : k | valuation k (b * y) < γ} ∈ nhds (0 : k) := by
    have h := (continuous_const.mul continuous_id : Continuous fun y : k => b * y).tendsto' 0 0 (mul_zero b)
    exact h hball
  have hU : (Set.univ.pi fun _ : Fin n => {y : k | valuation k (b * y) < γ}) ∈ nhds (0 : Fin n → k) :=
    set_pi_mem_nhds Set.finite_univ (fun j _ => hmul)
  refine Filter.mem_of_superset hU ?_
  intro x hx t ht
  apply hγ
  show valuation k (b * ∑ i, t i * x i) < γ
  rw [Finset.mul_sum]
  refine (valuation k).map_sum_lt hγ0 fun j _ => ?_
  have hxj : valuation k (b * x j) < γ := hx j (Set.mem_univ j)
  have htj : valuation k (t j) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (ht j)
  refine lt_of_le_of_lt ?_ hxj
  calc valuation k (b * (t j * x j)) = valuation k (t j) * valuation k (b * x j) := by
        rw [← map_mul]; ring_nf
    _ ≤ 1 * valuation k (b * x j) := mul_le_mul_left htj _
    _ = valuation k (b * x j) := one_mul _

theorem isClosed_annihilator (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) (b : k) :
    IsClosed (annihilator ψ n b : Set (Fin n → k)) := by
  have e : (annihilator ψ n b : Set (Fin n → k)) =
      ⋂ (t : Fin n → k) (_ : ∀ j, t j ∈ 𝒪[k]), {x | ψ (b * (t ⬝ᵥ x)) = 1} := by
    ext x
    simp only [Set.mem_iInter]
    rfl
  rw [e]
  exact isClosed_iInter fun t => isClosed_iInter fun _ =>
    isClosed_eq (hψ.comp (continuous_const.mul (continuous_const.dotProduct continuous_id)))
      continuous_const

theorem annihilator_subset (ψ : AddChar k Circle) (n : ℕ) (b : k) (hb : b ≠ 0) (y₀ : k)
    (hy : ψ y₀ ≠ 1) :
    (annihilator ψ n b : Set (Fin n → k)) ⊆
      Set.univ.pi (fun _ => {y : k | valuation k y ≤ valuation k (y₀ / b)}) := by
  intro x hx j _
  have hx' : ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1 := hx
  show valuation k (x j) ≤ valuation k (y₀ / b)
  by_contra hlt'
  have hlt := lt_of_not_ge hlt'
  have hxj : x j ≠ 0 := by
    intro h
    rw [h, map_zero] at hlt
    exact not_lt_zero hlt
  have ht : ∀ i, (Pi.single j (y₀ / b / x j) : Fin n → k) i ∈ 𝒪[k] := by
    intro i
    rw [Valuation.mem_integer_iff]
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same, map_div₀]
      exact (div_le_one₀ ((valuation k).pos_iff.2 hxj)).2 hlt.le
    · rw [Pi.single_eq_of_ne hij, map_zero]
      exact zero_le_one
  have h := hx' _ ht
  have e : b * ((Pi.single j (y₀ / b / x j) : Fin n → k) ⬝ᵥ x) = y₀ := by
    rw [single_dotProduct]
    field_simp
  rw [e] at h
  exact hy h

theorem isCompact_isOpen_annihilator :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (b : k), b ≠ 0 →
      IsCompact {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} ∧
      IsOpen {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} := by
  intro k _ _ _ _ ψ hψ hne n b hb
  have e : {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1} =
      (annihilator ψ n b : Set (Fin n → k)) := rfl
  rw [e]
  obtain ⟨y₀, hy⟩ : ∃ y₀, ψ y₀ ≠ 1 := by
    by_contra h
    exact hne (AddChar.ext ψ 1 fun y => by
      rw [AddChar.one_apply]
      by_contra hy
      exact h ⟨y, hy⟩)
  refine ⟨?_, isOpen_annihilator ψ hψ n b hb⟩
  exact (isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _).of_isClosed_subset
    (isClosed_annihilator ψ hψ n b) (annihilator_subset ψ n b hb y₀ hy)

end GlobalTheory.CompanionTheory.CharLattice
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHermitianSimultaneousDiagStatement
section
open Matrix Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_hermitian_simultaneous_diag : ∀ {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ)), (∀ A ∈ S, Aᴴ = A) → (∀ A ∈ S, ∀ B ∈ S, A * B = B * A) → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A ∈ S, (Uᴴ * A * U).IsDiag := by
  first | exact @GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag | exact GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag | (intros; apply GlobalTheory.CompanionTheory.SimDiag.exists_unitary_isDiag <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparableModSquareLocalization
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.CompMod

theorem exists_eq_add_of_mem_span_quot {S : Type} [CommRing S] (ϖ x y : S)
    (h : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) x ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) y}) :
    ∃ c d : S, x = y * c + ϖ ^ 2 * d := by
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.1 h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  rw [← map_mul] at hc'
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hc')
  exact ⟨c, d, by linear_combination hd⟩

theorem mem_span_or_mem_span {S : Type} [CommRing S] (ϖ : S)
    [IsAdicComplete (Ideal.span {ϖ}) S] (h0 : Val0 (S ⧸ Ideal.span {ϖ ^ 2}))
    (P : Ideal S) (hP : P.IsPrime) (f g : S ⧸ compI P) :
    f ∈ Ideal.span {g, Ideal.Quotient.mk (compI P) ϖ ^ 2} ∨
      g ∈ Ideal.span {f, Ideal.Quotient.mk (compI P) ϖ ^ 2} := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨ε, hε, h1, h2⟩ := h0 (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b)
  obtain ⟨e, ⟨he, rfl⟩, -⟩ :=
    IdemLift.existsUnique_idempotent_lift ϖ 2 two_ne_zero ε hε
  rw [← map_mul] at h1
  have h2' : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((1 - e) * b) ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) a} := by
    simpa [map_mul, map_sub, map_one] using h2
  obtain ⟨c, d, hcd⟩ := exists_eq_add_of_mem_span_quot ϖ _ _ h1
  obtain ⟨c', d', hcd'⟩ := exists_eq_add_of_mem_span_quot ϖ _ _ h2'
  have key : ∀ t : S, IsIdempotentElem t → t ∈ P →
      Ideal.Quotient.mk (compI P) t = 0 := fun t ht htP =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨ht, htP⟩)
  by_cases heP : e ∈ P
  · right
    have hz := key e he heP
    have hb := congrArg (Ideal.Quotient.mk (compI P)) hcd'
    simp only [map_mul, map_add, map_sub, map_one, map_pow, hz, sub_zero, one_mul] at hb
    rw [hb]
    exact Ideal.mem_span_pair.2 ⟨Ideal.Quotient.mk _ c', Ideal.Quotient.mk _ d', by ring⟩
  · left
    have hmul : e * (1 - e) ∈ P := by
      have : e * (1 - e) = 0 := by
        have he' : e * e = e := he
        linear_combination -he'
      rw [this]
      exact P.zero_mem
    have h1e : 1 - e ∈ P := (hP.mem_or_mem hmul).resolve_left heP
    have hz := key (1 - e) he.one_sub h1e
    have hz' : Ideal.Quotient.mk (compI P) e = 1 := by
      rw [map_sub, map_one] at hz
      exact (sub_eq_zero.1 hz).symm
    have ha := congrArg (Ideal.Quotient.mk (compI P)) hcd
    simp only [map_mul, map_add, map_pow, hz', one_mul] at ha
    rw [ha]
    exact Ideal.mem_span_pair.2 ⟨Ideal.Quotient.mk _ c, Ideal.Quotient.mk _ d, by ring⟩

end GlobalTheory.CompanionTheory.CompMod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAtOfSqBound
section
noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerVec

theorem ker_mul_right {G : Type} [Group G] (Γ : Subgroup G) (φ : G → ℂ) (z y w : G) :
    ker Γ (fun g => φ (g * w)) z y = ker Γ φ z (y * w) := by
  simp only [ker, mul_assoc]

theorem tst_mul_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {φ : G → ℂ} (h : Tst φ) (w : G) : Tst (fun g => φ (g * w)) :=
  ⟨h.1.comp (continuous_mul_const w), h.2.comp_homeomorph (Homeomorph.mulRight w)⟩

theorem continuousAt_of_sq_bound {G E : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SeminormedAddCommGroup E] (f : G → E) (y₀ : G) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ w in 𝓝 (1 : G),
      ‖f (y₀ * w) - f y₀‖ₑ ^ 2 ≤ c * ENNReal.ofReal ε ^ 2) : ContinuousAt f y₀ := by
  rw [ContinuousAt, ← map_mul_left_nhds_one y₀, Filter.tendsto_map'_iff, Metric.tendsto_nhds]
  intro ε hε
  have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hε' : 0 < ε / (c.toReal + 1) := by positivity
  filter_upwards [h _ hε'] with w hw
  have hb : ‖f (y₀ * w) - f y₀‖ ^ 2 ≤ c.toReal * (ε / (c.toReal + 1)) ^ 2 := by
    have hr : ENNReal.ofReal (‖f (y₀ * w) - f y₀‖ ^ 2) ≤
        ENNReal.ofReal (c.toReal * (ε / (c.toReal + 1)) ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul hc0,
        ENNReal.ofReal_pow hε'.le, ENNReal.ofReal_toReal hc, ofReal_norm]
      exact hw
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hr
  have hlt : c.toReal * (ε / (c.toReal + 1)) ^ 2 < ε ^ 2 := by
    have hd : 0 < (c.toReal + 1) ^ 2 := by positivity
    rw [div_pow, ← mul_div_assoc, div_lt_iff₀ hd]
    have : 0 < ε ^ 2 := by positivity
    nlinarith [mul_nonneg hc0 hc0, mul_nonneg hc0 this.le, mul_nonneg (mul_nonneg hc0 hc0) this.le]
  show dist (f ((fun x => y₀ * x) w)) (f y₀) < ε
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le (hb.trans_lt hlt)

theorem vecEx : CntBasic → KernelL2RowsColumns → TwoUnif → VecClose → VecEx := by
  intro hC hL hT hV X ι _ Φ hΦ
  let k : X.G → ι → X.Hs ι := fun y j =>
    WithLp.toLp 2 fun l => ((hL X (Φ l j) (hΦ l j)).1 y).toLp _
  have hk : ∀ y j, X.IsVec Φ y j (k y j) := fun y j l =>
    ((hL X (Φ l j) (hΦ l j)).1 y).coeFn_toLp
  refine ⟨k, fun j => continuous_iff_continuousAt.2 fun y₀ => ?_, hk⟩
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  have hS : IsCompact (⋃ l, tsupport (Φ l j)) := isCompact_iUnion fun l => (hΦ l j).2
  obtain ⟨Ω, hΩdef⟩ : ∃ Ω : Set X.G, Ω = (⋃ l, tsupport (Φ l j)) * N⁻¹ := ⟨_, rfl⟩
  have hΩ : IsCompact Ω := hΩdef ▸ hS.mul hNc.inv
  have hsub : ∀ (l : ι) (w : X.G), w ∈ N → Function.support (fun g => Φ l j (g * w)) ⊆ Ω := by
    intro l w hw g hg
    rw [hΩdef]
    have h1 : g * w ∈ ⋃ l, tsupport (Φ l j) :=
      Set.mem_iUnion.2 ⟨l, subset_tsupport _ hg⟩
    have h2 : w⁻¹ ∈ N⁻¹ := Set.inv_mem_inv.2 hw
    simpa using Set.mul_mem_mul h1 h2
  have hc : (Fintype.card ι : ℝ≥0∞) * (X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y₀) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top hΩ.inv.measure_lt_top.ne
      ((hC X).1 _ (hΩ.inv.mul hΩ) y₀))
  refine continuousAt_of_sq_bound (fun y => k y j) y₀ _ hc fun ε hε => ?_
  choose W hW hW' using fun l => hT X (Φ l j) ε (hΦ l j) hε
  filter_upwards [hN1, Filter.eventually_all.2 hW] with w hwN hwW
  have hv : X.IsVec (fun l i g => Φ l i (g * w)) y₀ j (k (y₀ * w) j) := fun l =>
    (hk (y₀ * w) j l).trans (Filter.Eventually.of_forall fun z => (ker_mul_right X.Γ (Φ l j) z y₀ w).symm)
  have key := hV X ι (fun l i g => Φ l i (g * w)) Φ Ω ε y₀ j _ _ hΩ
    (fun l => ⟨tst_mul_right (hΦ l j) w, hΦ l j, hsub l w hwN,
      by simpa using hsub l 1 h1N, fun z => by
        simpa using hW' l 1 (mem_of_mem_nhds (hW l)) w (hwW l) z⟩) hv (hk y₀ j)
  refine key.trans (le_of_eq ?_)
  ring

end GlobalTheory.CompanionTheory.KerVec

end
end

