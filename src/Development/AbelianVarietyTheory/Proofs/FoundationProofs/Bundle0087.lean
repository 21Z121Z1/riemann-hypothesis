import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitCoeffGaloisLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0069

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RepresentationRootSubgroupExchange
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem eq_zero_of_sum_joint_eigenvectors {ι κ M : Type} [AddCommGroup M] [Module ℂ M]
    (T : κ → M →ₗ[ℂ] M) (l : ι → κ → ℂ) (hl : ∀ i j, i ≠ j → ∃ k, l i k ≠ l j k)
    (s : Finset ι) : ∀ u : ι → M, (∀ i k, T k (u i) = l i k • u i) → ∑ i ∈ s, u i = 0 →
      ∀ i ∈ s, u i = 0 := by
  first
  | exact @_root_.GlobalTheory.ComplexValueBound.main
  | exact _root_.GlobalTheory.ComplexValueBound.main
  | (apply _root_.GlobalTheory.ComplexValueBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ComplexValueBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ComplexValueBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ComplexValueBound.main ..)

theorem root_exchange : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (B X Y : Subgroup G) (χ : G → ℂ), (∀ x ∈ X, x ∈ B → x = 1) → (∀ b ∈ B, ∀ x ∈ X, ∃ x' ∈ X, ∃ b' ∈ B, b * x = x' * b' ∧ χ b' = χ b) → (∀ x ∈ X, ∀ y ∈ Y, y⁻¹ * x⁻¹ * y * x ∈ B) → (∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → ∃ y ∈ Y, χ (y⁻¹ * x⁻¹ * y * x) ≠ χ (y⁻¹ * x'⁻¹ * y * x')) → ∀ (n : ℕ) (v : Fin n → M), LinearIndependent ℂ v → (∀ i, (∀ b ∈ B, ρ b (v i) = χ b • v i) ∧ ∀ y ∈ Y, ρ y (v i) = v i) → ∃ w : Fin n → M, LinearIndependent ℂ w ∧ ∀ i, (∀ b ∈ B, ρ b (w i) = χ b • w i) ∧ ∀ x ∈ X, ρ x (w i) = w i := by
  intro G _ _ M _ _ _ ρ B X Y χ hXB hBX hc hsep n v hv hvi
  have hmul : ∀ (g h : G) (m : M), ρ (g * h) m = ρ g (ρ h m) := fun g h m => by
    rw [map_mul]; rfl
  let S : M →ₗ[ℂ] M := ∑ x : X, ρ (x : G)
  have hS : ∀ m, S m = ∑ x : X, ρ (x : G) m := fun m => by
    simp only [S, LinearMap.sum_apply]
  have hinj : ∀ m : M, (∀ b ∈ B, ρ b m = χ b • m) → (∀ y ∈ Y, ρ y m = m) → S m = 0 → m = 0 := by
    intro m hb hy h0
    rw [hS] at h0
    have := eq_zero_of_sum_joint_eigenvectors (ι := X) (κ := Y) (fun y => ρ (y : G))
      (fun x y => χ ((y : G)⁻¹ * (x : G)⁻¹ * y * x))
      (fun x x' hne => by
        obtain ⟨y, hyY, h⟩ := hsep x x.2 x' x'.2 (fun h => hne (Subtype.ext h))
        exact ⟨⟨y, hyY⟩, h⟩) Finset.univ (fun x => ρ (x : G) m)
      (fun x y => by
        have e : (y : G) * x = x * (y * ((y : G)⁻¹ * (x : G)⁻¹ * y * x)) := by group
        show ρ (y : G) (ρ (x : G) m) = _
        rw [← hmul, e, hmul, hmul, hb _ (hc x x.2 y y.2), map_smul, hy y y.2, map_smul]) h0
      1 (Finset.mem_univ _)
    simpa using this
  refine ⟨fun i => S (v i), ?_, fun i => ⟨fun b hb => ?_, fun x hx => ?_⟩⟩
  · rw [Fintype.linearIndependent_iff] at hv ⊢
    intro g hg
    apply hv g
    apply hinj
    · intro b hb
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hvi i).1 b hb, smul_comm]
    · intro y hy
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hvi i).2 y hy]
    · rw [map_sum, ← hg]
      simp only [map_smul]
  · choose f hf g hg hfg hχ using hBX b hb
    let F : X → X := fun x => ⟨f x x.2, hf x x.2⟩
    have hF : Function.Injective F := by
      intro x1 x2 h
      have h' : f x1 x1.2 = f x2 x2.2 := congrArg Subtype.val h
      have e1 := hfg x1 x1.2
      have e2 := hfg x2 x2.2
      rw [← h'] at e2
      have e : (x1 : G)⁻¹ * x2 = (g x1 x1.2)⁻¹ * g x2 x2.2 := by
        calc (x1 : G)⁻¹ * x2 = (b * x1)⁻¹ * (b * x2) := by group
          _ = _ := by rw [e1, e2]; group
      have := hXB _ (X.mul_mem (X.inv_mem x1.2) x2.2)
        (e ▸ B.mul_mem (B.inv_mem (hg x1 x1.2)) (hg x2 x2.2))
      exact Subtype.ext (inv_mul_eq_one.1 this)
    have hB : Function.Bijective F := Finite.injective_iff_bijective.1 hF
    show ρ b (S (v i)) = χ b • S (v i)
    rw [hS, map_sum, Finset.smul_sum]
    refine Fintype.sum_bijective F hB _ _ fun x => ?_
    rw [← hmul, hfg x x.2, hmul, (hvi i).1 _ (hg x x.2), hχ, map_smul]
  · show ρ x (S (v i)) = S (v i)
    rw [hS, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨x, hx⟩ : X)) _ _ fun z => ?_
    rw [← hmul]; rfl

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitCoeffGaloisLevelStatement
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedSiegelUnit_coeff_galois_level : ∀ (c M a b d : ℕ) (σ : ℂ ≃+* ℂ), 0 < M → a < M → σ (ee (1 / (M : ℂ))) = ee ((d : ℂ) / M) → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → ∃ (k : ℤ) (A : ℕ → ℂ), HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A ∧ HasQ M (fun τ => sg c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => σ (A n)) := by
  first | exact @GlobalTheory.Sieg.sg_coeff_galois_int | exact GlobalTheory.Sieg.sg_coeff_galois_int | (intros; apply GlobalTheory.Sieg.sg_coeff_galois_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductDistributionRelationStatement
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedThetaQProduct_distribution_relation : ∀ (c m : ℕ) (q t : ℂ), 1 < c → Nat.Coprime c 6 → 0 < m → Nat.Coprime c m → ‖q‖ < 1 → q ≠ 0 → t ≠ 0 → (∀ n : ℤ, q ^ n * t ^ (c * m) ≠ 1) → ∏ j ∈ Finset.range m, cth c q (t * ee ((j : ℂ) / m)) = cth c (q ^ m) (t ^ m) := by
  first | exact @GlobalTheory.Sieg.prod_cth_mul_ee | exact GlobalTheory.Sieg.prod_cth_mul_ee | (intros; apply GlobalTheory.Sieg.prod_cth_mul_ee <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem specialLinearGroup_map_intCast_zmod_surjective :
    ∀ (M : ℕ), Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) :
      SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod M)) :=
  fun M => GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) M

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassUnionBoundsStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefreeLabelTorusMass_union_bounds : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ), (∀ A B : (ZMod g)[X] → Prop, (∀ f ∈ sqSet g N, A f → B f) → mass g N A ≤ mass g N B) ∧ (∀ A, 0 ≤ mass g N A) ∧ (∀ (κ : Type) (s : Finset κ) (A : (ZMod g)[X] → Prop) (B : κ → (ZMod g)[X] → Prop), (∀ f ∈ sqSet g N, A f → ∃ i ∈ s, B i f) → mass g N A ≤ ∑ i ∈ s, mass g N (B i)) ∧ ∀ A : (ZMod g)[X] → Prop, mass g N A + mass g N (fun f => ¬ A f) = mass g N fun _ => True := by
  first | exact @GlobalTheory.BadShare.mass_union_bounds | exact GlobalTheory.BadShare.mass_union_bounds | (intros; apply GlobalTheory.BadShare.mass_union_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubgroupCharacterIdempotentProperties
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare.EpsProj

variable {G : Type} [Group G] [Fintype G] {S : G → Prop} {χ : G → ℂ}

omit [Fintype G] in
theorem pow_spec (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (n : ℕ) :
    S (u ^ n) ∧ χ (u ^ n) = χ u ^ n := by
  induction n with
  | zero => simp [h1, c1]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ⟨hm _ _ ih.1 hu, by rw [cm _ _ ih.1 hu, ih.2]⟩

theorem inv_spec (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) :
    S u⁻¹ ∧ χ u⁻¹ = (χ u)⁻¹ ∧ ‖χ u‖ = 1 := by
  have hc : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hi : u⁻¹ = u ^ (Fintype.card G - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hc), pow_card_eq_one]
  have hS : S u⁻¹ := by rw [hi]; exact (pow_spec h1 hm c1 cm hu _).1
  refine ⟨hS, ?_, ?_⟩
  · have := cm _ _ hu hS
    rw [mul_inv_cancel, c1] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  · have := (pow_spec h1 hm c1 cm hu (Fintype.card G)).2
    rw [pow_card_eq_one, c1] at this
    exact Complex.norm_eq_one_of_pow_eq_one this.symm hc

theorem eps_mul (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (y : G) :
    eps S χ (u⁻¹ * y) = χ u * eps S χ y := by
  obtain ⟨hi, ci, -⟩ := inv_spec h1 hm c1 cm hu
  unfold eps
  by_cases hy : S y
  · rw [if_pos hy, if_pos (hm _ _ hi hy), cm _ _ hi hy, ci, mul_inv, inv_inv, mul_div_assoc]
  · have : ¬ S (u⁻¹ * y) := fun h => hy (by simpa using hm _ _ hu h)
    rw [if_neg hy, if_neg this, mul_zero]

omit [Group G] in
theorem sum_ite_card : ∑ y, (if S y then (1 : ℂ) else 0) = (Nat.card {u // S u} : ℂ) := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem sum_eps_chi (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) :
    ∑ y, eps S χ y * χ y = 1 := by
  haveI : Nonempty {u // S u} := ⟨⟨1, h1⟩⟩
  have hc : (Nat.card {u // S u} : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have : ∀ y, eps S χ y * χ y = (if S y then (1 : ℂ) else 0) / (Nat.card {u // S u} : ℂ) := by
    intro y
    unfold eps
    by_cases hy : S y
    · have hn : χ y ≠ 0 := by
        intro h
        have := (inv_spec h1 hm c1 cm hy).2.2
        rw [h] at this
        simp at this
      rw [if_pos hy, if_pos hy]
      field_simp
    · simp [hy]
  simp_rw [this]
  rw [← Finset.sum_div, sum_ite_card, div_self hc]

theorem isProj_eps (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) : IsProj (eps S χ) := by
  refine ⟨?_, ?_⟩
  · funext x
    unfold conv
    have : ∀ y, eps S χ y * eps S χ (y⁻¹ * x) = eps S χ y * χ y * eps S χ x := by
      intro y
      by_cases hy : S y
      · rw [eps_mul h1 hm c1 cm hy, mul_assoc]
      · have : eps S χ y = 0 := by simp [eps, hy]
        simp [this]
    simp_rw [this]
    rw [← Finset.sum_mul, sum_eps_chi h1 hm c1 cm, one_mul]
  · intro x
    unfold eps
    by_cases hx : S x
    · obtain ⟨hi, ci, hn⟩ := inv_spec h1 hm c1 cm hx
      rw [if_pos hx, if_pos hi, ci, map_div₀, map_inv₀, map_natCast, Complex.inv_eq_conj hn]
    · have : ¬ S x⁻¹ := fun h => hx (by simpa using (inv_spec h1 hm c1 cm h).1)
      rw [if_neg hx, if_neg this, map_zero]

theorem mem_range_iff {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) (x : M) :
    x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x := by
  constructor
  · rintro ⟨z, rfl⟩ u hu
    simp only [op, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun y => ?_
    have := eps_mul h1 hm c1 cm hu (u * y)
    rw [inv_mul_cancel_left] at this
    simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, smul_smul]
    rw [← this]
  · intro h
    refine ⟨x, ?_⟩
    simp only [op, LinearMap.sum_apply, LinearMap.smul_apply]
    have : ∀ y, eps S χ y • ρ y x = (eps S χ y * χ y) • x := by
      intro y
      by_cases hy : S y
      · rw [h y hy, smul_smul]
      · have : eps S χ y = 0 := by simp [eps, hy]
        simp [this]
    simp_rw [this]
    rw [← Finset.sum_smul, sum_eps_chi h1 hm c1 cm, one_smul]

theorem eps_spec : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), ∀ (S : G → Prop) (χ : G → ℂ), S 1 → (∀ u v, S u → S v → S (u * v)) → χ 1 = 1 → (∀ u v, S u → S v → χ (u * v) = χ u * χ v) → IsProj (eps S χ) ∧ eps S χ 1 = ((Nat.card {u // S u} : ℂ))⁻¹ ∧ (∀ x : M, x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x) ∧ ∀ (n : ℕ) (x : Fin n → M), LinearIndependent ℂ x → (∀ i u, S u → ρ u (x i) = χ u • x i) → n ≤ rk ρ (eps S χ) := by
  intro G _ _ M _ _ _ ρ S χ h1 hm c1 cm
  refine ⟨isProj_eps h1 hm c1 cm, ?_, mem_range_iff ρ h1 hm c1 cm, ?_⟩
  · simp only [eps, if_pos h1, c1, inv_one, one_div]
  · intro n x hx h
    have hmem : ∀ i, x i ∈ LinearMap.range (op ρ (eps S χ)) :=
      fun i => (mem_range_iff ρ h1 hm c1 cm _).2 (h i)
    have hli : LinearIndependent ℂ (fun i => (⟨x i, hmem i⟩ : LinearMap.range (op ρ (eps S χ)))) :=
      LinearIndependent.of_comp (LinearMap.range (op ρ (eps S χ))).subtype hx
    simpa [rk] using hli.fintype_card_le_finrank

end GlobalTheory.BadShare.EpsProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstUpperTriangularHahnMulAndOneStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.substUpperTriangularHahn_mul_and_one : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (a b d : ℚ), 0 < a / d → ∀ φ ψ : HahnSeries ℚ Ω,
  sub ε a b d (φ * ψ) = sub ε a b d φ * sub ε a b d ψ ∧ sub ε a b d 1 = 1 := by
  first | exact @GlobalTheory.CyclotomicQExpansion.sub_mul_and_one | exact GlobalTheory.CyclotomicQExpansion.sub_mul_and_one | (intros; apply GlobalTheory.CyclotomicQExpansion.sub_mul_and_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumUnitsPrimePowTeichmullerReindex
section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory

theorem sum_units_primePow_teichmuller_reindex :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (m : ℕ) (A : Type) [AddCommMonoid A] (f : ZMod (p ^ (m + 1)) → A),
      ∑ b : (ZMod (p ^ (m + 1)))ˣ, f (b : ZMod (p ^ (m + 1))) =
        ∑ c : (ZMod p)ˣ, ∑ l ∈ Finset.range (p ^ m),
          f ((((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l : ℕ)) : ZMod (p ^ (m + 1))) := by
  intro p hp hp2 m A _ f
  have hpp : p.Prime := hp.out
  haveI : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hcop : ∀ (c : (ZMod p)ˣ) (l : ℕ),
      Nat.Coprime ((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l) (p ^ (m + 1)) := by
    intro c l
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.mul
    · apply Nat.Coprime.pow_left
      rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
      intro h
      have h0 : (((c : ZMod p).val : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [ZMod.natCast_zmod_val] at h0
      exact c.ne_zero h0
    · apply Nat.Coprime.pow_left
      rw [Nat.coprime_comm, hpp.coprime_iff_not_dvd]
      intro h
      have h1 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).1 (by rwa [add_comm] at h)
      exact hpp.one_lt.ne' (Nat.dvd_one.1 h1)
  let g : (ZMod p)ˣ × Fin (p ^ m) → (ZMod (p ^ (m + 1)))ˣ :=
    fun x => ZMod.unitOfCoprime _ (hcop x.1 x.2)
  have hg : ∀ x, (g x : ZMod (p ^ (m + 1))) =
      (((x.1 : ZMod p).val ^ (p ^ m) * (1 + p) ^ (x.2 : ℕ) : ℕ) : ZMod (p ^ (m + 1))) := fun x => rfl
  have hinj : Function.Injective g := by
    rintro ⟨c, l⟩ ⟨c', l'⟩ h
    have h' := congrArg (fun u : (ZMod (p ^ (m + 1)))ˣ => (u : ZMod (p ^ (m + 1)))) h
    simp only [hg] at h'
    have hc : c = c' := by
      have h2 := congrArg (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero m)) (ZMod p)) h'
      simp only [map_natCast] at h2
      push_cast at h2
      simp only [ZMod.natCast_val, ZMod.cast_id', id, ZMod.natCast_self, add_zero, one_pow, mul_one,
        ZMod.pow_card_pow] at h2
      exact Units.ext h2
    subst hc
    have hu : IsUnit ((((c : ZMod p).val ^ (p ^ m) : ℕ) : ZMod (p ^ (m + 1)))) :=
      (ZMod.isUnit_iff_coprime _ _).2 (Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) (hcop c 0))
    have h3 : ((1 + p : ZMod (p ^ (m + 1)))) ^ (l : ℕ) = (1 + p) ^ (l' : ℕ) := by
      rw [Nat.cast_mul, Nat.cast_mul] at h'
      have h4 := hu.mul_left_cancel h'
      push_cast at h4
      exact h4
    have hu1 : IsUnit ((1 + p : ℕ) : ZMod (p ^ (m + 1))) := by
      refine (ZMod.isUnit_iff_coprime _ _).2 ?_
      have h5 := Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) (hcop c 1)
      rwa [pow_one] at h5
    obtain ⟨u, hu⟩ := hu1
    push_cast at hu
    have h6 : u ^ (l : ℕ) = u ^ (l' : ℕ) := Units.ext (by push_cast [hu]; exact h3)
    rw [pow_inj_mod, ← orderOf_units, hu, ZMod.orderOf_one_add_prime hpp hp2, Nat.mod_eq_of_lt l.2,
      Nat.mod_eq_of_lt l'.2] at h6
    exact Prod.ext rfl (Fin.ext h6)
  have hcard : Fintype.card ((ZMod p)ˣ × Fin (p ^ m)) = Fintype.card (ZMod (p ^ (m + 1)))ˣ := by
    rw [Fintype.card_prod, ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, Fintype.card_fin,
      Nat.totient_prime_pow_succ hpp, Nat.totient_prime hpp]
    ring
  have hbij : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, hcard⟩
  rw [← Fintype.sum_bijective g hbij (fun x => f (g x : ZMod (p ^ (m + 1)))) (fun b => f b)
    (fun _ => rfl), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact Fin.sum_univ_eq_sum_range
    (fun l => f ((((c : ZMod p).val ^ (p ^ m) * (1 + p) ^ l : ℕ)) : ZMod (p ^ (m + 1)))) (p ^ m)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumVonMangoldtDivSqIocLe
section
open Finset ArithmeticFunction

namespace GlobalTheory

theorem sum_von_mangoldt_div_sq_Ioc_le
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (K : ℕ) (hK : 1 ≤ K) (M : ℕ) (hM : K ≤ M) :
    ∑ m ∈ Ioc K M, Λ m / (m : ℝ) ^ 2 ≤
      (∑ n ∈ Icc 1 M, Λ n) / (M : ℝ) ^ 2 + 4 / (K : ℝ) - 4 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    have : 0 ≤ (∑ n ∈ Icc 1 K, Λ n) / (K : ℝ) ^ 2 :=
      div_nonneg (sum_nonneg fun _ _ => vonMangoldt_nonneg) (sq_nonneg _)
    simp only [Ioc_self, sum_empty]
    linarith
  | succ M hM ih =>
    rw [sum_Ioc_succ_top hM, sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hψ := h M
    set ψ := ∑ n ∈ Icc 1 M, Λ n
    push_cast
    have key : ψ / (M : ℝ) ^ 2 - ψ / ((M : ℝ) + 1) ^ 2 ≤ 4 / (M : ℝ) - 4 / ((M : ℝ) + 1) := by
      have e1 : ψ / (M : ℝ) ^ 2 - ψ / ((M : ℝ) + 1) ^ 2
          = ψ * ((2 * M + 1) / ((M : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2)) := by
        field_simp; ring
      have e2 : 4 / (M : ℝ) - 4 / ((M : ℝ) + 1)
          = 2 * M * ((2 * M + 2) / ((M : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2)) := by
        field_simp; ring
      rw [e1, e2]
      apply mul_le_mul hψ _ (by positivity) (by positivity)
      gcongr
      norm_num
    rw [add_div]
    linarith

theorem sum_vonMangoldt_div_sq_Ioc_le
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (K : ℕ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ m ∈ Ioc K M, Λ m / (m : ℝ) ^ 2 ≤ 4 / (K : ℝ) := by
  rcases le_total K M with hM | hM
  · have h1 := sum_von_mangoldt_div_sq_Ioc_le h K hK M hM
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have h2 : (∑ n ∈ Icc 1 M, Λ n) / (M : ℝ) ^ 2 ≤ 4 / (M : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hM0]
      have := h M
      nlinarith
    linarith
  · rw [Ioc_eq_empty (by omega), sum_empty]
    positivity

theorem sum_cn_isSquare_le
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (x : ℝ) (hx : 1 ≤ x) (N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (fun n => IsSquare n), Formalism.HermitianLattices.GL2PrimeSums.cn x n ≤ 10 * Real.sqrt x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hcn : ∀ n : ℕ, 0 ≤ Formalism.HermitianLattices.GL2PrimeSums.cn x n := fun n =>
    mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (div_nonneg hx0 (Nat.cast_nonneg _)))
  set y := Real.sqrt x with hy
  have hy1 : 1 ≤ y := Real.one_le_sqrt.mpr hx
  have hyy : y * y = x := Real.mul_self_sqrt hx0
  set K : ℕ := ⌊y⌋₊ with hKdef
  have hK1 : 1 ≤ K := Nat.le_floor (by simpa using hy1)
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hKy : (K : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyK : y < K + 1 := Nat.lt_floor_add_one y
  have hsub : (Icc 1 N).filter (fun n => IsSquare n) ⊆ (Icc 1 K ∪ Ioc K N).image (fun m => m ^ 2) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, r, rfl⟩ := hn
    refine mem_image.mpr ⟨r, ?_, sq r⟩
    have hr : 1 ≤ r := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    have hrN : r ≤ N := le_trans (Nat.le_mul_self r) h2
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 K) (Ioc K N) := by
    rw [disjoint_left]
    intro a h1 h2
    simp only [mem_Icc, mem_Ioc] at h1 h2
    omega
  have hA : ∑ m ∈ Icc 1 K, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ 2 * y := by
    calc ∑ m ∈ Icc 1 K, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ ∑ m ∈ Icc 1 K, Λ m := by
          refine sum_le_sum fun m _ => ?_
          unfold Formalism.HermitianLattices.GL2PrimeSums.cn
          rw [vonMangoldt_apply_pow (by norm_num)]
          exact mul_le_of_le_one_right vonMangoldt_nonneg (min_le_left _ _)
      _ ≤ 2 * (K : ℝ) := h K
      _ ≤ 2 * y := by linarith
  have hB : ∑ m ∈ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ 8 * y := by
    calc ∑ m ∈ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ ∑ m ∈ Ioc K N, x * (Λ m / (m : ℝ) ^ 2) := by
          refine sum_le_sum fun m _ => ?_
          unfold Formalism.HermitianLattices.GL2PrimeSums.cn
          rw [vonMangoldt_apply_pow (by norm_num)]
          calc Λ m * min 1 (x / ((m ^ 2 : ℕ) : ℝ)) ≤ Λ m * (x / ((m ^ 2 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) vonMangoldt_nonneg
            _ = x * (Λ m / (m : ℝ) ^ 2) := by push_cast; ring
      _ = x * ∑ m ∈ Ioc K N, Λ m / (m : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ x * (4 / (K : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_vonMangoldt_div_sq_Ioc_le h K hK1 N) hx0
      _ ≤ 8 * y := by
          rw [← mul_div_assoc, div_le_iff₀ (by linarith), ← hyy]
          nlinarith
  calc ∑ n ∈ (Icc 1 N).filter (fun n => IsSquare n), Formalism.HermitianLattices.GL2PrimeSums.cn x n
      ≤ ∑ n ∈ (Icc 1 K ∪ Ioc K N).image (fun m => m ^ 2), Formalism.HermitianLattices.GL2PrimeSums.cn x n :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hcn n
    _ = ∑ m ∈ Icc 1 K ∪ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) :=
        sum_image fun a _ b _ hab => Nat.pow_left_injective (by norm_num : 2 ≠ 0) hab
    _ = ∑ m ∈ Icc 1 K, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) + ∑ m ∈ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) :=
        sum_union hdisj
    _ ≤ 10 * y := by linarith

theorem remainder_smooth_rough_bound : Formalism.HermitianLattices.GL2a2.SizeR := by
  intro hψ
  have h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ) := fun M => by
    simpa using hψ M (Nat.cast_nonneg M)
  obtain ⟨C, hC⟩ := prime_power_von_mangoldt_sum_bound
  refine ⟨max C 10, fun ε hε _ x hx m₀ hm₀ hp => ?_⟩
  unfold Formalism.HermitianLattices.GL2a2.Rsum
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h10 : (10 : ℝ) ≤ max C 10 := le_max_right _ _
  have hw : 0 ≤ x ^ (ε / 5) := Real.rpow_nonneg hx0.le _
  have h1 := sum_cn_isSquare_le h x (by linarith) ⌊x ^ (400 : ℝ)⌋₊
  rw [Real.sqrt_eq_rpow] at h1
  have hs : 0 ≤ x ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
  set S := m₀.primeFactors.filter (fun p => p ≤ ⌊x ^ (400 : ℝ)⌋₊) with hS
  have hsub : S ⊆ Icc 1 ⌊x ^ (ε / 5)⌋₊ := by
    intro p hpS
    simp only [hS, mem_filter, Nat.mem_primeFactors] at hpS
    obtain ⟨⟨hpp, hd, _⟩, hle⟩ := hpS
    refine mem_Icc.mpr ⟨hpp.one_le, Nat.le_floor ?_⟩
    rcases hp p hpp hd with h' | h'
    · exact h'
    · exfalso
      have : (p : ℝ) ≤ x ^ (400 : ℝ) :=
        (Nat.le_floor_iff (Real.rpow_nonneg hx0.le _)).mp hle
      linarith
  have hcard : (S.card : ℝ) ≤ x ^ (ε / 5) := by
    have := card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact le_trans (by exact_mod_cast this) (Nat.floor_le hw)
  have h2 : ∑ p ∈ S, Formalism.HermitianLattices.GL2a2.sP x p ≤ max C 10 * (x ^ (ε / 5) * Real.log x) := by
    calc ∑ p ∈ S, Formalism.HermitianLattices.GL2a2.sP x p ≤ S.card • (max C 10 * Real.log x) := by
          refine sum_le_card_nsmul _ _ _ fun p hpS => ?_
          have hpp : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hpS).1
          exact (hC x hx p hpp).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
      _ = (S.card : ℝ) * (max C 10 * Real.log x) := nsmul_eq_mul _ _
      _ ≤ x ^ (ε / 5) * (max C 10 * Real.log x) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg (by linarith) hlog)
      _ = max C 10 * (x ^ (ε / 5) * Real.log x) := by ring
  have h3 : 10 * x ^ ((1 : ℝ) / 2) ≤ max C 10 * x ^ ((1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right h10 hs
  rw [mul_add]
  linarith

end GlobalTheory
end

