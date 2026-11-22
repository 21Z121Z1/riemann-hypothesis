import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearDescentToBaseChangeOfForm
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_semilinear_descent_to_baseChange :
  ∀ {LL : Type} [Field LL] [Algebra ℚ LL] (L0 : IntermediateField ℚ LL) {Ks : Type} [Field Ks] [Algebra Ks LL]
    (kKs : Ks →+* L0), (∀ x, ((kKs x : L0) : LL) = algebraMap Ks LL x) →
    ∀ {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    (WK : Submodule Ks WL) {n : ℕ} (bs : Fin n → WL), (∀ i, bs i ∈ WK) →
    Submodule.span Ks (Set.range bs) = WK → LinearIndependent LL bs → Submodule.span LL (Set.range bs) = ⊤ →
    ∀ {KT : Type} [Field KT] [Algebra Ks KT] (rd : L0 →+* KT), (∀ s, algebraMap Ks KT s = rd (kKs s)) →
    ∃ Φ : WL →+ KT ⊗[Ks] WK, (∀ (c : L0) (x : WL), Φ ((c : LL) • x) = rd c • Φ x) ∧
      (∀ (f : WL →ₗ[LL] WL) (fr : WK →ₗ[Ks] WK), (∀ w : WK, (fr w : WL) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange KT fr (Φ x)) ∧
      ∀ w : WK, Φ (w : WL) = (1 : KT) ⊗ₜ[Ks] w := by
  intro LL _ _ L0 Ks _ _ kKs hk WL _ _ _ _ WK n bs hb hKs hLi hLs KT _ _ rd hrd
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L0 LL)
    (LinearMap.ker_eq_bot.mpr (algebraMap L0 LL).injective)
  have hπ1 : π 1 = 1 := by
    have := LinearMap.congr_fun hπ 1
    simpa using this
  have hπx : ∀ (c : L0) (y : LL), π ((c : LL) * y) = c * π y := by
    intro c y
    have : ((c : LL) * y) = c • y := (Algebra.smul_def c y).symm
    rw [this, map_smul, smul_eq_mul]
  obtain ⟨B, hB⟩ : ∃ B : Module.Basis (Fin n) LL WL, ∀ k, B k = bs k :=
    ⟨Module.Basis.mk hLi (by rw [hLs]), fun k => Module.Basis.mk_apply _ _ k⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : WL →+ KT ⊗[Ks] WK,
      ∀ x, Φ x = ∑ k, rd (π (B.repr x k)) • ((1 : KT) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK)) :=
    ⟨{ toFun := fun x => ∑ k, rd (π (B.repr x k)) • ((1 : KT) ⊗ₜ[Ks] (⟨bs k, hb k⟩ : WK))
       map_zero' := by simp
       map_add' := by intro x y; simp [map_add, add_smul, Finset.sum_add_distrib] },
     fun _ => rfl⟩
  have key : ∀ (l : LL) (w : WK), Φ (l • (w : WL)) = rd (π l) • ((1 : KT) ⊗ₜ[Ks] w) := by
    intro l w
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun Ks).mp
      (show (w : WL) ∈ Submodule.span Ks (Set.range bs) by rw [hKs]; exact w.2)
    have hw : w = ∑ k, s k • (⟨bs k, hb k⟩ : WK) := by
      apply Subtype.ext; simp [hs]
    have hrep : ∀ k, B.repr (l • (w : WL)) k = l * algebraMap Ks LL (s k) := by
      have : l • (w : WL) = ∑ k, (l * algebraMap Ks LL (s k)) • B k := by
        rw [← hs, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hB, mul_smul, algebraMap_smul]
      intro k
      rw [this, B.repr_sum_self]
    rw [hΦ]
    conv_rhs => rw [hw, TensorProduct.tmul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrep, ← hk, mul_comm, hπx, map_mul, ← hrd, TensorProduct.tmul_smul, ← algebraMap_smul KT (s k),
      smul_smul, mul_comm]
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro c x
    rw [hΦ, hΦ x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hπx, map_mul, mul_smul]
  · intro f fr hf x
    conv_lhs => rw [← B.sum_repr x]
    rw [map_sum, map_sum, hΦ x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hB, ← hf ⟨bs k, hb k⟩, key, map_smul, LinearMap.baseChange_tmul]
  · intro w
    have := key 1 w
    rw [one_smul, hπ1, map_one, one_smul] at this
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulEqZeroOfCrossed
section
set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.TransferCommutator

theorem exists_smul_eq_zero_of_crossed {G : Type} [Group G] [Finite G] {R : Type} [CommRing R] (ε : R →+* ℤ)
    (ρ : G → R) (hρ : ∀ g, ε (ρ g) = 1) {X : Type} [AddCommGroup X] [Module R X] (d : G → X)
    (hd : ∀ g h, d (g * h) = d g + ρ g • d h) :
    ∃ μ : R, (ε μ).natAbs = Nat.card (Abelianization G) ∧ ∀ g, μ • d g = 0 := by
  classical
  have := Fintype.ofFinite G
  let J : Submodule R X := (Submodule.pi Set.univ fun _ : G => RingHom.ker ε).map (Fintype.linearCombination R d)
  let ψ : G →* Multiplicative (X ⧸ J) := MonoidHom.mk' (fun g => Multiplicative.ofAdd (J.mkQ (d g))) fun g h => by
    rw [← ofAdd_add, ← map_add]
    congr 1
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hd]
    refine ⟨Pi.single h (ρ g - 1), fun i _ => ?_, ?_⟩
    · by_cases hi : i = h
      · subst hi; simp [RingHom.mem_ker, hρ]
      · simp [hi]
    · rw [Fintype.linearCombination_apply_single, sub_smul, one_smul]; abel
  let ψ' : Additive (Abelianization G) →ₗ[ℤ] X ⧸ J :=
    (MonoidHom.toAdditiveLeft (Abelianization.lift ψ)).toIntLinearMap
  have hψ' : ∀ g, ψ' (Additive.ofMul (Abelianization.of g)) = J.mkQ (d g) := fun g => rfl
  let L : (G → ℤ) →ₗ[ℤ] Additive (Abelianization G) :=
    Fintype.linearCombination ℤ fun g => Additive.ofMul (Abelianization.of g)
  have hL : Function.Surjective L := fun q => by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (s := commutator G) q.toMul
    exact ⟨Pi.single g 1, by rw [Fintype.linearCombination_apply_single, one_smul]; exact congrArg Additive.ofMul hg⟩
  have eq := L.quotKerEquivOfSurjective hL
  have hfin : Finite (Abelianization G) := inferInstanceAs (Finite (G ⧸ commutator G))
  have : Finite ((G → ℤ) ⧸ LinearMap.ker L) := Finite.of_equiv _ eq.symm.toEquiv
  let e : (G → ℤ) ≃ₗ[ℤ] LinearMap.ker L :=
    LinearEquiv.ofFinrankEq _ _ ((Submodule.finiteQuotient_iff _).1 this).symm
  have hdet := Submodule.natAbs_det_equiv (LinearMap.ker L) e
  have hrel : ∀ n : LinearMap.ker L, ∃ ν : G → R, (∀ i, ε (ν i) = n.1 i) ∧ ∑ i, ν i • d i = 0 := fun n => by
    have h0 : ∑ i, n.1 i • d i ∈ J := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
      have := congrArg ψ' n.2
      rw [map_zero, Fintype.linearCombination_apply, map_sum] at this
      simpa only [map_zsmul, hψ'] using this
    obtain ⟨ν, hν, hs⟩ := h0
    refine ⟨fun i => (n.1 i : R) - ν i, fun i => ?_, ?_⟩
    · rw [map_sub, (RingHom.mem_ker).1 (hν i trivial)]; simp
    · simp only [sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul]
      rw [← hs, Fintype.linearCombination_apply, sub_self]
  choose ν hν hs using hrel
  let M : Matrix G G R := Matrix.of fun j i => ν (e (Pi.single j 1)) i
  refine ⟨M.det, ?_, fun k => ?_⟩
  · rw [RingHom.map_det, ← Matrix.det_transpose, ← Nat.card_congr (eq.toEquiv.trans Additive.toMul), ← hdet,
      ← LinearMap.det_toMatrix']
    congr 2
    ext i j
    simp [M, hν, LinearMap.toMatrix'_apply]
  · have h1 : M.det • d k = ∑ i, (M.adjugate * M) k i • d i := by
      rw [Matrix.adjugate_mul]
      simp [Matrix.one_apply]
    rw [h1]
    simp only [Matrix.mul_apply, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.smul_sum]
    exact (congrArg _ (hs _)).trans (smul_zero _)

theorem transfer_eq_one (G : Type) [Group G] [Finite G] (B : Type) [CommGroup B] (φ : commutator G →* B) :
    MonoidHom.transfer φ = 1 := by
  classical
  let Q := Abelianization G
  have hfin : Finite Q := inferInstanceAs (Finite (G ⧸ commutator G))
  let : Fintype Q := (commutator G).fintypeQuotientOfFiniteIndex
  let R := MonoidAlgebra ℤ Q
  let T : (commutator G).LeftTransversal := default
  let α : Q → G := fun q => (T.2.leftQuotientEquiv q : G)
  have hα : ∀ q, Abelianization.of (α q) = q := fun q => T.2.leftQuotientEquiv.symm_apply_apply q
  have hmem : ∀ g q, (α q)⁻¹ * g * α ((Abelianization.of g)⁻¹ * q) ∈ commutator G := fun g q => by
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    simp [hα]
  let b : G → Q → Additive B := fun g q => Additive.ofMul (φ ⟨_, hmem g q⟩)
  have hb : ∀ g h q, b (g * h) q = b g q + b h ((Abelianization.of g)⁻¹ * q) := fun g h q => by
    simp only [b]
    rw [← ofMul_mul, ← map_mul]
    congr 2
    ext
    simp [mul_assoc]
  let s : Q →* R := MonoidAlgebra.of ℤ Q
  let ε : R →ₐ[ℤ] ℤ := MonoidAlgebra.lift ℤ ℤ Q 1
  let d : G → (R ⊗[ℤ] Additive B) × R := fun g => (∑ q, s q ⊗ₜ b g q, s (Abelianization.of g) - 1)
  obtain ⟨μ, hμ, h0⟩ := exists_smul_eq_zero_of_crossed (ε : R →+* ℤ) (fun g => s (Abelianization.of g))
    (fun g => MonoidAlgebra.lift_of _ _) d fun g h => by
      refine Prod.ext ?_ ?_
      · simp only [d, Prod.fst_add, Prod.smul_fst, hb, TensorProduct.tmul_add, Finset.sum_add_distrib,
          Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, ← map_mul]
        congr 1
        exact (Fintype.sum_equiv (Equiv.mulLeft (Abelianization.of g)) _ _ fun q => by simp).symm
      · simp only [d, Prod.snd_add, Prod.smul_snd, map_mul, smul_eq_mul]; ring
  have hinv : ∀ q, μ * s q = μ := fun q => by
    have := congrArg Prod.snd (h0 (α q))
    simp only [d, Prod.smul_snd, hα, smul_eq_mul, mul_sub, mul_one, Prod.snd_zero] at this
    exact sub_eq_zero.1 this
  have hc : ∀ q, μ.coeff q = μ.coeff 1 := fun q => by
    have := MonoidAlgebra.coeff_mul_single_apply μ 1 q⁻¹ 1
    rw [show μ * MonoidAlgebra.single q⁻¹ 1 = μ from hinv q⁻¹] at this
    rw [inv_inv, one_mul, mul_one] at this
    exact this.symm
  have hε : ε μ = (Nat.card Q : ℤ) * μ.coeff 1 := by
    simp only [ε]
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [hc]
  have hu : (μ.coeff 1).natAbs = 1 := by
    rw [show (ε : R →+* ℤ) μ = _ from hε, Int.natAbs_mul, Int.natAbs_natCast] at hμ
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q)) (hμ.trans (mul_one _).symm)
  let c : R →ₗ[ℤ] ℤ := Finsupp.lapply (1 : Q) ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℤ (S := ℤ) (M := Q)).toLinearMap
  ext g
  have h1 := congrArg Prod.fst (h0 g)
  simp only [d, Prod.smul_fst, Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, hinv, Prod.fst_zero,
    ← TensorProduct.tmul_sum] at h1
  have h2 := congrArg (fun x => TensorProduct.lid ℤ _ (c.rTensor _ x)) h1
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero] at h2
  have h3 : ∑ q, b g q = 0 := by
    rcases Int.natAbs_eq_iff.1 hu with h | h
    · rw [show c μ = _ from h] at h2; simpa using h2
    · rw [show c μ = _ from h] at h2; simpa using h2
  rw [MonoidHom.transfer_def φ T, MonoidHom.one_apply]
  have h4 : ∏ q, (b g q).toMul = 1 := by rw [← toMul_sum, h3, toMul_zero]
  refine Eq.trans (Finset.prod_congr rfl fun q _ => congrArg φ (Subtype.ext ?_)) h4
  simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_assoc]
  rfl

end GlobalTheory.TransferCommutator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemSpanIntegers
section
namespace GlobalTheory.SmulMemSpanIntegers

theorem exists_smul_mem_span_integers {Ks : Type} [Field Ks] [NumberField Ks] {WL : Type}
    [AddCommGroup WL] [Module Ks WL] [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {T : Set WL} {g : WL}
    (hg : g ∈ Submodule.span Ks T) :
    ∃ d : NumberField.RingOfIntegers Ks, d ≠ 0 ∧
      d • g ∈ Submodule.span (NumberField.RingOfIntegers Ks) T := by

  induction hg using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨d₁, hd₁, h₁⟩ := ihx
    obtain ⟨d₂, hd₂, h₂⟩ := ihy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (x + y) = d₂ • (d₁ • x) + d₁ • (d₂ • y) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm d₁ d₂ x]
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  | smul c x _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers Ks) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap (NumberField.RingOfIntegers Ks) Ks b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ Ks)).2 hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have e : b • ((algebraMap (NumberField.RingOfIntegers Ks) Ks a /
        algebraMap (NumberField.RingOfIntegers Ks) Ks b) • x) = a • x := by
      rw [← smul_assoc, Algebra.smul_def, mul_div_cancel₀ _ hbK, algebraMap_smul]
    rw [mul_comm, mul_smul, e, smul_comm]
    exact Submodule.smul_mem _ _ h

end GlobalTheory.SmulMemSpanIntegers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossZeroOfExpTwoPiIBound
section
open Metric Filter Topology Set

namespace GlobalTheory.PuncturedDiscExtension

theorem analyticAt_update_of_bdd {F : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z)
    (hb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖F z‖ ≤ B) :
    AnalyticAt ℂ (Function.update F 0 (limUnder (𝓝[≠] (0:ℂ)) F)) 0 := by
  obtain ⟨B, hB⟩ := hb
  have ht : Tendsto F (𝓝[≠] (0:ℂ)) (𝓝 (limUnder (𝓝[≠] (0:ℂ)) F)) := by
    apply Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd
    refine isBoundedUnder_of_eventually_le (a := B + ‖F 0‖) ?_
    filter_upwards [hB] with z hz
    exact (norm_sub_le _ _).trans (by linarith)
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · rw [eventually_nhdsWithin_iff] at hd ⊢
    filter_upwards [hd] with z hz hz0
    have heq : Function.update F 0 (limUnder (𝓝[≠] (0:ℂ)) F) =ᶠ[𝓝 z] F := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      exact Function.update_of_ne hw _ _
    exact (hz hz0).congr_of_eventuallyEq heq
  · exact continuousAt_update_same.2 ht

theorem bdd_of_re_le {F : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z)
    {M : ℝ} (hM : ∀ᶠ z in 𝓝[≠] (0:ℂ), (F z).re ≤ M) :
    ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖F z‖ ≤ B := by
  set g : ℂ → ℂ := fun z => (F z - ((M:ℂ) + 1))⁻¹ with hg
  have hre : ∀ᶠ z in 𝓝[≠] (0:ℂ), (F z - ((M:ℂ)+1)).re ≤ -1 := by
    filter_upwards [hM] with z hz
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hne : ∀ᶠ z in 𝓝[≠] (0:ℂ), F z - ((M:ℂ)+1) ≠ 0 := by
    filter_upwards [hre] with z hz h
    rw [h, Complex.zero_re] at hz
    linarith
  have hnorm : ∀ᶠ z in 𝓝[≠] (0:ℂ), 1 ≤ ‖F z - ((M:ℂ)+1)‖ := by
    filter_upwards [hre] with z hz
    have h1 := Complex.abs_re_le_norm (F z - ((M:ℂ)+1))
    have h2 : 1 ≤ |(F z - ((M:ℂ)+1)).re| := by
      rw [abs_of_neg (by linarith)]; linarith
    linarith
  have hgd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ g z := by
    filter_upwards [hd, hne] with z h1 h2
    exact (h1.sub_const _).inv h2
  have hgb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖g z‖ ≤ B := ⟨1, by
    filter_upwards [hnorm] with z hz
    simp only [hg, norm_inv]
    exact inv_le_one_of_one_le₀ hz⟩
  have ha := analyticAt_update_of_bdd hgd hgb
  set g' := Function.update g 0 (limUnder (𝓝[≠] (0:ℂ)) g) with hg'
  have hg'eq : ∀ z, z ≠ 0 → g' z = g z := fun z hz => Function.update_of_ne hz _ _
  by_cases hL : g' 0 = 0
  · exfalso
    rcases ha.eventually_constant_or_nhds_le_map_nhds with h | h
    · have hF : ∀ᶠ z in 𝓝[≠] (0:ℂ), False := by
        filter_upwards [nhdsWithin_le_nhds h, hne, self_mem_nhdsWithin] with z h1 h2 h3
        rw [hg'eq z h3, hL] at h1
        exact inv_ne_zero h2 h1
      exact hF.exists.elim fun _ h => h
    · have hS : ∀ᶠ z in 𝓝 (0:ℂ), g' z = 0 ∨ ((g' z)⁻¹).re ≤ -1 := by
        have h0 := eventually_nhdsWithin_iff.1 hre
        filter_upwards [h0] with z hz
        by_cases hz0 : z = 0
        · left; rw [hz0]; exact hL
        · right; rw [hg'eq z hz0]; simp only [hg, inv_inv]; exact hz hz0
      have hS' : {w : ℂ | w = 0 ∨ (w⁻¹).re ≤ -1} ∈ 𝓝 (g' 0) := h hS
      rw [hL] at hS'
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS'
      have hmem : ((ε/2 : ℝ) : ℂ) ∈ ball (0:ℂ) ε := by
        rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      rcases hball hmem with h1 | h1
      · have : (ε/2 : ℝ) = 0 := by exact_mod_cast h1
        linarith
      · rw [← Complex.ofReal_inv, Complex.ofReal_re] at h1
        have : 0 < (ε/2)⁻¹ := inv_pos.2 (by linarith)
        linarith
  · have hpos : 0 < ‖g' 0‖ := norm_pos_iff.2 hL
    have hc : ContinuousAt g' 0 := ha.continuousAt
    have hev : ∀ᶠ z in 𝓝 (0:ℂ), ‖g' 0‖ / 2 < ‖g' z‖ :=
      hc.norm.eventually (lt_mem_nhds (by linarith))
    refine ⟨‖(M:ℂ)+1‖ + 2 / ‖g' 0‖, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin, hne] with z h1 h2 h3
    rw [hg'eq z h2] at h1
    have hq : 0 < ‖F z - ((M:ℂ)+1)‖ := norm_pos_iff.2 h3
    have hgz : ‖g z‖ = ‖F z - ((M:ℂ)+1)‖⁻¹ := by simp only [hg, norm_inv]
    rw [hgz] at h1
    have key : ‖F z - ((M:ℂ)+1)‖ ≤ 2 / ‖g' 0‖ := by
      have h4 := mul_lt_mul_of_pos_right h1 hq
      rw [inv_mul_cancel₀ hq.ne'] at h4
      rw [le_div_iff₀ hpos]
      nlinarith
    have h5 := norm_sub_norm_le (F z) ((M:ℂ)+1)
    linarith

end GlobalTheory.PuncturedDiscExtension

namespace GlobalTheory

open GlobalTheory.PuncturedDiscExtension in

theorem holomorphic_extension_of_exp_two_pi_I_bound :
    ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r →
      DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) →
      (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 →
        ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) →
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧
        ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t := by
  intro H r C N hr hH hC
  have hball : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ∈ ball (0:ℂ) r ∧ z ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0:ℂ) hr), self_mem_nhdsWithin]
      with z h1 h2
    exact ⟨h1, h2⟩
  have hHd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ H z := by
    filter_upwards [hball] with z hz
    exact hH.differentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz.1, hz.2⟩)
  set f : ℂ → ℂ := fun z => 2 * (Real.pi:ℂ) * Complex.I * H z with hf
  have hfd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ f z := by
    filter_upwards [hHd] with z hz
    exact hz.const_mul _
  have hfb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖f z‖ ≤ B := by
    set Gf : ℂ → ℂ := fun z => z ^ N * Complex.exp (f z) with hGf
    have hGd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ Gf z := by
      filter_upwards [hfd] with z hz
      exact (differentiableAt_id.pow N).mul hz.cexp
    have hGb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖Gf z‖ ≤ B := ⟨C, by
      filter_upwards [hball] with z hz
      have h := hC z hz.1 hz.2
      show ‖z ^ N * Complex.exp (f z)‖ ≤ C
      rw [norm_mul, norm_pow, mul_comm]
      exact h⟩
    have ha := analyticAt_update_of_bdd hGd hGb
    set G' := Function.update Gf 0 (limUnder (𝓝[≠] (0:ℂ)) Gf) with hG'
    have hG'eq : ∀ z, z ≠ 0 → G' z = Gf z := fun z hz => Function.update_of_ne hz _ _
    have hnz : ¬ ∀ᶠ z in 𝓝 (0:ℂ), G' z = 0 := by
      intro h
      have hF : ∀ᶠ z in 𝓝[≠] (0:ℂ), False := by
        filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z h1 h2
        rw [hG'eq z h2] at h1
        exact mul_ne_zero (pow_ne_zero _ h2) (Complex.exp_ne_zero _) h1
      exact hF.exists.elim fun _ h => h
    obtain ⟨k, u, hu, hu0, hGu⟩ := (ha.exists_eventuallyEq_pow_smul_nonzero_iff).2 hnz
    have hpos : 0 < ‖u 0‖ := norm_pos_iff.2 hu0
    have huc : ContinuousAt u 0 := hu.continuousAt
    have hup : ∀ᶠ z in 𝓝 (0:ℂ), ‖u z‖ < ‖u 0‖ + 1 :=
      huc.norm.eventually (gt_mem_nhds (by linarith))
    have hlo : ∀ᶠ z in 𝓝 (0:ℂ), ‖u 0‖ / 2 < ‖u z‖ :=
      huc.norm.eventually (lt_mem_nhds (by linarith))
    have h1 : ∀ᶠ z in 𝓝 (0:ℂ), ‖z‖ < 1 := by
      filter_upwards [ball_mem_nhds (0:ℂ) one_pos] with z hz
      simpa using hz
    have hrel : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ≠ 0 ∧ ‖z‖ < 1 ∧ ‖u z‖ < ‖u 0‖ + 1 ∧
        ‖u 0‖ / 2 < ‖u z‖ ∧ z ^ N * Complex.exp (f z) = z ^ k * u z := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (h1.and (hup.and (hlo.and hGu)))]
        with z hz hh
      obtain ⟨ha1, ha2, ha3, ha4⟩ := hh
      refine ⟨hz, ha1, ha2, ha3, ?_⟩
      have := hG'eq z hz
      rw [ha4, sub_zero, smul_eq_mul] at this
      exact this.symm
    rcases le_or_gt N k with hk | hk
    · refine bdd_of_re_le hfd (M := Real.log (‖u 0‖ + 1)) ?_
      filter_upwards [hrel] with z hh
      obtain ⟨hz, hz1, hu1, hu2, he⟩ := hh
      have hk' : z ^ k = z ^ N * z ^ (k - N) := by rw [← pow_add, Nat.add_sub_cancel' hk]
      rw [hk', mul_assoc] at he
      have he2 : Complex.exp (f z) = z ^ (k - N) * u z := mul_left_cancel₀ (pow_ne_zero _ hz) he
      have hn : ‖Complex.exp (f z)‖ ≤ ‖u 0‖ + 1 := by
        rw [he2, norm_mul, norm_pow]
        have : ‖z‖ ^ (k - N) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz1.le
        nlinarith [norm_nonneg (u z)]
      rw [Complex.norm_exp] at hn
      have := Real.log_le_log (Real.exp_pos _) hn
      rwa [Real.log_exp] at this
    · obtain ⟨B, hB⟩ := bdd_of_re_le (F := fun z => -f z)
        (by filter_upwards [hfd] with z hz; exact hz.neg) (M := -Real.log (‖u 0‖ / 2)) (by
        filter_upwards [hrel] with z hh
        obtain ⟨hz, hz1, hu1, hu2, he⟩ := hh
        have hN : z ^ N = z ^ k * z ^ (N - k) := by rw [← pow_add, Nat.add_sub_cancel' hk.le]
        rw [hN, mul_assoc] at he
        have he2 : z ^ (N - k) * Complex.exp (f z) = u z := mul_left_cancel₀ (pow_ne_zero _ hz) he
        have hn : ‖u 0‖ / 2 ≤ ‖Complex.exp (f z)‖ := by
          have : ‖u z‖ ≤ ‖Complex.exp (f z)‖ := by
            rw [← he2, norm_mul, norm_pow]
            have : ‖z‖ ^ (N - k) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz1.le
            nlinarith [norm_nonneg (Complex.exp (f z))]
          linarith
        rw [Complex.norm_exp] at hn
        have := Real.log_le_log (by positivity) hn
        rw [Real.log_exp] at this
        simp only [Complex.neg_re]
        linarith)
      exact ⟨B, by filter_upwards [hB] with z hz; simpa only [norm_neg] using hz⟩
  obtain ⟨B, hB⟩ := hfb
  have hHb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖H z‖ ≤ B := ⟨B / (2 * Real.pi), by
    filter_upwards [hB] with z hz
    have hf' : ‖f z‖ = 2 * Real.pi * ‖H z‖ := by
      simp only [hf, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      ring
    rw [hf'] at hz
    rw [le_div_iff₀ (by positivity)]
    linarith⟩
  have haH := analyticAt_update_of_bdd hHd hHb
  refine ⟨Function.update H 0 (limUnder (𝓝[≠] (0:ℂ)) H), ?_,
    fun t _ ht => Function.update_of_ne ht _ _⟩
  intro z hz
  by_cases h0 : z = 0
  · subst h0
    exact haH.differentiableAt.differentiableWithinAt
  · have hzd : DifferentiableAt ℂ H z :=
      hH.differentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz, h0⟩)
    have heq : Function.update H 0 (limUnder (𝓝[≠] (0:ℂ)) H) =ᶠ[𝓝 z] H := by
      filter_upwards [isOpen_ne.mem_nhds h0] with w hw
      exact Function.update_of_ne hw _ _
    exact (hzd.congr_of_eventuallyEq heq).differentiableWithinAt

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GLUpperTriangularEqDiagonalMulUnitriangular
section
open Matrix

namespace GlobalTheory

theorem GL_upperTriangular_eq_diagonal_mul_unitriangular :
    ∀ (n : ℕ) (B : GL (Fin n) ℂ), B.val.BlockTriangular id → ∃ D U : GL (Fin n) ℂ,
      B = D * U ∧ D.val.IsDiag ∧ (∀ i, D.val i i = B.val i i) ∧
      U.val.BlockTriangular id ∧ ∀ i, U.val i i = 1 := by
  intro n B hB
  have hdet : B.val.det = ∏ i, B.val i i := Matrix.det_of_upperTriangular hB
  have hdet0 : B.val.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit).ne_zero
  have hne : ∀ i, B.val i i ≠ 0 := by
    intro i h
    apply hdet0
    rw [hdet]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  let D : GL (Fin n) ℂ :=
    ⟨diagonal (fun i => B.val i i), diagonal (fun i => (B.val i i)⁻¹),
      by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i; exact mul_inv_cancel₀ (hne i),
      by
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i; exact inv_mul_cancel₀ (hne i)⟩
  have hU : ∀ i j, (D⁻¹ * B).val i j = (B.val i i)⁻¹ * B.val i j := by
    intro i j
    change (diagonal (fun i => (B.val i i)⁻¹) * B.val) i j = _
    rw [diagonal_mul]
  refine ⟨D, D⁻¹ * B, by simp, isDiag_diagonal _, fun i => diagonal_apply_eq _ _, ?_, ?_⟩
  · intro i j hij
    rw [hU, hB hij, mul_zero]
  · intro i
    rw [hU, inv_mul_cancel₀ (hne i)]

end GlobalTheory
end

