import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0021
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0015
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0016
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0023
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSkewValue
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open HermitianSublattices idealPowerSpanBounds

section Abstract

variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]

theorem card_skew_lift [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a)) (H : Matrix m m A) (hH : Hᴴ = H)
    (hS : ∀ S ∈ hermSub m (RingHom.ker π), ∃ Y : Matrix m m A, H * Y + Yᴴ * H = S) :
    Nat.card {Y : Matrix m m A // H * Y + Yᴴ * H = 0} * Nat.card (hermSub m (RingHom.ker π)) =
      Nat.card (entSub m m (RingHom.ker π)) *
        Nat.card {Y' : Matrix m m A' // H.map π * Y' + Y'ᴴ * H.map π = 0} := by
  have hgH : ∀ Y : Matrix m m A, (H * Y + Yᴴ * H)ᴴ = H * Y + Yᴴ * H := by
    intro Y
    rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH,
      add_comm]
  have h1 := card_uniform (⊤ : AddSubgroup (Matrix m m A)) (hermSub m (RingHom.ker π))
    (fun Y : Matrix m m A => H * Y + Yᴴ * H) (fun _ => True) (fun _ _ _ => Iff.rfl) (by
      intro X _ _
      refine ⟨AddMonoidHom.mk' (fun Y => H * Y.1 + Y.1ᴴ * H) (fun a b => by
        simp only [AddSubgroup.coe_add, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]; abel),
        ?_, ?_⟩
      · intro Y
        show H * (X + Y.1) + (X + Y.1)ᴴ * H = H * X + Xᴴ * H + (H * Y.1 + Y.1ᴴ * H)
        simp only [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
        abel
      · intro S hS'
        obtain ⟨Y, h⟩ := hS S hS'
        exact ⟨⟨Y, trivial⟩, h⟩)
  have e0 : {Y : Matrix m m A // H * Y + Yᴴ * H = 0} ≃
      {Y : Matrix m m A // True ∧ H * Y + Yᴴ * H = 0} :=
    Equiv.subtypeEquivRight fun X => by rw [true_and]
  rw [Nat.card_congr e0, ← h1]
  have hsurj : Function.Surjective (π.toAddMonoidHom.mapMatrix (m := m) (n := m)) := by
    intro X'
    choose f hf using hπ
    exact ⟨X'.map f, by ext i j; simp [hf]⟩
  have h2 := card_preimage (π.toAddMonoidHom.mapMatrix (m := m) (n := m)) hsurj
    (fun Y' => H.map π * Y' + Y'ᴴ * H.map π = 0)
  have hker : (π.toAddMonoidHom.mapMatrix (m := m) (n := m)).ker = entSub m m (RingHom.ker π) := by
    ext X
    rw [AddMonoidHom.mem_ker, mem_entSub]
    constructor
    · intro h i j
      have := congrFun (congrFun h i) j
      exact this
    · intro h
      ext i j
      exact h i j
  rw [← hker, ← h2]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun X => ?_)
  show _ ↔ H.map π * X.map π + (X.map π)ᴴ * H.map π = 0
  have hm : H.map π * X.map π + (X.map π)ᴴ * H.map π = (H * X + Xᴴ * H).map π := by
    rw [Matrix.map_add π (map_add π), Matrix.map_mul, Matrix.map_mul,
      conjTranspose_map π (fun a => hπs a)]
  rw [hm, mem_hermSub, true_and]
  constructor
  · rintro ⟨-, h3⟩
    ext i j
    exact h3 i j
  · intro h3
    exact ⟨hgH X, fun i j => congrFun (congrFun h3 i) j⟩

end Abstract

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

abbrev Hq (H : Matrix κ κ (𝓞 K)) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))

variable [Fact (IsFixF K F)]

theorem exists_theta_inv (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    ∃ θ e : 𝓞 K ⧸ extP K 𝔭 ^ k, (θ - star θ) * e = 1 := by
  obtain ⟨θ, hθ⟩ := exists_theta hK (Fact.out : IsFixF K F) h𝔭
  obtain ⟨e, he⟩ := exists_inv_theta hθ k
  refine ⟨Ideal.Quotient.mk _ θ, Ideal.Quotient.mk _ e, ?_⟩
  rw [star_mk, ← map_sub, ← map_mul, ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq]
  exact he

theorem Hq_conjTranspose {H : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (Hq H 𝔭 k)ᴴ = Hq H 𝔭 k := by
  conv_rhs => rw [← hH]
  exact (conjTranspose_map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) (fun a => (star_mk 𝔭 k a).symm)).symm

theorem exists_skew_value (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H E₀ : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H) {d : 𝓞 F} {e : ℕ} (hd : d ∉ 𝔭 ^ (e + 1))
    (hHE : H * E₀ = algebraMap (𝓞 F) (𝓞 K) d • (1 : Matrix κ κ (𝓞 K))) {j : ℕ} (hj : e ≤ j)
    (S : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1))) (hS : S ∈ hermSub κ (RingHom.ker (piQ K 𝔭 j))) :
    ∃ Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1)),
      Hq H 𝔭 (j + 1) * Y + Yᴴ * Hq H 𝔭 (j + 1) = S := by
  obtain ⟨θ, u, hu⟩ := exists_theta_inv hK h𝔭 (j + 1)
  have hτ : θ * u + star (θ * u) = 1 := by
    rw [star_mul', star_inv_eq_neg hu]
    linear_combination hu
  set mk := Ideal.Quotient.mk (extP K 𝔭 ^ (j + 1)) with hmk
  set dq := mk (algebraMap (𝓞 F) (𝓞 K) d) with hdq
  have hds : star dq = dq := by
    rw [hdq, hmk, star_mk, star_def, conjO_map Fact.out]
  have hfill : ∀ a b, ∃ r : 𝓞 K, S a b = dq * mk r := by
    intro a b
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (S a b)
    have hs' : s ∈ extP K 𝔭 ^ j := by
      rw [← mk_mem_ker_piQ, hs]
      exact hS.2 a b
    obtain ⟨r, -, hr⟩ := exists_fillO h𝔭 hd hj hs'
    refine ⟨r, ?_⟩
    rw [← hs, hdq, ← map_mul]
    exact Ideal.Quotient.eq.2 hr
  choose r hr using hfill
  set R : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1)) := Matrix.of fun a b => mk (r a b) with hR
  have hSR : S = dq • R := by
    ext a b
    rw [hr a b]
    rfl
  have hSR' : S = dq • Rᴴ := by
    conv_lhs => rw [← hS.1, hSR, conjTranspose_smul, hds]
  have hHEq : Hq H 𝔭 (j + 1) * E₀.map mk = dq • (1 : Matrix κ κ _) := by
    rw [← Matrix.map_mul, hHE]
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]
    rw [apply_ite mk, map_one, map_zero]
  have hEH : (E₀.map mk)ᴴ * Hq H 𝔭 (j + 1) = dq • (1 : Matrix κ κ _) := by
    have := congrArg conjTranspose hHEq
    rwa [conjTranspose_mul, Hq_conjTranspose hH, conjTranspose_smul, conjTranspose_one, hds] at this
  refine ⟨E₀.map mk * ((θ * u) • R), ?_⟩
  rw [← Matrix.mul_assoc, hHEq, conjTranspose_mul, Matrix.mul_assoc, hEH, conjTranspose_smul,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_comm dq, ← hSR,
    smul_comm dq, ← hSR', ← add_smul, hτ, one_smul]

theorem card_sigma_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H E₀ : Matrix κ κ (𝓞 K)} (hH : Hᴴ = H) {d : 𝓞 F} {e : ℕ} (hd : d ∉ 𝔭 ^ (e + 1))
    (hHE : H * E₀ = algebraMap (𝓞 F) (𝓞 K) d • (1 : Matrix κ κ (𝓞 K))) {j : ℕ} (hj : e ≤ j) :
    Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (j + 1)) //
        Hq H 𝔭 (j + 1) * Y + Yᴴ * Hq H 𝔭 (j + 1) = 0} =
      Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) *
        Nat.card {Y : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ j) // Hq H 𝔭 j * Y + Yᴴ * Hq H 𝔭 j = 0} := by
  have hF : IsFixF K F := Fact.out
  have := finite_quot (K := K) h𝔭 (j + 1)
  have h1 := card_skew_lift (piQ K 𝔭 j) (piQ_surjective 𝔭 j) (piQ_star 𝔭 j) (Hq H 𝔭 (j + 1))
    (Hq_conjTranspose hH 𝔭 (j + 1)) (exists_skew_value hK h𝔭 hH hd hHE hj)
  have hmap : (Hq H 𝔭 (j + 1)).map (piQ K 𝔭 j) = Hq H 𝔭 j := by
    ext a b
    rfl
  rw [hmap] at h1
  obtain ⟨θ, u, hu⟩ := exists_theta_inv hK h𝔭 (j + 1)
  have hst : ∀ a ∈ RingHom.ker (piQ K 𝔭 j), star a ∈ RingHom.ker (piQ K 𝔭 j) := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [piQ_star, ha, star_zero]
  have h2 := card_hermSub_sq (r := κ) hst hu
  have h3 : Nat.card (entSub κ κ (RingHom.ker (piQ K 𝔭 j))) =
      (Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2)) ^ 2 := by
    rw [card_entSub, card_ker_piQ hK hF h𝔭, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [h3] at h2
  have h4 : Nat.card (hermSub κ (RingHom.ker (piQ K 𝔭 j))) = Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) :=
    Nat.pow_left_injective (n := 2) (by norm_num) h2
  rw [h3, h4] at h1
  have hpos : 0 < Ideal.absNorm 𝔭 ^ (Fintype.card κ ^ 2) := by
    apply pow_pos
    exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact ne_bot h𝔭)
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  ring

end Formalism.HermitianLattices.Ext.L3.HU
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IntegralOfMemGenus
section
open NumberField Module
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallSum

open BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem repMass_eq_sum {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) {s : Finset (Submodule (𝓞 K) V)}
    (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) (t : K) :
    repMass h L t = ∑ M ∈ s, (repCount h M t : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) := by
  classical
  have hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := ⟨s, hsr⟩
  obtain ⟨sX, hsX, hX⟩ := StabilizerLattices.exists_pairReps hs hd hL t
  have e1 := StabilizerLattices.sum_pairs_eq_rep hs hd t hsr hsX hX
  have e2 := StabilizerLattices.sum_pairs_eq_rep hs hd t hex.choose_spec hsX hX
  simp only [repMass, dif_pos hex]
  rw [← e2, e1]

theorem integral_of_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {L M : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hM : M ∈ Formalism.HermitianLatticesTheory.genus h L) : Formalism.HermitianLatticesTheory.IsIntegralLat h M := by
  exact Formalism.HermitianLatticesTheory.genusBasic_int (IsFractionRing.injective (𝓞 K) K)
    (fun r => Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range r) h L M hM.2 hLi

theorem exists_mem_boxSet (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M) {T : ℝ} {x : V}
    (hx : x ∈ M) (hx0 : x ≠ 0) (hxT : ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T) :
    ∃ n ∈ boxSet K F T, h x x = algebraMap F K (n : F) := by
  have hsym : star (h x x) = h x x := by
    rw [← starRingEnd_apply]
    exact hs.eq x x
  obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hMi x hx x hx)
  have hy' : star (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) K y := by rw [hy]; exact hsym
  obtain ⟨n, hn⟩ := QuadraticExtensionConjugation.exists_int_of_star_eq hF y hy'
  have hkey : h x x = algebraMap F K (n : F) := by
    rw [← hy, ← hn]
    rfl
  refine ⟨n, fun φ => ?_, hkey⟩
  rw [← hkey]
  exact ⟨hd x hx0 φ, hxT φ⟩

theorem ballCount_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h M) {T : ℝ} (hT : 0 ≤ T) :
    ballCount h M T =
      1 + ∑ n ∈ (finite_boxSet hK hF T).toFinset, repCount h M (algebraMap F K (n : F)) := by
  classical
  let Fn : 𝓞 F → Finset V := fun n => (StabilizerLattices.finite_rep hd hM (algebraMap F K (n : F))).toFinset
  have hset : {x : V | x ∈ M ∧ ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T} =
      ↑(insert 0 ((finite_boxSet hK hF T).toFinset.biUnion Fn)) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
      Finset.mem_biUnion, Set.Finite.mem_toFinset, Fn]
    constructor
    · rintro ⟨hx, hxT⟩
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · obtain ⟨n, hn, he⟩ := exists_mem_boxSet hF hs hd hMi hx hx0 hxT
        exact Or.inr ⟨n, hn, hx, he⟩
    · rintro (rfl | ⟨n, hn, hx, he⟩)
      · exact ⟨M.zero_mem, fun φ => by simp [hT]⟩
      · exact ⟨hx, fun φ => by rw [he]; exact (hn φ).2⟩
  obtain ⟨φ0⟩ : Nonempty (K →+* ℂ) := inferInstance
  have h0 : (0 : V) ∉ (finite_boxSet hK hF T).toFinset.biUnion Fn := by
    simp only [Finset.mem_biUnion, Set.Finite.mem_toFinset, Fn, Set.mem_setOf_eq, not_exists, not_and]
    intro n hn _ he
    have h1 := (hn φ0).1
    rw [← he] at h1
    simp at h1
  have hdisj : ∀ n ∈ (finite_boxSet hK hF T).toFinset, ∀ m ∈ (finite_boxSet hK hF T).toFinset,
      n ≠ m → Disjoint (Fn n) (Fn m) := by
    intro n _ m _ hnm
    rw [Finset.disjoint_left]
    intro x hxn hxm
    simp only [Fn, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hxn hxm
    apply hnm
    exact RingOfIntegers.ext ((algebraMap F K).injective (hxn.2.symm.trans hxm.2))
  unfold ballCount
  rw [← Set.coe_setOf, Nat.card_coe_set_eq, hset, Set.ncard_coe_finset,
    Finset.card_insert_of_notMem h0, Finset.card_biUnion hdisj, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold repCount
  rw [← Set.coe_setOf, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (StabilizerLattices.finite_rep hd hM _)]

private theorem repCount_zero_eq_one_of_isTotPosDef {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) (M : Submodule (𝓞 K) V) :
    repCount h M 0 = 1 := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  rw [repCount, Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, M.zero_mem, by simp⟩, fun y => Subtype.ext ?_⟩
  by_contra hne
  have h1 := hd y.1 hne φ
  rw [y.2.2] at h1
  simp at h1

theorem sum_ballCount (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) {T : ℝ} (hT : 0 ≤ T) :
    ∑ M ∈ s, (ballCount h M T : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ) =
      Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F T, repMass h L (algebraMap F K (n : F)) := by
  classical
  have hM : ∀ M ∈ s, Submodule.IsLattice K M ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h M := fun M hMs =>
    ⟨(hsr.1 M hMs).1, integral_of_mem_genus hs hL hLi (hsr.1 M hMs)⟩
  have hmass : Formalism.HermitianLatticesTheory.mass h L = ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ := by
    have hex : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := ⟨s, hsr⟩
    rw [Formalism.HermitianLatticesTheory.massBasic_mass_eq h L hex]
    have e1 := repMass_eq_sum hs hd hL hsr 0
    have e2 := repMass_eq_sum hs hd hL hex.choose_spec 0
    simp only [repCount_zero_eq_one_of_isTotPosDef hd, Nat.cast_one, one_div] at e1 e2
    rw [← e2, e1]
  rw [finsum_mem_eq_finite_toFinset_sum _ (finite_boxSet hK hF T), hmass]
  have hsplit : ∀ M ∈ s, (ballCount h M T : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ) =
      ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ + ∑ n ∈ (finite_boxSet hK hF T).toFinset,
        (repCount h M (algebraMap F K (n : F)) : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) := by
    intro M hMs
    rw [ballCount_eq hK hF hs hd (hM M hMs).1 (hM M hMs).2 hT]
    push_cast
    rw [add_div, one_div, Finset.sum_div]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun n _ => (repMass_eq_sum hs hd hL hsr _).symm

end Formalism.HermitianLattices.Ext.L3.BallSum
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsoCountOneInert
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts

open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}

theorem isoCount_one_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤) :
    (isoCount (P.comap (algebraMap (𝓞 F) (𝓞 K))) 1 (diagonal u) : ℝ) =
      (Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ) ^ (m ^ 2) *
        ∏ j ∈ Finset.Icc 1 m,
          (1 - (-(Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ))⁻¹ ^ j) := by
  have hF := hFF.out
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  have e1 : extP K 𝔭 ^ 1 = P := by
    rw [pow_one]
    exact SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP
      (by rw [← conjIdeal_eq_comap]; exact hc) hθ
  let _ := Ideal.Quotient.field P
  have := NormResidues.finite_quot hP
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm 𝔭 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, NormResidues.natCard_quot, absNorm_comap_inert hK hF hP hc]
  have hσ : ∀ x, NormResidues.sigEquiv P hc (NormResidues.sigEquiv P hc x) = x := NormResidues.sigHom_sigHom P hc
  have hne : ∃ x, NormResidues.sigEquiv P hc x ≠ x := by
    refine ⟨Ideal.Quotient.mk P θ, fun h => hθ ?_⟩
    rw [NormResidues.sigEquiv_mk] at h
    exact Ideal.Quotient.eq.1 h.symm
  have h1 := UnitaryNormCounts.card_inert (m := Fin m) (Ideal.quotEquivOfEq e1) (NormResidues.sigEquiv P hc)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [star_mk, Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk, NormResidues.sigEquiv_mk]
      rfl) hσ hne _ hq (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (u i))
    (by
      intro i
      rw [star_mk, star_def, hu])
    (fun i => isUnit_mk (hunit i) 1)
  unfold isoCount
  rw [diagonal_map (map_zero _), h1]
  exact card_unitary_fin _ hσ hne _ hq m

theorem isoCount_one_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤) :
    (isoCount (P.comap (algebraMap (𝓞 F) (𝓞 K))) 1 (diagonal u) : ℝ) =
      (Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ) ^ (m ^ 2) *
        ∏ j ∈ Finset.Icc 1 m,
          (1 - ((Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ))⁻¹ ^ j) := by
  have hF := hFF.out
  have h𝔭 : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  have e1 : extP K 𝔭 ^ 1 ≤ P := by
    rw [pow_one]
    exact Ideal.map_comap_le
  let _ := Ideal.Quotient.field P
  have := NormResidues.finite_quot hP
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have := finite_quot (K := K) h𝔭 1
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm 𝔭 := by
    rw [← Nat.card_eq_fintype_card, NormResidues.natCard_quot, absNorm_comap_split hK hF hP hc]
  have hb : Function.Bijective fun a : 𝓞 K ⧸ extP K 𝔭 ^ 1 =>
      (Ideal.Quotient.factor e1 (star a), Ideal.Quotient.factor e1 a) := by
    apply Function.Surjective.bijective_of_nat_card_le
    · intro y
      obtain ⟨z, hz⟩ := NormResidues.pairHom_surjective hP hc y
      refine ⟨Ideal.Quotient.mk _ z, ?_⟩
      rw [← hz, NormResidues.pairHom_apply]
      show (Ideal.Quotient.factor e1 (star (Ideal.Quotient.mk _ z)), _) = _
      rw [star_mk]
      rfl
    · rw [absNorm_extP_pow hK hF h𝔭, Nat.card_prod, Nat.card_eq_fintype_card, hq]
      apply le_of_eq
      ring
  have h1 := UnitaryNormCounts.card_split (m := Fin m) (Ideal.Quotient.factor e1) hb
    ((diagonal u).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1)))
    (by
      rw [map_mk_conjTranspose, diagonal_conjTranspose]
      congr 2
      funext i
      exact hu i)
    (by
      rw [diagonal_map (map_zero _), det_diagonal]
      exact Finset.univ.prod_induction _ IsUnit (fun _ _ h1 h2 => h1.mul h2) isUnit_one
        (fun i _ => isUnit_mk (hunit i) 1))
  unfold isoCount
  rw [h1]
  exact card_GL_fin _ hq m

theorem isoCount_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) :
    (isoCount 𝔭 1 (diagonal u) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2) * alphaStd K 𝔭 m := by
  have hF := hFF.out
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  unfold alphaStd
  rw [etaF_comap hK hF hP]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · rw [isoCount_one_inert hK hP hc u hu hunit, if_pos hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, ← mul_pow, inv_neg]
    congr 2
    ring
  · rw [isoCount_one_split hK hP hc u hu hunit, if_neg hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, one_pow, one_mul]

theorem isoCount_diag (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) (k : ℕ) :
    (isoCount 𝔭 (k + 1) (diagonal u) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((k + 1) * m ^ 2) * alphaStd K 𝔭 m := by
  have hg : (diagonal u)ᴴ = diagonal u := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact hu i
  have hdet : Ideal.span {(diagonal u).det} ⊔ extP K 𝔭 = ⊤ := by
    rw [Matrix.det_diagonal, ← Ideal.prod_span_singleton]
    exact Ideal.prod_sup_eq_top fun i _ => hunit i
  rw [isoCount_eq_pow hK h𝔭 (diagonal u) hg hdet k]
  push_cast
  rw [isoCount_one hK h𝔭 u hu hunit]
  ring

end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
end
end

