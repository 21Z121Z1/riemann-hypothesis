import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0001

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFFS
section
noncomputable section

namespace PI.VolStabW

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k]

def cols {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) : Fin a → Fin M → k := fun j i ↦ P i j

theorem linInd_cols_iff {M a : ℕ} (P : Matrix (Fin M) (Fin a) k) :
    LinearIndependent k (cols P) ↔ ∀ v : Fin a → k, P *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  have h : ∀ v : Fin a → k, ∑ j, v j • cols P j = P *ᵥ v := by
    intro v
    ext i
    simp [cols, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  simp_rw [h]
  constructor
  · intro H v hv
    funext j
    exact H v hv j
  · intro H v hv j
    rw [H v hv]
    rfl

theorem exists_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) : ∃ L : Matrix (Fin a) (Fin M) k, L * P = 1 := by
  have hker : LinearMap.ker (Matrix.mulVecLin P) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact (linInd_cols_iff P).mp hP v (by simpa using hv)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin P) = LinearMap.toMatrix' g * P := by
    rw [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  rw [← this, hg, LinearMap.toMatrix'_id]

theorem linInd_of_left_inv {M a : ℕ} (W : Matrix (Fin a) (Fin M) k) (P : Matrix (Fin M) (Fin a) k)
    (h : W * P = 1) : LinearIndependent k (cols P) := by
  refine (linInd_cols_iff P).mpr fun v hv ↦ ?_
  have : W *ᵥ (P *ᵥ v) = (W * P) *ᵥ v := Matrix.mulVec_mulVec _ _ _
  rw [h, Matrix.one_mulVec, hv, Matrix.mulVec_zero] at this
  exact this.symm

theorem card_left_inv {M a : ℕ} (P : Matrix (Fin M) (Fin a) k)
    (hP : LinearIndependent k (cols P)) :
    Nat.card {W : Matrix (Fin a) (Fin M) k // W * P = 1} = Nat.card k ^ (a * (M - a)) := by
  classical
  obtain ⟨L, hL⟩ := exists_left_inv P hP
  let f : Matrix (Fin a) (Fin M) k →ₗ[k] Matrix (Fin a) (Fin a) k :=
    { toFun := fun W ↦ W * P
      map_add' := fun x y ↦ Matrix.add_mul x y P
      map_smul' := fun c x ↦ Matrix.smul_mul c x P }
  have hf : ∀ W, f W = W * P := fun _ ↦ rfl
  have hsurj : Function.Surjective f := fun Z ↦ ⟨Z * L, by rw [hf, Matrix.mul_assoc, hL, Matrix.mul_one]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_matrix,
    Module.finrank_matrix] at hrk
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hrk
  have hker : Module.finrank k (LinearMap.ker f) = a * (M - a) := by
    rw [Nat.mul_sub]
    omega
  let e : {W : Matrix (Fin a) (Fin M) k // W * P = 1} ≃ LinearMap.ker f :=
    { toFun := fun W ↦ ⟨W.1 - L, by
        rw [LinearMap.mem_ker, hf, Matrix.sub_mul, W.2, hL, sub_self]⟩
      invFun := fun Z ↦ ⟨Z.1 + L, by
        have h0 := Z.2
        rw [LinearMap.mem_ker, hf] at h0
        rw [Matrix.add_mul, h0, hL, zero_add]⟩
      left_inv := fun W ↦ by
        apply Subtype.ext
        simp
      right_inv := fun Z ↦ by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := k), hker]

theorem card_pairs {M a : ℕ} (ha : a ≤ M) :
    Nat.card {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  let e : {WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k // WP.1 * WP.2 = 1} ≃
      Σ P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)},
        {W : Matrix (Fin a) (Fin M) k // W * P.1 = 1} :=
    { toFun := fun x ↦ ⟨⟨x.1.2, linInd_of_left_inv x.1.1 x.1.2 x.2⟩, ⟨x.1.1, x.2⟩⟩
      invFun := fun y ↦ ⟨(y.2.1, y.1.1), y.2.2⟩
      left_inv := fun x ↦ rfl
      right_inv := fun y ↦ rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  simp_rw [fun P : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ↦
    card_left_inv P.1 P.2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  let e2 : {P : Matrix (Fin M) (Fin a) k // LinearIndependent k (cols P)} ≃
      {s : Fin a → Fin M → k // LinearIndependent k s} :=
    { toFun := fun P ↦ ⟨cols P.1, P.2⟩
      invFun := fun s ↦ ⟨fun i j ↦ s.1 j i, s.2⟩
      left_inv := fun P ↦ rfl
      right_inv := fun s ↦ rfl }
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e2, card_linearIndependent
    (by rw [Module.finrank_fin_fun]; exact ha), Module.finrank_fin_fun, Nat.card_eq_fintype_card]

end FiniteFieldSplitting

namespace FiniteFieldSplitting

open Matrix

variable {k : Type} [Field k] [Finite k] {M a : ℕ}

abbrev swapR (k : Type) [Field k] : k × k →+* k × k := (RingEquiv.prodComm (R := k) (S := k)).toRingHom

def U1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).1

def V1 (X : Fin a → Fin M → k × k) : Matrix (Fin a) (Fin M) k := fun r i ↦ (X r i).2

theorem ffH_fst (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).1 = ∑ i, ∑ j, (x i).2 * (J i j).1 * (y j).1 := by
  simp [ffH, Prod.fst_sum]

theorem ffH_snd (J : Matrix (Fin M) (Fin M) (k × k)) (x y : Fin M → k × k) :
    (ffH (swapR k) J x y).2 = ∑ i, ∑ j, (x i).1 * (J i j).2 * (y j).2 := by
  simp [ffH, Prod.snd_sum]

theorem gram_iff (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j)
    (X : Fin a → Fin M → k × k) :
    ffGram (swapR k) J X = T ↔
      V1 X * J.map Prod.fst * (U1 X)ᵀ = T.map Prod.fst := by
  have key : ∀ r s, (ffGram (swapR k) J X r s).1 = (V1 X * J.map Prod.fst * (U1 X)ᵀ) r s := by
    intro r s
    simp only [ffGram, ffH_fst, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, U1,
      V1, Finset.sum_mul]
    exact Finset.sum_comm
  have key2 : ∀ r s, (ffGram (swapR k) J X r s).2 = (ffGram (swapR k) J X s r).1 := by
    intro r s
    simp only [ffGram, ffH_fst, ffH_snd]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have h1 : (J j i).2 = (J i j).1 := by
      have := congrArg Prod.fst (hJ i j)
      simpa using this
    rw [h1]
    ring
  constructor
  · intro h
    ext r s
    rw [← key, h]
    rfl
  · intro h
    funext r s
    refine Prod.ext ?_ ?_
    · rw [key, h]
      rfl
    · rw [key2, key, h, Matrix.map_apply]
      have := congrArg Prod.fst (hT s r)
      simpa using this.symm

theorem fFSplit_nat (M a : ℕ) (ha : a ≤ M)
    (J : Matrix (Fin M) (Fin M) (k × k)) (hJ : ∀ i j, (J j i).swap = J i j) (hJd : IsUnit J.det)
    (T : Matrix (Fin a) (Fin a) (k × k)) (hT : ∀ i j, (T j i).swap = T i j) (hTd : IsUnit T.det) :
    Nat.card {X : Fin a → Fin M → k × k // ffGram (swapR k) J X = T} =
      (∏ i : Fin a, (Nat.card k ^ M - Nat.card k ^ (i : ℕ))) * Nat.card k ^ (a * (M - a)) := by
  classical
  set A := J.map Prod.fst with hA
  set T1 := T.map Prod.fst with hT1
  have hAd : IsUnit A.det := by
    have := hJd.map (RingHom.fst k k)
    rwa [RingHom.map_det] at this
  have hT1d : IsUnit T1.det := by
    have := hTd.map (RingHom.fst k k)
    rwa [RingHom.map_det] at this
  let e : (Fin a → Fin M → k × k) ≃ Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k :=
    { toFun := fun X ↦ (T1⁻¹ * V1 X, A * (U1 X)ᵀ)
      invFun := fun WP r i ↦ ((A⁻¹ * WP.2)ᵀ r i, (T1 * WP.1) r i)
      left_inv := fun X ↦ by
        funext r i
        simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hAd,
          Matrix.mul_nonsing_inv_cancel_left _ _ hT1d, Matrix.transpose_transpose]
        rfl
      right_inv := fun WP ↦ by
        have h1 : V1 (fun r i ↦ ((A⁻¹ * WP.2)ᵀ r i, (T1 * WP.1) r i)) = T1 * WP.1 := rfl
        have h2 : U1 (fun r i ↦ ((A⁻¹ * WP.2)ᵀ r i, (T1 * WP.1) r i)) = (A⁻¹ * WP.2)ᵀ := rfl
        simp only [h1, h2, Matrix.transpose_transpose, Matrix.nonsing_inv_mul_cancel_left _ _ hT1d,
          Matrix.mul_nonsing_inv_cancel_left _ _ hAd] }
  have hcond : ∀ X, ffGram (swapR k) J X = T ↔ (e X).1 * (e X).2 = 1 := by
    intro X
    rw [gram_iff J hJ T hT X, ← hT1, ← hA]
    change V1 X * A * (U1 X)ᵀ = T1 ↔ T1⁻¹ * V1 X * (A * (U1 X)ᵀ) = 1
    have hre : T1⁻¹ * V1 X * (A * (U1 X)ᵀ) = T1⁻¹ * (V1 X * A * (U1 X)ᵀ) := by
      simp only [Matrix.mul_assoc]
    rw [hre]
    constructor
    · intro h
      rw [h, Matrix.nonsing_inv_mul _ hT1d]
    · intro h
      calc V1 X * A * (U1 X)ᵀ = T1 * (T1⁻¹ * (V1 X * A * (U1 X)ᵀ)) :=
            (Matrix.mul_nonsing_inv_cancel_left _ _ hT1d).symm
        _ = T1 := by rw [h, Matrix.mul_one]
  rw [Nat.card_congr (Equiv.subtypeEquiv (p := fun X ↦ ffGram (swapR k) J X = T)
    (q := fun WP : Matrix (Fin a) (Fin M) k × Matrix (Fin M) (Fin a) k ↦ WP.1 * WP.2 = 1) e hcond),
    card_pairs ha]

end FiniteFieldSplitting

theorem fFSplit_holds : FFSplit := by
  intro k _ _ M a ha J hJ hJd T hT hTd
  rw [FiniteFieldSplitting.fFSplit_nat M a ha J hJ hJd T hT hTd]
  have hq : 0 < Nat.card k := Nat.card_pos
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
  push_cast
  rfl

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.MeasureEqOfCos
section
noncomputable section

namespace PI.VolStabW

open MeasureTheory Topology Set Filter

section CosMeas

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

omit [MeasurableSpace X] [OpensMeasurableSpace X] in

def thick (S : Set X) (Λ : AddSubgroup X) : Set X := {x | ∃ s ∈ S, x - s ∈ Λ}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem isOpen_thick (S : Set X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X)) :
    IsOpen (thick S Λ) := by
  have : thick S Λ = ⋃ s ∈ S, (fun x => x - s) ⁻¹' (Λ : Set X) := by
    ext x; simp [thick]
  rw [this]
  exact isOpen_biUnion fun s _ => hΛ.preimage (continuous_id.sub continuous_const)

theorem measure_thick_eq (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  have : DiscreteTopology (X ⧸ Λ) := QuotientAddGroup.discreteTopology hΛ
  let q : X → X ⧸ Λ := QuotientAddGroup.mk
  have hq : Continuous q := continuous_quot_mk
  have hfin : (q '' S).Finite := (hS.image hq).finite_of_discrete
  have hcos : ∀ y, q ⁻¹' {q y} = {z | z - y ∈ Λ} := by
    intro y
    ext z
    simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq, q]
    exact QuotientAddGroup.eq_iff_sub_mem
  have hset : thick S Λ = ⋃ p ∈ hfin.toFinset, q ⁻¹' {p} := by
    ext x
    simp only [thick, mem_setOf_eq, mem_iUnion, Finite.mem_toFinset, mem_image, exists_prop]
    constructor
    · rintro ⟨s, hs, hx⟩
      refine ⟨q s, ⟨s, hs, rfl⟩, ?_⟩
      rw [hcos]
      exact hx
    · rintro ⟨p, ⟨s, hs, rfl⟩, hx⟩
      rw [hcos] at hx
      exact ⟨s, hs, hx⟩
  have hmeas : ∀ p : X ⧸ Λ, MeasurableSet (q ⁻¹' {p}) := fun p =>
    ((isOpen_discrete ({p} : Set (X ⧸ Λ))).preimage hq).measurableSet
  have hdisj : PairwiseDisjoint (↑hfin.toFinset : Set (X ⧸ Λ)) (fun p => q ⁻¹' {p}) :=
    fun p _ p' _ hne => (disjoint_singleton.2 hne).preimage q
  rw [hset, measure_biUnion_finset hdisj (fun p _ => hmeas p),
    measure_biUnion_finset hdisj (fun p _ => hmeas p)]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective p
  have := hcos y
  simp only [q] at this
  rw [this]
  exact h y

omit [MeasurableSpace X] [OpensMeasurableSpace X] in

theorem iInter_thick (S : Set X) (hSc : IsClosed S) (Λ : ℕ → AddSubgroup X)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N) : ⋂ n, thick S (Λ n) = S := by
  ext x
  simp only [mem_iInter]
  constructor
  · intro hx
    rw [← hSc.closure_eq, mem_closure_iff_nhds]
    intro N hN
    have h0 : {d : X | x - d ∈ N} ∈ 𝓝 (0 : X) := by
      have hc : Continuous fun d : X => x - d := continuous_const.sub continuous_id
      have := hc.continuousAt (x := 0) (by simpa using hN)
      exact this
    obtain ⟨n, hn⟩ := hb _ h0
    obtain ⟨s, hs, hxs⟩ := hx n
    have := hn hxs
    simp only [mem_setOf_eq, sub_sub_cancel] at this
    exact ⟨s, this, hs⟩
  · intro hx n
    exact ⟨x, hx, by simp [(Λ n).zero_mem]⟩

theorem measure_eq_of_cos (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by
  have hA : Antitone fun n => thick S (Λ n) := by
    intro n k hnk
    rintro x ⟨s, hs, hx⟩
    exact ⟨s, hs, hanti hnk hx⟩
  have hm : ∀ n, NullMeasurableSet (thick S (Λ n)) m1 := fun n =>
    (isOpen_thick S _ (hΛo n)).measurableSet.nullMeasurableSet
  have hm2 : ∀ n, NullMeasurableSet (thick S (Λ n)) m2 := fun n =>
    (isOpen_thick S _ (hΛo n)).measurableSet.nullMeasurableSet
  have h0 := measure_thick_eq m1 m2 (Λ 0) (hΛo 0) (h 0) S hS
  rw [← iInter_thick S hSc Λ hb, hA.measure_iInter hm ⟨0, measure_ne_top _ _⟩,
    hA.measure_iInter hm2 ⟨0, h0 ▸ measure_ne_top _ _⟩]
  exact iInf_congr fun n => measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS

end CosMeas

theorem cosDens_holds : CosDens := by
  intro X _ _ _ _ _ _ ν m _ _ H hHo _ hHa hb c0 κ hCc hcos S hS
  set C : Set X := {z | z - c0 ∈ H 0} with hC
  have hCm : MeasurableSet C :=
    ((hHo 0).preimage (continuous_id.sub continuous_const)).measurableSet
  have key : ∀ n y, m {z | z - y ∈ H n} = (κ • ν.restrict C) {z | z - y ∈ H n} := by
    intro n y
    rw [Measure.smul_apply, Measure.restrict_apply' hCm, smul_eq_mul]
    by_cases hy : y - c0 ∈ H 0
    · have hsub : {z | z - y ∈ H n} ⊆ C := by
        intro z hz
        have := (H 0).add_mem (hHa (Nat.zero_le n) hz) hy
        simpa [hC, sub_add_sub_cancel] using this
      rw [Set.inter_eq_left.2 hsub]
      exact hcos n y hy
    · have hdis : {z | z - y ∈ H n} ∩ C = ∅ := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hC, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro hz hzc
        apply hy
        have := (H 0).sub_mem hzc (hHa (Nat.zero_le n) hz)
        simpa [sub_sub_sub_cancel_left] using this
      rw [hdis, measure_empty, mul_zero]
      refine measure_mono_null (fun z hz => ?_) hCc
      intro hzc
      apply hy
      have := (H 0).sub_mem hzc (hHa (Nat.zero_le n) hz)
      simpa [sub_sub_sub_cancel_left] using this
  have := measure_eq_of_cos m (κ • ν.restrict C) H hHo hHa hb key S hS hS.isClosed
  rw [this, Measure.smul_apply, Measure.restrict_apply' hCm, smul_eq_mul]

end PI.VolStabW
end
end

