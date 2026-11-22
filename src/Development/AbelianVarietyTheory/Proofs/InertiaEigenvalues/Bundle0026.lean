import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlFactorFromBlocksModUniformizer
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem gl_factor_fromBlocks_mod_uniformizer : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (g : GL (Fin r) (IsLocalRing.ResidueField O)) (L : Matrix (Fin r) (Fin r) O), L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∀ (B : Matrix (Fin r) (Fin t) O) (q : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O), (∀ i j, IsLocalRing.residue O (q i j) = IsLocalRing.residue O (Matrix.fromBlocks L B 0 (1 : Matrix (Fin t) (Fin t) O) i j)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) = q := by
  intro O _ _ _ r t ϖ hϖ g L hL B q hq
  classical
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hmem : ∀ x : O, IsLocalRing.residue O x = 0 → x ∈ Ideal.span {ϖ} := fun x hx =>
    hmax ▸ (IsLocalRing.residue_eq_zero_iff x).mp hx
  have hg : IsUnit (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have hLdet : IsLocalRing.residue O L.det = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hL]
  have hLu : IsUnit L.det :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [hLdet]; exact hg.ne_zero)
  set D : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O := Matrix.fromBlocks L 0 0 1 with hDdef
  have hDu : IsUnit D.det := by
    rw [hDdef, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]; exact hLu
  have hqmap : q.map (IsLocalRing.residue O) =
      (Matrix.fromBlocks L B 0 (1 : Matrix (Fin t) (Fin t) O)).map (IsLocalRing.residue O) := by
    ext i j; exact hq i j
  have hqu : IsUnit q.det := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hqmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, hLdet]
    exact hg.ne_zero
  have hHu : IsUnit (q * D⁻¹).det := by
    rw [Matrix.det_mul]; exact hqu.mul (Matrix.isUnit_nonsing_inv_det D hDu)
  have hHD : q * D⁻¹ * D = q := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hDu, Matrix.mul_one]
  have hMD : (q * D⁻¹).map (IsLocalRing.residue O) * D.map (IsLocalRing.residue O) =
      q.map (IsLocalRing.residue O) := by
    rw [← Matrix.map_mul, hHD]
  rw [hqmap, ← Matrix.fromBlocks_toBlocks ((q * D⁻¹).map (IsLocalRing.residue O)), hDdef,
    Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hMD
  obtain ⟨h11, -, h21, -⟩ := hMD
  simp only [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, add_zero, hL] at h11 h21
  have e11 : ((q * D⁻¹).map (IsLocalRing.residue O)).toBlocks₁₁ = 1 := by
    have := congrArg (· * ((g⁻¹ : GL (Fin r) (IsLocalRing.ResidueField O)) : Matrix (Fin r) (Fin r) _)) h11
    simpa [Matrix.mul_assoc] using this
  have e21 : ((q * D⁻¹).map (IsLocalRing.residue O)).toBlocks₂₁ = 0 := by
    have hgg : (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) *
        ((g⁻¹ : GL (Fin r) (IsLocalRing.ResidueField O)) : Matrix (Fin r) (Fin r) _) = 1 := Units.mul_inv g
    rw [hDdef, ← Matrix.mul_one (Matrix.toBlocks₂₁ _), ← hgg, ← Matrix.mul_assoc, h21, Matrix.zero_mul]
  refine ⟨Matrix.nonsingInvUnit (q * D⁻¹) hHu, ?_, ?_, hHD⟩
  · intro i j
    apply hmem
    have := congrFun (congrFun e11 i) j
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.map_apply] at this
    show IsLocalRing.residue O ((q * D⁻¹) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j) = 0
    rw [map_sub, this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · intro i j
    show (q * D⁻¹) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}
    apply hmem
    have := congrFun (congrFun e21 i) j
    simpa [Matrix.toBlocks₂₁] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HfAlgSmulRight
section
open scoped BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ}

def hf (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (x y : Fin r → K) : K :=
  (fun i => cK (x i)) ⬝ᵥ (J.mulVec y)

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_add_right (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K)
    (x y z : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J x (y + z) =
      _root_.GlobalTheory.HermNbr.hf cK J x y + _root_.GlobalTheory.HermNbr.hf cK J x z := by
  simp only [_root_.GlobalTheory.HermNbr.hf, Matrix.mulVec_add, dotProduct, Pi.add_apply,
    mul_add, Finset.sum_add_distrib]

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_add_left (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K)
    (x y z : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J (x + y) z =
      _root_.GlobalTheory.HermNbr.hf cK J x z + _root_.GlobalTheory.HermNbr.hf cK J y z := by
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Pi.add_apply, map_add, add_mul,
    Finset.sum_add_distrib]

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_smul_right (cK : K ≃+* K)
    (J : Matrix (Fin r) (Fin r) K) (a : K) (x y : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J x (a • y) = a * _root_.GlobalTheory.HermNbr.hf cK J x y := by
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Matrix.mulVec_smul, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_algSmul_right (cK : K ≃+* K)
    (J : Matrix (Fin r) (Fin r) K) (a : O)
    (x y : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J x (a • y) =
      algebraMap O K a * _root_.GlobalTheory.HermNbr.hf cK J x y := by
  rw [← algebraMap_smul K a y, _root_.GlobalTheory.HermNbr.hf_smul_right]

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_algSmul_left (cK : K ≃+* K)
    (J : Matrix (Fin r) (Fin r) K) (a : O)
    (x y : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J (a • x) y =
      cK (algebraMap O K a) * _root_.GlobalTheory.HermNbr.hf cK J x y := by
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Pi.smul_apply, Algebra.smul_def,
    map_mul, Finset.mul_sum, mul_assoc]

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_sub_right (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K)
    (x y z : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J x (y - z) =
      _root_.GlobalTheory.HermNbr.hf cK J x y - _root_.GlobalTheory.HermNbr.hf cK J x z := by
  simp only [_root_.GlobalTheory.HermNbr.hf, Matrix.mulVec_sub, dotProduct, Pi.sub_apply,
    mul_sub, Finset.sum_sub_distrib]

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.hf_sub_left (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K)
    (x y z : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J (x - y) z =
      _root_.GlobalTheory.HermNbr.hf cK J x z - _root_.GlobalTheory.HermNbr.hf cK J y z := by
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Pi.sub_apply, map_sub, sub_mul,
    Finset.sum_sub_distrib]

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in

theorem _root_.GlobalTheory.HermNbr.hf_conj (cK : K ≃+* K) (hc2 : ∀ x, cK (cK x) = x)
    (J : Matrix (Fin r) (Fin r) K)
    (hJ : J.transpose.map cK = J) (x y : Fin r → K) :
    _root_.GlobalTheory.HermNbr.hf cK J y x = cK (_root_.GlobalTheory.HermNbr.hf cK J x y) := by
  have hJ' : ∀ i j, cK (J i j) = J j i := fun i j => by
    simpa using congrFun (congrFun hJ j) i
  simp only [_root_.GlobalTheory.HermNbr.hf, dotProduct, Matrix.mulVec, map_sum, map_mul, hc2,
    hJ', Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def perp (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (L : Submodule O (Fin r → K))
    (v : Fin r → K) : Submodule O (Fin r → K) where
  carrier := {x | x ∈ L ∧ hf cK J v x ∈ (algebraMap O K).range}
  add_mem' := fun {a b} ha hb => ⟨L.add_mem ha.1 hb.1, by
    rw [hf_add_right]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨L.zero_mem, by
    have := hf_smul_right cK J 0 v 0
    simp only [zero_smul, zero_mul] at this
    rw [this]; exact zero_mem _⟩
  smul_mem' := fun a x hx => ⟨L.smul_mem a hx.1, by
    rw [hf_algSmul_right]; exact mul_mem ⟨a, rfl⟩ hx.2⟩

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in
theorem _root_.GlobalTheory.HermNbr.mem_perp {cK : K ≃+* K} {J : Matrix (Fin r) (Fin r) K}
    {L : Submodule O (Fin r → K)}
    {v x : Fin r → K} : x ∈ _root_.GlobalTheory.HermNbr.perp cK J L v ↔
      x ∈ L ∧ _root_.GlobalTheory.HermNbr.hf cK J v x ∈ (algebraMap O K).range :=
  Iff.rfl

def nb (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (L : Submodule O (Fin r → K))
    (v : Fin r → K) : Submodule O (Fin r → K) :=
  perp cK J L v ⊔ Submodule.span O {v}

def IsSD (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (L : Submodule O (Fin r → K)) : Prop :=
  ∀ x, x ∈ L ↔ ∀ y ∈ L, hf cK J x y ∈ (algebraMap O K).range

noncomputable def idx (ϖ : O) (L : Submodule O (Fin r → K)) : ℕ :=
  (L.map (ϖ • (LinearMap.id : (Fin r → K) →ₗ[O] (Fin r → K)))).toAddSubgroup.relIndex
    L.toAddSubgroup

def Good (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (ϖ : O) (N : ℕ)
    (L : Submodule O (Fin r → K)) : Prop :=
  IsSD cK J L ∧ (∀ x : Fin r → K, ∃ k : ℕ, (ϖ ^ k) • x ∈ L) ∧ idx ϖ L = N

def IsStep (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (ϖ : O)
    (L : Submodule O (Fin r → K)) (v : Fin r → K) : Prop :=
  v ∉ L ∧ ϖ • v ∈ L ∧ hf cK J v v ∈ (algebraMap O K).range

def Nbrs (cK : K ≃+* K) (J : Matrix (Fin r) (Fin r) K) (ϖ : O)
    (L : Submodule O (Fin r → K)) : Set (Submodule O (Fin r → K)) :=
  {L' | ∃ v, IsStep cK J ϖ L v ∧ L' = nb cK J L v}

open scoped BigOperators in
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} in

theorem _root_.GlobalTheory.HermNbr.graph_sum {X : Type} (S : Set X) (i : X → X → ℕ)
    (Nb : X → Set X) (Q : ℕ) (hQ : 2 ≤ Q)
    (s D : ℝ) (hs : 0 < s) (hD : 0 ≤ D)
    (hρ : D * (Q : ℝ) ^ (-s) < 1)
    (hself : ∀ L ∈ S, i L L = 1)
    (hstep : ∀ L ∈ S, ∀ Λ ∈ S, L ≠ Λ → i L Λ ≠ 0 →
      ∃ L' ∈ Nb L, L' ∈ S ∧ i L' Λ ≠ 0 ∧ Q * i L' Λ ≤ i L Λ)
    (hcard : ∀ L ∈ S, ∀ t : Finset X, (t : Set X) ⊆ Nb L → (t.card : ℝ) ≤ D)
    (L : X) (hL : L ∈ S) (C : Finset X) (hC : (C : Set X) ⊆ S) (hLC : L ∉ C) :
    ∑ Λ ∈ C, (i L Λ : ℝ) ^ (-s) ≤
      D * (Q : ℝ) ^ (-s) / (1 - D * (Q : ℝ) ^ (-s)) := by
  classical
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hq0 : 0 ≤ (Q : ℝ) ^ (-s) := Real.rpow_nonneg hQpos.le _
  generalize hq : (Q : ℝ) ^ (-s) = q at hρ hq0 ⊢
  obtain ⟨B, hBdef⟩ : ∃ B, B = D * q / (1 - D * q) := ⟨_, rfl⟩
  rw [← hBdef]
  have hne : (1 - D * q) ≠ 0 := (sub_pos.2 hρ).ne'
  have hB : 0 ≤ B := hBdef ▸ div_nonneg (mul_nonneg hD hq0) (sub_pos.2 hρ).le
  have hfix : D * q * (1 + B) = B := by
    rw [hBdef, one_add_div hne, sub_add_cancel, mul_div_assoc', mul_one]
  have hzero : (0 : ℝ) ^ (-s) = 0 := Real.zero_rpow (neg_ne_zero.2 hs.ne')
  have main : ∀ n : ℕ, ∀ L ∈ S, ∀ C : Finset X, (C : Set X) ⊆ S → L ∉ C →
      (∀ Λ ∈ C, i L Λ ≤ n) → ∑ Λ ∈ C, (i L Λ : ℝ) ^ (-s) ≤ B := by
    intro n
    induction n with
    | zero =>
      intro L hL C hC hLC hn
      have h0 : ∀ Λ ∈ C, (i L Λ : ℝ) ^ (-s) = 0 := fun Λ hΛ => by
        rw [Nat.le_zero.1 (hn Λ hΛ), Nat.cast_zero, hzero]
      rw [Finset.sum_eq_zero h0]
      exact hB
    | succ n ih =>
      intro L hL C hC hLC hn
      have key : ∀ Λ, ∃ L', Λ ∈ S → L ≠ Λ → i L Λ ≠ 0 →
          L' ∈ Nb L ∧ L' ∈ S ∧ i L' Λ ≠ 0 ∧ Q * i L' Λ ≤ i L Λ := by
        intro Λ
        by_cases h : Λ ∈ S ∧ L ≠ Λ ∧ i L Λ ≠ 0
        · obtain ⟨L', h1, h2, h3, h4⟩ := hstep L hL Λ h.1 h.2.1 h.2.2
          exact ⟨L', fun _ _ _ => ⟨h1, h2, h3, h4⟩⟩
        · exact ⟨L, fun a b c => absurd ⟨a, b, c⟩ h⟩
      choose f hf using key
      obtain ⟨C', hC'⟩ : ∃ C', C' = C.filter (fun Λ => i L Λ ≠ 0) := ⟨_, rfl⟩
      have hC'C : C' ⊆ C := hC' ▸ Finset.filter_subset _ _
      have hf' : ∀ Λ ∈ C', f Λ ∈ Nb L ∧ f Λ ∈ S ∧ i (f Λ) Λ ≠ 0 ∧ Q * i (f Λ) Λ ≤ i L Λ := by
        intro Λ hΛ
        rw [hC', Finset.mem_filter] at hΛ
        exact hf Λ (hC hΛ.1) (fun h => hLC (by rw [h]; exact hΛ.1)) hΛ.2
      have hsum : ∑ Λ ∈ C, (i L Λ : ℝ) ^ (-s) = ∑ Λ ∈ C', (i L Λ : ℝ) ^ (-s) := by
        rw [hC', Finset.sum_filter_of_ne]
        intro Λ _ h h0
        exact h (by rw [h0, Nat.cast_zero, hzero])
      have fibre : ∀ L1 ∈ S, ∀ Fb : Finset X, (∀ Λ ∈ Fb, Λ ∈ C' ∧ f Λ = L1) →
          ∑ Λ ∈ Fb, (i L Λ : ℝ) ^ (-s) ≤ q * (1 + B) := by
        intro L1 hL1 Fb hFb
        have hterm : ∀ Λ ∈ Fb, (i L Λ : ℝ) ^ (-s) ≤ q * (i L1 Λ : ℝ) ^ (-s) := by
          intro Λ hΛ
          obtain ⟨hΛC', hfΛ⟩ := hFb Λ hΛ
          obtain ⟨-, -, hne', hle⟩ := hf' Λ hΛC'
          rw [hfΛ] at hne' hle
          have h1 : (1 : ℝ) ≤ i L1 Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne'
          have h2 : (Q : ℝ) * i L1 Λ ≤ i L Λ := by exact_mod_cast hle
          have h3 : 0 < (Q : ℝ) * i L1 Λ := mul_pos hQpos (by linarith)
          rw [← hq, ← Real.mul_rpow hQpos.le (by linarith), Real.rpow_neg (Nat.cast_nonneg _),
            Real.rpow_neg h3.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos h3 _) (Real.rpow_le_rpow h3.le h2 hs.le)
        have hIH : ∑ Λ ∈ Fb.erase L1, (i L1 Λ : ℝ) ^ (-s) ≤ B := by
          refine ih L1 hL1 (Fb.erase L1) ?_ (Finset.notMem_erase L1 Fb) ?_
          · intro x hx
            exact hC (hC'C (hFb x (Finset.mem_of_mem_erase hx)).1)
          · intro Λ hΛ
            obtain ⟨hΛC', hfΛ⟩ := hFb Λ (Finset.mem_of_mem_erase hΛ)
            obtain ⟨-, -, hne', hle⟩ := hf' Λ hΛC'
            rw [hfΛ] at hne' hle
            have h1 := hn Λ (hC'C hΛC')
            have h2 : 1 ≤ i L1 Λ := Nat.one_le_iff_ne_zero.2 hne'
            have h3 : 2 * i L1 Λ ≤ Q * i L1 Λ := Nat.mul_le_mul_right _ hQ
            omega
        calc ∑ Λ ∈ Fb, (i L Λ : ℝ) ^ (-s) ≤ ∑ Λ ∈ Fb, q * (i L1 Λ : ℝ) ^ (-s) :=
              Finset.sum_le_sum hterm
          _ = q * ∑ Λ ∈ Fb, (i L1 Λ : ℝ) ^ (-s) := by rw [Finset.mul_sum]
          _ ≤ q * ∑ Λ ∈ insert L1 (Fb.erase L1), (i L1 Λ : ℝ) ^ (-s) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.subset_insert_iff.2 subset_rfl)
                (fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) hq0
          _ = q * (1 + ∑ Λ ∈ Fb.erase L1, (i L1 Λ : ℝ) ^ (-s)) := by
              rw [Finset.sum_insert (Finset.notMem_erase L1 Fb), hself L1 hL1, Nat.cast_one,
                Real.one_rpow]
          _ ≤ q * (1 + B) := mul_le_mul_of_nonneg_left (by linarith) hq0
      rw [hsum, ← Finset.sum_fiberwise_of_maps_to (g := f) (t := C'.image f)
        (fun Λ hΛ => Finset.mem_image_of_mem f hΛ)]
      calc _ ≤ ∑ _L' ∈ C'.image f, q * (1 + B) := by
            refine Finset.sum_le_sum fun L' hL' => ?_
            obtain ⟨Λ0, hΛ0, rfl⟩ := Finset.mem_image.1 hL'
            exact fibre _ (hf' Λ0 hΛ0).2.1 _ fun Λ hΛ => Finset.mem_filter.1 hΛ
        _ = ((C'.image f).card : ℝ) * (q * (1 + B)) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ D * (q * (1 + B)) := by
            refine mul_le_mul_of_nonneg_right (hcard L hL _ ?_) (mul_nonneg hq0 (by linarith))
            intro x hx
            obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.1 hx
            exact (hf' Λ hΛ).1
        _ = B := by rw [← mul_assoc]; exact hfix
  exact main (C.sup (i L)) L hL C hC hLC fun Λ hΛ => Finset.le_sup hΛ

end GlobalTheory.HermNbr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageFiniteExtension
section
namespace GlobalTheory

theorem exists_finiteDimensional_intermediateField_eq_range_fractionRing
    (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* PadicAlgCl l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) :
    ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧
      ∀ y, y ∈ L ↔ ∃ a, ι a = y := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := O)
  let f : O → PadicAlgCl l := fun o => ι (algebraMap O (FractionRing O) o)
  let S : Set (PadicAlgCl l) := f '' (s : Set O)
  haveI : Finite S := (s.finite_toSet.image f).to_subtype
  have hQ : ∀ x : ℚ_[l], algebraMap ℚ_[l] (PadicAlgCl l) x ∈ ι.fieldRange := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) x
    rw [map_div₀]
    refine ι.fieldRange.div_mem ⟨_, hι a⟩ ⟨_, hι b⟩
  refine ⟨IntermediateField.adjoin ℚ_[l] S, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) x).isIntegral)
  · have hO : ∀ o : O, f o ∈ IntermediateField.adjoin ℚ_[l] S := by
      intro o
      have ho : o ∈ Submodule.span ℤ_[l] (s : Set O) := by rw [hs]; trivial
      induction ho using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => simp [f]
      | add x y _ _ hx hy =>
        simp only [f, map_add]
        exact add_mem hx hy
      | smul z x _ hx =>
        simp only [f, Algebra.smul_def, map_mul, hι]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
    intro y
    constructor
    · intro hy
      have hle : IntermediateField.adjoin ℚ_[l] S ≤ ι.fieldRange.toIntermediateField hQ := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨o, -, rfl⟩
        exact ⟨_, rfl⟩
      exact hle hy
    · rintro ⟨a, rfl⟩
      obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := O) a
      rw [map_div₀]
      exact div_mem (hO p) (hO q)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Imports
section
namespace GlobalTheory.PowerBound

theorem pow_le {A : Type} [CommRing A] (a d : A) (n : ℕ) :
    (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + 1) ≤
      Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * (Ideal.span {a} ⊔ Ideal.span {d}) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    set I := Ideal.span {a} ⊔ Ideal.span {d} with hI
    have haI : a ^ (n + 1) ∈ I ^ (n + 1) :=
      Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) _
    calc I ^ (n + 1 + 1) = I * I ^ (n + 1) := pow_succ' I (n + 1)
      _ ≤ I * (Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * I ^ n) := Ideal.mul_mono_right ih
      _ = I * Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * (I * I ^ n) := by
          rw [Ideal.mul_sup, mul_left_comm]
      _ ≤ Ideal.span {a ^ (n + 1 + 1)} ⊔ Ideal.span {d} * I ^ (n + 1) := by
          apply sup_le
          · rw [hI, Ideal.sup_mul, Ideal.span_singleton_mul_span_singleton, ← pow_succ']
            apply sup_le_sup_left
            exact Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).2 haI)
          · rw [← pow_succ']
            exact le_sup_right

theorem main : ∀ {A : Type} [inst : CommRing A] (a d : A) (n : ℕ) {x : A},
    x ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + (1 : ℕ)) →
      ∃ (u : A), ∃ w ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ n, x = a ^ (n + (1 : ℕ)) * u + d * w := by
  intro A _ a d n x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (pow_le a d n hx)
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.1 hz
  exact ⟨u, w, hw, by ring⟩

end GlobalTheory.PowerBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsAlt
section
namespace GlobalTheory.TargetStatementAlt

open Polynomial

theorem main {R F : Type} [CommRing R] [Field F] [Algebra R F] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n F) (hM : IsIntegral R M) :
    IsIntegral R (Matrix.trace M) := by
  let f : F →ₐ[R] AlgebraicClosure F := IsScalarTower.toAlgHom R F (AlgebraicClosure F)
  let φ : Matrix n n F →ₐ[R] Matrix n n (AlgebraicClosure F) := f.mapMatrix
  obtain ⟨p, hpm, hp⟩ := hM.map φ
  have key : ∀ μ ∈ (φ M).charpoly.roots, IsIntegral R μ := by
    intro μ hμ
    have hroot : IsRoot (φ M).charpoly μ := (mem_roots'.mp hμ).2
    have hs : μ ∈ spectrum (AlgebraicClosure F) (φ M) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
    have h1 := spectrum.subset_polynomial_aeval (φ M) (p.map (algebraMap R (AlgebraicClosure F)))
      ⟨μ, hs, rfl⟩
    have h2 : aeval (φ M) (p.map (algebraMap R (AlgebraicClosure F))) = 0 := by
      rw [aeval_map_algebraMap, aeval_def]; exact hp
    rw [h2, spectrum.mem_iff, sub_zero] at h1
    refine ⟨p, hpm, ?_⟩
    by_contra hne
    apply h1
    have : eval μ (p.map (algebraMap R (AlgebraicClosure F))) ≠ 0 := by
      rwa [eval_map_algebraMap, aeval_def]
    exact (Ne.isUnit this).map _
  have ht : IsIntegral R (Matrix.trace (φ M)) := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    exact IsIntegral.multiset_sum key
  have he : Matrix.trace (φ M) = f (Matrix.trace M) := by
    simp [φ, Matrix.trace, map_sum, AlgHom.mapMatrix_apply]
  rw [he] at ht
  exact (isIntegral_algHom_iff f f.toRingHom.injective).mp ht

theorem target : ∀ {R F : Type} [inst : CommRing R] [inst_1 : Field F] [inst_2 : Algebra R F] {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] (M : Matrix n n F), IsIntegral R M → IsIntegral R (Matrix.trace M) :=
  fun M h => main M h

end GlobalTheory.TargetStatementAlt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBis
section
namespace GlobalTheory.IntegralCriterion

theorem main : ∀ (k : Type) [inst : Field k] (n : ℕ) (v : Fin (n + (1 : ℕ)) → k), v ≠ (0 : Fin (n + (1 : ℕ)) → k) → ∃ (P : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k), IsUnit P ∧ ∀ (a : Fin (n + (1 : ℕ))), P a (0 : Fin (n + (1 : ℕ))) = v a := by
  intro k _ n v hv
  set e0 : Fin (n + 1) → k := Pi.single 0 1 with he0def
  have he0 : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e0] at this
  let f : (k ∙ e0) ≃ₗ[k] (k ∙ v) :=
    (LinearEquiv.toSpanNonzeroSingleton k _ e0 he0).symm ≪≫ₗ
      LinearEquiv.toSpanNonzeroSingleton k _ v hv
  have hf : (f ⟨e0, Submodule.mem_span_singleton_self e0⟩ : Fin (n + 1) → k) = v := by
    have h1 : (⟨e0, Submodule.mem_span_singleton_self e0⟩ : k ∙ e0) =
        LinearEquiv.toSpanNonzeroSingleton k _ e0 he0 1 := by
      ext; simp
    simp only [f, LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply]
    simp
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hge : g e0 = v := by
    rw [← hf, hg]
  refine ⟨LinearMap.toMatrix' (g : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), ?_, ?_⟩
  · refine ⟨⟨LinearMap.toMatrix' (g : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)),
      LinearMap.toMatrix' (g.symm : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), ?_, ?_⟩, rfl⟩
    · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
      congr 1
      ext x : 1
      simp
    · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
      congr 1
      ext x : 1
      simp
  · intro a
    rw [LinearMap.toMatrix'_apply]
    change g e0 a = v a
    rw [hge]

end GlobalTheory.IntegralCriterion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsLast
section
namespace GlobalTheory.PowerDifferenceNormInertiaEigenvalues

universe u_1

theorem norm_pow_sub_pow_le {C : Type u_1} [NormedField C] [IsUltrametricDist C] {x y : C}
    (hx : ‖x‖ ≤ (1 : ℝ)) (hy : ‖y‖ ≤ (1 : ℝ)) (n : ℕ) : ‖x ^ n - y ^ n‖ ≤ ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + y ^ n * (x - y) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans ih
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)

end GlobalTheory.PowerDifferenceNormInertiaEigenvalues
end

