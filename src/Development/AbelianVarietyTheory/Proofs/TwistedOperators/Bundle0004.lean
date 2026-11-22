import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualPairIsUnitDetBlocks
section
open scoped Matrix

namespace GlobalTheory

theorem exists_det_add_mul_ne_zero_of_ker_inf {k : Type} [Field k] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) k)
    (h : ∀ v : Fin n → k, A *ᵥ v = 0 → C *ᵥ v = 0 → v = 0) :
    ∃ X : Matrix (Fin n) (Fin n) k, (A + X * C).det ≠ 0 := by
  classical
  set a := Matrix.toLin' A with ha
  set c := Matrix.toLin' C with hc
  obtain ⟨L', hL'⟩ := Submodule.exists_isCompl (LinearMap.ker c)
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl ((LinearMap.ker c).map a)

  have hkey : ∀ x ∈ LinearMap.ker c, a x = 0 → x = 0 := by
    intro x hx hax
    rw [LinearMap.mem_ker] at hx
    exact h x (by simpa [ha] using hax) (by simpa [hc] using hx)
  have hinj : Function.Injective (a.domRestrict (LinearMap.ker c)) := by
    intro x y hxy
    have hxy' : a ((x : Fin n → k) - y) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr (by simpa using hxy)
    have := hkey _ (Submodule.sub_mem _ x.2 y.2) hxy'
    exact Subtype.ext (sub_eq_zero.mp this)
  have hrank : Module.finrank k L' = Module.finrank k U := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hL'
    have h2 := Submodule.finrank_add_eq_of_isCompl hU
    have h3 : Module.finrank k ((LinearMap.ker c).map a) = Module.finrank k (LinearMap.ker c) := by
      rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
    omega
  let e : L' ≃ₗ[k] U := LinearEquiv.ofFinrankEq L' U hrank
  let g : (Fin n → k) →ₗ[k] (Fin n → k) :=
    LinearMap.ofIsCompl hL' (a.domRestrict (LinearMap.ker c)) (U.subtype ∘ₗ e.toLinearMap)
  have hgL : ∀ x (hx : x ∈ LinearMap.ker c), g x = a x := fun x hx =>
    LinearMap.ofIsCompl_apply_left hL' ⟨x, hx⟩
  have hgL' : ∀ y (hy : y ∈ L'), g y = (e ⟨y, hy⟩ : Fin n → k) := fun y hy =>
    LinearMap.ofIsCompl_apply_right hL' ⟨y, hy⟩

  have hg_inj : ∀ v, g v = 0 → v = 0 := by
    intro v hv
    have hvmem : v ∈ LinearMap.ker c ⊔ L' := by rw [hL'.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hvmem
    rw [map_add, hgL x hx, hgL' y hy] at hv
    have hax : a x ∈ (LinearMap.ker c).map a ⊓ U := by
      refine ⟨Submodule.mem_map_of_mem hx, ?_⟩
      rw [eq_neg_of_add_eq_zero_left hv]
      exact U.neg_mem (e ⟨y, hy⟩).2
    rw [hU.inf_eq_bot, Submodule.mem_bot] at hax
    have hx0 := hkey x hx hax
    rw [hax, zero_add] at hv
    have hy0 : e ⟨y, hy⟩ = 0 := Subtype.ext hv
    rw [LinearEquiv.map_eq_zero_iff] at hy0
    rw [hx0, zero_add]
    exact congrArg Subtype.val hy0

  have hle : LinearMap.ker c ≤ LinearMap.ker (g - a) := fun x hx => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hgL x hx, sub_self]
  let f0 : LinearMap.range c →ₗ[k] (Fin n → k) :=
    ((LinearMap.ker c).liftQ (g - a) hle) ∘ₗ (c.quotKerEquivRange.symm.toLinearMap)
  obtain ⟨Y, hY⟩ := LinearMap.exists_extend f0
  have hfac : ∀ v, Y (c v) = g v - a v := by
    intro v
    have h0 := LinearMap.congr_fun hY ⟨c v, LinearMap.mem_range_self c v⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h0
    rw [h0]
    simp only [f0, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.sub_apply]
  refine ⟨LinearMap.toMatrix' Y, fun hdet => ?_⟩
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  apply hg_inj
  have hmv : (A + LinearMap.toMatrix' Y * C) *ᵥ v = g v := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    have hcv : C *ᵥ v = c v := by rw [hc, Matrix.toLin'_apply]
    have hav : A *ᵥ v = a v := by rw [ha, Matrix.toLin'_apply]
    rw [hcv, hfac, hav]
    abel
  rw [← hmv, hv]

theorem exists_isUnit_det_toBlocks_add_mul {R : Type} [CommRing R] [IsLocalRing R] {n : ℕ}
    (H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (hH : IsUnit H.det) :
    ∃ X : Matrix (Fin n) (Fin n) R, IsUnit (H.toBlocks₁₁ + X * H.toBlocks₂₁).det := by
  classical
  set Hb := H.map (IsLocalRing.residue R) with hHb_def
  have hHb : Hb.det ≠ 0 := by
    rw [hHb_def, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hH.map (IsLocalRing.residue R)).ne_zero
  obtain ⟨Xb, hXb⟩ := exists_det_add_mul_ne_zero_of_ker_inf Hb.toBlocks₁₁ Hb.toBlocks₂₁ (by
    intro v h1 h2
    by_contra hv
    apply hHb
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Sum.elim v 0, ?_, ?_⟩
    · intro h0
      apply hv
      funext i
      simpa using congrFun h0 (Sum.inl i)
    · funext i
      cases i with
      | inl i =>
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁] using congrFun h1 i
      | inr i =>
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁] using congrFun h2 i)
  choose X hX using fun i j => IsLocalRing.residue_surjective (R := R) (Xb i j)
  refine ⟨Matrix.of X, ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hm : (IsLocalRing.residue R).mapMatrix (H.toBlocks₁₁ + Matrix.of X * H.toBlocks₂₁) =
      Hb.toBlocks₁₁ + Xb * Hb.toBlocks₂₁ := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.mul_apply, map_sum, hX, hHb_def, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁]
  rw [hm]
  exact hXb

theorem isUnit_det_of_dual_blocks {R : Type} [CommRing R] {n : ℕ}
    (S A B C D A' C' : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det)
    (h1 : Aᵀ * (S * C') + Cᵀ * (S * A') = 0)
    (h2 : IsUnit (Bᵀ * (S * C') + Dᵀ * (S * A')).det) : IsUnit A'.det := by
  have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
  have hSC : S * C' = -(Aᵀ⁻¹ * (Cᵀ * (S * A'))) := by
    have h1' : Aᵀ * (S * C') = -(Cᵀ * (S * A')) := eq_neg_of_add_eq_zero_left h1
    calc S * C' = Aᵀ⁻¹ * (Aᵀ * (S * C')) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAt, Matrix.one_mul]
      _ = -(Aᵀ⁻¹ * (Cᵀ * (S * A'))) := by rw [h1', Matrix.mul_neg]
  have key : Bᵀ * (S * C') + Dᵀ * (S * A') = (Dᵀ - Bᵀ * Aᵀ⁻¹ * Cᵀ) * (S * A') := by
    rw [hSC]
    generalize Aᵀ⁻¹ = M
    noncomm_ring
  rw [key, Matrix.det_mul, Matrix.det_mul] at h2
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right h2)

private lemma blocks_conj_eq_fromBlocks_sums {R : Type} [CommRing R] {n : ℕ}
    (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix.fromBlocks 1 1 1 (-1) * G * Matrix.fromBlocks 1 1 1 (-1) =
      Matrix.fromBlocks (G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂)
        (G.toBlocks₁₁ - G.toBlocks₁₂ + G.toBlocks₂₁ - G.toBlocks₂₂)
        (G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂)
        (G.toBlocks₁₁ - G.toBlocks₁₂ - G.toBlocks₂₁ + G.toBlocks₂₂) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks G]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1 <;> noncomm_ring

private lemma H_affine_combination_eq_of_quadratic_relation {R : Type} [CommRing R] {n : ℕ}
    (S a11 a12 a21 a22 b11 b12 b21 b22 X₁ X₂ : Matrix (Fin n) (Fin n) R)
    (E11 : a11ᵀ * S * b11 - a21ᵀ * S * b21 = S) (E12 : a11ᵀ * S * b12 - a21ᵀ * S * b22 = 0)
    (E21 : a12ᵀ * S * b11 - a22ᵀ * S * b21 = 0) (E22 : a12ᵀ * S * b12 - a22ᵀ * S * b22 = -S)
    (hX : X₁ᵀ * S + S * X₂ = 0) :
    (a11 + a12 + a21 + a22 + X₁ * (a11 + a12 - a21 - a22))ᵀ * (S * (b11 + b12 - b21 - b22)) +
        (a11 + a12 - a21 - a22)ᵀ *
          (S * (b11 + b12 + b21 + b22 + X₂ * (b11 + b12 - b21 - b22))) = 0 ∧
      (a11 - a12 + a21 - a22 + X₁ * (a11 - a12 - a21 + a22))ᵀ * (S * (b11 + b12 - b21 - b22)) +
        (a11 - a12 - a21 + a22)ᵀ *
          (S * (b11 + b12 + b21 + b22 + X₂ * (b11 + b12 - b21 - b22))) = S + S + S + S := by
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul]
  constructor
  · calc _ = ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) +
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) + (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) +
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) + (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          (a11ᵀ + a12ᵀ - a21ᵀ - a22ᵀ) * (X₁ᵀ * S + S * X₂) * (b11 + b12 - b21 - b22) := by
          noncomm_ring
      _ = 0 := by rw [E11, E12, E21, E22, hX]; noncomm_ring
  · calc _ = ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) -
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) - (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) -
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) - (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          (a11ᵀ - a12ᵀ - a21ᵀ + a22ᵀ) * (X₁ᵀ * S + S * X₂) * (b11 + b12 - b21 - b22) +
          (S + S + S + S) := by
          noncomm_ring
      _ = S + S + S + S := by rw [E11, E12, E21, E22, hX]; noncomm_ring

theorem exists_dual_pair_isUnit_det_blocks :
    ∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det := by
  intro R _ _ h2 n S hS G₁ G₂ hG₁ hG
  classical
  have hKdet : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R)
      (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R)).det := by
    rw [Matrix.det_fromBlocks_one₁₁]
    have e : (-1 - 1 * 1 : Matrix (Fin n) (Fin n) R) = (-2 : R) • (1 : Matrix (Fin n) (Fin n) R) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply]
      split_ifs <;> ring
    rw [e, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact h2.neg.pow n
  obtain ⟨X₁, hX₁⟩ := exists_isUnit_det_toBlocks_add_mul
    (Matrix.fromBlocks 1 1 1 (-1) * G₁ * Matrix.fromBlocks 1 1 1 (-1))
    (by rw [Matrix.det_mul, Matrix.det_mul]; exact (hKdet.mul hG₁).mul hKdet)
  rw [blocks_conj_eq_fromBlocks_sums, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁] at hX₁
  have hsum : X₁ᵀ * S + S * -(S⁻¹ * X₁ᵀ * S) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS,
      Matrix.one_mul, add_neg_cancel]
  refine ⟨X₁, -(S⁻¹ * X₁ᵀ * S), hsum, hX₁, ?_⟩
  have hG' := hG
  rw [← Matrix.fromBlocks_toBlocks G₁, ← Matrix.fromBlocks_toBlocks G₂, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hG'
  obtain ⟨e11, e12, e21, e22⟩ := Matrix.fromBlocks_inj.mp hG'
  have E11 : G₁.toBlocks₁₁ᵀ * S * G₂.toBlocks₁₁ - G₁.toBlocks₂₁ᵀ * S * G₂.toBlocks₂₁ = S := by
    convert e11 using 1; noncomm_ring
  have E12 : G₁.toBlocks₁₁ᵀ * S * G₂.toBlocks₁₂ - G₁.toBlocks₂₁ᵀ * S * G₂.toBlocks₂₂ = 0 := by
    convert e12 using 1; noncomm_ring
  have E21 : G₁.toBlocks₁₂ᵀ * S * G₂.toBlocks₁₁ - G₁.toBlocks₂₂ᵀ * S * G₂.toBlocks₂₁ = 0 := by
    convert e21 using 1; noncomm_ring
  have E22 : G₁.toBlocks₁₂ᵀ * S * G₂.toBlocks₁₂ - G₁.toBlocks₂₂ᵀ * S * G₂.toBlocks₂₂ = -S := by
    convert e22 using 1; noncomm_ring
  obtain ⟨c1, c2⟩ := H_affine_combination_eq_of_quadratic_relation S _ _ _ _ _ _ _ _ X₁ _ E11 E12 E21 E22 hsum
  have h4 : IsUnit (4 : R) := by
    have := h2.mul h2
    norm_num at this
    exact this
  have hU4 : IsUnit (S + S + S + S).det := by
    have e : S + S + S + S = (4 : R) • S := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e, Matrix.det_smul]
    exact (h4.pow _).mul hS
  rw [← c2] at hU4
  exact isUnit_det_of_dual_blocks S _ _ _ _ _ _ hX₁ c1 hU4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetKerEqBot
section
namespace GlobalTheory.FinsetKernelTrivial

open scoped BigOperators

noncomputable def restr {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X) :
    W →ₗ[ℂ] (P → ℂ) :=
  LinearMap.pi (fun x : P => (LinearMap.proj (R := ℂ) (φ := fun _ : X => ℂ) x.1).comp (V.subtype.comp W.subtype))

lemma restr_apply {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X)
    (w : W) (x : P) : restr V W P w x = ((w : V) : X → ℂ) x := rfl

lemma exists_finset_ker_eq_bot {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] : ∃ P : Finset X, LinearMap.ker (restr V W P) = ⊥ := by
  classical
  have hex : ∃ n, ∃ P : Finset X, Module.finrank ℂ (LinearMap.ker (restr V W P)) = n :=
    ⟨_, ∅, rfl⟩
  obtain ⟨P, hP⟩ := Nat.find_spec hex
  refine ⟨P, ?_⟩
  by_contra hne
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hf : ((w : V) : X → ℂ) ≠ 0 := by
    intro h
    apply hw0
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  have hle : LinearMap.ker (restr V W (insert x P)) < LinearMap.ker (restr V W P) := by
    refine lt_of_le_of_ne ?_ ?_
    · intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      funext y
      have := congrFun hv ⟨y.1, Finset.mem_insert_of_mem y.2⟩
      simpa [restr_apply] using this
    · intro heq
      have : w ∈ LinearMap.ker (restr V W (insert x P)) := heq ▸ hwK
      rw [LinearMap.mem_ker] at this
      have := congrFun this ⟨x, Finset.mem_insert_self x P⟩
      exact hx (by simpa [restr_apply] using this)
  have hlt := Submodule.finrank_lt_finrank_of_lt hle
  have hmin := Nat.find_min hex (hP ▸ hlt)
  exact hmin ⟨insert x P, rfl⟩

theorem main : ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ ↥V) [FiniteDimensional ℂ ↥W],
    ∃ (P : Finset X) (e : X → ↥V), ∀ w ∈ W, w = ∑ x ∈ P, (↑w : X → ℂ) x • e x := by
  intro X V W _
  classical
  obtain ⟨P, hP⟩ := exists_finset_ker_eq_bot V W
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (restr V W P) hP
  refine ⟨P, fun x => if h : x ∈ P then ((L (Pi.single ⟨x, h⟩ 1) : W) : V) else 0, ?_⟩
  intro w hw
  have h1 : (⟨w, hw⟩ : W) = L (restr V W P ⟨w, hw⟩) := by
    have := congrArg (fun g => g ⟨w, hw⟩) hL
    simpa using this.symm
  have h2 : restr V W P ⟨w, hw⟩ = ∑ x : P, ((w : X → ℂ) x.1) • (Pi.single x (1 : ℂ)) := by
    funext y
    simp [restr_apply, Finset.sum_apply, Pi.single_apply]
  have h3 : w = ∑ x : P, ((w : X → ℂ) x.1) • ((L (Pi.single x 1) : W) : V) := by
    have := congrArg (fun u : W => (u : V)) h1
    simp only at this
    conv_lhs => rw [this, h2, map_sum]
    simp [map_smul]
  conv_lhs => rw [h3]
  rw [← Finset.sum_attach P]
  refine Finset.sum_congr rfl ?_
  intro x _
  simp [x.2]

end GlobalTheory.FinsetKernelTrivial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHasDerivAtZeroOfMapAddMul
section
open MeasureTheory

namespace GlobalTheory

theorem continuous_of_map_add_mul_of_continuousAt_zero (ν : ℝ → ℂ)
    (hm : ∀ s t, ν (s + t) = ν s * ν t) (hc : ContinuousAt ν 0) : Continuous ν := by
  rw [continuous_iff_continuousAt]
  intro x
  have h1 : ν = fun y => ν x * ν (y - x) := by
    funext y
    rw [← hm]
    congr 1
    ring
  rw [h1]
  refine continuousAt_const.mul ?_
  have h2 : ContinuousAt (fun y : ℝ => y - x) x := by fun_prop
  exact ContinuousAt.comp (f := fun y : ℝ => y - x) (by simpa using hc) h2

theorem exists_hasDerivAt_zero_of_map_add_mul :
    ∀ ν : ℝ → ℂ, ν 0 = 1 → (∀ s t, ν (s + t) = ν s * ν t) → ContinuousAt ν 0 →
      ∃ a : ℂ, HasDerivAt ν a 0 := by
  intro ν h0 hm hc0
  have hc := continuous_of_map_add_mul_of_continuousAt_zero ν hm hc0
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, ν x with hF
  have hd : ∀ u, HasDerivAt F (ν u) u := fun u => (hc.deriv_integral ν 0 u ▸
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt.hasDerivAt)
  have hex : ∃ δ, F δ ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hz : F = fun _ => 0 := funext hne
    have h1 := hd 0
    rw [hz, h0] at h1
    exact one_ne_zero (h1.unique (hasDerivAt_const (0:ℝ) (0:ℂ)))
  obtain ⟨δ, hδ⟩ := hex
  have key : ∀ t, ν t = (F (t + δ) - F t) / F δ := by
    intro t
    rw [eq_div_iff hδ]
    have e1 : F (t + δ) - F t = ∫ x in t..(t + δ), ν x := by
      simp only [hF]
      exact intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)
    have e2 : ∫ x in t..(t + δ), ν x = ∫ x in (0:ℝ)..δ, ν (t + x) := by
      rw [intervalIntegral.integral_comp_add_left ν t, add_zero]
    rw [e1, e2]
    simp only [hm, hF]
    rw [intervalIntegral.integral_const_mul]
  have h1 : HasDerivAt (fun t => F (t + δ)) (ν (0 + δ)) 0 := (hd (0 + δ)).comp_add_const 0 δ
  refine ⟨(ν (0 + δ) - ν 0) / F δ, ?_⟩
  have h2 := (h1.sub (hd 0)).div_const (F δ)
  have h3 : ν = fun t => (F (t + δ) - F t) / F δ := funext key
  conv => arg 1; rw [h3]
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInterpolation
section
namespace GlobalTheory.LagrangeInterpolationExistence

theorem exists_sum_add {X M : Type} [AddCommGroup M] [Module ℂ M] (S : Finset X) (a : X → M)
    (y : X) (b : M) :
    ∃ (T : Finset X) (u : X → M), ∀ c : X → ℂ,
      ∑ x ∈ T, c x • u x = ∑ x ∈ S, c x • a x + c y • b := by
  classical
  refine ⟨insert y S, fun x => if x = y then (if y ∈ S then a y + b else b) else a x, fun c => ?_⟩
  by_cases hy : y ∈ S
  · rw [Finset.insert_eq_of_mem hy, ← Finset.add_sum_erase S _ hy, ← Finset.add_sum_erase S _ hy]
    simp only [if_pos rfl, hy, if_true, ite_true, smul_add]
    rw [Finset.sum_congr rfl (fun x hx => by rw [if_neg (Finset.ne_of_mem_erase hx)])]
    abel
  · rw [Finset.sum_insert hy]
    simp only [if_neg hy, eq_self_iff_true, if_true, ite_true]
    rw [Finset.sum_congr rfl (fun x hx => by rw [if_neg (fun (h : x = y) => hy (h ▸ hx))]), add_comm]

theorem exists_interpolation {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset V) :
    ∃ (S : Finset X) (u : X → V), ∀ f ∈ F, f = ∑ x ∈ S, (f : X → ℂ) x • u x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨∅, 0, by simp⟩
  | insert g F _ ih =>
    obtain ⟨S, u, hu⟩ := ih
    set h : V := g - ∑ x ∈ S, (g : X → ℂ) x • u x with hh
    by_cases h0 : h = 0
    · refine ⟨S, u, fun f hf => ?_⟩
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact sub_eq_zero.mp h0
      · exact hu f hf
    · obtain ⟨y, hy⟩ : ∃ y, (h : X → ℂ) y ≠ 0 := by
        by_contra hc
        apply h0
        ext y
        by_contra hy
        exact hc ⟨y, by simpa using hy⟩
      obtain ⟨T, w, hw⟩ := exists_sum_add S
        (fun x => u x - ((u x : X → ℂ) y / (h : X → ℂ) y) • h) y (((h : X → ℂ) y)⁻¹ • h)
      have key : ∀ f : V, ∑ x ∈ T, (f : X → ℂ) x • w x =
          ∑ x ∈ S, (f : X → ℂ) x • u x +
            (((f - ∑ x ∈ S, (f : X → ℂ) x • u x : V) : X → ℂ) y / (h : X → ℂ) y) • h := by
        intro f
        rw [hw]
        simp only [smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul,
          Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_div, sub_smul, Finset.sum_div,
          mul_div_assoc, div_eq_mul_inv, Finset.sum_mul, mul_assoc, sub_mul]
        abel
      refine ⟨T, w, fun f hf => ?_⟩
      rw [key]
      rcases Finset.mem_insert.mp hf with rfl | hf
      · rw [← hh, div_self hy, one_smul, hh]; abel
      · rw [← hu f hf]; simp

end GlobalTheory.LagrangeInterpolationExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsUnitIntegral
section
open NormedSpace Filter Topology

namespace GlobalTheory.ExponentialIntegralUnits

universe u_1

variable {𝔸 : Type u_1} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasDerivAt_primitive (M : ℝ → 𝔸) (hc : Continuous M) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, M s) (M t) t := by
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem exists_isUnit_integral (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1) :
    ∃ δ : ℝ, IsUnit (∫ s in (0 : ℝ)..δ, M s) := by
  have hd := (hasDerivAt_primitive M hc 0).tendsto_slope_zero
  rw [h0] at hd
  have hev := hd.eventually (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨δ, hδU, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0' : δ ≠ 0 := Set.mem_compl_singleton_iff.1 hδ0
  simp only [zero_add, intervalIntegral.integral_same, sub_zero] at hδU
  refine ⟨δ, ?_⟩
  have e : (∫ s in (0 : ℝ)..δ, M s) = algebraMap ℝ 𝔸 δ * (δ⁻¹ • ∫ s in (0 : ℝ)..δ, M s) := by
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hδ0', one_smul]
  rw [e]
  exact ((isUnit_iff_ne_zero.2 hδ0').map (algebraMap ℝ 𝔸)).mul hδU

theorem mul_integral (M : ℝ → 𝔸) (hc : Continuous M)
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) (t δ : ℝ) :
    M t * (∫ s in (0 : ℝ)..δ, M s)
      = (∫ s in (0 : ℝ)..(t + δ), M s) - ∫ s in (0 : ℝ)..t, M s := by
  have hL := ((ContinuousLinearMap.mul ℝ 𝔸) (M t)).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
  simp only [ContinuousLinearMap.mul_apply'] at hL
  rw [← hL]
  simp_rw [← hadd]
  rw [intervalIntegral.integral_comp_add_left (fun s => M s) t, add_zero,
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _) (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _)]

theorem exists_hasDerivAt (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1)
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t : ℝ, HasDerivAt M (M t * X) t := by
  obtain ⟨δ, hA⟩ := exists_isUnit_integral M hc h0
  have hAA : (∫ s in (0 : ℝ)..δ, M s) * ↑(hA.unit⁻¹) = 1 := hA.mul_val_inv
  refine ⟨(M δ - 1) * ↑(hA.unit⁻¹), fun t => ?_⟩
  have hM : ∀ u, M u = ((∫ s in (0 : ℝ)..(u + δ), M s) - ∫ s in (0 : ℝ)..u, M s) * ↑(hA.unit⁻¹) := fun u => by
    rw [← mul_integral M hc hadd u δ, mul_assoc, hAA, mul_one]
  have hP : HasDerivAt (fun u => ∫ s in (0 : ℝ)..(u + δ), M s) (M (t + δ)) t := by
    first
      | exact (hasDerivAt_primitive M hc (t + δ)).comp_add_const t δ
      | exact HasDerivAt.comp_add_const t δ (hasDerivAt_primitive M hc (t + δ))
  have hF := (hP.sub (hasDerivAt_primitive M hc t)).mul_const (↑(hA.unit⁻¹) : 𝔸)
  have hF' := hF.congr_of_eventuallyEq (Eventually.of_forall hM)
  refine hF'.congr_deriv ?_
  rw [hadd, ← mul_assoc, mul_sub, mul_one]

theorem exists_exp_eq (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M (0 : ℝ) = (1 : 𝔸))
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t : ℝ, NormedSpace.exp (t • X) = M t := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨X, hX⟩ := exists_hasDerivAt M hc h0 hadd
  refine ⟨X, fun t => ?_⟩
  have hN : ∀ u : ℝ, HasDerivAt (fun v => M v * NormedSpace.exp (v • (-X))) 0 u := fun u => by
    have h3 := (hX u).mul (hasDerivAt_exp_smul_const (-X) u)
    refine h3.congr_deriv ?_
    have hcomm : Commute (NormedSpace.exp (u • (-X))) X :=
      (((Commute.refl X).neg_left).smul_left u).exp_left
    rw [mul_neg, hcomm.eq, mul_neg, ← mul_assoc, add_neg_cancel]
  have hconst : ∀ u, M u * NormedSpace.exp (u • (-X)) = 1 := fun u => by
    have h4 := is_const_of_deriv_eq_zero (fun v => (hN v).differentiableAt) (fun v => (hN v).deriv) u 0
    rw [h4, h0, zero_smul, NormedSpace.exp_zero, one_mul]
  have hinv : NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X) = 1 := by
    rw [← NormedSpace.exp_add_of_commute ((((Commute.refl X).neg_left).smul_left t).smul_right t), smul_neg,
      neg_add_cancel, NormedSpace.exp_zero]
  calc NormedSpace.exp (t • X) = (M t * NormedSpace.exp (t • (-X))) * NormedSpace.exp (t • X) := by
        rw [hconst t, one_mul]
    _ = M t := by rw [mul_assoc, hinv, mul_one]

end GlobalTheory.ExponentialIntegralUnits
end

