import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommensurableConjRangeGLSubring
section
open Matrix

namespace GlobalTheory

section GLCong

variable {B : Type} [CommRing B] (R : Subring B) {n : ℕ}

theorem glcong_mem_range (A : GL (Fin n) B) (hA : ∀ i j, (A : Matrix (Fin n) (Fin n) B) i j ∈ R)
    (hA' : ∀ i j, ((A⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R) :
    A ∈ (GeneralLinearGroup.map (n := Fin n) R.subtype).range := by
  let M : Matrix (Fin n) (Fin n) R := fun i j => ⟨_, hA i j⟩
  let N : Matrix (Fin n) (Fin n) R := fun i j => ⟨_, hA' i j⟩
  have hM : R.subtype.mapMatrix M = (A : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
  have hN : R.subtype.mapMatrix N = ((A⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) := by ext i j; rfl
  have hinj : Function.Injective (R.subtype.mapMatrix : Matrix (Fin n) (Fin n) R →+* _) := by
    intro X Y h; ext i j; exact congrFun (congrFun h i) j
  have h1 : M * N = 1 := hinj (by rw [map_mul, map_one, hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have h2 : N * M = 1 := hinj (by rw [map_mul, map_one, hM, hN, ← Units.val_mul, inv_mul_cancel, Units.val_one])
  refine ⟨⟨M, N, h1, h2⟩, ?_⟩
  ext i j
  rfl

theorem glcong_entries (c : R) (h : GL (Fin n) R)
    (hh : GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (Ideal.span {c * c})) h = 1)
    (P Q : Matrix (Fin n) (Fin n) B) (hP : ∀ i j, (c : B) * P i j ∈ R) (hQ : ∀ i j, (c : B) * Q i j ∈ R)
    (hPQ : P * Q = 1) :
    ∀ i j, (P * R.subtype.mapMatrix (h : Matrix (Fin n) (Fin n) R) * Q) i j ∈ R := by
  have hX : ∀ i j, ∃ x : R, x * (c * c) = (h : Matrix (Fin n) (Fin n) R) i j - (1 : Matrix (Fin n) (Fin n) R) i j := by
    intro i j
    rw [← Ideal.mem_span_singleton', ← Ideal.Quotient.eq]
    have := congrArg (fun u : GL (Fin n) (R ⧸ Ideal.span {c * c}) => (u : Matrix (Fin n) (Fin n) (R ⧸ Ideal.span {c * c})) i j) hh
    simp only [GeneralLinearGroup.map_apply, Units.val_one] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  choose X hXe using hX
  let P' : Matrix (Fin n) (Fin n) R := fun i j => ⟨_, hP i j⟩
  let Q' : Matrix (Fin n) (Fin n) R := fun i j => ⟨_, hQ i j⟩
  let X' : Matrix (Fin n) (Fin n) R := fun i j => X i j
  have hP' : R.subtype.mapMatrix P' = (c : B) • P := by ext i j; rfl
  have hQ' : R.subtype.mapMatrix Q' = (c : B) • Q := by ext i j; rfl
  have hh' : (h : Matrix (Fin n) (Fin n) R) = 1 + (c * c) • X' := by
    refine Matrix.ext fun i j => ?_
    show _ = (1 : Matrix (Fin n) (Fin n) R) i j + (c * c) * X i j
    rw [mul_comm, hXe i j]; ring
  have key : P * R.subtype.mapMatrix (h : Matrix (Fin n) (Fin n) R) * Q
      = R.subtype.mapMatrix (1 + P' * X' * Q') := by
    have hs : R.subtype.mapMatrix ((c * c) • X') = ((c : B) * (c : B)) • R.subtype.mapMatrix X' := by
      ext i j
      change ((c * c * X i j : R) : B) = (c : B) * c * (X i j : B)
      push_cast; ring
    rw [map_add, map_one, map_mul, map_mul, hP', hQ', hh', map_add, map_one, hs]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPQ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  intro i j
  rw [key]
  exact ((1 + P' * X' * Q' : Matrix (Fin n) (Fin n) R) i j).2

theorem glcong_relIndex_ne_zero (c : R) (hfin : Finite (R ⧸ Ideal.span {c * c})) (g : GL (Fin n) B)
    (hg : ∀ i j, (c : B) * (g : Matrix (Fin n) (Fin n) B) i j ∈ R)
    (hg' : ∀ i j, (c : B) * ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R) :
    (((GeneralLinearGroup.map (n := Fin n) R.subtype).range).map (MulAut.conj g).toMonoidHom).relIndex
      (GeneralLinearGroup.map (n := Fin n) R.subtype).range ≠ 0 := by
  set φ := GeneralLinearGroup.map (n := Fin n) R.subtype
  set ψ := GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (Ideal.span {c * c}))
  have hΓ : ψ.ker.index ≠ 0 := by
    rw [Subgroup.index_ker]
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    ext i j
    exact congrArg (fun u : GL (Fin n) B => (u : Matrix (Fin n) (Fin n) B) i j) hab
  have h1 : (ψ.ker.map φ).relIndex φ.range ≠ 0 := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj,
      Subgroup.relIndex_top_right]
    exact hΓ
  have hval : ∀ h : GL (Fin n) R, ((φ h : GL (Fin n) B) : Matrix (Fin n) (Fin n) B)
      = R.subtype.mapMatrix (h : Matrix (Fin n) (Fin n) R) := fun h => rfl
  have hgg : ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) * (g : Matrix (Fin n) (Fin n) B) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : ψ.ker.map φ ≤ φ.range.map (MulAut.conj g).toMonoidHom := by
    rintro x ⟨h, hh, rfl⟩
    replace hh : ψ h = 1 := hh
    have hh' : ψ h⁻¹ = 1 := by rw [map_inv, hh, inv_one]
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ * φ h * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    apply glcong_mem_range
    · intro i j
      have := glcong_entries R c h hh _ _ hg' hg hgg i j
      rwa [Units.val_mul, Units.val_mul, hval]
    · intro i j
      have := glcong_entries R c h⁻¹ hh' _ _ hg' hg hgg i j
      rwa [show (g⁻¹ * φ h * g)⁻¹ = g⁻¹ * φ h⁻¹ * g by rw [map_inv]; group, Units.val_mul, Units.val_mul, hval]
  exact fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_left h2 h0)

end GLCong

theorem commensurable_conj_range_GL_subring {B : Type} [CommRing B] (R : Subring B) (n : ℕ) (c : R)
    (hfin : Finite (R ⧸ Ideal.span {c * c})) (g : GL (Fin n) B)
    (hg : ∀ i j, (c : B) * (g : Matrix (Fin n) (Fin n) B) i j ∈ R)
    (hg' : ∀ i j, (c : B) * ((g⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j ∈ R) :
    Subgroup.Commensurable ((GeneralLinearGroup.map R.subtype).range.map (MulAut.conj g).toMonoidHom)
      (GeneralLinearGroup.map R.subtype).range := by
  set K := (GeneralLinearGroup.map (n := Fin n) R.subtype).range
  refine ⟨glcong_relIndex_ne_zero R c hfin g hg hg', ?_⟩
  have e := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (K.map (MulAut.conj g⁻¹).toMonoidHom) K (MulEquiv.injective _)
  have hK : (K.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = K := by
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id K]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hK] at e
  rw [e]
  exact glcong_relIndex_ne_zero R c hfin g⁻¹ hg' (by simpa using hg)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfCommuteSeparableCharpoly
section
open Matrix Polynomial

namespace GlobalTheory

open Matrix Polynomial in
private theorem exists_eigenvector_of_isRoot_charpoly {L : Type} [Field L] {n : ℕ}
    (y : Matrix (Fin n) (Fin n) L) (r : L) (h : y.charpoly.IsRoot r) :
    ∃ v : Fin n → L, v ≠ 0 ∧ y *ᵥ v = r • v := by
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, not_not, ← Matrix.exists_mulVec_eq_zero_iff] at h
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero] at hv
  exact hv.symm

open Matrix Polynomial in
private theorem isUnit_of_eigenvector_columns_of_injective {L : Type} [Field L] {n : ℕ}
    (y : Matrix (Fin n) (Fin n) L) (μ : Fin n → L) (hμ : Function.Injective μ)
    (v : Fin n → Fin n → L) (hv0 : ∀ j, v j ≠ 0) (hv : ∀ j, y *ᵥ v j = μ j • v j) :
    IsUnit (Matrix.of fun i j => v j i) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  exact Module.End.eigenvectors_linearIndependent' (Matrix.toLin' y) μ hμ v
    (fun j => ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hv j), hv0 j⟩)

open Matrix Polynomial in
private theorem eq_diagonal_of_commute_diagonal_injective {L : Type} [Field L] {n : ℕ}
    (μ : Fin n → L) (hμ : Function.Injective μ) (m : Matrix (Fin n) (Fin n) L)
    (hm : m * diagonal μ = diagonal μ * m) : m = diagonal fun i => m i i := by
  ext i j
  have hij := congrFun (congrFun hm i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.diagonal_apply_ne _ h]
    have hne : μ j - μ i ≠ 0 := sub_ne_zero.mpr fun e => h (hμ e).symm
    have : m i j * (μ j - μ i) = 0 := by rw [mul_sub, hij, mul_comm]; ring
    exact (mul_eq_zero.mp this).resolve_right hne

open Matrix Polynomial in
private theorem commute_of_commute_of_charpoly_separable_of_isAlgClosed {L : Type} [Field L]
    [IsAlgClosed L] {n : ℕ} (y a b : Matrix (Fin n) (Fin n) L) (hy : y.charpoly.Separable)
    (ha : a * y = y * a) (hb : b * y = y * b) : a * b = b * a := by
  classical
  set s := y.charpoly.roots.toFinset with hs_def
  have hs : s.card = n := by
    rw [hs_def, Multiset.toFinset_card_of_nodup (nodup_roots hy),
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hs)).symm
  let μ : Fin n → L := fun i => (e i : L)
  have hμ : Function.Injective μ := fun i j hij => e.injective (Subtype.ext hij)
  have hroot : ∀ i, y.charpoly.IsRoot (μ i) := fun i => by
    have hmem : (μ i) ∈ s := (e i).2
    rw [hs_def, Multiset.mem_toFinset] at hmem
    exact (mem_roots hy.ne_zero).mp hmem
  choose v hv0 hv using fun i => exists_eigenvector_of_isRoot_charpoly y (μ i) (hroot i)
  set P : Matrix (Fin n) (Fin n) L := Matrix.of fun i j => v j i with hP
  have hPu : IsUnit P := isUnit_of_eigenvector_columns_of_injective y μ hμ v hv0 hv
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  set Q := P⁻¹ with hQ
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hdet
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPQ' : ∀ X : Matrix (Fin n) (Fin n) L, P * (Q * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hQP' : ∀ X : Matrix (Fin n) (Fin n) L, Q * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hyP : y * P = P * diagonal μ := by
    ext i j
    rw [Matrix.mul_diagonal]
    have := congrFun (hv j) i
    simpa [hP, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
  have hD : Q * y * P = diagonal μ := by
    rw [Matrix.mul_assoc, hyP, hQP']
  have hcomm : ∀ m : Matrix (Fin n) (Fin n) L, m * y = y * m →
      (Q * m * P) * diagonal μ = diagonal μ * (Q * m * P) := fun m hm => by
    rw [← hD]
    simp only [Matrix.mul_assoc, hPQ']
    rw [← Matrix.mul_assoc m y P, hm, Matrix.mul_assoc]
  have hA := eq_diagonal_of_commute_diagonal_injective μ hμ _ (hcomm a ha)
  have hB := eq_diagonal_of_commute_diagonal_injective μ hμ _ (hcomm b hb)
  have hAB : (Q * a * P) * (Q * b * P) = (Q * b * P) * (Q * a * P) := by
    rw [hA, hB, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have key : ∀ c d : Matrix (Fin n) (Fin n) L, c * d = P * ((Q * c * P) * (Q * d * P)) * Q :=
    fun c d => by
      simp only [Matrix.mul_assoc, hPQ', hPQ, Matrix.mul_one]
  rw [key a b, key b a, hAB]

open Matrix Polynomial in

theorem _root_.GlobalTheory.commute_of_commute_separable_charpoly :
    ∀ (K : Type) [Field K] (n : ℕ) (y a b : Matrix (Fin n) (Fin n) K), y.charpoly.Separable →
      a * y = y * a → b * y = y * b → a * b = b * a := by
  intro K _ n y a b hy ha hb
  let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hyL : (y.map f).charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact hy.map
  have haL : a.map f * y.map f = y.map f * a.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ha]
  have hbL : b.map f * y.map f = y.map f * b.map f := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hb]
  have h := commute_of_commute_of_charpoly_separable_of_isAlgClosed _ _ _ hyL haL hbL
  rw [← Matrix.map_mul, ← Matrix.map_mul] at h
  exact Matrix.map_injective f.injective h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCharEqOneOfForallCircleChar
section
namespace GlobalTheory

noncomputable def circArgChar {G : Type} [Group G] (ν : G →* ℂˣ) : G →* Circle where
  toFun g := ⟨(ν g : ℂ) / (‖(ν g : ℂ)‖ : ℂ), by
    have h : ‖(ν g : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν g).ne_zero
    simp [Submonoid.unitSphere, h]⟩
  map_one' := by
    apply Circle.ext
    simp
  map_mul' a b := by
    apply Circle.ext
    show ((ν (a * b) : ℂˣ) : ℂ) / (‖((ν (a * b) : ℂˣ) : ℂ)‖ : ℂ) =
      ((ν a : ℂ) / (‖(ν a : ℂ)‖ : ℂ)) * ((ν b : ℂ) / (‖(ν b : ℂ)‖ : ℂ))
    rw [ν.map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]

noncomputable def circNormChar {G : Type} [Group G] (ν : G →* ℂˣ) (t : ℝ) : G →* Circle where
  toFun g := Circle.exp (t * Real.log ‖(ν g : ℂ)‖)
  map_one' := by simp
  map_mul' a b := by
    have ha : ‖(ν a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν a).ne_zero
    have hb : ‖(ν b : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν b).ne_zero
    show Circle.exp (t * Real.log ‖((ν (a * b) : ℂˣ) : ℂ)‖) = _
    rw [ν.map_mul, Units.val_mul, norm_mul, Real.log_mul ha hb, mul_add, Circle.exp_add]

private theorem coe_circArgChar_eq_div_norm {G : Type} [Group G] (ν : G →* ℂˣ) (g : G) :
    ((circArgChar ν g : Circle) : ℂ) = (ν g : ℂ) / (‖(ν g : ℂ)‖ : ℂ) := by
  rfl

theorem complexChar_eq_one_of_forall_circleChar :
    ∀ {G : Type} [Group G] (ν : G →* ℂˣ) (x : G),
      (∀ μ : G →* Circle, (∀ g, ν g = 1 → μ g = 1) → μ x = 1) → ν x = 1 := by
  intro G _ ν x h
  have hx0 : (ν x : ℂ) ≠ 0 := (ν x).ne_zero
  have hpos : 0 < ‖(ν x : ℂ)‖ := norm_pos_iff.mpr hx0

  have hn : ‖(ν x : ℂ)‖ = 1 := by
    by_contra hne
    have hlog : Real.log ‖(ν x : ℂ)‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hne
    have h2 := h (circNormChar ν (Real.pi / Real.log ‖(ν x : ℂ)‖)) (fun g hg => by
      simp [circNormChar, hg])
    have h3 := congrArg (fun z : Circle => (z : ℂ)) h2
    simp only [circNormChar, MonoidHom.coe_mk, OneHom.coe_mk, Circle.coe_exp,
      div_mul_cancel₀ _ hlog, Circle.coe_one] at h3
    norm_num [Complex.exp_pi_mul_I] at h3

  have h1 := h (circArgChar ν) (fun g hg => by
    apply Circle.ext
    rw [coe_circArgChar_eq_div_norm, hg]
    simp)
  have h4 := congrArg (fun z : Circle => (z : ℂ)) h1
  simp only [coe_circArgChar_eq_div_norm, Circle.coe_one, hn, Complex.ofReal_one, div_one] at h4
  apply Units.ext
  simpa using h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexMatrixDescendsOfRationalOnTuple
section
namespace GlobalTheory

theorem complex_matrix_descends_of_rational_on_tuple : ∀ {K : Type} [Field K] (σ : K →+* ℂ) {T : Type} (n D : ℕ) (dQ nV : T → ℕ) (ι : ∀ t, Matrix (Fin D) (Fin (dQ t)) K) (Pq : ∀ t, Matrix (Fin (dQ t)) (Fin (nV t)) K) (V : ∀ t, Matrix (Fin n) (Fin (nV t)) K) (r : T → K) (U : Set T) (t0 : T) (Ψc : Matrix (Fin n) (Fin D) ℂ), t0 ∈ U → Function.Bijective (ι t0).mulVec → Function.Surjective (Pq t0).mulVec → (∀ t ∈ U, Ψc * (ι t * Pq t).map σ = ((r t)⁻¹ • V t).map σ) → (∃ Ψ : Matrix (Fin n) (Fin D) K, Ψ.map σ = Ψc ∧ ∀ t ∈ U, Ψ * ι t * Pq t = (r t)⁻¹ • V t) ∧ (Function.Injective Ψc.mulVec → r t0 = 1 → LinearMap.ker (V t0).mulVecLin = LinearMap.ker (Pq t0).mulVecLin) := by
  intro K _ σ T n D dQ nV ι Pq V r U t0 Ψc ht0 hι hP h
  have hσ : Function.Injective σ := σ.injective
  have hsurj : Function.Surjective (ι t0 * Pq t0).mulVec := by
    intro y
    obtain ⟨x, rfl⟩ := hι.2 y
    obtain ⟨z, rfl⟩ := hP x
    exact ⟨z, (Matrix.mulVec_mulVec _ _ _).symm⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.1 hsurj
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Matrix (Fin n) (Fin D) K, Ψ = ((r t0)⁻¹ • V t0) * R := ⟨_, rfl⟩
  have hΨc : Ψ.map σ = Ψc := by
    calc Ψ.map σ = ((r t0)⁻¹ • V t0).map σ * R.map σ := by rw [hΨ, Matrix.map_mul]
      _ = Ψc * (ι t0 * Pq t0).map σ * R.map σ := by rw [h t0 ht0]
      _ = Ψc * ((ι t0 * Pq t0) * R).map σ := by rw [Matrix.map_mul (M := R), Matrix.mul_assoc]
      _ = Ψc := by rw [hR, Matrix.map_one σ σ.map_zero σ.map_one, Matrix.mul_one]
  have hall : ∀ t ∈ U, Ψ * ι t * Pq t = (r t)⁻¹ • V t := by
    intro t ht
    apply Matrix.map_injective hσ
    show (Ψ * ι t * Pq t).map σ = ((r t)⁻¹ • V t).map σ
    rw [Matrix.mul_assoc, Matrix.map_mul, hΨc, h t ht]
  refine ⟨⟨Ψ, hΨc, hall⟩, fun hinj hr => ?_⟩
  have key : Ψ * ι t0 * Pq t0 = V t0 := by
    rw [hall t0 ht0, hr, inv_one, one_smul]
  have hΨinj : Function.Injective Ψ.mulVec := by
    intro x y hxy
    have hc : Ψc.mulVec (fun j => σ (x j)) = Ψc.mulVec (fun j => σ (y j)) := by
      funext i
      change (Ψc).mulVec (σ ∘ x) i = (Ψc).mulVec (σ ∘ y) i
      rw [← hΨc, ← RingHom.map_mulVec, ← RingHom.map_mulVec, hxy]
    funext j
    exact hσ (congrFun (hinj hc) j)
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hv
    rw [← key, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hv
    have h1 : (ι t0).mulVec ((Pq t0).mulVec v) = 0 := hΨinj (hv.trans (Matrix.mulVec_zero Ψ).symm)
    exact hι.1 (h1.trans (Matrix.mulVec_zero (ι t0)).symm)
  · intro hv
    rw [← key, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentInFibreIffOfIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem image_connectedComponent_of_isEmbedding {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {q : A → B} (hq : Topology.IsEmbedding q) (a : A) :
    q '' connectedComponent a = connectedComponentIn (Set.range q) (q a) := by
  apply Set.Subset.antisymm
  · exact (isPreconnected_connectedComponent.image q hq.continuous.continuousOn).subset_connectedComponentIn
      ⟨a, mem_connectedComponent, rfl⟩ (Set.image_subset_range _ _)
  · intro x hx
    have hsub : connectedComponentIn (Set.range q) (q a) ⊆ Set.range q := connectedComponentIn_subset _ _
    have himg : q '' (q ⁻¹' connectedComponentIn (Set.range q) (q a)) = connectedComponentIn (Set.range q) (q a) :=
      Set.image_preimage_eq_of_subset hsub
    have hpc : IsPreconnected (q ⁻¹' connectedComponentIn (Set.range q) (q a)) := by
      rw [← hq.isInducing.isPreconnected_image, himg]
      exact isPreconnected_connectedComponentIn
    have hS : q ⁻¹' connectedComponentIn (Set.range q) (q a) ⊆ connectedComponent a :=
      hpc.subset_connectedComponent (mem_connectedComponentIn ⟨a, rfl⟩)
    rw [← himg] at hx
    exact Set.image_mono hS hx

theorem component_in_fibre_iff_of_isPullback :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X) (s : S) (Y : Scheme.{0}) (g : Y ⟶ Spec (S.residueField s))
      (q : Y ⟶ X) (y₀ : Y), IsPullback q g f (S.fromSpecResidueField s) → q y₀ = e s →
      ∀ y : Y, q y ∈ connectedComponentIn (f ⁻¹' {s}) (e s) ↔ y ∈ connectedComponent y₀ := by
  intro X S f e s Y g q y₀ hP h0 y
  haveI : IsPreimmersion q :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hP.flip inferInstance
  have hq : Topology.IsEmbedding q := q.isEmbedding
  have hr : Set.range q = f ⁻¹' {s} := by
    have h1 : Set.range q = Set.range (pullback.fst f (S.fromSpecResidueField s)) := by
      rw [← hP.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr, Set.image_univ]
      exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso hP.isoPullback)).surjective
    rw [h1, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
  rw [← h0, ← hr, ← image_connectedComponent_of_isEmbedding hq]
  exact hq.injective.mem_set_image

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAlgApply
section
namespace GlobalTheory.ConjugateAlgebraLemmas

open Matrix

def conjAlg {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) K where
  toFun M := ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (g : Matrix (Fin n) (Fin n) K)
  map_one' := by simp
  map_mul' M N := by
    have h : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (M * N) * (g : Matrix (Fin n) (Fin n) K)
        = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * ((g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * N * (g : Matrix (Fin n) (Fin n) K) := by rw [h, Matrix.mul_one, Matrix.mul_assoc ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M N]
      _ = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (g : Matrix (Fin n) (Fin n) K) * (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * N * (g : Matrix (Fin n) (Fin n) K)) := by simp only [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' r := by
    have h : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h]

theorem conjAlg_apply {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) (M : Matrix (Fin n) (Fin n) K) :
    conjAlg g M = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (g : Matrix (Fin n) (Fin n) K) := rfl

theorem aeval_conj {K : Type} [Field K] {n : ℕ} (γ g : GL (Fin n) K) (Q : Polynomial K) :
    Polynomial.aeval ((↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K)) Q
      = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q * (g : Matrix (Fin n) (Fin n) K) := by
  have h : ((↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K)) = conjAlg g (γ : Matrix (Fin n) (Fin n) K) := by
    rw [conjAlg_apply, Units.val_mul, Units.val_mul]
  rw [h, Polynomial.aeval_algHom_apply, conjAlg_apply]

theorem gram_eq {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (g : Matrix (Fin n) (Fin n) K)
    (hg : (g.map σ)ᵀ * g = 1) (a b : Fin n → K) :
    ∑ k : Fin n, σ ((g *ᵥ a) k) * (g *ᵥ b) k = ∑ k : Fin n, σ (a k) * b k := by
  have h1 : ∀ k, σ ((g *ᵥ a) k) = ((g.map σ) *ᵥ (fun i => σ (a i))) k := by
    intro k
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp_rw [h1]
  change (g.map σ *ᵥ fun i => σ (a i)) ⬝ᵥ (g *ᵥ b) = (fun i => σ (a i)) ⬝ᵥ b
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hg, Matrix.vecMul_one]

theorem main : ∀ {K : Type} [inst : Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K), Matrix.transpose (Matrix.map (↑g : Matrix (Fin n) (Fin n) K) (⇑σ : K → K)) * (↑g : Matrix (Fin n) (Fin n) K) = (1 : Matrix (Fin n) (Fin n) K) → ∀ (Q : Polynomial K) {ι : Type} (u : ι → Fin n → K), LinearIndependent K u → Submodule.span K (Set.range u) = LinearMap.ker ((Matrix.toLin' : Matrix (Fin n) (Fin n) K → (Fin n → K) →ₗ[K] Fin n → K) ((Polynomial.aeval (↑(g⁻¹ * γ * g) : Matrix (Fin n) (Fin n) K) : Polynomial K → Matrix (Fin n) (Fin n) K) Q)) → (LinearIndependent K fun (i : ι) ↦ Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u i)) ∧ Submodule.span K (Set.range fun (i : ι) ↦ Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u i)) = LinearMap.ker ((Matrix.toLin' : Matrix (Fin n) (Fin n) K → (Fin n → K) →ₗ[K] Fin n → K) ((Polynomial.aeval (↑γ : Matrix (Fin n) (Fin n) K) : Polynomial K → Matrix (Fin n) (Fin n) K) Q)) ∧ ((Matrix.of : (ι → ι → K) → Matrix ι ι K) fun (i j : ι) ↦ ∑ k : Fin n, (σ : K → K) (Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u i) k) * Matrix.mulVec (↑g : Matrix (Fin n) (Fin n) K) (u j) k) = (Matrix.of : (ι → ι → K) → Matrix ι ι K) fun (i j : ι) ↦ ∑ k : Fin n, (σ : K → K) (u i k) * u j k := by
  intro K _ σ n γ g hg Q ι u hu hspan
  have hgg : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgg' : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨?_, ?_, ?_⟩
  · have hinj : Function.Injective (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) := by
      intro x y hxy
      have h := congrArg (fun z => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z) hxy
      simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hgg'] using h
    exact hu.map' (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) (LinearMap.ker_eq_bot.mpr hinj)
  · have hmap : Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
        (Submodule.span K (Set.range u)).map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap, hspan, aeval_conj]
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker, Matrix.toLin'_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      calc Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ x)
          = (g : Matrix (Fin n) (Fin n) K) *ᵥ ((((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q * (g : Matrix (Fin n) (Fin n) K)) *ᵥ x) := by
            simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hgg, Matrix.one_mul]
        _ = 0 := by rw [hx, Matrix.mulVec_zero]
    · intro hy
      refine ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y, ?_, ?_⟩
      · calc (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q * (g : Matrix (Fin n) (Fin n) K)) *ᵥ
              (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y)
            = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
              (Polynomial.aeval (γ : Matrix (Fin n) (Fin n) K) Q *ᵥ y) := by
              simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hgg, Matrix.mul_one]
          _ = 0 := by rw [hy, Matrix.mulVec_zero]
      · rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  · ext i j
    simp only [Matrix.of_apply]
    exact gram_eq σ (g : Matrix (Fin n) (Fin n) K) hg (u i) (u j)

end GlobalTheory.ConjugateAlgebraLemmas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffHasse
section
namespace GlobalTheory.PicDiv

variable {R : Type*} [CommRing R]

noncomputable def hasse (l : ℕ) : PowerSeries R →ₗ[R] PowerSeries R where
  toFun φ := PowerSeries.mk fun n => ((n + l).choose l : R) * PowerSeries.coeff (n + l) φ
  map_add' φ ψ := by ext n; simp [mul_add]
  map_smul' c φ := by ext n; simp [mul_left_comm]

theorem coeff_hasse (l n : ℕ) (φ : PowerSeries R) :
    PowerSeries.coeff n (hasse l φ) = ((n + l).choose l : R) * PowerSeries.coeff (n + l) φ := by
  simp [hasse]

theorem constantCoeff_hasse (l : ℕ) (φ : PowerSeries R) :
    PowerSeries.constantCoeff (hasse l φ) = PowerSeries.coeff l φ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_hasse]; simp

theorem coeff_one_hasse (l : ℕ) (φ : PowerSeries R) :
    PowerSeries.coeff 1 (hasse l φ) = ((l + 1 : ℕ) : R) * PowerSeries.coeff (l + 1) φ := by
  rw [coeff_hasse, add_comm 1 l, Nat.choose_succ_self_right]

theorem hasse_zero (φ : PowerSeries R) : hasse 0 φ = φ := by
  ext n; simp [coeff_hasse]

end GlobalTheory.PicDiv
end

