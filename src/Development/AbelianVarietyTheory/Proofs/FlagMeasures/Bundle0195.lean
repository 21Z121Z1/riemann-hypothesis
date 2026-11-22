import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLayerCoordsToBlocks
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.LayerIso

variable {n m d : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
  {U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {B : Fin d → Matrix (Fin n) (Fin n) ℂ} {deg : Fin d → ℕ}

theorem block_eq_zero (hU : Biorth r m U (fun b => (U b)ᴴ)) {t : ℕ} (ht : m ≤ t) : U t = 0 := by
  obtain ⟨-, h2, h3⟩ := hU
  have : U t = (∑ b ∈ range m, U b * (U b)ᴴ) * U t := by rw [h3, Matrix.one_mul]
  rw [this, Matrix.sum_mul]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hb' : b ≠ t := by have := Finset.mem_range.1 hb; omega
  rw [Matrix.mul_assoc, h2 b t hb', Matrix.mul_zero]

theorem mem_lowers_iff (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) (c : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y ∈ lowers W c ↔ ∀ s t, t ≤ s + c → (U s)ᴴ * Y * U t = 0 := by
  obtain ⟨-, h2, h3⟩ := hU
  rw [mem_lowers]
  constructor
  · intro h s t hst
    rw [Matrix.ext_iff_mulVec]
    intro x
    have hx : U t *ᵥ x ∈ W (s + c + 1) := by
      rw [hW]
      intro b hb
      rw [Matrix.mulVec_mulVec, h2 b t (by omega), Matrix.zero_mulVec]
    have := (hW _ _).1 (h s _ hx) s le_rfl
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rw [this, Matrix.zero_mulVec]
  · intro h b y hy
    rw [hW] at hy ⊢
    intro s hs
    have : y = (∑ t ∈ range m, U t * (U t)ᴴ) *ᵥ y := by rw [h3, Matrix.one_mulVec]
    rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_sum, Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [← Matrix.mul_assoc]
    by_cases ht : t ≤ s + c
    · rw [h s t ht, Matrix.zero_mul, Matrix.zero_mulVec]
    · rw [← Matrix.mulVec_mulVec, hy t (by omega), Matrix.mulVec_zero]

theorem expand (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) (S : Set (Fin d))
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ Submodule.span ℂ (B '' S)) :
    Y = ∑ i, (Y * (B i)ᴴ).trace • B i ∧ ∀ i, i ∉ S → (Y * (B i)ᴴ).trace = 0 := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨by simp [hB], fun i hi => ?_⟩
    rw [hB, if_neg]
    rintro rfl
    exact hi hj
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [Matrix.add_mul, trace_add, add_smul, Finset.sum_add_distrib]
      rw [← hx.1, ← hy.1]
    · rw [Matrix.add_mul, trace_add, hx.2 i hi, hy.2 i hi, add_zero]
  | smul a x _ hx =>
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [Matrix.smul_mul, trace_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
      rw [← hx.1]
    · rw [Matrix.smul_mul, trace_smul, hx.2 i hi, smul_zero]

theorem trace_self {p q : Type} [Fintype p] [Fintype q] (A : Matrix p q ℂ) :
    (A * Aᴴ).trace = ((∑ s, ∑ t, ‖A s t‖ ^ 2 : ℝ) : ℂ) := by
  simp [Matrix.trace, Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem trace_blocks (hU : Biorth r m U (fun b => (U b)ᴴ)) (Y : Matrix (Fin n) (Fin n) ℂ) :
    (Y * Yᴴ).trace = ∑ s ∈ range m, ∑ t ∈ range m,
      (((U s)ᴴ * Y * U t) * ((U s)ᴴ * Y * U t)ᴴ).trace := by
  obtain ⟨-, -, h3⟩ := hU
  have : Y * Yᴴ = (∑ b ∈ range m, U b * (U b)ᴴ) * (Y * (∑ b ∈ range m, U b * (U b)ᴴ) * Yᴴ) := by
    rw [h3, Matrix.one_mul, Matrix.mul_one]
  rw [this, Matrix.sum_mul, trace_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Matrix.mul_assoc (U s), Matrix.trace_mul_comm]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem placed_block (hU : Biorth r m U (fun b => (U b)ᴴ)) {s t s' t' : ℕ}
    (Z : Matrix (Fin (r s)) (Fin (r t)) ℂ) (h : s' ≠ s ∨ t ≠ t') :
    (U s')ᴴ * (U s * Z * (U t)ᴴ) * U t' = 0 := by
  obtain ⟨-, h2, -⟩ := hU
  have : (U s')ᴴ * (U s * Z * (U t)ᴴ) * U t' = ((U s')ᴴ * U s) * Z * ((U t)ᴴ * U t') := by
    simp only [Matrix.mul_assoc]
  rw [this]
  rcases h with h | h
  · rw [h2 _ _ h]; simp
  · rw [h2 _ _ h]; simp

theorem placed_block_self (hU : Biorth r m U (fun b => (U b)ᴴ)) {s t : ℕ}
    (Z : Matrix (Fin (r s)) (Fin (r t)) ℂ) :
    (U s)ᴴ * (U s * Z * (U t)ᴴ) * U t = Z := by
  obtain ⟨h1, -, -⟩ := hU
  have : (U s)ᴴ * (U s * Z * (U t)ᴴ) * U t = ((U s)ᴴ * U s) * Z * ((U t)ᴴ * U t) := by
    simp only [Matrix.mul_assoc]
  rw [this, h1, h1]; simp

noncomputable def toBlocks (m : ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ)
    (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ) (c : ℕ) :
    ({i : Fin d // deg i = c} → ℂ) →ₗ[ℂ] (∀ b : Fin m, Fin (r b) → Fin (r (b + c + 1)) → ℂ) where
  toFun z b s t := ((U b)ᴴ * (∑ i, z i • B i.1) * U (b + c + 1)) s t
  map_add' z w := by
    funext b s t
    simp [add_smul, Finset.sum_add_distrib, Matrix.mul_add, Matrix.add_mul]
  map_smul' a z := by
    funext b s t
    simp [mul_smul, ← Finset.smul_sum]

theorem of_toBlocks (c : ℕ) (z : {i : Fin d // deg i = c} → ℂ) (b : Fin m) :
    Matrix.of (toBlocks m U B deg c z b) = (U b)ᴴ * (∑ i, z i • B i.1) * U (b + c + 1) := rfl

theorem toBlocks_coords (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hL : ∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) (c : ℕ)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y ∈ lowers W c) (b : Fin m) :
    Matrix.of (toBlocks m U B deg c (fun i => (Y * (B i.1)ᴴ).trace) b)
      = (U b)ᴴ * Y * U (b + c + 1) := by
  rw [of_toBlocks]
  rw [hL] at hY
  obtain ⟨h1, h2⟩ := expand hB _ hY
  conv_rhs => rw [h1]
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => deg i = c) (by simp)
    (fun i => (Y * (B i)ᴴ).trace • B i)]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  have hi' : deg i ≠ c := by simpa using hi
  by_cases hc : c ≤ deg i
  · have : B i ∈ lowers W (c + 1) := by
      rw [hL]
      exact Submodule.subset_span ⟨i, by show c + 1 ≤ deg i; omega, rfl⟩
    rw [Matrix.mul_smul, Matrix.smul_mul,
      (mem_lowers_iff hU hW _ _).1 this b (b + c + 1) (by omega), smul_zero]
  · rw [h2 i hc]; simp

theorem toBlocks_surjective (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hL : ∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) (c : ℕ) :
    Function.Surjective (toBlocks m U B deg c) := by
  intro Z
  set Y : Matrix (Fin n) (Fin n) ℂ :=
    ∑ b : Fin m, U b * Matrix.of (Z b) * (U (b + c + 1))ᴴ with hYdef
  have hY : Y ∈ lowers W c := by
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [mem_lowers_iff hU hW]
    intro s t hst
    exact placed_block hU _ (by omega)
  refine ⟨fun i => (Y * (B i.1)ᴴ).trace, funext fun b => ?_⟩
  apply Matrix.of.injective
  rw [toBlocks_coords hU hW hB hL c Y hY b, hYdef, Matrix.mul_sum, Matrix.sum_mul,
    Finset.sum_eq_single b]
  · exact placed_block_self hU _
  · intro b' _ hb
    exact placed_block hU _ (Or.inl fun h => hb (Fin.ext h.symm))
  · simp

theorem toBlocks_norm (hU : Biorth r m U (fun b => (U b)ᴴ))
    (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hL : ∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) (c : ℕ)
    (z : {i : Fin d // deg i = c} → ℂ) :
    ∑ b, ∑ s, ∑ t, ‖toBlocks m U B deg c z b s t‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  set Y : Matrix (Fin n) (Fin n) ℂ := ∑ i, z i • B i.1 with hYdef
  have hY : Y ∈ lowers W c := by
    rw [hL]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i.1, i.2.ge, rfl⟩)
  have h1 : (Y * Yᴴ).trace = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
    simp [hYdef, conjTranspose_sum, Matrix.mul_sum, Matrix.sum_mul, trace_sum, hB,
      Subtype.val_inj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.conj_mul']
  have horth : ∀ X ∈ lowers W (c + 1), (X * Yᴴ).trace = 0 := by
    intro X hX
    rw [hL] at hX
    have h2 := (expand hB _ hX).2
    rw [hYdef, conjTranspose_sum, Matrix.mul_sum, trace_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [conjTranspose_smul, Matrix.mul_smul, trace_smul, h2 i.1, smul_zero]
    have := i.2
    show ¬ (c + 1 ≤ deg i.1)
    omega
  have h2 : (Y * Yᴴ).trace = ∑ s ∈ range m,
      (((U s)ᴴ * Y * U (s + c + 1)) * ((U s)ᴴ * Y * U (s + c + 1))ᴴ).trace := by
    rw [trace_blocks hU]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_eq_single _ (fun t _ ht => ?_) (fun h => ?_)
    · by_cases hst : t ≤ s + c
      · rw [(mem_lowers_iff hU hW _ _).1 hY s t hst]; simp
      · have hX : U s * ((U s)ᴴ * Y * U t) * (U t)ᴴ ∈ lowers W (c + 1) := by
          rw [mem_lowers_iff hU hW]
          intro s' t' h'
          exact placed_block hU _ (by omega)
        rw [← horth _ hX, Matrix.mul_assoc (U s), Matrix.mul_assoc (U s), Matrix.trace_mul_comm (U s)]
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    · rw [block_eq_zero hU (t := s + c + 1) (by simpa using h)]; simp
  rw [h2, ← Fin.sum_univ_eq_sum_range
    (fun s => (((U s)ᴴ * Y * U (s + c + 1)) * ((U s)ᴴ * Y * U (s + c + 1))ᴴ).trace)] at h1
  simp only [trace_self] at h1
  rw [← Complex.ofReal_sum] at h1
  exact Complex.ofReal_injective h1

theorem exists_layerIso : ∀ (n m d : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ), Biorth r m U (fun b => (U b)ᴴ) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) → (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) → (∀ c, lowers W c = Submodule.span ℂ (B '' {i | c ≤ deg i})) → ∀ c : ℕ, ∃ Φ : ({i : Fin d // deg i = c} → ℂ) ≃ₗ[ℂ] (∀ b : Fin m, Fin (r b) → Fin (r (b + c + 1)) → ℂ), (∀ z, ∑ b, ∑ s, ∑ t, ‖Φ z b s t‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) ∧ ∀ Y ∈ lowers W c, ∀ b : Fin m, Matrix.of (Φ (fun i => (Y * (B i.1)ᴴ).trace) b) = (U b)ᴴ * Y * U (b + c + 1) := by
  intro n m d W r U B deg hU hW hB hL c
  have hinj : Function.Injective (toBlocks m U B deg c) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have h := toBlocks_norm hU hW hB hL c z
    rw [hz] at h
    have h0 : ∑ i, ‖z i‖ ^ 2 = 0 := by rw [← h]; simp
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)] at h0
    funext i
    simpa using h0 i (Finset.mem_univ i)
  exact ⟨LinearEquiv.ofBijective _ ⟨hinj, toBlocks_surjective hU hW hB hL c⟩,
    toBlocks_norm hU hW hB hL c, toBlocks_coords hU hW hB hL c⟩

end GlobalTheory.LayerIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLeadingTermOfSkewLayer
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem exists_unitary_of_skew_layer (R K : Type) [CommRing R] [Field K] [StarRing K]
    [Algebra R K] (n m : ℕ) (J : Matrix (Fin n) (Fin n) K)
    (A : ℕ → Submodule R (Matrix (Fin n) (Fin n) K)) (w : R)
    (hJ : Jᴴ = J) (hdet : J.det ≠ 0)
    (hw : algebraMap R K w + star (algebraMap R K w) = 1)
    (hA : ∀ c, A (c + 1) ≤ A c) (hm : A m = ⊥)
    (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (_hadj : ∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J ∈ A c)
    (c : ℕ) (X : Matrix (Fin n) (Fin n) K) (hX : X ∈ A c) (hskew : J⁻¹ * Xᴴ * J = -X) :
    ∃ Y ∈ A (c + 1), (1 + X + Y)ᴴ * J * (1 + X + Y) = J := by
  classical
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
  have cL : ∀ B : Matrix (Fin n) (Fin n) K, J * (J⁻¹ * B) = B :=
    fun B => Matrix.mul_nonsing_inv_cancel_left J B hu
  have cL' : ∀ B : Matrix (Fin n) (Fin n) K, J⁻¹ * (J * B) = B :=
    fun B => Matrix.nonsing_inv_mul_cancel_left J B hu
  have cR : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have cR' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have hJi : (J⁻¹)ᴴ = J⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hJ]
  have hanti : Antitone A := antitone_nat_of_succ_le hA
  have to0 : ∀ {d : ℕ} {M : Matrix (Fin n) (Fin n) K}, M ∈ A d → M ∈ A 0 :=
    fun h => hanti (Nat.zero_le _) h
  have smem : ∀ (r : R) {d : ℕ} {M : Matrix (Fin n) (Fin n) K}, M ∈ A d →
      algebraMap R K r • M ∈ A d := by
    intro r d M h
    rw [algebraMap_smul]
    exact (A d).smul_mem r h
  set β : K := algebraMap R K w with hβ
  have hst : star β = 1 - β := by rw [← hw]; ring

  have key : ∀ k : ℕ, ∃ Y ∈ A (c + 1),
      J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y) - 1 ∈ A (c + 1 + k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, (A (c + 1)).zero_mem, ?_⟩
      have hX' : Xᴴ = -(J * (X * J⁻¹)) := by
        calc Xᴴ = J * ((J⁻¹ * Xᴴ * J) * J⁻¹) := by
              simp only [mul_assoc, cR, mul_one, cL]
          _ = -(J * (X * J⁻¹)) := by rw [hskew]; simp only [neg_mul, mul_neg]
      have h0 : J⁻¹ * (1 + X + 0)ᴴ * J * (1 + X + 0) - 1 = -(X * X) := by
        simp only [add_zero, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hX']
        simp only [mul_add, add_mul, mul_one, one_mul, mul_neg, neg_mul, mul_assoc, cL', cR']
        abel
      rw [h0, Nat.add_zero]
      exact (A (c + 1)).neg_mem (hmul c X hX X (to0 hX)).1
    | succ k ih =>
      obtain ⟨Y, hY, hE⟩ := ih
      set g := 1 + X + Y with hg
      set E := J⁻¹ * gᴴ * J * g - 1 with hEdef
      have hEE : E * E ∈ A (c + 1 + (k + 1)) := (hmul (c + 1 + k) E hE E (to0 hE)).1
      have hEEE : E * (E * E) ∈ A (c + 1 + (k + 1)) :=
        (hmul (c + 1 + k) E hE (E * E) (to0 hEE)).1
      refine ⟨Y - β • (g * E), ?_, ?_⟩
      · have hEc : E ∈ A (c + 1) := hanti (by omega) hE
        have hgE : g * E ∈ A (c + 1) := by
          rw [hg, add_mul, add_mul, one_mul]
          exact add_mem (add_mem hEc (hmul c X hX E (to0 hE)).1)
            (hanti (by omega) (hmul (c + 1) Y hY E (to0 hE)).1)
        exact sub_mem hY (smem w hgE)
      · have hgeq : 1 + X + (Y - β • (g * E)) = g - β • (g * E) := by rw [hg]; abel
        rw [hgeq]

        have hEH : J⁻¹ * Eᴴ * J = E := by
          rw [hEdef]
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, hJi, hJ, sub_mul, mul_sub, mul_one, mul_assoc, cR']
        have h1 : J⁻¹ * (Eᴴ * (gᴴ * J)) = E * (J⁻¹ * (gᴴ * J)) := by
          calc J⁻¹ * (Eᴴ * (gᴴ * J)) = (J⁻¹ * Eᴴ * J) * (J⁻¹ * (gᴴ * J)) := by
                simp only [mul_assoc, cL]
            _ = E * (J⁻¹ * (gᴴ * J)) := by rw [hEH]
        have hP' : J⁻¹ * (g - β • (g * E))ᴴ * J
            = J⁻¹ * (gᴴ * J) - star β • (E * (J⁻¹ * (gᴴ * J))) := by
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
            mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, h1]
        have hPg0 : J⁻¹ * (gᴴ * (J * g)) = 1 + E := by
          rw [hEdef]; simp only [mul_assoc]; abel
        have hPg : ∀ M, J⁻¹ * (gᴴ * (J * (g * M))) = M + E * M := by
          intro M
          rw [hEdef]; simp only [sub_mul, one_mul, mul_assoc]; abel
        have hid : J⁻¹ * (g - β • (g * E))ᴴ * J * (g - β • (g * E)) - 1
            = (β - β * β - 1) • (E * E) + (β - β * β) • (E * (E * E)) := by
          rw [hP']
          simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc, hPg, hPg0,
            mul_add, mul_one, smul_add, hst]
          module
        have s1 : β - β * β - 1 = algebraMap R K (w - w * w - 1) := by simp [hβ]
        have s2 : β - β * β = algebraMap R K (w - w * w) := by simp [hβ]
        rw [hid, s1, s2]
        exact add_mem (smem _ hEE) (smem _ hEEE)
  obtain ⟨Y, hY, hEm⟩ := key m
  refine ⟨Y, hY, ?_⟩
  have hz : J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y) - 1 ∈ A m := hanti (by omega) hEm
  rw [hm, Submodule.mem_bot, sub_eq_zero] at hz
  calc (1 + X + Y)ᴴ * J * (1 + X + Y)
      = J * (J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y)) := by simp only [mul_assoc, cL]
    _ = J := by rw [hz, mul_one]

end GlobalTheory.RadCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryOrthogonalEmbeddingStabilizer
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabRing

open Formalism.UG

theorem cT_add_rect {R : Type} [CommRing R] (σ : R →+* R) {a b : Type} (M N : Matrix a b R) :
    cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

theorem exists_emb_block {R : Type} [CommRing R] (σ : R →+* R) {n m k : Type}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]
    (J : Matrix n n R) (J' : Matrix m m R) (X : Matrix n k R) (U : Matrix k n R)
    (A : Matrix n m R) (A' : Matrix m n R)
    (hB : IsUnit (cT σ X * J * X)) (hXA : cT σ X * J * A = 0) (hAX : cT σ A * J * X = 0)
    (hJ : cT σ A * J * A = J') (h1 : A' * A = 1) (h2 : A' * X = 0) (h3 : U * A = 0) (h4 : U * X = 1)
    (h5 : X * U + A * A' = 1) :
    ∃ j : UJ σ J' →* UJ σ J,
      (∀ g, ((j g : GL n R) : Matrix n n R) = X * U + A * ((g : GL m R) : Matrix m m R) * A') ∧
      ∀ h : UJ σ J, ((h : GL n R) : Matrix n n R) * X = X → h ∈ j.range := by
  have hmul : ∀ g g' : Matrix m m R,
      (X * U + A * g * A') * (X * U + A * g' * A') = X * U + A * (g * g') * A' := by
    intro g g'
    calc (X * U + A * g * A') * (X * U + A * g' * A')
        = X * (U * X) * U + X * (U * A) * g' * A' + (A * g * (A' * X) * U + A * g * (A' * A) * g' * A') := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
      _ = _ := by rw [h1, h2, h3, h4]; simp [Matrix.mul_assoc]
  have hone : X * U + A * (1 : Matrix m m R) * A' = 1 := by rw [Matrix.mul_one, h5]
  have hform : ∀ g : Matrix m m R, cT σ (X * U + A * g * A') * J * (X * U + A * g * A')
      = cT σ U * (cT σ X * J * X) * U + cT σ A' * (cT σ g * J' * g) * A' := by
    intro g
    calc cT σ (X * U + A * g * A') * J * (X * U + A * g * A')
        = cT σ U * (cT σ X * J * X) * U + cT σ U * (cT σ X * J * A) * g * A'
          + (cT σ A' * cT σ g * (cT σ A * J * X) * U
            + cT σ A' * (cT σ g * (cT σ A * J * A) * g) * A') := by
          simp only [cT_add_rect, cT_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
      _ = _ := by rw [hXA, hAX, hJ]; simp
  have hJJ : cT σ U * (cT σ X * J * X) * U + cT σ A' * J' * A' = J := by
    have := hform 1
    rw [hone] at this
    simpa [cT_one] using this.symm
  let j0 : GL m R → GL n R := fun g =>
    ⟨X * U + A * (g : Matrix m m R) * A', X * U + A * ((g⁻¹ : GL m R) : Matrix m m R) * A',
      by rw [hmul, Units.mul_inv, hone], by rw [hmul, Units.inv_mul, hone]⟩
  have hmem : ∀ g : UJ σ J', j0 g ∈ UJ σ J := by
    intro g
    have hg : cT σ ((g : GL m R) : Matrix m m R) * J' * ((g : GL m R) : Matrix m m R) = J' := g.2
    change cT σ (X * U + A * ((g : GL m R) : Matrix m m R) * A') * J
      * (X * U + A * ((g : GL m R) : Matrix m m R) * A') = J
    rw [hform, hg, hJJ]
  let j : UJ σ J' →* UJ σ J :=
    { toFun := fun g => ⟨j0 g, hmem g⟩
      map_one' := by
        apply Subtype.ext; apply Units.ext
        exact hone
      map_mul' := by
        intro g g'
        apply Subtype.ext; apply Units.ext
        exact (hmul _ _).symm }
  refine ⟨j, fun g => rfl, ?_⟩
  have hXJ : cT σ X * J = cT σ X * J * X * U := by
    calc cT σ X * J = cT σ X * J * (X * U + A * A') := by rw [h5, Matrix.mul_one]
      _ = cT σ X * J * X * U + cT σ X * J * A * A' := by
        simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = _ := by rw [hXA]; simp
  have key : ∀ h : Matrix n n R, cT σ h * J * h = J → h * X = X → A * (A' * h * A) = h * A := by
    intro h hh hX
    have e1 : cT σ X * J * X * (U * h * A) = 0 := by
      calc cT σ X * J * X * (U * h * A) = (cT σ X * J * X * U) * h * A := by
            simp only [Matrix.mul_assoc]
        _ = cT σ (h * X) * J * h * A := by rw [← hXJ, hX]
        _ = cT σ X * (cT σ h * J * h) * A := by simp only [cT_mul, Matrix.mul_assoc]
        _ = 0 := by rw [hh, hXA]
    have e2 : U * h * A = 0 := by
      obtain ⟨b, hb⟩ := hB
      rw [← hb] at e1
      calc U * h * A = ((b⁻¹ : GL k R) : Matrix k k R) * (b : Matrix k k R) * (U * h * A) := by
            rw [Units.inv_mul, Matrix.one_mul]
        _ = 0 := by rw [Matrix.mul_assoc, e1, Matrix.mul_zero]
    calc A * (A' * h * A) = X * (U * h * A) + A * (A' * h * A) := by rw [e2]; simp
      _ = (X * U + A * A') * h * A := by simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = h * A := by rw [h5, Matrix.one_mul]
  intro h hX
  have hh : cT σ ((h : GL n R) : Matrix n n R) * J * ((h : GL n R) : Matrix n n R) = J := h.2
  have hh' : cT σ (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * J
      * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) = J := (h⁻¹).2
  have hX' : (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * X = X := by
    conv_lhs => rw [← hX]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have k1 := key _ hh hX
  have k2 := key _ hh' hX'
  let g : GL m R := ⟨A' * ((h : GL n R) : Matrix n n R) * A,
    A' * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R) * A,
    by rw [Matrix.mul_assoc _ A, k2, Matrix.mul_assoc A', ← Matrix.mul_assoc _ _ A, Units.mul_inv,
      Matrix.one_mul, h1],
    by rw [Matrix.mul_assoc _ A, k1, Matrix.mul_assoc A', ← Matrix.mul_assoc _ _ A, Units.inv_mul,
      Matrix.one_mul, h1]⟩
  have hg : g ∈ UJ σ J' := by
    change cT σ (A' * ((h : GL n R) : Matrix n n R) * A) * J'
      * (A' * ((h : GL n R) : Matrix n n R) * A) = J'
    calc cT σ (A' * ((h : GL n R) : Matrix n n R) * A) * J' * (A' * ((h : GL n R) : Matrix n n R) * A)
        = cT σ (A * (A' * ((h : GL n R) : Matrix n n R) * A)) * J
          * (A * (A' * ((h : GL n R) : Matrix n n R) * A)) := by
          rw [cT_mul σ A, ← hJ]; simp only [Matrix.mul_assoc]
      _ = cT σ A * (cT σ ((h : GL n R) : Matrix n n R) * J * ((h : GL n R) : Matrix n n R)) * A := by
          rw [k1]; simp only [cT_mul, Matrix.mul_assoc]
      _ = J' := by rw [hh, hJ]
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Subtype.ext; apply Units.ext
  change X * U + A * (A' * ((h : GL n R) : Matrix n n R) * A) * A' = ((h : GL n R) : Matrix n n R)
  rw [k1]
  calc X * U + ((h : GL n R) : Matrix n n R) * A * A'
      = ((h : GL n R) : Matrix n n R) * X * U + ((h : GL n R) : Matrix n n R) * A * A' := by rw [hX]
    _ = ((h : GL n R) : Matrix n n R) * (X * U + A * A') := by
      simp only [Matrix.mul_add, Matrix.mul_assoc]
    _ = _ := by rw [h5, Matrix.mul_one]

theorem exists_emb : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n m : ℕ) (J : Matrix (Fin n) (Fin n) R) (J' : Matrix (Fin m) (Fin m) R) (x u : Fin n → R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R), IsUnit ((fun i => σ (x i)) ⬝ᵥ (J *ᵥ x)) → (fun i => σ (x i)) ᵥ* (J * A) = 0 → Formalism.UG.cT σ A *ᵥ (J *ᵥ x) = 0 → Formalism.UG.cT σ A * J * A = J' → A' * A = 1 → A' *ᵥ x = 0 → u ᵥ* A = 0 → u ⬝ᵥ x = 1 → vecMulVec x u + A * A' = 1 → ∃ j : Formalism.UG.UJ σ J' →* Formalism.UG.UJ σ J, (∀ g, ((j g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = vecMulVec x u + A * ((g : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * A') ∧ ∀ h : Formalism.UG.UJ σ J, ((h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ x = x → h ∈ j.range := by
  intro R _ σ n m J J' x u A A' hB hXA hAX hJ h1 h2 h3 h4 h5
  have hc : cT σ (replicateCol Unit x) = replicateRow Unit (fun i => σ (x i)) := by
    ext i j; simp [cT]
  rw [vecMulVec_eq Unit] at h5 ⊢
  obtain ⟨j, hj1, hj2⟩ := exists_emb_block σ J J' (replicateCol Unit x) (replicateRow Unit u) A A'
    (by
      rw [hc, Matrix.mul_assoc, ← replicateCol_mulVec, replicateRow_mul_replicateCol,
        Matrix.isUnit_iff_isUnit_det]
      simpa using hB)
    (by rw [hc, Matrix.mul_assoc, ← replicateRow_vecMul, hXA]; simp)
    (by rw [Matrix.mul_assoc, ← replicateCol_mulVec, ← replicateCol_mulVec, hAX]; simp)
    hJ h1
    (by rw [← replicateCol_mulVec, h2]; simp)
    (by rw [← replicateRow_vecMul, h3]; simp)
    (by rw [replicateRow_mul_replicateCol, h4]; ext i j; simp)
    h5
  exact ⟨j, hj1, fun h hx => hj2 h (by rw [← replicateCol_mulVec, hx])⟩

end GlobalTheory.StabRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorGramMatrixConstDoubleCoset
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem leadMinorE_zhatL_dcrel :
    ∀ (D : D7) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (T T' : D.host.E)
      (F : LFlag (VS D) D.R.rS T) (F₁ F₂ : LFlag (VS D) D.R.rS T'),
      Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂ → ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l := by
  intro D Λ T T' F F₁ F₂ h l
  obtain ⟨A, B, hA0, hA1, hB0, hB1, hZ⟩ := Formalism.L2.SG.Pf.zhat_rel F h
  rw [hZ]
  exact Formalism.L2.SG.Pf.leadMinor_uni A _ B hA0 hA1 hB0 hB1 l

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralCompactLeQuotientMeasureBesselStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_compact_le_quotientMeasure_bessel : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r)) (K₀ : Set (Mt k r)), IsClosedSub k r S → IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → IsQuotMeas μG μS ν → IsCompact K₀ → ∃ C : ENNReal, C < ⊤ ∧ ∀ F : Mt k r → ENNReal, Measurable F → (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) → ∫⁻ x in K₀, F x ∂μG ≤ C * ∫⁻ x, F x ∂ν := by
  first | exact @GlobalTheory.SgInf.lint_compact_le_quot | exact GlobalTheory.SgInf.lint_compact_le_quot | (intros; apply GlobalTheory.SgInf.lint_compact_le_quot <;> assumption)
end

