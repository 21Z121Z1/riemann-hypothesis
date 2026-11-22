import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowsSubgroupOfSelfSPow
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pows_subgroupOf_self_sPow (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    (pows p U).subgroupOf U = pows p (⊤ : Subgroup U) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, Subgroup.mem_top _, Subtype.ext h⟩
  · rintro ⟨y, -, h⟩
    exact ⟨y.1, y.2, congrArg Subtype.val h⟩

theorem pTor_sUnits (p : ℕ) (F : Type) [Field F] [NumberField F] (ζ : F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) :
    pTor p (sUnits F S) = p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hmem : ∀ x : Fˣ, x ^ p = 1 → x ∈ sUnits F S := by
    intro x hx
    rw [mem_sUnits]
    intro v _
    have h1 : (v.valuation F (x : F)) ^ p = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hx]; simp
    first
      | exact (pow_eq_one_iff hp.ne_zero).mp h1
      | exact (pow_eq_one_iff_left hp.ne_zero).mp h1
      | exact (pow_eq_one_iff_of_nonneg zero_le' hp.ne_zero).mp h1
  have e : {x : Fˣ // x ∈ sUnits F S ∧ x ^ p = 1} ≃ rootsOfUnity p F :=
    Equiv.subtypeEquivRight (fun x => by
      rw [mem_rootsOfUnity]; exact ⟨fun h => h.2, fun h => ⟨hmem x h, h⟩⟩)
  rw [pTor, Nat.card_congr e]
  first
    | exact hζ.card_rootsOfUnity
    | (rw [Nat.card_eq_fintype_card]; exact hζ.card_rootsOfUnity)

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in

theorem _root_.GlobalTheory.CNorm.pTor_pIdx_sUnits : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F]
    (ζ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p →
    _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) = p ∧
      _root_.GlobalTheory.CNorm.pIdx p (_root_.GlobalTheory.QNorm.sUnits F S) =
        p ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro p F _ _ ζ S hp hζ
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Group.FG (_root_.GlobalTheory.QNorm.sUnits F S) := _root_.GlobalTheory.QNorm.sUnits_fg F S
  obtain ⟨-, h2⟩ := _root_.GlobalTheory.CNorm.pIdx_top_of_fg p (_root_.GlobalTheory.QNorm.sUnits F S) hp.pos
  have hroots : ∀ x : Fˣ, x ^ p = 1 → x ∈ _root_.GlobalTheory.QNorm.sUnits F S := by
    intro x hx
    rw [_root_.GlobalTheory.QNorm.mem_sUnits]
    intro v _
    have h := congrArg (fun y : Fˣ => HeightOneSpectrum.valuation F v (y : F)) hx
    simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h
    exact (pow_eq_one_iff_of_nonneg zero_le' hp.ne_zero).mp h
  have htor : _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) = p := by
    unfold _root_.GlobalTheory.CNorm.pTor
    refine (Nat.card_congr ?_).trans hζ.card_rootsOfUnity
    exact
      { toFun := fun x => ⟨x.1, (mem_rootsOfUnity p x.1).mpr x.2.2⟩
        invFun := fun y => ⟨y.1, hroots y.1 ((mem_rootsOfUnity p y.1).mp y.2),
          (mem_rootsOfUnity p y.1).mp y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have htorTop : _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup (_root_.GlobalTheory.QNorm.sUnits F S)) =
      _root_.GlobalTheory.CNorm.pTor p (_root_.GlobalTheory.QNorm.sUnits F S) := by
    unfold _root_.GlobalTheory.CNorm.pTor
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, by rw [← Subgroup.coe_pow, x.2.2, OneMemClass.coe_one]⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subgroup.mem_top _, Subtype.ext y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hidxTop : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup (_root_.GlobalTheory.QNorm.sUnits F S)) =
      _root_.GlobalTheory.CNorm.pIdx p (_root_.GlobalTheory.QNorm.sUnits F S) := by
    unfold _root_.GlobalTheory.CNorm.pIdx _root_.GlobalTheory.CNorm.pows
    rw [Subgroup.relIndex_top_right]
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, powMonoidHom_apply,
      Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, y.2, by rw [← hy]; rfl⟩
    · rintro ⟨y, hyH, hy⟩
      exact ⟨⟨y, hyH⟩, Subtype.ext hy⟩
  refine ⟨htor, ?_⟩
  rw [← hidxTop, h2, htorTop, htor, ← _root_.GlobalTheory.QNorm.sUnits_rank F S, pow_succ]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.QuasiReflectionEqMulTransvectionsOfHyperbolicPla
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.PlaneRefl

variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)

theorem hf_add_left (x y v : Fin n → R) : hf σ G (x + y) v = hf σ G x v + hf σ G y v := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y v : Fin n → R) : hf σ G v (x + y) = hf σ G v x + hf σ G v y := by
  simp only [hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (a : R) (x v : Fin n → R) : hf σ G (a • x) v = a * hf σ G x v := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (a : R) (x v : Fin n → R) : hf σ G v (a • x) = σ a * hf σ G v x := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem tv_zero (x : Fin n → R) : tv σ G x 0 = 1 := by
  ext a b; simp [tv]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma transvection_zero' {E : Type} [Field E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (w : Fin n → E) : _root_.GlobalTheory.UTrans.tv σ G w 0 = 1 := by
  unfold _root_.GlobalTheory.UTrans.tv
  ext i j
  simp

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma quasiReflection_eq_transvectionGen_mul_shifted {E : Type} [Field E] [CharZero E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (hinv : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a)
    (x z : Fin n → E) (a u : E) (hzz : _root_.GlobalTheory.UTrans.hf σ G z z = 0)
    (hxz : _root_.GlobalTheory.UTrans.hf σ G x z ≠ 0) (hxx : _root_.GlobalTheory.UTrans.hf σ G x x ≠ 0)
    (hyy : _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z) ≠ 0) (hu : u * σ u = 1)
    (hu1 : u ≠ 1)
    (hD : u * σ a * _root_.GlobalTheory.UTrans.hf σ G x z + a * σ (_root_.GlobalTheory.UTrans.hf σ G x z) ≠ 0) :
    ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen σ G,
      _root_.GlobalTheory.UTrans.tv σ G x ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G x x) =
        m * _root_.GlobalTheory.UTrans.tv σ G (x + a • z)
          ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z)) := by
  set β := _root_.GlobalTheory.UTrans.hf σ G x z with hβ
  set α := _root_.GlobalTheory.UTrans.hf σ G x x with hα
  have hzx : _root_.GlobalTheory.UTrans.hf σ G z x = σ β := by
    rw [hβ, _root_.GlobalTheory.UTrans.Model.hf_conj σ G hinv hG]
  have hαr : σ α = α := by rw [hα, _root_.GlobalTheory.UTrans.Model.hf_conj σ G hinv hG]
  have hα' : _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z) = α + σ a * β + a * σ β := by
    rw [_root_.GlobalTheory.UTrans.Model.hf_add_smul_left, _root_.GlobalTheory.UTrans.Model.hf_add_smul_right,
      _root_.GlobalTheory.UTrans.Model.hf_add_smul_right, hzz, hzx]
    ring
  rw [hα'] at hyy ⊢
  clear_value α β
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
  have hsu : σ u = u⁻¹ := eq_inv_of_mul_eq_one_right hu
  have hu1' : u - 1 ≠ 0 := sub_ne_zero.2 hu1
  have hsβ : σ β ≠ 0 := fun h => hxz (by rw [← hinv β, h, map_zero])
  obtain ⟨D, hDdef⟩ : ∃ D, D = u * σ a * β + a * σ β := ⟨_, rfl⟩
  rw [← hDdef] at hD
  obtain ⟨N, hN⟩ : ∃ N, N = β * σ β := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = -(σ a * β + a * σ β) * u * α / (D * (u - 1) * N) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = (u * α * (σ a * β + a * σ β) - (u - 1) ^ 2 * (σ a * β) * (a * σ β)) /
      (D * (u - 1) * N) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = -(D * α / ((α + σ a * β + a * σ β) * (u - 1) * N)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (u - 1) / α := ⟨_, rfl⟩
  have hσc : σ c = (u⁻¹ - 1) / α := by rw [hc, map_div₀, map_sub, map_one, hsu, hαr]
  have hyy2 : α + a * σ β + σ a * β ≠ 0 := by rw [add_assoc, add_comm (a * σ β), ← add_assoc]; exact hyy
  have hN0 : N ≠ 0 := by rw [hN]; exact mul_ne_zero hxz hsβ
  have hσD : σ D = D / u := by
    rw [hDdef]
    simp only [map_add, map_mul, hinv, hsu]
    field_simp
    ring
  have hσN : σ N = N := by rw [hN]; simp only [map_mul, hinv]; ring
  have trA : A + σ A = 0 := by
    rw [hA]
    simp only [map_div₀, map_mul, map_neg, map_sub, map_one, map_add, map_pow, hinv, hsu, hαr, hσD, hσN]
    field_simp
    ring
  have trB : B + σ B = 0 := by
    rw [hB]
    simp only [map_div₀, map_mul, map_neg, map_sub, map_one, map_add, map_pow, hinv, hsu, hαr, hσD, hσN]
    field_simp
    ring
  have trR : R + σ R = 0 := by
    rw [hR]
    simp only [map_div₀, map_mul, map_neg, map_sub, map_one, map_add, map_pow, hinv, hsu, hαr, hσD, hσN]
    field_simp
    ring
  obtain ⟨w, hw⟩ : ∃ w, w = z + (c * σ β) • x := ⟨_, rfl⟩
  have hww : _root_.GlobalTheory.UTrans.hf σ G w w = 0 := by
    rw [hw, _root_.GlobalTheory.UTrans.Model.hf_add_smul_left, _root_.GlobalTheory.UTrans.Model.hf_add_smul_right,
      _root_.GlobalTheory.UTrans.Model.hf_add_smul_right, hzz, hzx, map_mul, hσc, hinv, ← hβ, ← hα]
    rw [hc]
    field_simp
    ring
  refine ⟨_root_.GlobalTheory.UTrans.tv σ G z A * _root_.GlobalTheory.UTrans.tv σ G w R *
      _root_.GlobalTheory.UTrans.tv σ G z B, ?_, ?_⟩
  · unfold _root_.GlobalTheory.UTrans.TvGen
    refine mul_mem (mul_mem ?_ ?_) ?_
    · exact Submonoid.subset_closure ⟨z, A, hzz, trA, rfl⟩
    · exact Submonoid.subset_closure ⟨w, R, hww, trR, rfl⟩
    · exact Submonoid.subset_closure ⟨z, B, hzz, trB, rfl⟩
  rw [← hc]
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [_root_.GlobalTheory.UTrans.Model.tv_mulVec]
  subst hw
  simp only [_root_.GlobalTheory.UTrans.Model.hf_add_smul_left, _root_.GlobalTheory.UTrans.Model.hf_add_smul_right]
  simp only [hzz, hzx, ← hβ, ← hα]
  simp only [map_mul, hσc, hinv]
  generalize _root_.GlobalTheory.UTrans.hf σ G v x = p at *
  generalize _root_.GlobalTheory.UTrans.hf σ G v z = q at *
  subst hA hB hR hc hDdef hN
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma transvection_isometry {E : Type} [Field E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (hinv : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a)
    (w : Fin n → E) (t : E)
    (ht : t + σ t + t * σ t * _root_.GlobalTheory.UTrans.hf σ G w w = 0) (v v' : Fin n → E) :
    _root_.GlobalTheory.UTrans.hf σ G ((_root_.GlobalTheory.UTrans.tv σ G w t).mulVec v)
      ((_root_.GlobalTheory.UTrans.tv σ G w t).mulVec v') = _root_.GlobalTheory.UTrans.hf σ G v v' := by
  simp only [_root_.GlobalTheory.UTrans.Model.tv_mulVec, _root_.GlobalTheory.UTrans.Model.hf_add_smul_left,
    _root_.GlobalTheory.UTrans.Model.hf_add_smul_right, map_mul]
  rw [_root_.GlobalTheory.UTrans.Model.hf_conj σ G hinv hG v' w]
  linear_combination (_root_.GlobalTheory.UTrans.hf σ G v w * _root_.GlobalTheory.UTrans.hf σ G w v') * ht

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma isometry_mul_transvection {E : Type} [Field E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) E)
    (hg : ∀ v w, _root_.GlobalTheory.UTrans.hf σ G (g.mulVec v) (g.mulVec w) =
      _root_.GlobalTheory.UTrans.hf σ G v w) (w : Fin n → E) (t : E) :
    g * _root_.GlobalTheory.UTrans.tv σ G w t = _root_.GlobalTheory.UTrans.tv σ G (g.mulVec w) t * g := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, _root_.GlobalTheory.UTrans.Model.tv_mulVec, hg,
    Matrix.mulVec_add, Matrix.mulVec_smul]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private lemma transvection_mul_isotropic {E : Type} [Field E] {n : ℕ} (σ : E →+* E)
    (G : Matrix (Fin n) (Fin n) E) (w : Fin n → E) (hw : _root_.GlobalTheory.UTrans.hf σ G w w = 0)
    (s t : E) : _root_.GlobalTheory.UTrans.tv σ G w s * _root_.GlobalTheory.UTrans.tv σ G w t =
      _root_.GlobalTheory.UTrans.tv σ G w (s + t) := by
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, _root_.GlobalTheory.UTrans.Model.tv_mulVec,
    _root_.GlobalTheory.UTrans.Model.hf_add_smul_left, hw]
  rw [add_assoc, ← add_smul]
  congr 2
  ring

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) in

theorem _root_.GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane : ∀ (E : Type) [Field E] [CharZero E]
    (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), _root_.GlobalTheory.UTrans.IsHerm σ G →
    ∀ (x z : Fin n → E) (a u : E), _root_.GlobalTheory.UTrans.hf σ G z z = 0 →
    _root_.GlobalTheory.UTrans.hf σ G x z ≠ 0 → _root_.GlobalTheory.UTrans.hf σ G x x ≠ 0 →
    _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z) ≠ 0 → u * σ u = 1 →
    ∃ m ∈ _root_.GlobalTheory.UTrans.TvGen σ G,
      _root_.GlobalTheory.UTrans.tv σ G x ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G x x) =
        m * _root_.GlobalTheory.UTrans.tv σ G (x + a • z)
          ((u - 1) / _root_.GlobalTheory.UTrans.hf σ G (x + a • z) (x + a • z)) := by
  intro E _ _ n σ G hH x z a u hzz hxz hxx hyy hu
  obtain ⟨hinv, hne, hG, -⟩ := hH
  by_cases hu1 : u = 1
  · subst hu1
    refine ⟨1, one_mem _, ?_⟩
    simp only [sub_self, zero_div, transvection_zero', one_mul]
  by_cases hD : u * σ a * _root_.GlobalTheory.UTrans.hf σ G x z +
      a * σ (_root_.GlobalTheory.UTrans.hf σ G x z) ≠ 0
  · exact quasiReflection_eq_transvectionGen_mul_shifted σ G hinv hG x z a u hzz hxz hxx hyy hu hu1 hD
  push_neg at hD
  obtain ⟨e, he⟩ := hne
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = e - σ e := ⟨_, rfl⟩
  have hσω : σ ω = -ω := by rw [hωdef, map_sub, hinv]; ring
  have hω0 : ω ≠ 0 := by rw [hωdef]; exact sub_ne_zero.2 (Ne.symm he)
  set β := _root_.GlobalTheory.UTrans.hf σ G x z with hβ
  set y := x + a • z with hy
  set E₁ := _root_.GlobalTheory.UTrans.tv σ G z ω with hE₁
  set E₂ := _root_.GlobalTheory.UTrans.tv σ G z (-ω) with hE₂
  have hEiso : ∀ v w, _root_.GlobalTheory.UTrans.hf σ G (E₁.mulVec v) (E₁.mulVec w) =
      _root_.GlobalTheory.UTrans.hf σ G v w :=
    transvection_isometry σ G hinv hG z ω (by rw [hσω, hzz]; ring)
  have hy1 : E₁.mulVec y = x + (a + ω * β) • z := by
    rw [hE₁, _root_.GlobalTheory.UTrans.Model.tv_mulVec, hy, _root_.GlobalTheory.UTrans.Model.hf_add_smul_left, hzz,
      ← hβ, add_smul, add_assoc]
    congr 2
    ring_nf
  have hnorm : _root_.GlobalTheory.UTrans.hf σ G (x + (a + ω * β) • z) (x + (a + ω * β) • z) =
      _root_.GlobalTheory.UTrans.hf σ G y y := by rw [← hy1, hEiso]
  have hD1 : u * σ (a + ω * β) * β + (a + ω * β) * σ β ≠ 0 := by
    have e1 : u * σ (a + ω * β) * β + (a + ω * β) * σ β = ω * β * σ β * (1 - u) := by
      rw [map_add, map_mul, hσω]
      linear_combination hD
    rw [e1]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hω0 hxz) ?_) (sub_ne_zero.2 (Ne.symm hu1))
    intro h; exact hxz (by rw [← hinv β, h, map_zero])
  obtain ⟨m₁, hm₁, h₁⟩ := quasiReflection_eq_transvectionGen_mul_shifted σ G hinv hG x z (a + ω * β) u hzz hxz hxx
    (by rw [hnorm]; exact hyy) hu hu1 hD1
  rw [hnorm] at h₁
  set c' := (u - 1) / _root_.GlobalTheory.UTrans.hf σ G y y with hc'
  have hyr : σ (_root_.GlobalTheory.UTrans.hf σ G y y) = _root_.GlobalTheory.UTrans.hf σ G y y :=
    _root_.GlobalTheory.UTrans.Model.hf_conj σ G hinv hG y y
  have hτiso : ∀ v w, _root_.GlobalTheory.UTrans.hf σ G
      ((_root_.GlobalTheory.UTrans.tv σ G y c').mulVec v) ((_root_.GlobalTheory.UTrans.tv σ G y c').mulVec w) =
      _root_.GlobalTheory.UTrans.hf σ G v w := by
    refine transvection_isometry σ G hinv hG y c' ?_
    rw [hc', map_div₀, map_sub, map_one, hyr]
    field_simp
    linear_combination hu
  have hc1 : E₁ * _root_.GlobalTheory.UTrans.tv σ G y c' = _root_.GlobalTheory.UTrans.tv σ G (x + (a + ω * β) • z) c' * E₁ := by
    rw [isometry_mul_transvection σ G E₁ hEiso, hy1]
  have hEE : E₁ * E₂ = 1 := by
    rw [hE₁, hE₂, transvection_mul_isotropic σ G z hzz, add_neg_cancel, transvection_zero']
  have hc2 : _root_.GlobalTheory.UTrans.tv σ G y c' * E₂ =
      _root_.GlobalTheory.UTrans.tv σ G ((_root_.GlobalTheory.UTrans.tv σ G y c').mulVec z) (-ω) *
        _root_.GlobalTheory.UTrans.tv σ G y c' := by
    rw [hE₂, isometry_mul_transvection σ G _ hτiso]
  refine ⟨m₁ * E₁ * _root_.GlobalTheory.UTrans.tv σ G ((_root_.GlobalTheory.UTrans.tv σ G y c').mulVec z) (-ω), ?_, ?_⟩
  · refine mul_mem (mul_mem hm₁ ?_) ?_
    · unfold _root_.GlobalTheory.UTrans.TvGen
      exact Submonoid.subset_closure ⟨z, ω, hzz, by rw [hσω]; ring, rfl⟩
    · unfold _root_.GlobalTheory.UTrans.TvGen
      exact Submonoid.subset_closure ⟨_, -ω, by rw [hτiso, hzz], by rw [map_neg, hσω]; ring, rfl⟩
  · have key : _root_.GlobalTheory.UTrans.tv σ G (x + (a + ω * β) • z) c' =
        E₁ * _root_.GlobalTheory.UTrans.tv σ G y c' * E₂ := by
      rw [hc1, mul_assoc, hEE, mul_one]
    rw [h₁, key, mul_assoc E₁, hc2]
    simp only [mul_assoc]

end GlobalTheory.UTrans.PlaneRefl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsPlacesOverAndQuadraticConjStatement
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sUnits_places_over_and_quadratic_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → (∀ x : Fˣ, Units.map (algebraMap F E : F →* E) x ∈ sUnits E SE ↔ x ∈ sUnits F S) ∧ ∀ y : Eˣ, y ∈ sUnits E SE → Units.map (σ : E →* E) y ∈ sUnits E SE := by
  first | exact @GlobalTheory.QNorm.sUnits_over_and_conj | exact GlobalTheory.QNorm.sUnits_over_and_conj | (intros; apply GlobalTheory.QNorm.sUnits_over_and_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpecialLinearClassNumberOneAdelicStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialLinear_classNumber_one_adelic : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), AdelicPair R R₀ → ∀ x : Matrix ι ι R, x.det = 1 → ∃ (h : Matrix ι ι ℚ) (k : Matrix ι ι R), h.det = 1 ∧ k.det = 1 ∧ (∀ i j, k i j ∈ R₀) ∧ x = h.map (algebraMap ℚ R) * k := by
  first | exact @GlobalTheory.ClassFin.sl_class_number_one | exact GlobalTheory.ClassFin.sl_class_number_one | (intros; apply GlobalTheory.ClassFin.sl_class_number_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowImageUnitsCongruentOneModOfIsAdicCompStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subgroupPowImage_unitsCongruentOneMod_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → pows p (oneUnits ((p : O) * π)) = oneUnits ((p : O) ^ 2 * π) ∧ pTor p (oneUnits ((p : O) * π)) = 1 := by
  first | exact @GlobalTheory.CNorm.deep_units_pows | exact GlobalTheory.CNorm.deep_units_pows | (intros; apply GlobalTheory.CNorm.deep_units_pows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorActionHermitianExpFixedOfMinNorm
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.act_exp_eq_of_isMinVec : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (U : Matrix ι ι ℂ) (δ : ι → ℝ), _root_.GlobalTheory.ClassFin.IsMinVec d v → U * Uᴴ = 1 → ∑ i, δ i = 0 → _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v (U * diagonal (fun i => (Real.exp (δ i) : ℂ)) * Uᴴ)) = _root_.GlobalTheory.ClassFin.nsq v → ∀ s : ℝ, _root_.GlobalTheory.ClassFin.act d v (U * diagonal (fun i => (Real.exp (s * δ i) : ℂ)) * Uᴴ) = v := by
  intro ι _ _ m d v U δ hmin hU hδ hone s
  obtain ⟨act1, actmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v
  have hUH : Uᴴ * Uᴴᴴ = 1 := by
    rw [conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hU
  have hnormU := (_root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity ι m d).1
  set u := _root_.GlobalTheory.ClassFin.act d v U with hu
  set lam : _root_.GlobalTheory.ClassFin.TIdx ι d → ℝ := fun k => ∑ j, δ (k.2 j) with hlam
  have hdiag : ∀ r : ℝ,
      _root_.GlobalTheory.ClassFin.act d u (diagonal fun i => (Real.exp (r * δ i) : ℂ)) =
        fun k => u k * (Real.exp (r * lam k) : ℂ) := by
    intro r
    funext k
    rw [((_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d u).2.2.1]
    simp only [hlam, Finset.mul_sum, Real.exp_sum, Complex.ofReal_prod]
  have hsplit : ∀ r : ℝ,
      _root_.GlobalTheory.ClassFin.act d v (U * diagonal (fun i => (Real.exp (r * δ i) : ℂ)) * Uᴴ) =
        _root_.GlobalTheory.ClassFin.act d (fun k => u k * (Real.exp (r * lam k) : ℂ)) Uᴴ := by
    intro r
    rw [actmul, actmul, hdiag]
  have hF : ∀ r : ℝ, _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v
      (U * diagonal (fun i => (Real.exp (r * δ i) : ℂ)) * Uᴴ)) =
        ∑ k, ‖u k‖ ^ 2 * Real.exp (r * lam k) ^ 2 := by
    intro r
    rw [hsplit, hnormU _ _ hUH]
    unfold _root_.GlobalTheory.ClassFin.nsq
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
  have hdet : ∀ r : ℝ, (U * diagonal (fun i => (Real.exp (r * δ i) : ℂ)) * Uᴴ).det = 1 := by
    intro r
    have h1 : U.det * Uᴴ.det = 1 := by rw [← det_mul, hU, det_one]
    rw [det_mul, det_mul, det_diagonal, ← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum,
      hδ, mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one, h1]
  have hmin' : ∀ r : ℝ, _root_.GlobalTheory.ClassFin.nsq v ≤ ∑ k, ‖u k‖ ^ 2 * Real.exp (r * lam k) ^ 2 := by
    intro r
    rw [← hF r]
    exact hmin _ ⟨_, hdet r, rfl⟩
  have h0 : ∑ k, ‖u k‖ ^ 2 * Real.exp (0 * lam k) ^ 2 = _root_.GlobalTheory.ClassFin.nsq v := by
    simp only [zero_mul, Real.exp_zero, one_pow, mul_one]
    exact hnormU v U hU
  have h1 : ∑ k, ‖u k‖ ^ 2 * Real.exp (1 * lam k) ^ 2 = _root_.GlobalTheory.ClassFin.nsq v := by
    rw [← hF 1]
    simpa only [one_mul] using hone
  have hhalf := hmin' (1 / 2)
  have hsq : ∀ k, Real.exp (1 * lam k) ^ 2 = (Real.exp (1 / 2 * lam k) ^ 2) ^ 2 := by
    intro k
    have e : Real.exp (1 * lam k) = Real.exp (1 / 2 * lam k) ^ 2 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [e]
  have hterm : ∀ k ∈ Finset.univ, 0 ≤ ‖u k‖ ^ 2 * (Real.exp (1 / 2 * lam k) ^ 2 - 1) ^ 2 :=
    fun k _ => by positivity
  have hsum : ∑ k, ‖u k‖ ^ 2 * (Real.exp (1 / 2 * lam k) ^ 2 - 1) ^ 2 = 0 := by
    have e : ∑ k, ‖u k‖ ^ 2 * (Real.exp (1 / 2 * lam k) ^ 2 - 1) ^ 2 =
        ∑ k, ‖u k‖ ^ 2 * Real.exp (1 * lam k) ^ 2 + ∑ k, ‖u k‖ ^ 2 * Real.exp (0 * lam k) ^ 2
          - 2 * ∑ k, ‖u k‖ ^ 2 * Real.exp (1 / 2 * lam k) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsq]
      simp only [zero_mul, Real.exp_zero]
      ring
    refine le_antisymm ?_ (Finset.sum_nonneg hterm)
    rw [e, h0, h1]
    linarith
  have hfix : ∀ k, u k * (Real.exp (s * lam k) : ℂ) = u k := by
    intro k
    have hk := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum k (Finset.mem_univ k)
    rcases mul_eq_zero.mp hk with ha | hb
    · have hz : u k = 0 := by simpa using ha
      simp [hz]
    · have ht : Real.exp (1 / 2 * lam k) ^ 2 = 1 := by
        have := (pow_eq_zero_iff (n := 2) two_ne_zero).mp hb
        linarith
      have hl : lam k = 0 := by
        rw [← Real.exp_nat_mul] at ht
        simpa using (Real.exp_eq_one_iff _).mp ht
      simp [hl]
  rw [hsplit s]
  simp only [hfix]
  rw [← actmul, hU, act1]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorExistsOfGaloisFixedStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_eq_of_fixed_by_algEquiv : ∀ (F M E K : Type) [Field F] [CharZero F] [Field M] [Field E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional M E] [IsGalois M E] [CommRing K] [Algebra F K] (y : K ⊗[F] E), (∀ h : E ≃ₐ[M] E, Algebra.TensorProduct.map (AlgHom.id K K) ((h.restrictScalars F : E ≃ₐ[F] E) : E →ₐ[F] E) y = y) → ∃ z : K ⊗[F] M, Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) z = y := by
  first | exact @GlobalTheory.CNorm.tensor_exists_of_galois_fixed | exact GlobalTheory.CNorm.tensor_exists_of_galois_fixed | (intros; apply GlobalTheory.CNorm.tensor_exists_of_galois_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLawsStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryQuasiReflection_laws : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ x : Fin n → E, hermE c G x x ≠ 0 → (∀ u v, refl c G x u *ᵥ v = v + ((u - 1) * hermE c G v x / hermE c G x x) • x) ∧ refl c G x 1 = 1 ∧ (∀ u u', refl c G x u * refl c G x u' = refl c G x (u * u')) ∧ ∀ u, u * c u = 1 → IsUnE c G (refl c G x u) := by
  first | exact @GlobalTheory.UnRep.ReflLaws.refl_laws | exact GlobalTheory.UnRep.ReflLaws.refl_laws | (intros; apply GlobalTheory.UnRep.ReflLaws.refl_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNormsStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms : ∀ (p : ℕ), 0 < p → (∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), powSub p φ ≤ kNorm p φ δ) ∧ ∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (δ : F), kNorm p (RingHom.id F) δ ≤ kNorm p φ δ := by
  first | exact @GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map | exact GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map | (intros; apply GlobalTheory.CNorm.powSub_le_kNorm_and_kNorm_map <;> assumption)
end

