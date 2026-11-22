import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeMulCardPlacesLeCardOverKummer
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem prime_mul_card_le_card_over : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → p * S.card ≤ SE.card + (p - 1) * tNon p F δ S := by
  intro p F E _ _ _ _ _ ζ δ θ σ hq S SE hSE
  classical
  have hp := hq.prime
  obtain ⟨-, hrk, hgal, -, -, -, hemb⟩ := kummer_galois p F E ζ δ θ σ hq
  have h1 : SE.card = ∑ v ∈ S, (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun w hw => (hSE w).1 hw)
  have h2 : tNon p F δ S
      = ∑ v ∈ S, if (∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ)
        then 1 else 0 := by
    rw [← Finset.card_filter, tNon, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_le_sum (fun v hv => ?_)
  by_cases hs : ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ
  · obtain ⟨w, hw⟩ := (places_over F E).2.1 v
    have : 0 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩⟩
    rw [if_pos hs]
    omega
  · rw [if_neg hs]
    push Not at hs
    obtain ⟨r, hr⟩ := hs
    have hδ : δ ≠ 0 := fun h0 => hq.nonpow 0 (by rw [h0, zero_pow hp.ne_zero])
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero, eq_comm, map_eq_zero] at hr
      exact hδ hr
    obtain ⟨ψ, hψ⟩ := hemb (v.adicCompletion F) r hr
    obtain ⟨ψ', hψ'⟩ := hemb (v.adicCompletion F) (algebraMap F (v.adicCompletion F) ζ * r)
      (by rw [mul_pow, ← map_pow, hq.root.pow_eq_one, map_one, one_mul, hr])
    have hne : ψ ≠ ψ' := by
      intro h
      rw [← h, hψ, eq_comm, mul_eq_right₀ hr0,
        ← map_one (algebraMap F (v.adicCompletion F))] at hψ'
      exact hq.root.ne_one hp.one_lt ((algebraMap F (v.adicCompletion F)).injective hψ')
    obtain ⟨w, w', hww, hw, hw'⟩ := two_places_of_embeddings F E v ψ ψ' hne
    have h3 := ncard_places_over_eq_of_prime_degree p F E hp hrk v w w' hww hw hw'
    have h4 : (SE.filter (fun w => w.under (𝓞 F) = v)).card = p := by
      rw [← h3, ← Set.ncard_coe_finset]
      congr 1
      ext u
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨(hSE u).2 (h ▸ hv), h⟩⟩
    omega

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresSUnitsNumberField
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sqs_subgroupOf_self {G : Type} [CommGroup G] (U : Subgroup G) :
    (sqs U).subgroupOf U = sqs (⊤ : Subgroup U) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨⟨y, hy⟩, Subgroup.mem_top _, Subtype.ext h⟩
  · rintro ⟨y, -, h⟩
    exact ⟨y.1, y.2, congrArg Subtype.val h⟩

theorem card_sq_eq_one_sUnits (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Nat.card {a : sUnits F S // a ^ 2 = 1} = 2 := by
  have hm : (-1 : Fˣ) ∈ sUnits F S := by
    rw [mem_sUnits]; intro v _; simp
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, by simp⟩, ⟨⟨-1, hm⟩, Subtype.ext (by simp)⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun a : {a : sUnits F S // a ^ 2 = 1} => ((a.1.1 : Fˣ) : F)) h
    simp only [OneMemClass.coe_one, Units.val_one, Units.val_neg] at h1
    norm_num at h1
  · rw [Set.eq_univ_iff_forall]
    rintro ⟨⟨a, ha⟩, h⟩
    have h1 : (a : F) ^ 2 = 1 := by
      have := congrArg (fun a : sUnits F S => ((a.1 : Fˣ) : F)) h
      simpa using this
    rcases sq_eq_one_iff.mp h1 with h2 | h2
    · left
      exact Subtype.ext (Subtype.ext (Units.ext h2))
    · right
      exact Subtype.ext (Subtype.ext (Units.ext h2))

theorem relIndex_sqs_sUnits : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (sqs (sUnits F S)).relIndex (sUnits F S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  intro F _ _ S
  haveI := GlobalTheory.T.sUnitsNumberField_fg F S
  rw [Subgroup.relIndex, sqs_subgroupOf_self, GlobalTheory.T.index_sqs_of_fg, card_sq_eq_one_sUnits,
    ← GlobalTheory.T.finrank_sUnitsNumberField_add_one F S, pow_succ]

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SiegelCover
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma le_two_pow_mul_of_consecutive_le {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (h : ∀ p q : Fin N, (q : ℕ) = p + 1 → a p ≤ 2 * a q) (i j : Fin N) (hij : i < j) :
    a i ≤ 2 ^ N * a j := by
  have key : ∀ d : ℕ, ∀ i j : Fin N, (j : ℕ) = i + d → a i ≤ 2 ^ d * a j := by
    intro d
    induction d with
    | zero =>
      intro i j hij
      have : i = j := Fin.ext (by simpa using hij.symm)
      subst this
      simp
    | succ d ih =>
      intro i j hij
      have hm : (i : ℕ) + d < N := by have := j.isLt; omega
      have h1 := ih i ⟨i + d, hm⟩ rfl
      have h2 := h ⟨i + d, hm⟩ j (by simp only; omega)
      calc a i ≤ 2 ^ d * a ⟨i + d, hm⟩ := h1
        _ ≤ 2 ^ d * (2 * a j) := by gcongr
        _ = 2 ^ (d + 1) * a j := by ring
  have hlt : (i : ℕ) < j := hij
  have hd := key ((j : ℕ) - i) i j (by omega)
  calc a i ≤ 2 ^ ((j : ℕ) - i) * a j := hd
    _ ≤ 2 ^ N * a j :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by have := j.isLt; omega))
        (ha j).le

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_reduced_iwasawa_decomposition {ι : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] (g : Matrix ι ι ℝ) (hg : g.det ≠ 0) :
    ∃ (γ : Matrix ι ι ℤ) (k : Matrix ι ι ℝ) (a : ι → ℝ) (n : Matrix ι ι ℝ),
      (γ.det = 1 ∨ γ.det = -1) ∧ kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧
      (∀ i j, j < i → n i j = 0) ∧ (∀ i j, |n i j| ≤ 1) ∧
      (∀ i j, i < j → a i ≤ 2 ^ Fintype.card ι * a j) ∧
      g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  set N := Fintype.card ι
  let e : Fin N ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  let f : Fin N ≃ ι := e.toEquiv
  have hmono : ∀ i j : ι, f.symm i < f.symm j ↔ i < j := by
    intro i j
    have := (e.lt_iff_lt (x := f.symm i) (y := f.symm j))
    simpa [f] using this
  obtain ⟨γ, k, a, n, hγ, hk, ha, hn1, hn0, hnb, hcons, hdec⟩ :=
    _root_.GlobalTheory.ClassFin.HermiteReduction.exists_reduced N (g.submatrix f f)
      (by rw [det_submatrix_equiv_self f g]; exact hg)
  refine ⟨γ.submatrix f.symm f.symm, k.submatrix f.symm f.symm, a ∘ f.symm,
    n.submatrix f.symm f.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self]; exact hγ
  · rw [transpose_submatrix, submatrix_mul_equiv, hk, submatrix_one_equiv]
  · exact fun i => ha _
  · exact fun i => hn1 _
  · intro i j hij
    exact hn0 _ _ ((hmono j i).mpr hij)
  · intro i j
    show |n (f.symm i) (f.symm j)| ≤ 1
    rcases lt_trichotomy (f.symm i) (f.symm j) with h | h | h
    · exact (hnb _ _ h).trans (by norm_num)
    · rw [h, hn1]; simp
    · rw [hn0 _ _ h]; simp
  · intro i j hij
    exact le_two_pow_mul_of_consecutive_le a ha hcons _ _ ((hmono i j).mpr hij)
  · have hg' : g = (g.submatrix f f).submatrix f.symm f.symm := by ext i j; simp
    rw [hg', ← submatrix_map, submatrix_mul_equiv, hdec, ← submatrix_diagonal_equiv,
      submatrix_mul_equiv, submatrix_mul_equiv]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma isSiegel_of_reduced {ι : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] {C : ℝ} {g : Matrix ι ι ℝ} {γ : Matrix ι ι ℤ} {k : Matrix ι ι ℝ}
    {a : ι → ℝ} {n : Matrix ι ι ℝ} (hC : 1 ≤ C) (hg : g.det = 1) (hγ : γ.det = 1)
    (hk : kᵀ * k = 1) (ha : ∀ i, 0 < a i) (hn1 : ∀ i, n i i = 1)
    (hn0 : ∀ i j, j < i → n i j = 0) (hnb : ∀ i j, |n i j| ≤ 1)
    (hlt : ∀ i j, i < j → a i ≤ C * a j)
    (hdec : g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n) :
    _root_.GlobalTheory.ClassFin.IsSiegel C k a n := by
  have hn : n.det = 1 := by
    rw [det_of_upperTriangular (by intro i j h; exact hn0 i j h)]
    simp [hn1]
  have hγR : (γ.map (Int.cast : ℤ → ℝ)).det = 1 := by
    rw [show γ.map (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ).mapMatrix γ from rfl,
      ← RingHom.map_det, hγ]
    simp
  have hdet : k.det * ∏ i, a i = 1 := by
    have := congrArg det hdec
    rw [det_mul, det_mul, det_mul, hg, hn, det_diagonal, hγR] at this
    linarith
  have hk2 : k.det * k.det = 1 := by
    have := congrArg det hk
    rwa [det_mul, det_transpose, det_one] at this
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  have hk1 : k.det = 1 := by
    rcases mul_self_eq_one_iff.mp hk2 with h | h
    · exact h
    · exfalso
      rw [h] at hdet
      linarith
  refine ⟨hk, hk1, ha, ?_, hlt, hn1, hn0, fun i j => (hnb i j).trans hC⟩
  rw [hk1, one_mul] at hdet
  exact hdet

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma exists_det_one_of_det_neg_one {ι : Type} [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] {g : Matrix ι ι ℝ} {γ : Matrix ι ι ℤ} {k : Matrix ι ι ℝ} {a : ι → ℝ}
    {n : Matrix ι ι ℝ} (hγ : γ.det = -1) (hk : kᵀ * k = 1) (hn1 : ∀ i, n i i = 1)
    (hn0 : ∀ i j, j < i → n i j = 0) (hnb : ∀ i j, |n i j| ≤ 1)
    (hdec : g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n) :
    ∃ (γ' : Matrix ι ι ℤ) (k' n' : Matrix ι ι ℝ), γ'.det = 1 ∧ k'ᵀ * k' = 1 ∧
      (∀ i, n' i i = 1) ∧ (∀ i j, j < i → n' i j = 0) ∧ (∀ i j, |n' i j| ≤ 1) ∧
      g * γ'.map (Int.cast : ℤ → ℝ) = k' * diagonal a * n' := by
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [det_isEmpty] at hγ
    norm_num at hγ
  set d : ι → ℤ := fun i => if i = i₀ then -1 else 1 with hd_def
  have hd : ∀ i, (d i : ℝ) * d i = 1 := by
    intro i; simp only [hd_def]; split_ifs <;> norm_num
  have hda : ∀ i, |(d i : ℝ)| = 1 := by
    intro i; simp only [hd_def]; split_ifs <;> norm_num
  set D : Matrix ι ι ℝ := diagonal (fun i => (d i : ℝ)) with hD
  have hDD : D * D = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hd i
  have hcomm : D * diagonal a = diagonal a * D := by
    rw [hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have hentry : ∀ i j, (D * n * D) i j = d i * n i j * d j := by
    intro i j
    simp [hD, mul_diagonal, diagonal_mul]
  refine ⟨γ * diagonal d, k * D, D * n * D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_mul, hγ, det_diagonal]
    have : ∏ i, d i = -1 := by
      simp [hd_def, Finset.prod_ite_eq']
    rw [this]; norm_num
  · rw [transpose_mul, hD, diagonal_transpose, ← hD, Matrix.mul_assoc, ← Matrix.mul_assoc kᵀ,
      hk, Matrix.one_mul, hDD]
  · intro i
    rw [hentry, hn1, mul_one]
    exact hd i
  · intro i j hij
    rw [hentry, hn0 i j hij]; simp
  · intro i j
    rw [hentry, abs_mul, abs_mul, hda, hda]
    simpa using hnb i j
  · have hmap : (γ * diagonal d).map (Int.cast : ℤ → ℝ) = γ.map (Int.cast) * D := by
      ext i j
      simp [hD, mul_diagonal]
    rw [hmap, ← Matrix.mul_assoc, hdec]
    calc k * diagonal a * n * D = k * (D * D) * diagonal a * n * D := by
          rw [hDD, Matrix.mul_one]
      _ = k * D * diagonal a * (D * n * D) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (diagonal a) D (n * D), ← hcomm]
          simp only [Matrix.mul_assoc]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.siegel_cover (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] :
    ∃ C : ℝ, ∀ g : Matrix ι ι ℝ, g.det = 1 → ∃ γ : Matrix ι ι ℤ, γ.det = 1 ∧ ∃ k a n, _root_.GlobalTheory.ClassFin.IsSiegel C k a n ∧
      g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  refine ⟨2 ^ Fintype.card ι, fun g hg => ?_⟩
  have hC : (1 : ℝ) ≤ 2 ^ Fintype.card ι := one_le_pow₀ (by norm_num)
  obtain ⟨γ, k, a, n, hγ, hk, ha, hn1, hn0, hnb, hlt, hdec⟩ :=
    exists_reduced_iwasawa_decomposition g (by rw [hg]; norm_num)
  rcases hγ with hγ | hγ
  · exact ⟨γ, hγ, k, a, n,
      isSiegel_of_reduced hC hg hγ hk ha hn1 hn0 hnb hlt hdec, hdec⟩
  · obtain ⟨γ', k', n', hγ', hk', hn1', hn0', hnb', hdec'⟩ :=
      exists_det_one_of_det_neg_one hγ hk hn1 hn0 hnb hdec
    exact ⟨γ', hγ', k', a, n',
      isSiegel_of_reduced hC hg hγ' hk' ha hn1' hn0' hnb' hlt hdec', hdec'⟩

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SubgroupPowRelIndexUnitsOfIsAdicComplete
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pIdx_eq_pTor_of_finite_group (p : ℕ) {G : Type} [CommGroup G] [Finite G]
    (U : Subgroup G) : pTor p U ≠ 0 ∧ pIdx p U = pTor p U := by
  have h1 : pTor p U = Nat.card (powMonoidHom p : U →* U).ker := by
    unfold pTor
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
        invFun := fun y => ⟨y.1.1, y.1.2, congrArg Subtype.val y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h2 : pIdx p U = (powMonoidHom p : U →* U).range.index := by
    unfold pIdx pows Subgroup.relIndex
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext h⟩
    · rintro ⟨y, h⟩
      exact ⟨y.1, y.2, congrArg Subtype.val h⟩
  have h3 := (powMonoidHom p : U →* U).range.card_mul_index
  have h4 := (powMonoidHom p : U →* U).ker.card_mul_index
  rw [Subgroup.index_ker] at h4
  have h5 : Nat.card (powMonoidHom p : U →* U).range ≠ 0 := Nat.card_pos.ne'
  refine ⟨h1 ▸ Nat.card_pos.ne', ?_⟩
  rw [h1, h2]
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h5)
  rw [h3, ← h4, mul_comm]

theorem pIdx_units_of_isAdicComplete : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 → IsAdicComplete (Ideal.span {π}) O → Nat.card (O ⧸ Ideal.span {(p : O) * π}) ≠ 0 → pTor p (⊤ : Subgroup Oˣ) ≠ 0 ∧ pIdx p (⊤ : Subgroup Oˣ) = Nat.card (O ⧸ Ideal.span {(p : O)}) * pTor p (⊤ : Subgroup Oˣ) := by
  intro p O _ _ _ π hp hπ hc hfin
  haveI : Finite (O ⧸ Ideal.span {(p : O) * π}) := Nat.finite_of_card_ne_zero hfin
  have hp0 : (p : O) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  obtain ⟨hd1, hd2⟩ := GlobalTheory.T.subgroupPowImage_unitsCongruentOneMod_of_isAdicComplete p O π hp hπ hc
  have hle : Ideal.span {(p : O) * π} ≤ Ideal.span {π} :=
    Ideal.span_singleton_le_span_singleton.mpr (Dvd.intro_left _ rfl)
  have hle' : Ideal.span {(p : O) * π} ≤ Ideal.span {(p : O)} :=
    Ideal.span_singleton_le_span_singleton.mpr (Dvd.intro _ rfl)
  have hs := GlobalTheory.T.relIndex_oneUnits_mul_eq_card_quotient' O ((p : O) * π) p (mul_ne_zero hp0 hπ) (Dvd.intro _ rfl)
    (hle.trans (IsAdicComplete.le_jacobson_bot _))
  have hk : pIdx p (oneUnits ((p : O) * π)) = Nat.card (O ⧸ Ideal.span {(p : O)}) := by
    unfold pIdx
    rw [hd1, ← hs, sq, mul_assoc]
  haveI : Finite (O ⧸ Ideal.span {(p : O)}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle')
  have hk0 : Nat.card (O ⧸ Ideal.span {(p : O)}) ≠ 0 := Nat.card_pos.ne'
  let g : Oˣ →* (O ⧸ Ideal.span {(p : O) * π})ˣ :=
    Units.map (Ideal.Quotient.mk (Ideal.span {(p : O) * π}) : O →* O ⧸ Ideal.span {(p : O) * π})
  have hker : g.ker = oneUnits ((p : O) * π) := rfl
  obtain ⟨hr1, hr2⟩ := pIdx_eq_pTor_of_finite_group p g.range
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.powIndex_torsion_ker_range_mul p _ _ g (by rw [hker, hk]; exact hk0)
    (by rw [hker, hd2]; exact one_ne_zero) (by rw [hr2]; exact hr1) hr1
  refine ⟨h2, ?_⟩
  rw [hker, hd2, hk, hr2, mul_one, mul_right_comm] at h3
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hr1) h3

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TwoMulCardPlacesLeCardOverQuadratic
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_mul_card_le_card_over : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → 2 * S.card ≤ SE.card + tFin F δ S := by
  intro F E _ _ _ _ _ δ θ σ hq S SE hSE
  classical
  have h1 : SE.card = ∑ v ∈ S, (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun w hw => (hSE w).1 hw)
  have h2 : tFin F δ S
      = ∑ v ∈ S, if ¬ IsSquare (algebraMap F (v.adicCompletion F) δ) then 1 else 0 := by
    rw [← Finset.card_filter, tFin, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  rw [h1, h2, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun v hv => ?_)
  by_cases hs : IsSquare (algebraMap F (v.adicCompletion F) δ)
  · obtain ⟨w, w', hne, hw, hw'⟩ := GlobalTheory.T.exists_two_places_over_of_isSquare_local F E δ θ σ hq v hs
    have : 1 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.one_lt_card.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩,
        w', Finset.mem_filter.2 ⟨(hSE w').2 (hw' ▸ hv), hw'⟩, hne⟩
    omega
  · obtain ⟨w, hw⟩ := (places_over F E).2.1 v
    have : 0 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩⟩
    rw [if_pos hs]
    omega

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalKummerNormsEqTopOfPowStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow : ∀ (p : ℕ) (F L : Type) [Field F] [Field L] [CharZero L] (φ : F →+* L) (δ : F) (r : L), 0 < p → δ ≠ 0 → r ^ p = φ δ → kNorm p φ δ = ⊤ := by
  first | exact @GlobalTheory.CNorm.kNorm_eq_top_of_pow | exact GlobalTheory.CNorm.kNorm_eq_top_of_pow | (intros; apply GlobalTheory.CNorm.kNorm_eq_top_of_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ValuationUnramifiedKummerOfCoprimeUnitStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_unramified_kummer_of_coprime_unit : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 F)).valuation F (p : F) = 1 → (w.under (𝓞 F)).valuation F δ = 1 → ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x := by
  first | exact @GlobalTheory.CNorm.kummer_valuation_unramified | exact GlobalTheory.CNorm.kummer_valuation_unramified | (intros; apply GlobalTheory.CNorm.kummer_valuation_unramified <;> assumption)
end

