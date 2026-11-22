import ReciprocityTheory.DualLattices.Bundle0021
import ReciprocityTheory.DualLattices.Bundle0020
import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf
import ReciprocityTheory.DualLattices.UpSmith
import ReciprocityTheory.DualLattices.Bundle0007

-- bundled from ReciprocityTheory.DualLattices.ATowerInh
section
noncomputable section

open PowerSeries

namespace ReciprocityTheory.PGsh

namespace TowerExample

variable (p : ℕ) [Fact p.Prime]

abbrev TQ (m : ℕ) := (ZMod p)⟦X⟧ ⧸ Ideal.span {(X : (ZMod p)⟦X⟧) ^ m}

lemma ne_top (m : ℕ) (hm : 0 < m) : Ideal.span {(X : (ZMod p)⟦X⟧) ^ m} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top, PowerSeries.isUnit_iff_constantCoeff]
  simp [zero_pow hm.ne']

lemma nontriv (m : ℕ) (hm : 0 < m) : Nontrivial (TQ p m) := by
  rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
  exact ne_top p m hm

lemma isLocal (m : ℕ) (hm : 0 < m) : IsLocalRing (TQ p m) := by
  haveI := nontriv p m hm
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

lemma charP_of_zmod (A : Type) [CommRing A] [Algebra (ZMod p) A] [Nontrivial A] : CharP A p := charP_of_injective_algebraMap (algebraMap (ZMod p) A).injective p

lemma isLocalHom_of_surj {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [Nontrivial S]
    (f : R →+* S) (hf : Function.Surjective f) : IsLocalHom f := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  obtain ⟨c, hc⟩ := hf (↑ha.unit⁻¹ : S)
  have hker : RingHom.ker f ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
  have h1 : 1 - a * c ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, map_one, map_mul, hc, IsUnit.mul_val_inv, sub_self]
  have h2 : a * c ∈ IsLocalRing.maximalIdeal R :=
    Ideal.mul_mem_right c _ ((IsLocalRing.mem_maximalIdeal a).2 hna)
  have h3 := Ideal.add_mem _ (hker h1) h2
  rw [sub_add_cancel] at h3
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3

lemma pos (n : ℕ) : 0 < p ^ (n + 1) := pow_pos (Fact.out : p.Prime).pos _

lemma pos2 (n : ℕ) : 0 < 2 * p ^ (n + 1) := by
  have := pos p n
  omega

def alg (m : ℕ) (hm : 0 < m) : LAlg (ZMod p) :=
  { carrier := TQ p m, loc := isLocal p m hm }

def algO : LAlg (ZMod p) := { carrier := (ZMod p)⟦X⟧ }

def red (m : ℕ) : TQ p (2 * m) →ₐ[ZMod p] TQ p m :=
  Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ (ZMod p) _) (fun a ha => by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    rw [Ideal.mem_span_singleton] at ha
    exact (pow_dvd_pow X (by omega : m ≤ 2 * m)).trans ha)

lemma red_mk (m : ℕ) (f : (ZMod p)⟦X⟧) :
    red p m (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ f := rfl

lemma red_surj (m : ℕ) : Function.Surjective (red p m) := by
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ f, red_mk p m f⟩

lemma red_ker (m : ℕ) : RingHom.ker (red p m) =
    Ideal.span {(Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ (2 * m)}) (X ^ m))} := by
  ext a
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [RingHom.mem_ker]
  change red p m (Ideal.Quotient.mk _ f) = 0 ↔ _
  rw [red_mk, Ideal.Quotient.eq_zero_iff_mem]
  simp only [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨Ideal.Quotient.mk _ g, map_mul _ _ _⟩
  · rintro ⟨b, hb⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hb
    have h1 : X ^ m ∣ f - X ^ m * g := (pow_dvd_pow X (by omega : m ≤ 2 * m)).trans hb
    have h2 : (X : (ZMod p)⟦X⟧) ^ m ∣ X ^ m * g := dvd_mul_right _ _
    simpa using dvd_add h1 h2

lemma red_ann (m : ℕ) (a : TQ p (2 * m))
    (ha : a * Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ (2 * m)}) (X ^ m) = 0) :
    a ∈ Ideal.span {(Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ (2 * m)}) (X ^ m))} := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at ha
  rw [Ideal.mem_span_singleton]
  have h : (X : (ZMod p)⟦X⟧) ^ m ∣ f := by
    rw [two_mul, pow_add] at ha
    exact (mul_dvd_mul_iff_right (pow_ne_zero m PowerSeries.X_ne_zero)).1 ha
  obtain ⟨g, rfl⟩ := h
  exact ⟨Ideal.Quotient.mk _ g, map_mul _ _ _⟩

lemma lt_pow_succ (j : ℕ) (hp : 2 ≤ p) : j < p ^ (j + 1) := by
  induction j with
  | zero =>
    rw [zero_add, pow_one]
    omega
  | succ k ih =>
    have h1 : p ^ (k + 1) * 2 ≤ p ^ (k + 1) * p := Nat.mul_le_mul_left _ hp
    rw [pow_succ p (k + 1)]
    omega

lemma xi_sq (m : ℕ) : Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ (2 * m)}) (X ^ m) *
    Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ (2 * m)}) (X ^ m) = 0 := by
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_add, ← two_mul]
  exact Ideal.subset_span (Set.mem_singleton _)

lemma char_lemma (m k : ℕ) (hm : 0 < m) (hk : 0 < k) : ((p ^ k : ℕ) : TQ p m) = 0 := by
  haveI := nontriv p m hm
  haveI := charP_of_zmod p (TQ p m)
  rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow hk.ne']

lemma sep_lemma (a : (ZMod p)⟦X⟧)
    (ha : ∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ p ^ (n + 1)}) a = 0) :
    a = 0 := by
  ext j
  have h := ha j
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at h
  simpa using h j (lt_pow_succ p j (Fact.out : p.Prime).two_le)

lemma frob_lemma (m k : ℕ) (hm : 0 < m) :
    (Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ m}) (1 + X)) ^ p ^ k =
      1 + 1 * Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ m}) (X ^ p ^ k) := by
  haveI := nontriv p m hm
  haveI := charP_of_zmod p (TQ p m)
  haveI : ExpChar (TQ p m) p := ExpChar.prime (Fact.out : p.Prime)
  rw [map_add, map_one, add_pow_char_pow, one_pow, one_mul, map_pow]

def u1X : ((ZMod p)⟦X⟧)ˣ :=
  (show IsUnit (1 + X : (ZMod p)⟦X⟧) by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp).unit

end TowerExample

open TowerExample in

def toyTower (p : ℕ) [Fact p.Prime] : ATower (ZMod p) p where
  O := algO p
  R' n := alg p (2 * p ^ (n + 1)) (pos2 p n)
  R n := alg p (p ^ (n + 1)) (pos p n)
  π n := ⟨red p (p ^ (n + 1)), by
    haveI := isLocal p _ (pos2 p n); haveI := nontriv p _ (pos p n)
    exact isLocalHom_of_surj _ (red_surj p _)⟩
  q n := ⟨Ideal.Quotient.mkₐ (ZMod p) (Ideal.span {(X : (ZMod p)⟦X⟧) ^ p ^ (n + 1)}), by
    haveI := nontriv p _ (pos p n)
    exact isLocalHom_of_surj _
      (Ideal.Quotient.mkₐ_surjective (ZMod p) (Ideal.span {(X : (ZMod p)⟦X⟧) ^ p ^ (n + 1)}))⟩
  ξ n := Ideal.Quotient.mk _ (X ^ p ^ (n + 1))
  surj n := red_surj p _
  ker_eq n := red_ker p _
  ξ_sq n := xi_sq p _
  ann n a ha := red_ann p _ a ha
  char n := char_lemma p _ _ (pos2 p n) (Nat.succ_pos n)
  sep a ha := sep_lemma p a ha
  c := 1
  cp n := 1
  cp_spec n := (map_one _).trans (map_one _).symm
  zh n := Units.map (Ideal.Quotient.mk (Ideal.span {(X : (ZMod p)⟦X⟧) ^ (2 * p ^ (n + 1))}) : (ZMod p)⟦X⟧ →* TQ p (2 * p ^ (n + 1))) (u1X p)
  zh_pow n := frob_lemma p _ _ (pos2 p n)
  ζ n := u1X p
  ζ_spec n := rfl

lemma toyTower_c_ne_zero (p : ℕ) [Fact p.Prime] : (toyTower p).c ≠ 0 := (show (1 : (ZMod p)⟦X⟧) ≠ 0 from one_ne_zero)

theorem toyTower_isDomain (p : ℕ) [Fact p.Prime] : IsDomain ((toyTower p).O : Type) := (inferInstance : IsDomain (ZMod p)⟦X⟧)

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.EmbeddingSeparatingGroupStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def EmbeddingSeparatingGroupStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H),
    ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (β : G → O),
      (∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) ∧ H.ρ (β 1) = 1 ∧
      IsUnit (Fintype.card G : R) ∧
      (∀ i γ, U.εT i ≠ 0 → U.sg (U.φ i) (β γ) = U.sg i (β γ) ^ p) ∧
      (∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
        ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1) ∧
      (∀ i, U.εT i ≠ 0 → ∃ γ, v (algebraMap R C (U.sg i (β γ) - 1)) = 1)

def EigenElementaryDivisorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) →
    ∃ (κ : Ix g → Fin U.m) (Λ : Matrix (Ix g) (Ix g) R) (ε : Ix g → R),
      IsUnit Λ.det ∧ (∀ j, Matrix.vecMul (Λ j) (U.εT (κ j)) = Λ j) ∧
      (∀ j, ∃ c, cp = ε j * c) ∧
      (∀ i, ∏ j ∈ Finset.univ.filter (fun j => κ j = i), v (algebraMap R C (ε j)) = X i) ∧
      (∀ i (n : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT i)) ≃ₗ[R] (Fin n → R)) →
        (Finset.univ.filter fun j => κ j = i).card = n) ∧
      (∀ i, Submodule.span R (Set.range fun k => (fromRows H.Ht (bt2 H U) * U.εT i) k) =
        Submodule.span R ((fun j => ε j • Λ j) '' {j | κ j = i}))

def EigenRankStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (U : UnramData p g v R O σ cp H),
    (∀ i, ∃ n : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT i)) ≃ₗ[R] (Fin n → R)) ∧
      Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT (U.φ i))) ≃ₗ[R] (Fin n → R))) ∧
    (∀ i, U.εT i = 0 → U.r i = 0)

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.ExistsFromRowsMulVecIff
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

variable {R : Type} [CommRing R] {g : ℕ}

private lemma smulMV {κ μ : Type} [Fintype μ] (c : R) (M : Matrix κ μ R) (v : μ → R) :
    (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
    Finset.mul_sum, mul_assoc]

private theorem matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S]
    [IsDomain S] {A B : Matrix n n S} {c : S} (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n S)) :
    B * A = c • (1 : Matrix n n S) := by
  have hdet : A.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have key : A.det • (B * A) = A.det • (c • (1 : Matrix n n S)) := by
    calc A.det • (B * A) = (A.adjugate * A) * (B * A) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = A.adjugate * ((A * B) * A) := by simp only [Matrix.mul_assoc]
      _ = A.adjugate * (c • A) := by rw [h, Matrix.smul_mul, Matrix.one_mul]
      _ = c • (A.adjugate * A) := by rw [Matrix.mul_smul]
      _ = A.det • (c • (1 : Matrix n n S)) := by rw [Matrix.adjugate_mul]; exact smul_comm _ _ _
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  simpa only [Matrix.smul_apply, smul_eq_mul] using mul_left_cancel₀ hdet h2

private theorem block_products_of_transpose_form_eq_smul [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R}
    {E : Matrix (Ix g) (Ix g) R} {cp : R} (hcp : cp ≠ 0) (hE : IsUnit E.det)
    (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E) :
    Bt * (Eᵀ)⁻¹ * Htᵀ = cp • 1 ∧ Bt * (Eᵀ)⁻¹ * Btᵀ = 0 ∧ -(Ht * (Eᵀ)⁻¹) * Htᵀ = 0 ∧
      -(Ht * (Eᵀ)⁻¹) * Btᵀ = cp • 1 := by
  have hT1 : Htᵀ * Bt - Btᵀ * Ht = cp • Eᵀ := by
    simpa only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul] using congrArg Matrix.transpose hform
  have hEF : Eᵀ * (Eᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose])
  have hP : Matrix.fromCols Htᵀ Btᵀ * Matrix.fromRows (Bt * (Eᵀ)⁻¹) (-(Ht * (Eᵀ)⁻¹)) =
      cp • (1 : Matrix (Ix g) (Ix g) R) := by
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_neg, ← sub_eq_add_neg, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.sub_mul, hT1, Matrix.smul_mul, hEF]
  have hQ := matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero hcp hP
  rw [Matrix.fromRows_mul_fromCols] at hQ
  have h1 : (cp • (1 : Matrix (Ix g) (Ix g) R)) = Matrix.fromBlocks (cp • 1) 0 0 (cp • 1) := by
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  rw [h1, Matrix.fromBlocks_inj] at hQ
  exact hQ

lemma hb_facts [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E) :
    Ht * ((Eᵀ)⁻¹ * Htᵀ) = 0 ∧ Bt * ((Eᵀ)⁻¹ * Htᵀ) = cp • (1 : Matrix (Fin g) (Fin g) R) := by
  obtain ⟨h11, -, h21, -⟩ := block_products_of_transpose_form_eq_smul hcp hE hform
  refine ⟨?_, ?_⟩
  · rw [Matrix.neg_mul, neg_eq_zero, Matrix.mul_assoc] at h21
    exact h21
  · rw [Matrix.mul_assoc] at h11
    exact h11

variable {m : ℕ}

lemma exists_fromRows_mulVec_iff [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) (hHt : Ht * εT i = (εL (π i))ᵀ * Ht)
    (hBt : Bt * εT i = εL i * Bt) (x : Fin g → R) (hx : εL i *ᵥ x = x) :
    (∃ t, fromRows Ht Bt *ᵥ (εT i *ᵥ t) = Sum.elim (0 : Fin g → R) x) ↔
      ∃ z, Htᵀ *ᵥ x = cp • z := by
  have hT1 : Htᵀ * Bt - Btᵀ * Ht = cp • Eᵀ := by
    simpa only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul] using congrArg Matrix.transpose hform
  constructor
  · rintro ⟨t, ht⟩
    rw [Matrix.fromRows_mulVec] at ht
    have h1 : Ht *ᵥ (εT i *ᵥ t) = 0 := funext fun k => by simpa using congrFun ht (Sum.inl k)
    have h2 : Bt *ᵥ (εT i *ᵥ t) = x := funext fun k => by simpa using congrFun ht (Sum.inr k)
    refine ⟨Eᵀ *ᵥ (εT i *ᵥ t), ?_⟩
    rw [← smulMV, ← hT1, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1,
      h2, Matrix.mulVec_zero, sub_zero]
  · rintro ⟨z, hz⟩
    obtain ⟨hHF, hBF⟩ := hb_facts hcp hE hform
    have hs1 : Ht *ᵥ ((Eᵀ)⁻¹ *ᵥ z) = 0 := by
      have h : cp • (Ht *ᵥ ((Eᵀ)⁻¹ *ᵥ z)) = 0 := by
        rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hz]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        rw [hHF, Matrix.zero_mulVec]
      exact (smul_eq_zero.mp h).resolve_left hcp
    have hs2 : Bt *ᵥ ((Eᵀ)⁻¹ *ᵥ z) = x := by
      have h : cp • (Bt *ᵥ ((Eᵀ)⁻¹ *ᵥ z)) = cp • x := by
        rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hz]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        rw [hBF, smulMV, Matrix.one_mulVec]
      exact smul_right_injective _ hcp h
    generalize (Eᵀ)⁻¹ *ᵥ z = s at hs1 hs2
    have e1 : Ht *ᵥ (εT i *ᵥ s) = 0 := by
      rw [Matrix.mulVec_mulVec, hHt, ← Matrix.mulVec_mulVec, hs1, Matrix.mulVec_zero]
    have e2 : Bt *ᵥ (εT i *ᵥ s) = x := by
      rw [Matrix.mulVec_mulVec, hBt, ← Matrix.mulVec_mulVec, hs2, hx]
    exact ⟨s, by rw [Matrix.fromRows_mulVec, e1, e2]⟩

lemma cok_kill [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) (hπi : π (π i) = i)
    (hHt : ∀ j, Ht * εT j = (εL (π j))ᵀ * Ht) :
    ∀ f ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ), ∃ t, Ht *ᵥ (εT (π i) *ᵥ t) = cp • f := by
  intro f hf
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hf
  obtain ⟨-, -, -, h22⟩ := block_products_of_transpose_form_eq_smul hcp hE hform
  rw [Matrix.neg_mul, Matrix.mul_assoc] at h22
  have hHt' : Ht *ᵥ (-((Eᵀ)⁻¹ *ᵥ (Btᵀ *ᵥ y))) = cp • y := by
    rw [Matrix.mulVec_neg]
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.neg_mulVec, h22, smulMV, Matrix.one_mulVec]
  generalize -((Eᵀ)⁻¹ *ᵥ (Btᵀ *ᵥ y)) = t at hHt'
  refine ⟨t, ?_⟩
  simp only [Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, hHt, hπi, ← Matrix.mulVec_mulVec, hHt', Matrix.mulVec_smul]

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.HasLenCokerDet
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

lemma hasLen_of_equiv {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {x : NNReal} (h : HasLen v R N x) : HasLen v R M x := by
  obtain ⟨k, c, ⟨f⟩, hx⟩ := h
  exact ⟨k, c, ⟨e.trans f⟩, hx⟩

theorem hasLen_coker_det' {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R) :
    HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)) := by
  set e := Fintype.equivFin κ
  set X' := X.submatrix e.symm e.symm
  have hdet : X'.det = X.det := Matrix.det_submatrix_equiv_self e.symm X
  let Φ : (κ → R) ≃ₗ[R] (Fin (Fintype.card κ) → R) := LinearEquiv.funCongrLeft R R e.symm
  have hrange : (LinearMap.range X.mulVecLin).map (Φ : (κ → R) →ₗ[R] (Fin (Fintype.card κ) → R)) =
      LinearMap.range X'.mulVecLin := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨y ∘ e.symm, ?_⟩
      funext i
      show (X' *ᵥ (y ∘ e.symm)) i = (X *ᵥ y) (e.symm i)
      simp only [X', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply]
      exact Equiv.sum_comp e.symm (fun k => X (e.symm i) k * y k)
    · rintro ⟨y, rfl⟩
      refine ⟨X *ᵥ (y ∘ e), ⟨y ∘ e, rfl⟩, ?_⟩
      funext i
      simp only [Matrix.mulVecLin_apply, X', Matrix.submatrix_mulVec_equiv, Φ,
        LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply]
      simp
  have h := Smith.hasLen_coker_det hv X'
  rw [hdet] at h
  exact hasLen_of_equiv (Submodule.Quotient.equiv _ _ Φ hrange) h

theorem lenId_of_B (hB : LenIdBStatement) : LenIdStatement :=
  lenId_of (fun C _ v R _ _ hv => hasLen_coker_det' v R hv) hB

theorem hasLen_ext' {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R)
    {A B D : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup D]
    [Module R D] (ι : A →ₗ[R] B) (π : B →ₗ[R] D) (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hex : LinearMap.range ι = LinearMap.ker π) {a c : NNReal}
    (ha : HasLen v R A a) (hc : HasLen v R D c) : HasLen v R B (a * c) :=
  hasLen_ext (hasLen_coker_det' v R hv) ι π hι hπ hex ha hc

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.HtLinStatement
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

structure ATowerL (R₀ : Type u) [CommRing R₀] (p : ℕ) extends ATower R₀ p where
  r' : ∀ n, LHom (R' (n + 1)) (R' n)
  r : ∀ n, LHom (R (n + 1)) (R n)
  r_π : ∀ n (x : (R' (n + 1) : Type u)), (r n).1 ((π (n + 1)).1 x) = (π n).1 ((r' n).1 x)
  r_q : ∀ n (x : (O : Type u)), (r n).1 ((q (n + 1)).1 x) = (q n).1 x
  r'_ξ : ∀ n, (r' n).1 (ξ (n + 1)) = ξ n
  complete : ∀ x : ∀ n, (R n : Type u), (∀ n, (r n).1 (x (n + 1)) = x n) →
    ∃ a : (O : Type u), ∀ n, (q n).1 a = x n

variable {R₀ : Type u} [CommRing R₀]

structure DualTower {p : ℕ} (Tw : ATowerL R₀ p) where
  Dp : ∀ n, DualPair (Tw.R n)
  d : ∀ n, LHom (Dp (n + 1)).D (Dp n).D
  d_π : ∀ n (x : ((Dp (n + 1)).D : Type u)), (Dp n).π.1 ((d n).1 x) = (Tw.r n).1 ((Dp (n + 1)).π.1 x)
  d_σ : ∀ n (x : (Tw.R (n + 1) : Type u)), (d n).1 ((Dp (n + 1)).σ.1 x) = (Dp n).σ.1 ((Tw.r n).1 x)
  d_η : ∀ n, (d n).1 (Dp (n + 1)).η = (Dp n).η

def LimStatement (B : BX R₀) {p : ℕ} (Tw : ATowerL R₀ p) (Dt : DualTower Tw) : Prop :=
  ∀ (ι : Type) (τ : ι → ℕ → B.G Tw.O),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    ∃ (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u)) (bt : ι → B.gg ⊗[R₀] (Tw.O : Type u)),
      (∀ i n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
        ((Tw.q n).1.toLinearMap ∘ₗ ht i)) ∧
      (∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
        B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
        (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
          (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
        LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
          LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i))

def HtLinStatement (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) (Dp : ∀ n, DualPair (Tw.R n)) : Prop :=
  ∀ (ι : Type) [Fintype ι] (τ : ι → ℕ → B.G Tw.O) (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u))
    (a : ι → ℕ → ℤ) (α : ι → (Tw.O : Type u)),
    (∀ i n, (p ^ (n + 1)) • τ i n = 0) →
    (∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i)) →
    (∀ i n, (Tw.q n).1 (α i) = a i n) →
    ∀ n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (∑ i, a i n • τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ∑ i, α i • ht i)

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.ImportsBis
section
namespace ReciprocityTheory.PGsh.L2

theorem h3 (C R : Type) [Field C] [CommRing R] [Algebra R C] :
    SubgroupFreenessStatement (C := C) (R := R) := by
  intro hC hC0 v hv N _ _ _ K _ _ _ AA
  haveI := hC
  haveI := hC0
  exact ⟨exists_coset_basis hv AA K, mem_of_restrictToSubgroup_eq_zero hv AA K, hasColength_eq_pow_mul_pow hv AA K, mem_sup_of_restrictToSubgroup_mem_sq hv AA K⟩

end ReciprocityTheory.PGsh.L2
end

