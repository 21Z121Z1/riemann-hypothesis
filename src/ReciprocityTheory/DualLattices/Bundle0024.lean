import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0022
import ReciprocityTheory.DualLattices.Bundle0014
import ReciprocityTheory.DualLattices.ValuationPairwiseDifferenceProductPowLeColengthS
import ReciprocityTheory.DualLattices.ColengthSqMulLe
import ReciprocityTheory.DualLattices.Bundle0023
import ReciprocityTheory.DualLattices.Bundle0002
import ReciprocityTheory.DualLattices.Bundle0011

-- bundled from ReciprocityTheory.DualLattices.AinfFacts
section
noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

namespace Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

abbrev A := WittVector p (PreTilt O p)

def root (ε : PreTilt O p) (k : ℕ) : PreTilt O p := (frobeniusEquiv (PreTilt O p) p).symm^[k] ε

def xi (ε : PreTilt O p) : A p O := ∑ i ∈ Finset.range p, teichmuller p (root p O ε 1) ^ i

def nu (ε : PreTilt O p) : A p O := teichmuller p (root p O ε 1) - 1

lemma root_pow (ε : PreTilt O p) (k : ℕ) : root p O ε k ^ p ^ k = ε := by
  have hsp : ∀ x : PreTilt O p, ((frobeniusEquiv (PreTilt O p) p).symm x) ^ p = x := fun x => by
    rw [← frobenius_def, ← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  induction k with
  | zero => simp [root]
  | succ k ih =>
    simp only [root] at ih ⊢
    rw [Function.iterate_succ_apply', pow_succ', pow_mul, hsp]
    exact ih

lemma torsion_free (hv : v.Integers O) (n : ℕ) (a : O) (h : a * (p : O) ^ n = 0) : a = 0 := by
  have h' := congrArg (algebraMap O C) h
  rw [map_mul, map_pow, map_natCast, map_zero] at h'
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have h0 : algebraMap O C a = 0 := (mul_eq_zero.1 h').resolve_right (pow_ne_zero _ hpC)
  exact hv.hom_inj (by rw [h0, map_zero])

lemma frob_surj (hv : v.Integers O) : Function.Surjective (frobenius (ModP O p) p) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C x) hp.out.pos
  have hvy : v y ≤ 1 := by
    have h1 : v y ^ p ≤ 1 := by
      rw [← map_pow, hy]
      exact hv.map_le_one x
    exact (pow_le_one_iff_of_nonneg (by positivity) hp.out.ne_zero).1 h1
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hvy
  refine ⟨Ideal.Quotient.mk _ z, ?_⟩
  rw [frobenius_def, ← map_pow]
  congr 1
  exact hv.hom_inj (by rw [map_pow, hy])

lemma theta_surj (hv : v.Integers O) : Function.Surjective (fontaineTheta O p) :=
  surjective_fontaineTheta (frob_surj p O hv)

lemma O_local (hv : v.Integers O) : IsLocalRing O := by
  haveI : Nontrivial O :=
    ⟨⟨(0 : O), (1 : O), fun h => by
      have h2 := congrArg (algebraMap O C) h
      simp at h2⟩⟩
  have hu : ∀ y : O, v (algebraMap O C y) = 1 → IsUnit y := fun y hy =>
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by
      rw [h0, map_zero] at hy
      exact zero_ne_one hy) hy
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases (hv.map_le_one x).lt_or_eq with hlt | heq
  · right
    apply hu
    rw [map_sub, map_one]
    exact Valuation.map_one_sub_of_lt v hlt
  · left
    exact hu x heq

lemma sepO (a : O) (h : ∀ n : ℕ, a ∈ span {(p : O) ^ (n + 1)}) : a = 0 := by
  apply IsHausdorff.haus' (I := span {(p : O)})
  intro n
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  cases n with
  | zero => simp
  | succ k => exact SModEq.zero.2 (h k)

lemma quot_nontrivial {R : Type} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) : Nontrivial (R ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.2 hI

lemma local_of_surj_sq {S T : Type} [CommRing S] [CommRing T] [IsLocalRing T] (f : S →+* T)
    (hf : Function.Surjective f) (hk : ∀ k ∈ RingHom.ker f, k * k = 0) : IsLocalRing S := by
  haveI : Nontrivial S := hf.nontrivial
  have key : ∀ y : S, IsUnit (f y) → IsUnit y := by
    intro y hy
    obtain ⟨u, hu⟩ := hy
    obtain ⟨z, hz⟩ := hf (↑u⁻¹ : T)
    have hker : y * z - 1 ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, hz, ← hu, Units.mul_inv, sub_self]
    have hsq := hk _ hker
    have h1 : y * (z * (1 - (y * z - 1))) = 1 := by linear_combination -hsq
    exact ⟨⟨y, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (f x) with h | h
  · exact Or.inl (key x h)
  · exact Or.inr (key (1 - x) (by rwa [map_sub, map_one]))

variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

lemma ker_theta : RingHom.ker (fontaineTheta O p) = span {xi p O ε} := by
  obtain ⟨pflat, hpf⟩ := exists_pflat (p := p) (C := _) (v := v) (O := O) (hv := hv)
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  exact (hX.2.2.2 pflat hpf).1

lemma theta_xi : fontaineTheta O p (xi p O ε) = 0 := by
  rw [← RingHom.mem_ker, ker_theta p O hv ε hε]
  exact Ideal.mem_span_singleton_self _

lemma xi_nzd (y : A p O) (hy : y * xi p O ε = 0) : y = 0 := by
  obtain ⟨pflat, hpf⟩ := exists_pflat (p := p) (C := _) (v := v) (O := O) (hv := hv)
  have hK := (kerTheta (p := p) (C := C) (O := O) (v := v) hv) pflat hpf
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  obtain ⟨u, hu⟩ := (hX.2.2.2 pflat hpf).2
  rw [hu, ← mul_assoc] at hy
  have h1 : y * ↑u = 0 := (mem_nonZeroDivisors_iff.1 hK.2.1).2 _ hy
  have h2 : y * ↑u * ↑u⁻¹ = 0 := by rw [h1, zero_mul]
  rwa [mul_assoc, Units.mul_inv, mul_one] at h2

lemma teich_eps : teichmuller p ε = 1 + nu p O ε * xi p O ε := by
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  linear_combination hX.1

lemma theta_nu : fontaineTheta O p (nu p O ε) ≠ 0 := by
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  rw [hX.2.1]
  exact sub_ne_zero.2 (hε.ne_one hp.out.one_lt)

lemma untilt_eps : ε.untilt = 1 := by
  have he : ε = ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ p := by
    rw [← frobenius_def, ← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  rw [he, map_pow, hε.pow_eq_one]

end Ainf

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.DiscriminantColengthStatementHolds
section
namespace ReciprocityTheory.PGsh.Up

theorem discriminantColengthStatement_holds : DiscriminantColengthStatement := by
  intro C _ _ v R _ _ _ _ n a hinj ha
  exact ⟨fun s F S hF hS => colength_sq_blockVandermonde a s F S hF hS,
    fun s M S Mτ hM hτ hS => valuation_pairwiseDifferenceProduct_pow_le_colength_sq C v n a s M S Mτ hM hτ hS,
    fun s h A F M' S Mτ hF _ hM' hτ hS => colength_sq_mul_le a hinj ha s h A F M' S Mτ hF hM' hτ hS⟩

end ReciprocityTheory.PGsh.Up
end

-- bundled from ReciprocityTheory.DualLattices.DualLenStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

def zSub {R : Type} [CommRing R] {d : ℕ} {κ : Type} [Fintype κ] (A : Matrix (Fin d) κ R) (c : R) :
    Submodule R (Fin d → R) where
  carrier := {y | ∃ z, Aᵀ *ᵥ y = c • z}
  add_mem' := by
    rintro y y' ⟨z, hz⟩ ⟨z', hz'⟩
    exact ⟨z + z', by rw [mulVec_add, hz, hz', smul_add]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a y ⟨z, hz⟩
    exact ⟨a • z, by rw [mulVec_smul, hz, smul_comm]⟩

def DualLenStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (d : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix (Fin d) κ R)
    (c : R), c ≠ 0 → (∀ w : Fin d → R, ∃ t, A *ᵥ t = c • w) →
    ∀ c₁ : NNReal, HasLen v R ((Fin d → R) ⧸ LinearMap.range A.mulVecLin) c₁ →
      ∃ y : NNReal, HasLen v R ((Fin d → R) ⧸ zSub A c) y ∧ y * c₁ = v (algebraMap R C c) ^ d

section Coord

variable {R : Type} [CommRing R] {g d : ℕ} (P : Matrix (Fin g) (Fin g) R) (hP : P * P = P)
  (φ : LinearMap.range (Matrix.mulVecLin P) ≃ₗ[R] (Fin d → R))

def matU : Matrix (Fin g) (Fin d) R := Matrix.of fun k l => ((φ.symm (Pi.single l 1)) : Fin g → R) k

def matV : Matrix (Fin d) (Fin g) R :=
  Matrix.of fun l k => φ ⟨P *ᵥ Pi.single k 1, ⟨_, rfl⟩⟩ l

lemma sum_single' {n : ℕ} (y : Fin n → R) : y = ∑ l, y l • (Pi.single l 1 : Fin n → R) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

include hP in
lemma P_fix (x : Fin g → R) (hx : x ∈ LinearMap.range (Matrix.mulVecLin P)) : P *ᵥ x = x := by
  obtain ⟨w, rfl⟩ := hx
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]

lemma matU_mulVec (y : Fin d → R) : matU P φ *ᵥ y = (φ.symm y : Fin g → R) := by
  conv_rhs => rw [sum_single' y]
  rw [map_sum]
  funext k
  simp [matU, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma matV_mulVec (w : Fin g → R) :
    matV P φ *ᵥ w = φ ⟨P *ᵥ w, ⟨_, rfl⟩⟩ := by
  have hw : (⟨P *ᵥ w, ⟨_, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin P)) =
      ∑ k, w k • (⟨P *ᵥ Pi.single k 1, ⟨_, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin P)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    conv_lhs => rw [sum_single' w]
    rw [show P *ᵥ (∑ k, w k • (Pi.single k 1 : Fin g → R)) =
        Matrix.mulVecLin P (∑ k, w k • (Pi.single k 1 : Fin g → R)) from rfl, map_sum]
    simp only [map_smul, Matrix.mulVecLin_apply]
  rw [hw, map_sum]
  simp only [LinearEquiv.map_smul]
  funext l
  simp only [Matrix.mulVec, dotProduct, matV, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

include hP in
lemma matV_matU : matV P φ * matU P φ = 1 := by
  have key : ∀ y, (matV P φ * matU P φ) *ᵥ y = y := by
    intro y
    rw [← Matrix.mulVec_mulVec, matU_mulVec, matV_mulVec]
    have e : (⟨P *ᵥ (φ.symm y : Fin g → R), ⟨_, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin P)) = φ.symm y :=
      Subtype.ext (P_fix P hP _ (φ.symm y).2)
    rw [e, LinearEquiv.apply_symm_apply]
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this

lemma matU_matV : matU P φ * matV P φ = P := by
  have key : ∀ w, (matU P φ * matV P φ) *ᵥ w = P *ᵥ w := by
    intro w
    rw [← Matrix.mulVec_mulVec, matV_mulVec, matU_mulVec, LinearEquiv.symm_apply_apply]
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

end Coord

theorem lenIdB_of (hPL : DualLenStatement) : LenIdBStatement := by
  intro C _ v R _ _ hv g m Ht Bt E cp hcp hE hform εT εL π hπ hTo hTs hLo hLs hHt hBt hadj i d hd
    c₁ hc₁
  haveI : IsDomain R := Function.Injective.isDomain _ hv.hom_inj
  obtain ⟨φ⟩ := hd
  have hP : εL i * εL i = εL i := by rw [hLo, if_pos rfl]
  set U := matU (εL i) φ with hU
  set V := matV (εL i) φ with hV
  have hVU : V * U = 1 := matV_matU (εL i) hP φ
  have hUV : U * V = εL i := matU_matV (εL i) φ
  have hHtT : (εT (π i))ᵀ * Htᵀ = Htᵀ * εL i := by
    have h := congrArg transpose (hHt (π i))
    rw [hπ i, transpose_mul, transpose_mul, transpose_transpose] at h
    exact h
  set A : Matrix (Fin d) (Ix g) R := Uᵀ * Ht * εT (π i) with hA
  have hmemT : ∀ w, Vᵀ *ᵥ w ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) := by
    intro w
    refine ⟨Vᵀ *ᵥ w, ?_⟩
    show (εL i)ᵀ *ᵥ (Vᵀ *ᵥ w) = Vᵀ *ᵥ w
    rw [mulVec_mulVec, ← transpose_mul, ← hUV, ← Matrix.mul_assoc, hVU, Matrix.one_mul]
  have hfixT : ∀ f ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ), (εL i)ᵀ *ᵥ f = f := by
    rintro f ⟨z, rfl⟩
    show (εL i)ᵀ *ᵥ ((εL i)ᵀ *ᵥ z) = (εL i)ᵀ *ᵥ z
    rw [mulVec_mulVec, ← transpose_mul, hP]
  let ψ : LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) ≃ₗ[R] (Fin d → R) :=
    { toFun := fun f => Uᵀ *ᵥ (f : Fin g → R)
      invFun := fun y => ⟨Vᵀ *ᵥ y, hmemT y⟩
      map_add' := fun f f' => by simp [mulVec_add]
      map_smul' := fun a f => by simp [mulVec_smul]
      left_inv := fun f => by
        apply Subtype.ext
        show Vᵀ *ᵥ (Uᵀ *ᵥ (f : Fin g → R)) = f
        rw [mulVec_mulVec, ← transpose_mul, hUV, hfixT f f.2]
      right_inv := fun y => by
        show Uᵀ *ᵥ (Vᵀ *ᵥ y) = y
        rw [mulVec_mulVec, ← transpose_mul, hVU, transpose_one, one_mulVec] }
  have hmapC : (((LinearMap.range (Matrix.mulVecLin (εT (π i)))).map (Matrix.mulVecLin Ht)).comap
      (LinearMap.range (Matrix.mulVecLin (εL i)ᵀ)).subtype).map
        (ψ : LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) →ₗ[R] (Fin d → R)) =
      LinearMap.range A.mulVecLin := by
    ext y
    constructor
    · rintro ⟨f, ⟨_, ⟨t, rfl⟩, hft⟩, rfl⟩
      refine ⟨t, ?_⟩
      show A *ᵥ t = Uᵀ *ᵥ (f : Fin g → R)
      have hft' : Ht *ᵥ (εT (π i) *ᵥ t) = (f : Fin g → R) := hft
      rw [← hft']
      show A *ᵥ t = Uᵀ *ᵥ (Ht *ᵥ (εT (π i) *ᵥ t))
      rw [hA, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    · rintro ⟨t, rfl⟩
      have hmem : Ht *ᵥ (εT (π i) *ᵥ t) ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) := by
        refine ⟨Ht *ᵥ t, ?_⟩
        show (εL i)ᵀ *ᵥ (Ht *ᵥ t) = Ht *ᵥ (εT (π i) *ᵥ t)
        rw [mulVec_mulVec, mulVec_mulVec, hHt (π i), hπ i]
      refine ⟨⟨_, hmem⟩, ⟨_, ⟨t, rfl⟩, rfl⟩, ?_⟩
      show Uᵀ *ᵥ (Ht *ᵥ (εT (π i) *ᵥ t)) = A *ᵥ t
      rw [hA, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hcA : HasLen v R ((Fin d → R) ⧸ LinearMap.range A.mulVecLin) c₁ :=
    hasLen_of_equiv (Submodule.Quotient.equiv _ _ ψ hmapC).symm hc₁
  have hkill : ∀ w : Fin d → R, ∃ t, A *ᵥ t = cp • w := by
    intro w
    obtain ⟨t, ht⟩ := cok_kill hcp hE hform εT εL π i (hπ i) hHt _ (hmemT w)
    refine ⟨t, ?_⟩
    rw [hA, ← mulVec_mulVec, ← mulVec_mulVec, ht, mulVec_smul, mulVec_mulVec, ← transpose_mul,
      hVU, transpose_one, one_mulVec]
  obtain ⟨y, hy, hyc⟩ := hPL C v R hv d (Ix g) A cp hcp hkill c₁ hcA
  have hmapY : ((sxE Ht Bt εT εL π i).comap (inclE εL i (π i))).map
      (φ : LinearMap.range (Matrix.mulVecLin (εL i)) →ₗ[R] (Fin d → R)) = zSub A cp := by
    have key : ∀ x : LinearMap.range (Matrix.mulVecLin (εL i)),
        x ∈ (sxE Ht Bt εT εL π i).comap (inclE εL i (π i)) ↔ φ x ∈ zSub A cp := by
      intro x
      have hx : εL i *ᵥ (x : Fin g → R) = x := P_fix (εL i) hP _ x.2
      have hAx : Aᵀ *ᵥ φ x = Htᵀ *ᵥ (x : Fin g → R) := by
        have hAT : Aᵀ = (εT (π i))ᵀ * Htᵀ * U := by
          rw [hA, transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc]
        rw [hAT, hHtT, ← mulVec_mulVec, ← mulVec_mulVec, matU_mulVec, LinearEquiv.symm_apply_apply,
          hx]
      rw [Submodule.mem_comap]
      show (∃ s, s ∈ LinearMap.range (Matrix.mulVecLin (εT i)) ∧
          fromRows Ht Bt *ᵥ s = Sum.elim (0 : Fin g → R) (x : Fin g → R)) ↔ ∃ z, Aᵀ *ᵥ φ x = cp • z
      rw [hAx, ← exists_fromRows_mulVec_iff hcp hE hform εT εL π i (hHt i) (hBt i) _ hx]
      constructor
      · rintro ⟨_, ⟨t, rfl⟩, h⟩; exact ⟨t, h⟩
      · rintro ⟨t, h⟩; exact ⟨_, ⟨t, rfl⟩, h⟩
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (key x).1 hx
    · intro hz
      refine ⟨φ.symm z, (key _).2 (by rwa [LinearEquiv.apply_symm_apply]), ?_⟩
      exact LinearEquiv.apply_symm_apply φ z
  exact ⟨y, hasLen_of_equiv (Submodule.Quotient.equiv _ _ φ hmapY) hy, hyc⟩

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.EigenQuotientSmithStatement
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def EigenQuotientSmithStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (r : ℕ) (Bw : Matrix (Ix g) (Fin r) ℤ_[p]),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ (e w))) →
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ →
    ∀ X : NNReal, HasLen v R (xMod H e π w) X →
    ∃ (Λ : Matrix (Fin r) (Fin r) R) (dj : Fin r → R), IsUnit Λ.det ∧
      (∀ j, dj j • Λ j ∈ Submodule.span R (Set.range fun k : Fin g ⊕ Fin g =>
        fun i : Fin r => (phiP H e * Bw.map (algebraMap ℤ_[p] R)) k i)) ∧
      (∀ j, v (algebraMap R C cp) ≤ v (algebraMap R C (dj j))) ∧
      X = ∏ j, v (algebraMap R C (dj j))

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.LiftMonomialDeterminantStatementHolds
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

def uR (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (y : Nb p g) : R :=
  (hv.exists_of_le_one (D.u_int j y)).choose

theorem uR_spec (hv : v.Integers R) (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    algebraMap R C (uR hv D j y) = D.u j y :=
  (hv.exists_of_le_one (D.u_int j y)).choose_spec

def MuR (hv : v.Integers R) (D : Lifts H U X) : Matrix (Nb p g) (Nb p g) R :=
  Matrix.of fun y α => ∏ j, uR hv D j y ^ (α j).val

theorem det_map' {S : Type} [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) : (M.map f).det = f M.det := by
  exact (f.map_det M).symm

theorem mem_max_of_lt (hv : v.Integers R) [IsLocalRing R] {x : R} (hx : v (algebraMap R C x) < 1) :
    x ∈ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  rw [hv.isUnit_iff_valuation_eq_one.mp hu] at hx
  exact lt_irrefl _ hx

theorem residue_p (hv : v.Integers R) [IsLocalRing R] (hp1 : v (algebraMap R C (p : R)) < 1) :
    ((p : ℕ) : IsLocalRing.ResidueField R) = 0 := by
  rw [← map_natCast (IsLocalRing.residue R) p, IsLocalRing.residue_eq_zero_iff]
  exact mem_max_of_lt hv hp1

theorem residue_uR (hv : v.Integers R) [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (D : Lifts H U X) (j : Ix g) (y : Nb p g) :
    IsLocalRing.residue R (uR hv D j y) = lam (D.Λ.map (IsLocalRing.residue R)) j y := by
  have h := D.u_cong j y
  rw [← uR_spec hv D j y, ← map_sub] at h
  have hm := mem_max_of_lt hv h
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
  rw [hm, lam]
  simp only [map_sum, map_mul, map_natCast, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [xc, ZMod.castHom_apply, ZMod.natCast_val]

theorem isUnit_det_MuR (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1)
    (D : Lifts H U X) : IsUnit (MuR hv D).det := by
  haveI : Nontrivial R := (algebraMap R C).domain_nontrivial
  have hlt : ∀ x : R, x ∈ nonunits R → v (algebraMap R C x) < 1 := fun x hx =>
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_iff_valuation_eq_one.mpr h)
  letI : IsLocalRing R := IsLocalRing.of_nonunits_add fun a b ha hb hu => by
    have h1 := hv.isUnit_iff_valuation_eq_one.mp hu
    have h2 : v (algebraMap R C (a + b)) < 1 := by
      rw [map_add]; exact v.map_add_lt (hlt a ha) (hlt b hb)
    rw [h1] at h2
    exact lt_irrefl _ h2
  haveI : CharP (IsLocalRing.ResidueField R) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).mpr (residue_p hv hp1)
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hM : (IsLocalRing.residue R).mapMatrix (MuR hv D) =
      Matrix.of fun (x α : Nb p g) => monF (p := p) (D.Λ.map (IsLocalRing.residue R)) α x := by
    ext y α
    simp [MuR, monF, residue_uR hv D]
  rw [hM]
  refine det_monF_ne_zero _ ?_
  rw [det_map']
  exact D.Λ_det.map _

theorem valM_eq (hv : v.Integers R) (D : Lifts H U X) :
    valM D = (MuR hv D).map (algebraMap R C) *
      Matrix.diagonal fun α : Nb p g => algebraMap R C (∏ j, D.ε j ^ (α j).val) := by
  ext y α
  simp only [valM, monX, xL, MuR, Matrix.of_apply, Matrix.mul_diagonal, Matrix.map_apply,
    map_prod, map_pow, uR_spec, mul_pow, Finset.prod_mul_distrib]
  ring

theorem det_valM_ne (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1) (D : Lifts H U X) :
    (valM D).det ≠ 0 := by
  rw [valM_eq hv D, Matrix.det_mul, det_map', Matrix.det_diagonal]
  refine mul_ne_zero ((isUnit_det_MuR hv hp1 D).map (algebraMap R C)).ne_zero ?_
  refine Finset.prod_ne_zero_iff.mpr fun α _ => ?_
  rw [map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  rw [map_pow]
  exact pow_ne_zero _ ((map_ne_zero_iff _ hv.hom_inj).mpr (D.ε_ne j))

end ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix

namespace ReciprocityTheory.PGsh.Up

theorem liftMonomialDeterminantStatement_holds : LiftMonomialDeterminantStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H U X D
  exact FrobeniusValuationMatrix.det_valM_ne hS.integers hS.p_lt D

end ReciprocityTheory.PGsh.Up
end
end

