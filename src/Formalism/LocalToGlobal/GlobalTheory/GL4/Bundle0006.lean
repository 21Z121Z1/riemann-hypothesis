import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0005
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.XiNorm
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.InitMinorIdEqLpMinor
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility

theorem hw_add_const (R : Type) [CommRing R] {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) :
    hw R (r := m + 1) (n := m + 1) le_rfl (fun s => ν s + c) =
      hw R (r := m + 1) (n := m + 1) le_rfl ν * lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c := by
  unfold hw
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]
  congr 1
  · apply Finset.prod_congr rfl
    intro s _
    congr 1
    unfold nuNext
    have h : (s.castSucc : Fin (m + 1)).val + 1 < m + 1 := by simp only [Fin.val_castSucc]; omega
    rw [dif_pos h, dif_pos h]
    dsimp only
    omega
  · have h : ¬ ((Fin.last m : Fin (m + 1)).val + 1 < m + 1) := by simp
    unfold nuNext
    rw [dif_neg h, dif_neg h]
    dsimp only
    rw [Nat.sub_zero, Nat.sub_zero, pow_add]
    rfl

theorem rowGen_det (R : Type) [CommRing R] {m : ℕ} (a b : Fin m) (hab : a ≠ b) :
    rowGen R a b (lpMinor R (r := m) (n := m) m le_rfl le_rfl) =
      Polynomial.C (lpMinor R (r := m) (n := m) m le_rfl le_rfl) := by
  unfold lpMinor
  set M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) R) :=
    Matrix.of fun p q : Fin m => X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) with hMdef
  rw [AlgHom.map_det, RingHom.map_det]
  have hM : (rowGen R a b).mapMatrix M =
      Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) b
        (((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) b +
          (Polynomial.X : Polynomial (MvPolynomial (Fin m × Fin m) R)) •
            ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a) := by
    ext p q
    by_cases hp : p = b
    · subst hp
      simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl]
      try ring
    · simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl, hp]
  rw [hM, Matrix.det_updateRow_add_smul_self _ (Ne.symm hab)]

theorem rowDiv_det_mul (R : Type) [CommRing R] {m : ℕ} (a b : Fin m) (hab : a ≠ b) (k c : ℕ)
    (f : MvPolynomial (Fin m × Fin m) R) :
    rowDiv R a b k (lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * f) =
      lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * rowDiv R a b k f := by
  unfold rowDiv
  rw [map_mul, map_pow, rowGen_det R a b hab, ← Polynomial.C_pow, Polynomial.coeff_C_mul]

theorem rowGen_det_self (R : Type) [CommRing R] {m : ℕ} (a : Fin m) :
    rowGen R a a (lpMinor R (r := m) (n := m) m le_rfl le_rfl) =
      (1 + Polynomial.X) * Polynomial.C (lpMinor R (r := m) (n := m) m le_rfl le_rfl) := by
  unfold lpMinor
  set M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m × Fin m) R) :=
    Matrix.of fun p q : Fin m => X (Fin.castLE le_rfl p, Fin.castLE le_rfl q) with hMdef
  rw [AlgHom.map_det, RingHom.map_det]
  have hM : (rowGen R a a).mapMatrix M =
      Matrix.updateRow ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a
        ((1 + Polynomial.X : Polynomial (MvPolynomial (Fin m × Fin m) R)) •
            ((Polynomial.C : MvPolynomial (Fin m × Fin m) R →+* _).mapMatrix M) a) := by
    refine Matrix.ext fun p q => ?_
    by_cases hp : p = a
    · subst hp
      simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl]
      try ring
    · simp [hMdef, Matrix.updateRow_apply, rowGen, Fin.castLE_refl, hp]
  rw [hM, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

theorem rowDiv_det_mul_self (R : Type) [CommRing R] {m : ℕ} (a : Fin m) (k c : ℕ)
    (f : MvPolynomial (Fin m × Fin m) R) :
    rowDiv R a a k (lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c * f) =
      lpMinor R (r := m) (n := m) m le_rfl le_rfl ^ c *
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, ((c.choose p.1 : ℕ) : MvPolynomial (Fin m × Fin m) R) * rowDiv R a a p.2 f := by
  unfold rowDiv
  rw [map_mul, map_pow, rowGen_det_self, mul_pow, ← Polynomial.C_pow, mul_comm ((1 + Polynomial.X) ^ c) _,
    mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [add_comm (1 : Polynomial (MvPolynomial (Fin m × Fin m) R)), Polynomial.coeff_X_add_one_pow]

theorem rowDiv_add (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f + g) = rowDiv R a b k f + rowDiv R a b k g := by
  unfold rowDiv
  rw [map_add, Polynomial.coeff_add]

theorem rowDiv_smul (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (t : R) (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (t • f) = t • rowDiv R a b k f := by
  unfold rowDiv
  rw [map_smul, Polynomial.coeff_smul]

theorem rowDiv_zero (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) :
    rowDiv R a b k (0 : MvPolynomial (Fin r × Fin n) R) = 0 := by
  unfold rowDiv
  rw [map_zero, Polynomial.coeff_zero]

theorem rowDiv_mem_weyl (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ weyl R r n hn ν) : rowDiv R a b k f ∈ weyl R r n hn ν := by
  unfold weyl at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  | zero => rw [rowDiv_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [rowDiv_add]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [rowDiv_smul]; exact Submodule.smul_mem _ t hx

theorem det_mul_mem_weyl (R : Type) [CommRing R] {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ)
    (g : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) (hg : g ∈ weyl R (m + 1) (m + 1) le_rfl ν) :
    lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * g ∈
      weyl R (m + 1) (m + 1) le_rfl (fun s => ν s + c) := by
  set D := lpMinor R (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c with hD
  set W' := weyl R (m + 1) (m + 1) le_rfl (fun s => ν s + c) with hW'
  have key : ∀ w : List (Fin (m + 1) × Fin (m + 1) × ℕ), D * applyWord R w (hw R le_rfl ν) ∈ W' := by
    intro w
    induction w with
    | nil =>
      simp only [applyWord, List.foldr_nil]
      rw [hD, mul_comm, ← hw_add_const]
      exact Submodule.subset_span ⟨[], rfl⟩
    | cons x w ih =>
      obtain ⟨a, b, k⟩ := x
      show D * rowDiv R a b k (applyWord R w (hw R le_rfl ν)) ∈ W'
      set g := applyWord R w (hw R le_rfl ν)
      by_cases hab : a = b
      · subst hab
        induction k using Nat.strong_induction_on with
        | _ k ihk =>
          have h1 := rowDiv_det_mul_self R a k c g
          have hmem : ((0 : ℕ), k) ∈ Finset.HasAntidiagonal.antidiagonal k := by simp
          rw [← Finset.add_sum_erase _ _ hmem] at h1
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at h1
          have h2 : D * rowDiv R a a k g = rowDiv R a a k (D * g) -
              ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal k).erase (0, k),
                D * (((c.choose p.1 : ℕ) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) * rowDiv R a a p.2 g) := by
            rw [hD, h1, mul_add, Finset.mul_sum]
            ring
          rw [h2]
          refine Submodule.sub_mem _ (rowDiv_mem_weyl R le_rfl _ a a k _ ih) ?_
          refine Submodule.sum_mem _ fun p hp => ?_
          have hp2 : p.2 < k := by
            rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
            have hne : p.1 ≠ 0 := fun h => hp.1 (Prod.ext h (by simp; omega))
            omega
          rw [mul_left_comm, ← nsmul_eq_mul]
          exact Submodule.smul_of_tower_mem _ _ (ihk p.2 hp2)
      · rw [← rowDiv_det_mul R a b hab]
        exact rowDiv_mem_weyl R le_rfl _ a b k _ ih
  unfold weyl at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact key w
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul t x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ t hx

theorem initMinor_id_eq_lpMinor (R : Type) [CommRing R] (m : ℕ) :
    initMinor R (r := m) (n := m) (s := m) id le_rfl = lpMinor R (r := m) (n := m) m le_rfl le_rfl := by
  unfold initMinor lpMinor
  congr 1

theorem xnN_det_mul {m : ℕ} (ν : Fin (m + 1) → ℕ) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℂ)
    (hf : f ∈ dualWeyl ℂ (m + 1) (m + 1) ν) :
    Formalism.BranchingDeterminantCap.xnN (lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl * f) =
      Formalism.BranchingDeterminantCap.xnC (m + 1) (Formalism.BranchingDeterminantCap.xnLam ν) (m + 1) * Formalism.BranchingDeterminantCap.xnN f := by
  rw [← initMinor_id_eq_lpMinor]
  apply Formalism.BranchingDeterminantCap.xn_L id Function.injective_id (Formalism.BranchingDeterminantCap.xnLam ν) f
  · intro t s hts
    exact Formalism.BranchingDeterminantCap.xn_hR hf t s hts
  · intro s
    have h := Formalism.BranchingDeterminantCap.xn_hW hf s
    have hs : Formalism.BranchingDeterminantCap.xnLam ν s.val = ν s := by
      unfold Formalism.BranchingDeterminantCap.xnLam
      rw [dif_pos s.isLt]
    rw [hs]
    exact h

theorem xnC_pos (M : ℕ) (mm : ℕ → ℕ) : 0 < Formalism.BranchingDeterminantCap.xnC M mm M := by
  unfold Formalism.BranchingDeterminantCap.xnC
  apply Finset.prod_pos
  intro q hq
  rw [Finset.mem_range] at hq
  have h1 : (q : ℝ) < M := by exact_mod_cast hq
  have h2 : (0 : ℝ) ≤ (mm q : ℝ) := Nat.cast_nonneg _
  linarith

def detConst {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) : ℝ :=
  ∏ j ∈ Finset.range c, Formalism.BranchingDeterminantCap.xnC (m + 1) (Formalism.BranchingDeterminantCap.xnLam (fun s => ν s + j)) (m + 1)

theorem detConst_pos {m : ℕ} (ν : Fin (m + 1) → ℕ) (c : ℕ) : 0 < detConst ν c :=
  Finset.prod_pos fun _ _ => xnC_pos _ _

theorem xnN_det_pow_mul {m : ℕ} (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (c : ℕ) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℂ)
    (hf : f ∈ weyl ℂ (m + 1) (m + 1) le_rfl ν) :
    Formalism.BranchingDeterminantCap.xnN (lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * f) = detConst ν c * Formalism.BranchingDeterminantCap.xnN f := by
  induction c with
  | zero => simp [detConst]
  | succ c ih =>
    have hmem : lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * f ∈
        dualWeyl ℂ (m + 1) (m + 1) (fun s => ν s + c) :=
      Formalism.GradedWeylDivisibility.weylLeDual ℂ (m + 1) (m + 1) le_rfl _ (fun a b h => Nat.add_le_add_right (hν h) c) (det_mul_mem_weyl ℂ ν c f hf)
    rw [pow_succ', mul_assoc, xnN_det_mul _ _ hmem, ih, detConst, detConst, Finset.prod_range_succ]
    ring

theorem fockF_self_eq {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f = ((Formalism.BranchingDeterminantCap.xnN f : ℝ) : ℂ) := by
  unfold Formalism.BranchingDeterminantCap.xnN
  rw [Formalism.GradedWeylDivisibility.LFockb_fockF_self, Complex.ofReal_re]

theorem fock_ratio_det_pow {m : ℕ} (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (c : ℕ) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) ℂ)
    (hf : f ∈ weyl ℂ (m + 1) (m + 1) le_rfl ν) :
    Formalism.REAL.fockF (lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * f)
              (lpMinor ℂ (r := m + 1) (n := m + 1) (m + 1) le_rfl le_rfl ^ c * f) /
      Formalism.REAL.fockF (hw ℂ le_rfl (fun s => ν s + c)) (hw ℂ le_rfl (fun s => ν s + c)) =
    Formalism.REAL.fockF f f / Formalism.REAL.fockF (hw ℂ le_rfl ν) (hw ℂ le_rfl ν) := by
  have hhw : hw ℂ le_rfl ν ∈ weyl ℂ (m + 1) (m + 1) le_rfl ν := Submodule.subset_span ⟨[], rfl⟩
  rw [hw_add_const, mul_comm (hw ℂ le_rfl ν), fockF_self_eq, fockF_self_eq, fockF_self_eq, fockF_self_eq,
    xnN_det_pow_mul ν hν c f hf, xnN_det_pow_mul ν hν c _ hhw, ← Complex.ofReal_div, ← Complex.ofReal_div,
    mul_div_mul_left _ _ (detConst_pos ν c).ne']

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.PClsTieP
section
noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem star_int (a : 𝓞 E) : star (a : E) ∈ (algebraMap (𝓞 E) E).range := by
  exact ⟨RingOfIntegers.mapRingHom (starRingEnd E) a, rfl⟩

theorem dual_le_of_split (S S' : HSpace E) (ι : S'.V →ₗ[E] S.V) (hι : HSpace.IsIsomEmb S' S ι) (z0 : S.V)
    (horth : ∀ x, S.hT (ι x) z0 = 0) (T : ℕ) (hT0 : T ≠ 0) (hz0 : S.hT z0 z0 = (T : E))
    (γ : S.V ≃ₗ[E] S.V) (hγ : ∀ x y, S.hT (γ x) (γ y) = S.hT x y)
    (L : Submodule (𝓞 E) S.V) (hint : L ≤ Formalism.HermitianLatticesTheory.dual S.hT L)
    (hidx : L.toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual S.hT L).toAddSubgroup = T ^ Module.finrank ℚ E)
    (L' : Submodule (𝓞 E) S'.V)
    (htil : Formalism.HermitianLatticesTheory.gmap γ L = L'.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0}) :
    Formalism.HermitianLatticesTheory.dual S'.hT L' ≤ L' := by
  have hTE : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT0
  have horth' : ∀ x, S.hT z0 (ι x) = 0 := by
    intro x
    have := S.herm.eq (ι x) z0
    rw [horth, map_zero] at this
    exact this.symm

  have huniq : ∀ (v : S'.V) (t : E), ι v + t • z0 = 0 → v = 0 ∧ t = 0 := by
    intro v t h
    have h1 : S.hT z0 (ι v + t • z0) = 0 := by rw [h, map_zero]
    rw [map_add, map_smul, horth', hz0, smul_eq_mul, zero_add, mul_eq_zero] at h1
    have ht : t = 0 := h1.resolve_right hTE
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at h
    apply S'.nondeg.2 v
    intro x
    rw [← hι, h, map_zero]

  have hdec : ∀ l ∈ L, ∃ l' ∈ L', ∃ a : 𝓞 E, γ l = ι l' + (a : E) • z0 := by
    intro l hl
    have : γ l ∈ Formalism.HermitianLatticesTheory.gmap γ L := ⟨l, hl, rfl⟩
    rw [htil, Submodule.mem_sup] at this
    obtain ⟨y, ⟨l', hl', rfl⟩, w, hw, hsum⟩ := this
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨l', hl', a, by rw [← hsum, algebraMap_smul]; rfl⟩
  have hcomp : ∀ (l' : S'.V), l' ∈ L' → ∀ a : 𝓞 E, γ.symm (ι l' + (a : E) • z0) ∈ L := by
    intro l' hl' a
    have : ι l' + (a : E) • z0 ∈ Formalism.HermitianLatticesTheory.gmap γ L := by
      rw [htil]
      refine Submodule.add_mem_sup ⟨l', hl', rfl⟩ ?_
      exact Submodule.mem_span_singleton.2 ⟨a, (algebraMap_smul E a z0).symm⟩
    obtain ⟨l, hl, he⟩ := this
    have : l = γ.symm (ι l' + (a : E) • z0) := by rw [← he]; simp
    rw [← this]; exact hl
  have hpair : ∀ (v : S'.V) (a t : E), S.hT (ι v + a • z0) (t • z0) = star a * t * (T : E) := by
    intro v a t
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, map_smul, horth, hz0, smul_eq_mul,
      starRingEnd_apply, zero_add]
    ring
  have hpair2 : ∀ (v x : S'.V) (a : E), S.hT (ι v + a • z0) (ι x) = S'.hT v x := by
    intro v x a
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ₂, horth', smul_zero, add_zero]
    exact hι v x
  set q : S.V := γ.symm ((T : E)⁻¹ • z0) with hq
  have hγq : γ q = (T : E)⁻¹ • z0 := by simp [hq]

  have hqd : q ∈ Formalism.HermitianLatticesTheory.dual S.hT L := by
    rw [Formalism.L2.Herm.mem_dual]
    intro l hl
    obtain ⟨l', _, a, ha⟩ := hdec l hl
    rw [← hγ, ha, hγq, hpair, mul_assoc, inv_mul_cancel₀ hTE, mul_one]
    exact star_int a
  set Q : Submodule (𝓞 E) S.V := L ⊔ Submodule.span (𝓞 E) {q} with hQ
  have hLQ : L ≤ Q := le_sup_left
  have hQd : Q ≤ Formalism.HermitianLatticesTheory.dual S.hT L :=
    sup_le hint ((Submodule.span_singleton_le_iff_mem _ _).2 hqd)

  let φ : 𝓞 E →+ S.V := (LinearMap.toSpanSingleton (𝓞 E) S.V q).toAddMonoidHom
  have hrange : (Submodule.span (𝓞 E) {q}).toAddSubgroup = φ.range := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, AddMonoidHom.mem_range, φ,
      LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply]
  have hcomap : L.toAddSubgroup.comap φ = (Ideal.span {((T : ℕ) : 𝓞 E)}).toAddSubgroup := by
    ext a
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, φ, LinearMap.toAddMonoidHom_coe,
      LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton]
    constructor
    · intro h
      obtain ⟨l', _, b, hb⟩ := hdec _ h
      rw [← algebraMap_smul E a q, map_smul, hγq, smul_smul] at hb
      have h2 := huniq (-l') ((a : E) * (T : E)⁻¹ - (b : E)) (by
        rw [map_neg, sub_smul, hb]; abel)
      have h3 : (a : E) = (T : E) * (b : E) := by
        have := h2.2
        field_simp at this
        linear_combination this
      refine ⟨b, ?_⟩
      apply RingOfIntegers.coe_injective
      push_cast
      exact h3
    · rintro ⟨b, rfl⟩
      convert hcomp 0 (zero_mem _) b using 1
      have e1 : algebraMap (𝓞 E) E (((T : ℕ) : 𝓞 E) * b) = (T : E) * (b : E) := by simp
      rw [map_zero, zero_add, hq, ← algebraMap_smul E (((T : ℕ) : 𝓞 E) * b), e1, ← LinearEquiv.map_smul, smul_smul]
      congr 2
      field_simp
  have hLQi : L.toAddSubgroup.relIndex Q.toAddSubgroup = T ^ Module.finrank ℚ E := by
    rw [hQ, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left, hrange, ← AddSubgroup.index_comap,
      hcomap, ← card_quot_nat E T]
    rfl
  have hQi : Q.toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual S.hT L).toAddSubgroup = 1 := by
    have h := AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hLQ)
      (Submodule.toAddSubgroup_mono hQd)
    rw [hLQi, hidx] at h
    have hp : 0 < T ^ Module.finrank ℚ E := pow_pos (Nat.pos_of_ne_zero hT0) _
    exact (Nat.mul_eq_left hp.ne').1 h
  have hdQ : Formalism.HermitianLatticesTheory.dual S.hT L ≤ Q :=
    (Submodule.toAddSubgroup_le _ _).1 (AddSubgroup.relIndex_eq_one.1 hQi)

  intro x hx
  have hw : γ.symm (ι x) ∈ Formalism.HermitianLatticesTheory.dual S.hT L := by
    rw [Formalism.L2.Herm.mem_dual]
    intro l hl
    obtain ⟨l', hl', a, ha⟩ := hdec l hl
    rw [← hγ, ha, LinearEquiv.apply_symm_apply, hpair2]
    exact (Formalism.L2.Herm.mem_dual S' L' x).1 hx l' hl'
  obtain ⟨l, hl, r, hr, hsum⟩ := Submodule.mem_sup.1 (hdQ hw)
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hr
  obtain ⟨l', hl', a, ha⟩ := hdec l hl
  have he : ι x = ι l' + (a : E) • z0 + (b : E) • ((T : E)⁻¹ • z0) := by
    have := congrArg γ hsum
    rw [LinearEquiv.apply_symm_apply, map_add, ha, ← algebraMap_smul E b q, map_smul, hγq] at this
    exact this.symm
  have h2 := huniq (x - l') (-((a : E) + (b : E) * (T : E)⁻¹)) (by
    rw [map_sub, he, neg_smul, add_smul, smul_smul]; abel)
  have : x = l' := sub_eq_zero.1 h2.1
  rw [this]; exact hl'

theorem span_top_of_split (S S' : HSpace E) (ι : S'.V →ₗ[E] S.V) (hι : HSpace.IsIsomEmb S' S ι) (z0 : S.V)
    (horth : ∀ x, S.hT (ι x) z0 = 0) (T : ℕ) (hT0 : T ≠ 0) (hz0 : S.hT z0 z0 = (T : E))
    (γ : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) (hspan : Submodule.span E (L : Set S.V) = ⊤)
    (L' : Submodule (𝓞 E) S'.V)
    (htil : Formalism.HermitianLatticesTheory.gmap γ L = L'.map (ι.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {z0}) :
    Submodule.span E (L' : Set S'.V) = ⊤ := by
  have hTE : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT0
  have horth' : ∀ x, S.hT z0 (ι x) = 0 := by
    intro x
    have := S.herm.eq (ι x) z0
    rw [horth, map_zero] at this
    exact this.symm
  have huniq : ∀ (v : S'.V) (t : E), ι v + t • z0 = 0 → v = 0 ∧ t = 0 := by
    intro v t h
    have h1 : S.hT z0 (ι v + t • z0) = 0 := by rw [h, map_zero]
    rw [map_add, map_smul, horth', hz0, smul_eq_mul, zero_add, mul_eq_zero] at h1
    have ht : t = 0 := h1.resolve_right hTE
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at h
    apply S'.nondeg.2 v
    intro x
    rw [← hι, h, map_zero]
  have key : ∀ w ∈ Submodule.span E ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V),
      ∃ y ∈ Submodule.span E (L' : Set S'.V), ∃ t : E, w = ι y + t • z0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      rw [htil, SetLike.mem_coe, Submodule.mem_sup] at hw
      obtain ⟨y, ⟨l', hl', rfl⟩, w', hw', rfl⟩ := hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw'
      exact ⟨l', Submodule.subset_span hl', (a : E), by rw [← algebraMap_smul E a z0]; rfl⟩
    | zero => exact ⟨0, zero_mem _, 0, by simp⟩
    | add w w' _ _ h h' =>
      obtain ⟨y, hy, t, rfl⟩ := h
      obtain ⟨y', hy', t', rfl⟩ := h'
      exact ⟨y + y', add_mem hy hy', t + t', by rw [map_add, add_smul]; abel⟩
    | smul e w _ h =>
      obtain ⟨y, hy, t, rfl⟩ := h
      exact ⟨e • y, Submodule.smul_mem _ e hy, e * t, by rw [smul_add, map_smul, smul_smul]⟩
  have htop : Submodule.span E ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V) = ⊤ := by
    have : ((Formalism.HermitianLatticesTheory.gmap γ L : Submodule (𝓞 E) S.V) : Set S.V) = γ '' (L : Set S.V) := by
      ext x; simp [Formalism.HermitianLatticesTheory.gmap]
    rw [this]
    show Submodule.span E ((γ : S.V →ₗ[E] S.V) '' (L : Set S.V)) = ⊤
    rw [Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact γ.surjective
  rw [eq_top_iff]
  intro v _
  obtain ⟨y, hy, t, he⟩ := key (ι v) (by rw [htop]; exact Submodule.mem_top)
  have h2 := huniq (v - y) (-t) (by rw [map_sub, he, neg_smul]; abel)
  rw [show v = y from sub_eq_zero.1 h2.1]; exact hy

end General

open Formalism.L2.Herm in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem localLattice_selfDual {D : D7} (X : FullTied D) (u : D.what₂.Word) (c : (D.fm u).clsP) :
    Submodule.IsLattice D.host.E ((X.atT u).lattice₂ c) ∧ Formalism.MainNotions.flipTwoThree.LatT D.sp.X' 1 ((X.atT u).lattice₂ c) := by
  have hT0 : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have horth : ∀ x, (D.sp.X D.R.m).hT (D.sp.iX' x) (X.atT u).z0 = 0 := by
    intro x
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (X.atT u).cocycle_zero_mem_invariants
    rw [← ht, map_smul, D.sp.z_orth, smul_zero]
  set L := D.clsLat u D.R.m ((D.fm u).til c)
  have hint : L ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X D.R.m).hT L := by
    intro x hx
    have := clsLat_int X u D.R.m le_rfl _ x hx
    rw [dualSub_eq] at this
    exact this
  have hidx : L.toAddSubgroup.relIndex (Formalism.HermitianLatticesTheory.dual (D.sp.X D.R.m).hT L).toAddSubgroup =
      (D.mem u).A.T ^ Module.finrank ℚ D.host.E := by
    have := clsLat_index X u D.R.m le_rfl ((D.fm u).til c)
    rw [dualSub_eq] at this
    rw [this, finrank_E]; rfl
  have htil := ((X.atT u).til_tie c).1
  have hle := dual_le_of_split (D.sp.X D.R.m) D.sp.X' D.sp.iX' D.sp.iX'_isom (X.atT u).z0 horth
    (D.mem u).A.T hT0 (X.atT u).hermitianForm_lastCoordinateUniformizerVector_self ((X.atT u).tilG c).1 ((X.atT u).tilG c).2 L hint hidx _ htil
  have hsp := span_top_of_split (D.sp.X D.R.m) D.sp.X' D.sp.iX' D.sp.iX'_isom (X.atT u).z0 horth
    (D.mem u).A.T hT0 (X.atT u).hermitianForm_lastCoordinateUniformizerVector_self ((X.atT u).tilG c).1 L (D.clsLat_lat u D.R.m _).span_eq_top _ htil
  refine ⟨⟨?_, hsp⟩, clsLatP_int X u c, ?_⟩
  ·
    have hfgM : (Formalism.HermitianLatticesTheory.gmap ((X.atT u).tilG c).1 L).FG := (D.clsLat_lat u D.R.m _).fg.map _
    have hle' : ((X.atT u).lattice₂ c).map (D.sp.iX'.restrictScalars (𝓞 D.host.E)) ≤
        Formalism.HermitianLatticesTheory.gmap ((X.atT u).tilG c).1 L := by rw [htil]; exact le_sup_left
    have hn : IsNoetherian (𝓞 D.host.E) (Formalism.HermitianLatticesTheory.gmap ((X.atT u).tilG c).1 L) :=
      isNoetherian_of_fg_of_noetherian _ hfgM
    have hfg := isNoetherian_submodule.1 hn _ hle'
    refine Submodule.fg_of_fg_map_injective _ ?_ hfg
    intro a b hab
    have h0 : D.sp.iX' (a - b) = 0 := by rw [map_sub]; exact sub_eq_zero.2 hab
    refine sub_eq_zero.1 (D.sp.X'.nondeg.2 _ fun x => ?_)
    rw [← D.sp.iX'_isom, h0, map_zero]
  · rw [dualSub_eq]
    exact AddSubgroup.relIndex_eq_one.2 ((Submodule.toAddSubgroup_le _ _).2 hle)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

