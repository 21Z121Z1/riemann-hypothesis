import Mathlib

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus
section
open IsLocalRing MvPolynomial

namespace UpperTheory.V.AlgebraTools

variable {P : Type} [CommRing P] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem isPrime_map_C (p : Ideal P) [p.IsPrime] :
    (p.map (C : P →+* MvPolynomial ι P)).IsPrime := by
  have he : p.map (C : P →+* MvPolynomial ι P) =
      RingHom.ker (MvPolynomial.map (σ := ι) (Ideal.Quotient.mk p)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rw [he]
  exact RingHom.ker_isPrime _

def relIdeal (z : Matrix ι ι P) (m : ι → P) : Ideal P := Ideal.span (Set.range (z.mulVec m))

def detIdeal (z : Matrix ι ι P) (m : ι → P) : Ideal P := relIdeal z m ⊔ Ideal.span {z.det}

noncomputable def lam (P : Type) [CommRing P] (c : ι) (j : ι) : MvPolynomial ι P :=
  if j = c then 1 else X j

noncomputable def chartGen (z : Matrix ι ι P) (m : ι → P) (c : ι) :
    ι ⊕ {j : ι // j ≠ c} → MvPolynomial ι P :=
  Sum.elim ((z.map C).mulVec (lam P c)) (fun j => C (m j.1) - lam P c j.1 * C (m c))

noncomputable def chartIdeal (z : Matrix ι ι P) (m : ι → P) (c : ι) : Ideal (MvPolynomial ι P) :=
  Ideal.span (Set.range (chartGen z m c))

noncomputable def genKer [IsLocalRing P] (z : Matrix ι ι P) (m : ι → P) (c : ι) : Ideal P where
  carrier := {f | ∃ s : MvPolynomial ι P, s ∉ (maximalIdeal P).map (C : P →+* MvPolynomial ι P) ∧
    s * C f ∈ chartIdeal z m c}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 (Ideal.IsPrime.ne_top (by
    have : (maximalIdeal P).IsPrime := inferInstance
    exact isPrime_map_C _)), by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs, ha⟩ ⟨t, ht, hb⟩
    have hp : ((maximalIdeal P).map (C : P →+* MvPolynomial ι P)).IsPrime :=
      isPrime_map_C _
    refine ⟨s * t, fun h => (hp.mem_or_mem h).elim hs ht, ?_⟩
    have : s * t * C (a + b) = t * (s * C a) + s * (t * C b) := by rw [map_add]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
  smul_mem' := by
    rintro r a ⟨s, hs, ha⟩
    refine ⟨s, hs, ?_⟩
    have : s * C (r • a) = C r * (s * C a) := by rw [smul_eq_mul, map_mul]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ ha

end UpperTheory.V.AlgebraTools
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DiagLocal
section
open Polynomial Matrix IsLocalRing TensorProduct

namespace UpperTheory.V.AlgebraTools

private def DGood {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι R) : Prop :=
  ∃ P : Matrix ι ι R, IsUnit P.det ∧ (Pᵀ * H * P).IsDiag

private theorem dgood_congr {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H Q : Matrix ι ι R) (hQ : IsUnit Q.det) (h : DGood (Qᵀ * H * Q)) : DGood H := by
  obtain ⟨P, hP, hD⟩ := h
  refine ⟨Q * P, by rw [det_mul]; exact hQ.mul hP, ?_⟩
  rw [transpose_mul]
  simpa only [Matrix.mul_assoc] using hD

private theorem dgood_reindex {R : Type} [CommRing R] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    (H : Matrix ι ι R) (h : DGood (H.submatrix e e)) : DGood H := by
  obtain ⟨P, hP, hD⟩ := h
  refine ⟨P.submatrix e.symm e.symm, by rw [det_submatrix_equiv_self]; exact hP, ?_⟩
  have key : (P.submatrix e.symm e.symm)ᵀ * H * P.submatrix e.symm e.symm
      = (Pᵀ * H.submatrix e e * P).submatrix e.symm e.symm := by
    rw [← submatrix_mul_equiv _ _ _ e.symm _, ← submatrix_mul_equiv _ _ _ e.symm _,
      transpose_submatrix, submatrix_submatrix]
    simp
  rw [key]
  exact hD.submatrix e.symm.injective

private theorem pivot {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι R) (h2 : IsUnit (2 : R)) (hs : Hᵀ = H) (hd : IsUnit H.det) (i : ι) :
    ∃ Q : Matrix ι ι R, IsUnit Q.det ∧ IsUnit ((Qᵀ * H * Q) i i) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (H i j) := by
    by_contra hne
    push_neg at hne
    have key : ∑ j, H i j * adjugate H j i = H.det := by
      have := congrFun (congrFun (mul_adjugate H) i) i
      simpa [Matrix.mul_apply] using this
    have hm : ∑ j, H i j * adjugate H j i ∈ maximalIdeal R :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _
        (by rw [mem_maximalIdeal, mem_nonunits_iff]; exact hne j)
    rw [key, mem_maximalIdeal, mem_nonunits_iff] at hm
    exact hm hd
  by_cases hij : j = i
  · subst hij
    exact ⟨1, by simp, by simpa using hj⟩
  · have hji : H j i = H i j := by
      have := congrFun (congrFun hs i) j
      simpa using this
    have hent : ∀ c : R, ((transvection j i c)ᵀ * H * transvection j i c) i i
        = H i i + 2 * c * H i j + c * c * H j j := by
      intro c
      simp [transvection, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, Ne.symm hij, hij, hji]
      ring
    by_cases hp : IsUnit (H i i + 2 * 1 * H i j + 1 * 1 * H j j)
    · exact ⟨transvection j i 1, by rw [det_transvection_of_ne j i hij]; exact isUnit_one,
        by rw [hent]; exact hp⟩
    · refine ⟨transvection j i (-1), by rw [det_transvection_of_ne j i hij]; exact isUnit_one, ?_⟩
      rw [hent]
      by_contra hm
      have hx : (H i i + 2 * 1 * H i j + 1 * 1 * H j j)
          - (H i i + 2 * (-1) * H i j + (-1) * (-1) * H j j) ∈ maximalIdeal R :=
        Ideal.sub_mem _ ((mem_maximalIdeal _).2 hp) ((mem_maximalIdeal _).2 hm)
      have e4 : (H i i + 2 * 1 * H i j + 1 * 1 * H j j)
          - (H i i + 2 * (-1) * H i j + (-1) * (-1) * H j j) = 2 * 2 * H i j := by ring
      rw [e4, mem_maximalIdeal, mem_nonunits_iff] at hx
      exact hx ((h2.mul h2).mul hj)

private theorem step {R : Type} [CommRing R] {κ : Type} [Fintype κ] [DecidableEq κ]
    (ih : ∀ H : Matrix κ κ R, Hᵀ = H → IsUnit H.det → DGood H)
    (H : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R) (hs : Hᵀ = H) (hd : IsUnit H.det)
    (h0 : IsUnit (H (Sum.inl ()) (Sum.inl ()))) : DGood H := by
  classical
  have hH : H = fromBlocks (H (Sum.inl ()) (Sum.inl ()) • (1 : Matrix Unit Unit R))
      H.toBlocks₁₂ H.toBlocks₁₂ᵀ H.toBlocks₂₂ := by
    ext (⟨⟩ | k) (⟨⟩ | l)
    · simp
    · simp [toBlocks₁₂]
    · have := congrFun (congrFun hs (Sum.inl ())) (Sum.inr k)
      simp only [transpose_apply] at this
      simp [toBlocks₁₂, this]
    · simp [toBlocks₂₂]
  generalize H (Sum.inl ()) (Sum.inl ()) = a at hH h0
  generalize H.toBlocks₁₂ = B at hH
  generalize H.toBlocks₂₂ = D at hH
  subst hH
  have hDs : Dᵀ = D := by
    have := hs
    rw [fromBlocks_transpose] at this
    exact (fromBlocks_inj.1 this).2.2.2
  obtain ⟨b, hab⟩ := h0.exists_right_inv
  have hba : b * a = 1 := by rw [mul_comm]; exact hab
  have hE : (fromBlocks 1 (-(b • B)) 0 1 : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R)ᵀ
      * fromBlocks (a • 1) B Bᵀ D * fromBlocks 1 (-(b • B)) 0 1
      = fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) := by
    simp [fromBlocks_transpose, fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hba, hab, sub_eq_neg_add]
  have hQ : IsUnit (fromBlocks 1 (-(b • B)) 0 1 : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R).det := by
    rw [det_fromBlocks_zero₂₁]; simp
  apply dgood_congr _ _ hQ
  rw [hE]
  have hSs : (D - b • (Bᵀ * B))ᵀ = D - b • (Bᵀ * B) := by
    rw [transpose_sub, transpose_smul, transpose_mul, transpose_transpose, hDs]
  have hSd : IsUnit (D - b • (Bᵀ * B)).det := by
    have h1 : IsUnit (fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) :
        Matrix (Unit ⊕ κ) (Unit ⊕ κ) R).det := by
      rw [← hE, det_mul, det_mul, det_transpose]
      exact (hQ.mul hd).mul hQ
    rw [det_fromBlocks_zero₂₁] at h1
    exact isUnit_of_mul_isUnit_right h1
  obtain ⟨P₀, hP₀, hP₀d⟩ := ih _ hSs hSd
  refine ⟨fromBlocks 1 0 0 P₀, ?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁, det_one, one_mul]; exact hP₀
  · have hF : (fromBlocks 1 0 0 P₀ : Matrix (Unit ⊕ κ) (Unit ⊕ κ) R)ᵀ
        * fromBlocks (a • 1) 0 0 (D - b • (Bᵀ * B)) * fromBlocks 1 0 0 P₀
        = fromBlocks (a • 1) 0 0 (P₀ᵀ * (D - b • (Bᵀ * B)) * P₀) := by
      simp [fromBlocks_transpose, fromBlocks_multiply]
    rw [hF]
    exact IsDiag.fromBlocks (fun i j h => absurd (Subsingleton.elim i j) h) hP₀d

private theorem dgood_fin {R : Type} [CommRing R] [IsLocalRing R] (h2 : IsUnit (2 : R)) (n : ℕ) :
    ∀ H : Matrix (Fin n) (Fin n) R, Hᵀ = H → IsUnit H.det → DGood H := by
  induction n with
  | zero =>
    intro H _ _
    exact ⟨1, by simp, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro H hs hd
    have e : Unit ⊕ Fin n ≃ Fin (n + 1) := Fintype.equivFinOfCardEq (by simp [add_comm])
    obtain ⟨Q, hQ, hQi⟩ := pivot H h2 hs hd (e (Sum.inl ()))
    apply dgood_congr H Q hQ
    apply dgood_reindex e
    apply step ih
    · simp [transpose_submatrix, transpose_mul, hs, Matrix.mul_assoc]
    · rw [det_submatrix_equiv_self, det_mul, det_mul, det_transpose]
      exact (hQ.mul hd).mul hQ
    · exact hQi

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.diag_local :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {n : ℕ} (H : Matrix (Fin n) (Fin n) R), IsUnit (2 : R) → Hᵀ = H → IsUnit H.det → ∃ (P : GL (Fin n) R) (c : Fin n → Rˣ), (P : Matrix (Fin n) (Fin n) R)ᵀ * H * P = diagonal fun i => (c i : R) := by
  intro R _ _ n H h2 hs hd
  obtain ⟨P, hP, hD⟩ := UpperTheory.V.AlgebraTools.dgood_fin h2 n H hs hd
  have hDu : IsUnit (Pᵀ * H * P).det := by
    rw [det_mul, det_mul, det_transpose]
    exact (hP.mul hd).mul hP
  have hdiag : ∀ i, IsUnit ((Pᵀ * H * P) i i) := by
    intro i
    rw [← hD.diagonal_diag, det_diagonal] at hDu
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (Pᵀ * H * P).diag (Finset.mem_univ i)) hDu
  refine ⟨((isUnit_iff_isUnit_det P).2 hP).unit, fun i => (hdiag i).unit, ?_⟩
  simp only [IsUnit.unit_spec]
  exact hD.diagonal_diag.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
section
noncomputable section

open Polynomial

namespace UpperTheory.V.AlgebraTools

def lag {R E ι : Type*} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (a : ι → R) (P : E) (i : ι) : E :=
  Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j)) •
    aeval P (∏ j ∈ Finset.univ.erase i, (X - C (a j)))

theorem eq_lag_iff {R E ι : Type*} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (a : ι → R) (P : E) (i : ι) (h : ∀ j, j ≠ i → IsUnit (a i - a j)) (f : E) :
    f = lag a P i ↔ (∏ j ∈ Finset.univ.erase i, (a i - a j)) • f =
      aeval P (∏ j ∈ Finset.univ.erase i, (X - C (a j))) := by
  have hu : IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j)) := by
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one ?_
    intro j hj
    exact h j (Finset.ne_of_mem_erase hj)
  obtain ⟨v, hv⟩ := hu
  unfold lag
  rw [← hv, Ring.inverse_unit, ← Units.smul_def, ← Units.smul_def]
  exact eq_inv_smul_iff

example (R : Type) [CommRing R] (a : Unit → R) (P : R) : lag a P () = 1 := by
  have : (Finset.univ : Finset Unit).erase () = ∅ := rfl
  simp [lag, this]

def pat {ι : Type*} (R : Type*) [CommRing R] (p : ι → ι → Prop) : Submodule R (Matrix ι ι R) where
  carrier := {X | ∀ i j, ¬ p i j → X i j = 0}
  add_mem' := fun hX hY i j h => by simp [hX i j h, hY i j h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c X hX i j h => by simp [hX i j h]

theorem mem_pat {ι R : Type*} [CommRing R] {p : ι → ι → Prop} {X : Matrix ι ι R} :
    X ∈ pat R p ↔ ∀ i j, ¬ p i j → X i j = 0 := Iff.rfl

example {ι R : Type} [CommRing R] : pat R (fun _ _ : ι => True) = ⊤ := by
  ext X; simp [mem_pat]

end UpperTheory.V.AlgebraTools
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FrobFormTrunc
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.frob_form_trunc :
    ∀ {k : Type} [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) k] (m : ℕ), ∃ lam : (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ (m + 1)}) →+ ZMod l, (∀ f, lam (Ideal.Quotient.mk _ f) = Algebra.trace (ZMod l) k (PowerSeries.coeff m f)) ∧ (∀ x, (∀ y, lam (x * y) = 0) → x = 0) ∧ Finite (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k) ^ (m + 1)}) := by
  intro k _ _ l _ _ m
  classical
  let I : Ideal (PowerSeries k) := Ideal.span {(PowerSeries.X : PowerSeries k) ^ (m + 1)}
  have hmem : ∀ f : PowerSeries k, f ∈ I ↔ ∀ j, j < m + 1 → PowerSeries.coeff j f = 0 := by
    intro f
    rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  have hW : ∀ f g : PowerSeries k, Ideal.Quotient.mk I f = Ideal.Quotient.mk I g →
      ∀ j, j < m + 1 → PowerSeries.coeff j f = PowerSeries.coeff j g := by
    intro f g h j hj
    rw [Ideal.Quotient.eq, hmem] at h
    have := h j hj
    rw [map_sub, sub_eq_zero] at this
    exact this
  let s := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  have hs : ∀ x, Ideal.Quotient.mk I (s x) = x := Function.surjInv_eq _
  let L : (PowerSeries k ⧸ I) → ZMod l := fun x => Algebra.trace (ZMod l) k (PowerSeries.coeff m (s x))
  have hL : ∀ f, L (Ideal.Quotient.mk I f) = Algebra.trace (ZMod l) k (PowerSeries.coeff m f) := by
    intro f
    simp only [L]
    rw [hW _ _ (hs _) m (Nat.lt_succ_self m)]
  let lam : (PowerSeries k ⧸ I) →+ ZMod l :=
    { toFun := L
      map_zero' := by
        have := hL 0
        rw [map_zero, map_zero, map_zero] at this
        exact this
      map_add' := by
        intro x y
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [← map_add, hL, hL, hL, map_add, map_add] }
  refine ⟨lam, hL, ?_, ?_⟩
  · intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    by_contra hne
    have hnot : f ∉ I := fun h => hne (Ideal.Quotient.eq_zero_iff_mem.2 h)
    rw [hmem] at hnot
    push_neg at hnot
    obtain ⟨j, hj, hfj⟩ := hnot
    have hnd := (traceForm_nondegenerate (ZMod l) k).1 (PowerSeries.coeff j f)
    have hex : ∃ b : k, Algebra.trace (ZMod l) k (PowerSeries.coeff j f * b) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hfj (hnd fun b => by rw [Algebra.traceForm_apply]; exact hc b)
    obtain ⟨b, hb⟩ := hex
    apply hb
    have := hx (Ideal.Quotient.mk I (PowerSeries.C b * PowerSeries.X ^ (m - j)))
    rw [← map_mul] at this
    change L _ = 0 at this
    rw [hL] at this
    have hjm : j ≤ m := Nat.lt_succ_iff.mp hj
    have hc : PowerSeries.coeff m (f * (PowerSeries.C b * PowerSeries.X ^ (m - j))) =
        PowerSeries.coeff j f * b := by
      rw [show f * (PowerSeries.C b * PowerSeries.X ^ (m - j)) =
          PowerSeries.C b * (PowerSeries.X ^ (m - j) * f) by ring]
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (Nat.sub_le m j),
        Nat.sub_sub_self hjm, mul_comm]
    rw [hc] at this
    exact this
  · let e : (PowerSeries k ⧸ I) → (Fin (m + 1) → k) := fun x j => PowerSeries.coeff j (s x)
    apply Finite.of_injective e
    intro x y hxy
    rw [← hs x, ← hs y, Ideal.Quotient.eq, hmem]
    intro j hj
    have := congrFun hxy ⟨j, hj⟩
    rw [map_sub, sub_eq_zero]
    exact this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
section
noncomputable section

open MvPolynomial Equiv

namespace UpperTheory.V.AlgebraTools.Hk

variable (R : Type) [CommRing R] (n : ℕ)

def pairs : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.1 < p.2

def De : MvPolynomial (Fin n) R := ∏ p ∈ pairs n, (X p.2 - X p.1)

variable {R} in

def NN (q : R) : MvPolynomial (Fin n) R := ∏ p ∈ pairs n, (X p.2 - C q * X p.1)

variable {R n}

def alt (x : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R := ∑ w : Perm (Fin n), Perm.sign w • rename w x

open Classical in

def dd (x : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R :=
  if h : ∃ y, De R n * y = alt x then h.choose else 0

def invSet (w : Perm (Fin n)) : Finset (Fin n × Fin n) := (pairs n).filter fun p => w⁻¹ p.2 < w⁻¹ p.1

def invN (w : Perm (Fin n)) : ℕ := (invSet w).card

variable (n) in

def poin (q : R) : R := ∑ w : Perm (Fin n), q ^ invN w

def IsDual {ι : Type} [Fintype ι] (a b : ι → MvPolynomial (Fin n) R) : Prop :=
  ∀ w : Perm (Fin n), ∑ i, a i * rename w (b i) = if w = 1 then De R n else 0

structure Bern (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] where
  th : MvPolynomial (Fin n) R →ₐ[R] H
  T : Perm (Fin n) → H
  T_one : T 1 = 1
  T_mul : ∀ a b : Fin n, a.val + 1 = b.val → ∀ w : Perm (Fin n), w⁻¹ a < w⁻¹ b → T (swap a b * w) = T (swap a b) * T w
  T_sq : ∀ a b : Fin n, a.val + 1 = b.val → T (swap a b) * T (swap a b) = (q - 1) • T (swap a b) + q • (1 : H)
  comm : ∀ a b : Fin n, a.val + 1 = b.val → ∀ j, j ≠ a → j ≠ b → T (swap a b) * th (X j) = th (X j) * T (swap a b)
  relA : ∀ a b : Fin n, a.val + 1 = b.val →
    T (swap a b) * th (X a) = th (X b) * T (swap a b) + (q - 1) • th (X a)
  relB : ∀ a b : Fin n, a.val + 1 = b.val →
    T (swap a b) * th (X b) = th (X a) * T (swap a b) - (q - 1) • th (X a)

namespace Bern

variable {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)

def one : H := ∑ w, b.T w

def Faithful : Prop := ∀ x, b.th x * b.one = 0 → x = 0

def sph (V : Type) [AddCommGroup V] [Module R V] [Module H V] [IsScalarTower R H V] : Submodule R V where
  carrier := {v | ∀ a c : Fin n, a.val + 1 = c.val → b.T (swap a c) • v = q • v}
  add_mem' hu hv a c h := by rw [smul_add, hu a c h, hv a c h, smul_add]
  zero_mem' _ _ _ := by rw [smul_zero, smul_zero]
  smul_mem' r v hv a c h := by
    rw [← algebraMap_smul H r v, ← mul_smul, ← Algebra.commutes, mul_smul, hv a c h, algebraMap_smul, algebraMap_smul,
      smul_comm]

theorem rel_of_quad {H : Type} [Ring H] [Algebra R H] {q : R} (hq : IsUnit q) (T x y : H)
    (hT : T * T = (q - 1) • T + q • (1 : H)) (h : T * y * T = q • x) :
    T * x = y * T + (q - 1) • x ∧ T * y = x * T - (q - 1) • x := by
  have cancel : ∀ a c : H, q • a = q • c → a = c := by
    intro a c hac
    obtain ⟨u, rfl⟩ := hq
    have := congrArg (fun z => ((u⁻¹ : Rˣ) : R) • z) hac
    simpa [smul_smul] using this
  constructor
  · apply cancel
    rw [← mul_smul_comm, ← h, ← mul_assoc, ← mul_assoc, hT]
    rw [add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, one_mul, h]
    rw [smul_add, smul_comm q (q - 1) x]
    abel
  · apply cancel
    symm
    rw [smul_sub, ← smul_mul_assoc, ← h, mul_assoc (T * y), hT, mul_add, mul_smul_comm,
      mul_smul_comm, mul_one, h, smul_comm q (q - 1) x]
    abel

end Bern

def Bern.std (R : Type) [CommRing R] (n : ℕ) : Bern n (1 : R) (Module.End R (MvPolynomial (Fin n) R)) where
  th := Algebra.lsmul R R _
  T w := (rename w).toLinearMap
  T_one := LinearMap.ext fun x => by simp
  T_mul a b _ w _ := LinearMap.ext fun x => by simp [rename_rename]
  T_sq a b _ := LinearMap.ext fun x => by
    simp [rename_rename, Function.comp_def]
    first | exact rename_id_apply x | exact AlgHom.congr_fun rename_id x
  comm a b _ j ha hb := LinearMap.ext fun x => by simp [swap_apply_of_ne_of_ne ha hb]
  relA a b _ := LinearMap.ext fun x => by simp
  relB a b _ := LinearMap.ext fun x => by simp

end UpperTheory.V.AlgebraTools.Hk

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
section
open IsLocalRing

namespace UpperTheory.V.AlgebraTools

structure IsCplAt (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B]
    [Algebra R B] : Prop where
  noeth : IsNoetherianRing B
  complete : IsAdicComplete (maximalIdeal B) B
  comap_eq : (maximalIdeal B).comap (algebraMap R B) = p
  dense : ∀ (n : ℕ) (b : B), ∃ a s : R, s ∉ p ∧
    algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n
  strict : ∀ (n : ℕ) (a : R), algebraMap R B a ∈ maximalIdeal B ^ n → ∃ s : R, s ∉ p ∧ s * a ∈ p ^ n

theorem IsCplAt.isPrime {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) : p.IsPrime := by
  rw [← h.comap_eq]
  exact Ideal.comap_isPrime _ _

abbrev CplAt (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] : Type :=
  AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)

end UpperTheory.V.AlgebraTools
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OrdExt
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.ord_ext :
    ∀ {R Γ E : Type} [CommRing R] [Monoid Γ] [Ring E] [Algebra R E] {n : ℕ} (r : Γ →* E) (ψ : Fin n → Γ →* R), (∀ g : Fin n → Γ, (List.ofFn fun i => r (g i) - algebraMap R E (ψ i (g i))).prod = 0) → ∀ z : Fin n → MonoidAlgebra R Γ, (List.ofFn fun i => MonoidAlgebra.lift R E Γ r (z i) - algebraMap R E (MonoidAlgebra.lift R R Γ (ψ i) (z i))).prod = 0 := by
  intro R Γ E _ _ _ _ n r ψ h z
  let φ : Fin n → (MonoidAlgebra R Γ →ₗ[R] E) := fun i =>
    (MonoidAlgebra.lift R E Γ r).toLinearMap -
      (Algebra.linearMap R E).comp (MonoidAlgebra.lift R R Γ (ψ i)).toLinearMap
  let F : MultilinearMap R (fun _ : Fin n => MonoidAlgebra R Γ) E :=
    (MultilinearMap.mkPiAlgebraFin R n E).compLinearMap φ
  have hF : F = 0 := by
    refine Module.Basis.ext_multilinear (f := F) (g := 0)
      (fun _ => MonoidAlgebra.basis Γ R) ?_
    intro v
    simp only [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply,
      MultilinearMap.zero_apply, MonoidAlgebra.basis_apply]
    convert h v using 3
    funext i
    simp [φ, MonoidAlgebra.lift_single]
  have := congrArg (fun G => G z) hF
  simpa [F, φ] using this
end

