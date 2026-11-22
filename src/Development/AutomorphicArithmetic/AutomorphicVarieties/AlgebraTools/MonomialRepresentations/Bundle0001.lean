import Mathlib

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.CharpolyPowInt
section
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.charpolyPowInt :
    ∀ (R ι : Type) [CommRing R] [Fintype ι] [DecidableEq ι] (S : Subring R) (M : Matrix ι ι R) (N : ℕ), 0 < N →
      (∀ i, (M ^ N).charpoly.coeff i ∈ S) → ∀ i, IsIntegral S (M.charpoly.coeff i) := by
  intro R ι _ _ _ S M N hN h i
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨1, Polynomial.monic_one, Subsingleton.elim _ _⟩
  haveI : Nontrivial S := ⟨⟨0, 1, fun e => zero_ne_one (congrArg Subtype.val e)⟩⟩
  have hdvd : M.charpoly ∣ (M ^ N).charpoly.comp (X ^ N) := by
    set A : Matrix ι ι R[X] := Matrix.scalar ι (X : R[X]) with hAdef
    set B : Matrix ι ι R[X] := (C : R →+* R[X]).mapMatrix M with hBdef
    have hAB : Commute A B := Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
    have e1 : (M ^ N).charpoly.comp (X ^ N) = (A ^ N - B ^ N).det := by
      have hA : A ^ N = Matrix.scalar ι ((X : R[X]) ^ N) := (map_pow (Matrix.scalar ι) X N).symm
      have hB : B ^ N = (C : R →+* R[X]).mapMatrix (M ^ N) := (map_pow _ M N).symm
      rw [hA, hB, Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
      congr 1
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [Matrix.charmatrix_apply_eq]
      · simp [Matrix.charmatrix_apply_ne _ _ _ hab, hab]
    rw [e1, ← hAB.geom_sum₂_mul N, Matrix.det_mul]
    exact Dvd.intro_left _ rfl
  have hl : (M ^ N).charpoly ∈ Polynomial.lifts (algebraMap S R) :=
    (Polynomial.lifts_iff_coeff_lifts _).2 fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨p₀, hp₀, -, hmon⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hl (Matrix.charpoly_monic _)
  refine Polynomial.isIntegral_coeff_of_dvd (p₀.comp (X ^ N)) M.charpoly
    (hmon.comp (Polynomial.monic_X_pow N) (by rw [Polynomial.natDegree_X_pow]; omega))
    (Matrix.charpoly_monic M) ?_ i
  rw [Polynomial.map_comp, hp₀, Polynomial.map_pow, Polynomial.map_X]
  exact hdvd
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.Clifford
section
open Polynomial Matrix

namespace UpperTheory.V.AlgebraTools

section

variable {K G V : Type} [Field K] [Group G] [AddCommGroup V] [Module K V]
  (ρ : Representation K G V) (N : Subgroup G) [hN : N.Normal]

private def cliffTr (g : G) (W : Subrepresentation (ρ.comp N.subtype : Representation K N V)) :
    Subrepresentation (ρ.comp N.subtype : Representation K N V) where
  toSubmodule := W.toSubmodule.comap (ρ g)
  apply_mem_toSubmodule n v hv := by
    have h := W.apply_mem_toSubmodule ⟨g * n * g⁻¹, hN.conj_mem _ n.2 g⟩ hv
    have e : ρ (g * n * g⁻¹) (ρ g v) = ρ g (ρ n v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    change ρ g (ρ n v) ∈ W.toSubmodule
    rw [← e]
    exact h

private theorem cliffTr_mul (g h : G) (hgh : g * h = 1)
    (W : Subrepresentation (ρ.comp N.subtype : Representation K N V)) :
    cliffTr ρ N h (cliffTr ρ N g W) = W := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  change ρ g (ρ h v) ∈ W.toSubmodule ↔ _
  rw [← Module.End.mul_apply, ← map_mul, hgh, map_one]
  rfl

private def cliffIso (g : G) :
    Subrepresentation (ρ.comp N.subtype : Representation K N V) ≃o
      Subrepresentation (ρ.comp N.subtype : Representation K N V) :=
  Equiv.toOrderIso
    { toFun := cliffTr ρ N g
      invFun := cliffTr ρ N g⁻¹
      left_inv := cliffTr_mul ρ N g g⁻¹ (by simp)
      right_inv := cliffTr_mul ρ N g⁻¹ g (by simp) }
    (fun _ _ h _ hv => h hv) (fun _ _ h _ hv => h hv)

end

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.clifford :
    ∀ (K G V : Type) [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V)
      (N : Subgroup G) [N.Normal], ρ.IsIrreducible → Representation.IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  intro K G V _ _ _ _ _ ρ N _ hirr
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    ← sSup_simples_eq_top_iff_isSemisimpleModule]
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp N.subtype)
  let A := {m : Submodule (MonoidAlgebra K N) (Representation.asModule (ρ.comp N.subtype)) |
    IsSimpleModule (MonoidAlgebra K N) m}
  have hA : ∀ m, m ∈ A ↔ IsAtom m := fun m => isSimpleModule_iff_isAtom
  change sSup A = ⊤
  have inv : ∀ g : G, ∀ v : V, v ∈ e.symm (sSup A) → ρ g v ∈ e.symm (sSup A) := by
    intro g v hv
    let φ := e.symm.trans ((UpperTheory.V.AlgebraTools.cliffIso ρ N g).trans e)
    have hφ : φ (sSup A) = sSup A := by
      rw [OrderIso.map_sSup]
      apply le_antisymm
      · refine iSup₂_le fun a ha => le_sSup ?_
        exact (hA _).2 ((φ.isAtom_iff a).2 ((hA a).1 ha))
      · refine sSup_le fun b hb => ?_
        have hb' : φ.symm b ∈ A := (hA _).2 ((φ.symm.isAtom_iff b).2 ((hA b).1 hb))
        have h := le_iSup₂ (f := fun a (_ : a ∈ A) => φ a) (φ.symm b) hb'
        simpa using h
    have h : v ∈ e.symm (φ (sSup A)) := by rw [hφ]; exact hv
    exact h
  let T : Subrepresentation ρ := ⟨(e.symm (sSup A)).toSubmodule, fun g v hv => inv g v hv⟩
  rcases eq_bot_or_eq_top T with hT | hT
  · exfalso
    have hmono : StrictMono (Subrepresentation.toSubmodule :
        Subrepresentation (ρ.comp N.subtype) → Submodule K V) :=
      fun x y h => h
    haveI := hmono.wellFoundedLT
    haveI : IsAtomic (Subrepresentation (ρ.comp N.subtype)) :=
      isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
    have hne : (⊤ : Subrepresentation (ρ.comp N.subtype)) ≠ ⊥ := by
      intro h
      apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
      apply Subrepresentation.ext
      exact (congrArg Subrepresentation.toSubmodule h).symm
    obtain ⟨a, ha, -⟩ :=
      (eq_bot_or_exists_atom_le (⊤ : Subrepresentation (ρ.comp N.subtype))).resolve_left hne
    have h1 : a ≤ e.symm (sSup A) := by
      have h0 : e a ≤ sSup A := le_sSup ((hA _).2 ((e.isAtom_iff a).2 ha))
      simpa using e.symm.monotone h0
    have h2 : (e.symm (sSup A)).toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hT
    apply ha.1
    apply Subrepresentation.ext
    apply le_antisymm _ bot_le
    intro v hv
    have h3 : v ∈ (e.symm (sSup A)).toSubmodule := h1 hv
    rw [h2] at h3
    exact h3
  · refine eq_top_iff.2 fun v _ => ?_
    have h3 : (show V from v) ∈ T.toSubmodule := by rw [hT]; exact Submodule.mem_top
    exact h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.CoordSub
section
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.coordSub :
    ∀ (C ι : Type) [CommRing C] [Fintype ι] [DecidableEq ι] (d : ι → C), (∀ i j, i ≠ j → IsUnit (d i - d j)) →
      ∀ W : Submodule C (ι → C), (∀ w ∈ W, diagonal d *ᵥ w ∈ W) → ∀ w ∈ W, ∀ i, Pi.single i (w i) ∈ W := by
  intro C ι _ _ _ d hd W hD w hw i
  have key : ∀ S : Finset ι, (fun k => (∏ j ∈ S, (d k - d j)) * w k) ∈ W := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simpa using hw
    · intro j S hj ih
      have h2 := W.sub_mem (hD _ ih) (W.smul_mem (d j) ih)
      convert h2 using 1
      funext k
      simp only [Finset.prod_insert hj, mulVec_diagonal, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hu : IsUnit (∏ j ∈ Finset.univ.erase i, (d i - d j)) :=
    IsUnit.prod_iff.mpr fun j hj => hd i j (Finset.ne_of_mem_erase hj).symm
  have h3 := W.smul_mem (↑hu.unit⁻¹ : C) (key (Finset.univ.erase i))
  convert h3 using 1
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · have hz : ∏ j ∈ Finset.univ.erase i, (d k - d j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩) (sub_self _)
    simp [Pi.single_eq_of_ne hk, hz]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.DiscSwap
section
open Polynomial Matrix

private theorem charpoly_fromBlocks_antidiagonal_fin_two {F : Type} [Field F] (P Q : Matrix (Fin 2) (Fin 2) F) :
    (fromBlocks 0 P Q 0).charpoly = X ^ 4 - C ((Q * P) 0 0 + (Q * P) 1 1) * X ^ 2
      + C ((Q * P) 0 0 * (Q * P) 1 1 - (Q * P) 0 1 * (Q * P) 1 0) := by
  unfold Matrix.charpoly
  rw [charmatrix_fromBlocks]
  have hcz : charmatrix (0 : Matrix (Fin 2) (Fin 2) F) = diagonal (fun _ : Fin 2 => (X : F[X])) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [charmatrix_apply]
    · simp [charmatrix_apply, diagonal_apply_ne _ h]
  rw [hcz]
  generalize hS : (diagonal (fun _ : Fin 2 => (X : F[X])) : Matrix (Fin 2) (Fin 2) F[X]) = S
  generalize hP' : P.map C = P'
  generalize hQ' : Q.map C = Q'
  have hcomm : S * P' = P' * S := by
    subst hS
    ext i j
    simp [mul_comm]
  have hprod : fromBlocks S (-P') (-Q') S * fromBlocks S P' 0 S
      = fromBlocks (S * S) 0 (-(Q' * S)) (S * S - Q' * P') := by
    rw [fromBlocks_multiply, fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · rw [hcomm, neg_mul, add_neg_cancel]
    · simp
    · rw [neg_mul, add_comm, sub_eq_add_neg]
  have hdet := congrArg det hprod
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at hdet
  have hSd : det S = X ^ 2 := by
    subst hS
    simp [det_diagonal, Fin.prod_univ_two, sq]
  rw [det_mul, hSd] at hdet
  have hX : (X ^ 2 * X ^ 2 : F[X]) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ X_ne_zero)
  have hG : det (fromBlocks S (-P') (-Q') S) = det (S * S - Q' * P') := by
    apply mul_right_cancel₀ hX
    rw [hdet]
    ring
  rw [hG, det_fin_two]
  subst hS hP' hQ'
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem separable_biquadratic_of_ne_zero_of_discrim_ne_zero {F : Type} [Field F] (a d : F) (h2 : (2 : F) ≠ 0) (hd : d ≠ 0)
    (he : a ^ 2 - 4 * d ≠ 0) : (X ^ 4 - C a * X ^ 2 + C d : F[X]).Separable := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hk : 4 * d * (8 * d - 2 * a ^ 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero h4 hd) ?_
    rw [show 8 * d - 2 * a ^ 2 = -2 * (a ^ 2 - 4 * d) by ring]
    exact mul_ne_zero (neg_ne_zero.2 h2) he
  have hder : derivative (X ^ 4 - C a * X ^ 2 + C d : F[X]) = 4 * X ^ 3 - 2 * C a * X := by
    rw [derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul_X_pow, derivative_C]
    norm_num
    simp only [map_ofNat]
    ring
  have hCe : (C (8 * d - 2 * a ^ 2) : F[X]) = 8 * C d - 2 * C a ^ 2 := by
    simp only [map_mul, map_sub, map_pow, map_ofNat]
  have key : (4 * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2)) * (X ^ 4 - C a * X ^ 2 + C d)
      + (-X * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2) + 2 * C a ^ 2 * X) * (4 * X ^ 3 - 2 * C a * X)
      = C (4 * d * (8 * d - 2 * a ^ 2)) := by
    rw [map_mul, map_mul, hCe]
    simp only [map_ofNat]
    ring
  unfold Polynomial.Separable IsCoprime
  refine ⟨C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * (4 * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2)),
    C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * (-X * (C (8 * d - 2 * a ^ 2) + 4 * C a * X ^ 2) + 2 * C a ^ 2 * X), ?_⟩
  rw [hder]
  calc _ = C (4 * d * (8 * d - 2 * a ^ 2))⁻¹ * C (4 * d * (8 * d - 2 * a ^ 2)) := by rw [← key]; ring
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hk, C_1]

private theorem discSwap_lemma_3 {K : Type} [Field K] (b c : Matrix (Fin 2) (Fin 2) K) (w₁ w₂ : Fin 2 → ℤ)
    (hw₁ : StrictAnti w₁) (hw₂ : StrictAnti w₂) (hb : b 0 0 ≠ 0) (hc : c 0 0 ≠ 0)
    (hbd : b.det ≠ 0) (hcd : c.det ≠ 0) :
    let N := (c.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₁ i)) *
      (b.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))
    N 0 0 * N 1 1 - N 0 1 * N 1 0 ≠ 0 ∧
      (N 0 0 + N 1 1) ^ 2 - 4 * (N 0 0 * N 1 1 - N 0 1 * N 1 0) ≠ 0 := by
  intro N
  have h01 : (0 : Fin 2) < 1 := by decide
  obtain ⟨n, hn, hn0⟩ : ∃ n : ℕ, w₁ 0 = w₁ 1 + n ∧ 0 < n :=
    ⟨(w₁ 0 - w₁ 1).toNat, by have := hw₁ h01; omega, by have := hw₁ h01; omega⟩
  obtain ⟨m, hm, hm0⟩ : ∃ m : ℕ, w₂ 0 = w₂ 1 + m ∧ 0 < m :=
    ⟨(w₂ 0 - w₂ 1).toNat, by have := hw₂ h01; omega, by have := hw₂ h01; omega⟩
  set f := algebraMap K (RatFunc K) with hf
  set Y : RatFunc K := RatFunc.X with hY
  have hY0 : Y ≠ 0 := RatFunc.X_ne_zero
  have hA : Y ^ w₁ 0 = Y ^ w₁ 1 * Y ^ n := by rw [hn, zpow_add₀ hY0, zpow_natCast]
  have hB : Y ^ w₂ 0 = Y ^ w₂ 1 * Y ^ m := by rw [hm, zpow_add₀ hY0, zpow_natCast]
  have hu : Y ^ w₁ 1 ≠ 0 := zpow_ne_zero _ hY0
  have hv : Y ^ w₂ 1 ≠ 0 := zpow_ne_zero _ hY0
  have e00 : N 0 0 = f (c 0 0) * Y ^ w₁ 0 * (f (b 0 0) * Y ^ w₂ 0)
      + f (c 0 1) * Y ^ w₁ 1 * (f (b 1 0) * Y ^ w₂ 0) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e01 : N 0 1 = f (c 0 0) * Y ^ w₁ 0 * (f (b 0 1) * Y ^ w₂ 1)
      + f (c 0 1) * Y ^ w₁ 1 * (f (b 1 1) * Y ^ w₂ 1) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e10 : N 1 0 = f (c 1 0) * Y ^ w₁ 0 * (f (b 0 0) * Y ^ w₂ 0)
      + f (c 1 1) * Y ^ w₁ 1 * (f (b 1 0) * Y ^ w₂ 0) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have e11 : N 1 1 = f (c 1 0) * Y ^ w₁ 0 * (f (b 0 1) * Y ^ w₂ 1)
      + f (c 1 1) * Y ^ w₁ 1 * (f (b 1 1) * Y ^ w₂ 1) := by
    simp [N, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, hf, hY] <;> ring
  have hdet : N 0 0 * N 1 1 - N 0 1 * N 1 0
      = f (c.det * b.det) * (Y ^ w₁ 1) ^ 2 * (Y ^ w₂ 1) ^ 2 * Y ^ (n + m) := by
    rw [e00, e01, e10, e11, hA, hB, det_fin_two, det_fin_two]
    simp only [map_mul, map_sub]
    ring
  refine ⟨?_, ?_⟩
  · rw [hdet]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hu)) (pow_ne_zero _ hv)) (pow_ne_zero _ hY0)
    exact (map_ne_zero f).2 (mul_ne_zero hcd hbd)
  · set q : K[X] := C (c 0 0 * b 0 0) * X ^ (n + m)
      + (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1)) with hq
    set Pol : K[X] := q ^ 2 - C (4 * (c.det * b.det)) * X ^ (n + m) with hPol
    have hkey : (N 0 0 + N 1 1) ^ 2 - 4 * (N 0 0 * N 1 1 - N 0 1 * N 1 0)
        = (Y ^ w₁ 1 * Y ^ w₂ 1) ^ 2 * algebraMap K[X] (RatFunc K) Pol := by
      rw [hdet, e00, e11, hA, hB, hPol, hq]
      simp only [map_mul, map_sub, map_add, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
        map_ofNat, hf, RatFunc.algebraMap_eq_C, hY]
      ring
    have hrest : (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1) : K[X]).natDegree
        < n + m := by
      have h1 : (C (c 0 1 * b 1 0) * X ^ m + C (c 1 0 * b 0 1) * X ^ n + C (c 1 1 * b 1 1) : K[X]).natDegree
          ≤ max n m := by
        refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
        · exact (natDegree_C_mul_X_pow_le _ _).trans (le_max_right _ _)
        · exact (natDegree_C_mul_X_pow_le _ _).trans (le_max_left _ _)
        · rw [natDegree_C]; exact Nat.zero_le _
      omega
    have hqd : q.natDegree = n + m := by
      rw [hq, natDegree_add_eq_left_of_natDegree_lt] <;> rw [natDegree_C_mul_X_pow _ _ (mul_ne_zero hc hb)]
      exact hrest
    have hPol0 : Pol ≠ 0 := by
      intro h0
      have hsq : q ^ 2 = C (4 * (c.det * b.det)) * X ^ (n + m) := sub_eq_zero.1 (hPol ▸ h0)
      have := congrArg natDegree hsq
      rw [natDegree_pow, hqd] at this
      have hle := natDegree_C_mul_X_pow_le (4 * (c.det * b.det)) (n + m)
      omega
    rw [hkey]
    refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero hu hv)) ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 hPol0

theorem UpperTheory.V.AlgebraTools.discSwap :
    ∀ (K : Type) [Field K], (2 : K) ≠ 0 → ∀ (b c : Matrix (Fin 2) (Fin 2) K) (w₁ w₂ : Fin 2 → ℤ), StrictAnti w₁ → StrictAnti w₂ →
      b 0 0 ≠ 0 → c 0 0 ≠ 0 → b.det ≠ 0 → c.det ≠ 0 →
      ((fromBlocks 0 b c 0).map (algebraMap K (RatFunc K)) *
        diagonal (Sum.elim (fun i => (RatFunc.X : RatFunc K) ^ w₁ i) (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))).charpoly.Separable := by
  intro K _ h2 b c w₁ w₂ hw₁ hw₂ hb hc hbd hcd
  have hblk : (fromBlocks 0 b c 0).map (algebraMap K (RatFunc K)) *
      diagonal (Sum.elim (fun i => (RatFunc.X : RatFunc K) ^ w₁ i) (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))
      = fromBlocks 0 (b.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₂ i))
          (c.map (algebraMap K (RatFunc K)) * diagonal (fun i => (RatFunc.X : RatFunc K) ^ w₁ i)) 0 := by
    ext (i | i) (j | j) <;> simp [Matrix.mul_diagonal]
  have h2' : (2 : RatFunc K) ≠ 0 := by
    rw [show (2 : RatFunc K) = algebraMap K (RatFunc K) 2 from (map_ofNat _ 2).symm]
    exact (_root_.map_ne_zero _).2 h2
  obtain ⟨hd, he⟩ := discSwap_lemma_3 b c w₁ w₂ hw₁ hw₂ hb hc hbd hcd
  rw [hblk, charpoly_fromBlocks_antidiagonal_fin_two]
  exact separable_biquadratic_of_ne_zero_of_discrim_ne_zero _ _ h2' hd he
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.HenselDiag
section
open Polynomial Matrix

section
variable {C ι : Type} [CommRing C] [Fintype ι] [DecidableEq ι]

private theorem res_one [IsLocalRing C] (u : Matrix ι ι C) :
    (∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C) ↔ (IsLocalRing.residue C).mapMatrix u = 1 := by
  rw [← map_one (IsLocalRing.residue C).mapMatrix, ← sub_eq_zero, ← map_sub, ← Matrix.ext_iff]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, IsLocalRing.residue_eq_zero_iff]

private theorem unit_of_res [IsLocalRing C] (x : C) (h : IsLocalRing.residue C x ≠ 0) : IsUnit x := by
  by_contra hx
  exact h ((IsLocalRing.residue_eq_zero_iff _).mpr hx)

private theorem res_diag [IsLocalRing C] (M : Matrix ι ι C)
    (h : ∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) :
    (IsLocalRing.residue C).mapMatrix M = diagonal fun i => IsLocalRing.residue C (M i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, IsLocalRing.residue_eq_zero_iff, h i j hij]

private theorem exists_root [HenselianLocalRing C] (M : Matrix ι ι C)
    (h : ∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) (hu : ∀ i j, i ≠ j → IsUnit (M i i - M j j)) (i : ι) :
    ∃ d : C, (Matrix.scalar ι d - M).det = 0 ∧ d - M i i ∈ IsLocalRing.maximalIdeal C := by
  have hc : M.charpoly.map (IsLocalRing.residue C) = ∏ j, (X - Polynomial.C (IsLocalRing.residue C (M j j))) := by
    rw [← Matrix.charpoly_map, ← RingHom.mapMatrix_apply, res_diag M h, Matrix.charpoly_diagonal]
  have h1 : M.charpoly.eval (M i i) ∈ IsLocalRing.maximalIdeal C := by
    rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.eval_map_apply, hc, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have h2 : IsUnit (M.charpoly.derivative.eval (M i i)) := by
    apply unit_of_res
    rw [← Polynomial.eval_map_apply, ← Polynomial.derivative_map, hc,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, sub_self, zero_mul, add_zero, eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun a ha => ?_
    rw [← map_sub]
    exact ((hu i a (Finset.ne_of_mem_erase ha).symm).map _).ne_zero
  obtain ⟨d, hd, hd'⟩ := HenselianLocalRing.is_henselian M.charpoly M.charpoly_monic (M i i) h1 h2
  exact ⟨d, by rw [← Matrix.eval_charpoly]; exact hd, hd'⟩

private theorem exists_vec [IsLocalRing C] (M : Matrix ι ι C)
    (h : ∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) (hu : ∀ i j, i ≠ j → IsUnit (M i i - M j j)) (i : ι)
    (d : C) (hd : (Matrix.scalar ι d - M).det = 0) (hd' : d - M i i ∈ IsLocalRing.maximalIdeal C) :
    ∃ v : ι → C, (∀ k, ∑ j, M k j * v j = v k * d) ∧ v i = 1 ∧ ∀ k, k ≠ i → v k ∈ IsLocalRing.maximalIdeal C := by
  have hdi : IsLocalRing.residue C d = IsLocalRing.residue C (M i i) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hd'
  set A := (Matrix.scalar ι d - M).adjugate with hA
  have h0 : (Matrix.scalar ι d - M) * A = 0 := by rw [hA, Matrix.mul_adjugate, hd, zero_smul]
  have h1 : (IsLocalRing.residue C).mapMatrix (Matrix.scalar ι d - M) =
      diagonal fun k => IsLocalRing.residue C (M i i - M k k) := by
    rw [map_sub, res_diag M h]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hdi]
    · simp [hab]
  have h2 : (IsLocalRing.residue C).mapMatrix A =
      diagonal fun k => ∏ j ∈ Finset.univ.erase k, IsLocalRing.residue C (M i i - M j j) := by
    rw [hA, RingHom.map_adjugate, h1, Matrix.adjugate_diagonal]
  have h3 : IsUnit (A i i) := by
    apply unit_of_res
    have := congrFun (congrFun h2 i) i
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq] at this
    rw [this]
    exact Finset.prod_ne_zero_iff.mpr fun a ha => ((hu i a (Finset.ne_of_mem_erase ha).symm).map _).ne_zero
  obtain ⟨c, hc⟩ := h3.exists_right_inv
  refine ⟨fun k => A k i * c, fun k => ?_, hc, fun k hk => ?_⟩
  · rw [sub_mul, sub_eq_zero] at h0
    have := congrFun (congrFun h0 k) i
    rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_apply] at this
    simp only [← mul_assoc]
    rw [← Finset.sum_mul, ← this]; ring
  · have := congrFun (congrFun h2 k) i
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_ne _ hk,
      IsLocalRing.residue_eq_zero_iff] at this
    exact Ideal.mul_mem_right _ _ this

end

theorem UpperTheory.V.AlgebraTools.henselDiag :
    ∀ (C ι : Type) [CommRing C] [HenselianLocalRing C] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι C),
      (∀ i j, i ≠ j → M i j ∈ IsLocalRing.maximalIdeal C) → (∀ i j, i ≠ j → IsUnit (M i i - M j j)) →
      ∃ (u : Matrix ι ι C) (d : ι → C), (∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C) ∧ M * u = u * diagonal d ∧
        (∀ i, d i - M i i ∈ IsLocalRing.maximalIdeal C) ∧
        ∀ (u' : Matrix ι ι C) (d' : ι → C), (∀ i j, (u' - 1) i j ∈ IsLocalRing.maximalIdeal C) → M * u' = u' * diagonal d' →
          d' = d ∧ ∃ t : ι → C, u' = u * diagonal t := by
  intro C ι _ _ _ _ M h hu
  choose d hd hd' using exists_root M h hu
  choose v hv hv1 hv0 using fun i => exists_vec M h hu i (d i) (hd i) (hd' i)
  let u : Matrix ι ι C := Matrix.of fun k i => v i k
  have hu1 : ∀ i j, (u - 1) i j ∈ IsLocalRing.maximalIdeal C := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [u, hv1]
    · simpa [u, hij] using hv0 j i hij
  have hMu : M * u = u * diagonal d := by
    ext k i
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    exact hv i k
  refine ⟨u, d, hu1, hMu, hd', fun u' d' hu' hM' => ?_⟩
  have r1 := (res_one u).mp hu1
  have r2 := (res_one u').mp hu'
  have hdet : IsUnit u := by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply unit_of_res
    rw [RingHom.map_det, r1, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨U, hU⟩ := hdet
  set w : Matrix ι ι C := (U⁻¹ : (Matrix ι ι C)ˣ) * u' with hw
  have huw : u' = u * w := by rw [hw, ← hU, Units.mul_inv_cancel_left]
  have r3 : (IsLocalRing.residue C).mapMatrix w = 1 := by
    rw [huw, map_mul, r1, one_mul] at r2; exact r2
  have hcomm : diagonal d * w = w * diagonal d' := by
    rw [huw, ← mul_assoc, hMu, mul_assoc, mul_assoc, ← hU] at hM'
    exact (Units.mul_right_inj U).mp hM'
  have he : ∀ i j, (d i - d' j) * w i j = 0 := by
    intro i j
    have := congrFun (congrFun hcomm i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    rw [sub_mul, this]; ring
  have hd2 : ∀ j, IsLocalRing.residue C (d' j) = IsLocalRing.residue C (M j j) := by
    intro j
    have := congrArg (IsLocalRing.residue C).mapMatrix hM'
    rw [map_mul, map_mul, r2, mul_one, one_mul] at this
    have := congrFun (congrFun this j) j
    simpa using this.symm
  have hd1 : ∀ j, IsLocalRing.residue C (d j) = IsLocalRing.residue C (M j j) := by
    intro j
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hd' j
  constructor
  · funext i
    have hwi : IsUnit (w i i) := by
      apply unit_of_res
      have := congrFun (congrFun r3 i) i
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply_eq] at this
      rw [this]; exact one_ne_zero
    exact (sub_eq_zero.mp (hwi.mul_left_eq_zero.mp (he i i))).symm
  · refine ⟨fun i => w i i, ?_⟩
    rw [huw]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      refine (unit_of_res (d i - d' j) ?_).mul_right_eq_zero.mp (he i j)
      rw [map_sub, hd1, hd2, ← map_sub]
      exact ((hu i j hij).map _).ne_zero
end

