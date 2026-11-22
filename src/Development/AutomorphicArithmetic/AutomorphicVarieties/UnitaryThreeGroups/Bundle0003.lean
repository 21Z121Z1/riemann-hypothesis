import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0059

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsCoordOfNotMatIrr
section
open Matrix UpperTheory.V.U3

private theorem single_mem_of_diag {κ : Type} [Field κ] {m : ℕ} (d : Fin m → κ)
    (hd : Function.Injective d) (W : Submodule κ (Fin m → κ))
    (hW : ∀ v ∈ W, Matrix.diagonal d *ᵥ v ∈ W) (v : Fin m → κ) (hv : v ∈ W) (i : Fin m)
    (hi : v i ≠ 0) : (Pi.single i 1 : Fin m → κ) ∈ W :=
  _root_.UpperTheory.Reformulated.B.SingleMemOfDiagonal.single_mem_of_diag d hd W hW v hv i hi

private theorem exists_coord_of_not_matIrr {G κ : Type} [Group G] [Field κ] {m : ℕ}
    (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) κ) (d : Fin m → κ)
    (hd : Function.Injective d) (g₁ g₂ : G) (h₁ : g₁ ∈ H) (h₂ : g₂ ∈ H)
    (hD : a g₁ - a g₂ = Matrix.diagonal d) (h : ¬ MatIrr H a) :
    ∃ S : Fin m → Prop, (∃ j, S j) ∧ (∃ i, ¬ S i) ∧
      ∀ i j, S j → ¬ S i → ∀ g ∈ H, a g i j = 0 := by
  classical
  unfold MatIrr at h
  push Not at h
  obtain ⟨W, hW, hb, ht⟩ := h
  have hWd : ∀ v ∈ W, Matrix.diagonal d *ᵥ v ∈ W := fun v hv => by
    rw [← hD, Matrix.sub_mulVec]
    exact W.sub_mem (hW _ h₁ _ hv) (hW _ h₂ _ hv)
  have hs := single_mem_of_diag d hd W hWd
  refine ⟨fun j => (Pi.single j 1 : Fin m → κ) ∈ W, ?_, ?_, ?_⟩
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
    exact ⟨j, hs v hv j hj⟩
  · by_contra hc
    push Not at hc
    apply ht
    rw [eq_top_iff]
    intro v _
    rw [pi_eq_sum_univ' v]
    exact W.sum_mem fun i _ => W.smul_mem _ (hc i)
  · intro i j hj hi g hg
    by_contra hc
    apply hi
    refine hs _ (hW g hg _ hj) i ?_
    simpa using hc

theorem UpperTheory.V.U3.shape_cases :
    ∀ {G κ : Type} [Group G] [Field κ] (η : G →* ℤˣ) (r : G →* GG 3 κ) (c g₁ : G), (2 : κ) ≠ 0 → HasMult η r → η c = -1 → η g₁ = 1 →
      Normalised c g₁ r → zeta c g₁ r ≠ 0 → TypeI η r ∨ Upper η r ∨ Lower η r ∨ TypeII η r := by
  intro G κ _ _ η r c g₁ h2 hm hc hg hn hz
  have hc' : (r c).right = -1 := (hm c).trans hc
  have hD := zmat_diag r c g₁ h2.isUnit hc' ((hm g₁).trans hg) hn
  have hst : ∀ g ∈ η.ker, gstar c g ∈ η.ker := fun g hg =>
    (hm _).symm.trans (mat_gstar r c g hn.atc hc' ((hm g).trans hg)).2
  set ζ := zeta c g₁ r with hζ
  have hne : ζ ≠ -ζ := fun h => hz (by
    have : (2 : κ) * ζ = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2)
  let Z : Fin 3 → Fin 3 → Prop := fun i j => ∀ g ∈ η.ker, (r g).mat i j = 0
  have hsym : ∀ i j : Fin 3, Z i j → Z j.rev i.rev := by
    intro i j h g hg
    have h1 := h _ (hst g hg)
    rw [(mat_gstar r c g hn.atc hc' ((hm g).trans hg)).1] at h1
    revert h1
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
  have s10 : Z 1 0 → Z 2 1 := hsym 1 0
  have s21 : Z 2 1 → Z 1 0 := hsym 2 1
  have s01 : Z 0 1 → Z 1 2 := hsym 0 1
  have s12 : Z 1 2 → Z 0 1 := hsym 1 2
  have hU : Z 1 0 → Z 2 0 → Upper η r := by
    intro h1 h2 g hg a b hab
    have := h1 g hg
    have := h2 g hg
    have := s10 h1 g hg
    fin_cases a <;> fin_cases b <;> first | assumption | (exfalso; revert hab; decide)
  have hL : Z 0 1 → Z 0 2 → Lower η r := by
    intro h1 h2 g hg a b hab
    have := h1 g hg
    have := h2 g hg
    have := s01 h1 g hg
    fin_cases a <;> fin_cases b <;> first | assumption | (exfalso; revert hab; decide)
  have hB : Z 0 1 → Z 1 0 → Upper η r ∨ Lower η r ∨ TypeII η r := by
    intro h1 h2
    by_cases hI : MatIrr η.ker fun g => corner (r g).mat
    · refine Or.inr (Or.inr ⟨?_, hI⟩)
      intro g hg a b hab
      have := h1 g hg
      have := h2 g hg
      have := s01 h1 g hg
      have := s10 h2 g hg
      fin_cases a <;> fin_cases b <;> first | assumption | (exfalso; revert hab; decide)
    · have hinj : Function.Injective ![ζ, -ζ] := by
        intro i j h
        fin_cases i <;> fin_cases j <;> simp_all [hne.symm]
      obtain ⟨S, ⟨j, hj⟩, ⟨i, hi⟩, hS⟩ := exists_coord_of_not_matIrr η.ker _ ![ζ, -ζ] hinj g₁
        (gstar c g₁) hg (hst g₁ hg) (by
          ext i j
          have := congrFun (congrFun hD (![0, 2] i)) (![0, 2] j)
          refine Eq.trans this ?_
          fin_cases i <;> fin_cases j <;> simp) hI
      have h3 := hS i j hj hi
      fin_cases i <;> fin_cases j
      · exact absurd hj hi
      · exact Or.inr (Or.inl (hL h1 h3))
      · exact Or.inl (hU h2 h3)
      · exact absurd hj hi
  by_cases hI : TypeI η r
  · exact Or.inl hI
  right
  have hinj : Function.Injective ![ζ, 0, -ζ] := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [hne.symm]
  obtain ⟨S, ⟨j, hj⟩, ⟨i, hi⟩, hS⟩ := exists_coord_of_not_matIrr η.ker (mats r) _ hinj g₁
    (gstar c g₁) hg (hst g₁ hg) hD hI
  have hS' : ∀ i j, S j → ¬ S i → Z i j := hS
  by_cases a0 : S 0 <;> by_cases a1 : S 1 <;> by_cases a2 : S 2
  · fin_cases i <;> contradiction
  · exact Or.inl (hU (s21 (hS' _ _ a1 a2)) (hS' _ _ a0 a2))
  · exact hB (s12 (hS' _ _ a2 a1)) (hS' _ _ a0 a1)
  · exact Or.inl (hU (hS' _ _ a0 a1) (hS' _ _ a0 a2))
  · exact Or.inr (Or.inl (hL (hS' _ _ a1 a0) (hS' _ _ a2 a0)))
  · exact hB (hS' _ _ a1 a0) (s21 (hS' _ _ a1 a2))
  · exact Or.inr (Or.inl (hL (s12 (hS' _ _ a2 a1)) (hS' _ _ a2 a0)))
  · fin_cases j <;> contradiction
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.FreeEtaleSheafZmodExistsHomSendingGenerator
section
open Matrix UpperTheory.V.U3

private theorem offdiag_zero {κ : Type} [Field κ] (M : Matrix (Fin 3) (Fin 3) κ) (z z' : κ)
    (hz : z ≠ 0) (hz' : z' ≠ 0) (hne : z' ≠ -z)
    (h : M * Matrix.diagonal ![z, 0, -z] = Matrix.diagonal ![z', 0, -z'] * M) :
    ∀ i j, i ≠ j → M i j = 0 := by
  intro i j hij
  have e := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm] at e
  by_contra hM
  have e' := mul_right_cancel₀ hM e
  have hne' : z ≠ -z' := fun h => hne (by rw [h, neg_neg])
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

private theorem free_etale_sheaf_zmod_exists_hom_sending_generator {κ ι : Type} [Field κ] [IsAlgClosed κ] (m : Fin 3 → κ) (hm : ∀ i, m i ≠ 0)
    (a a' : ι → Matrix (Fin 3) (Fin 3) κ)
    (h1 : ∀ g i j, m i * a g i j = a' g i j * m j)
    (h2 : ∀ g i j, m j.rev * a g i j = a' g i j * m i.rev) :
    ∃ t : κˣ, ∀ g i j, a' g i j = ((t ^ wt i j : κˣ) : κ) * a g i j := by
  have h0 := hm 0
  have h1' := hm 1
  have h2' := hm 2
  have ha : ∀ g i j, a' g i j = m i / m j * a g i j := by
    intro g i j
    have := hm j
    field_simp
    linear_combination -h1 g i j
  by_cases hd : m 0 * m 2 = m 1 * m 1
  · refine ⟨Units.mk0 (m 0 / m 1) (div_ne_zero h0 h1'), fun g i j => ?_⟩
    rw [ha]
    congr 1
    have e2 : m 2 = m 1 * m 1 / m 0 := by field_simp; linear_combination hd
    fin_cases i <;> fin_cases j <;> simp [wt, wt1, e2, zpow_ofNat, h0, h1'] <;> field_simp
  · obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (m 0 / m 2)
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact div_ne_zero h0 h2' (by simpa using hs)
    have hz : ∀ g i j, (m i * m i.rev - m j * m j.rev) * a g i j = 0 := by
      intro g i j
      linear_combination m i.rev * h1 g i j - m j * h2 g i j
    have hd1 : m 0 * m 2 - m 1 * m 1 ≠ 0 := sub_ne_zero.2 hd
    have hd2 : m 2 * m 0 - m 1 * m 1 ≠ 0 := by rwa [mul_comm (m 2)]
    have hd3 : m 1 * m 1 - m 0 * m 2 ≠ 0 := sub_ne_zero.2 (Ne.symm hd)
    have hd4 : m 1 * m 1 - m 2 * m 0 ≠ 0 := by rwa [mul_comm (m 2)]
    refine ⟨Units.mk0 s hs0, fun g i j => ?_⟩
    have z01 : a g 0 1 = 0 := (mul_eq_zero.1 (hz g 0 1)).resolve_left hd1
    have z21 : a g 2 1 = 0 := (mul_eq_zero.1 (hz g 2 1)).resolve_left hd2
    have z10 : a g 1 0 = 0 := (mul_eq_zero.1 (hz g 1 0)).resolve_left hd3
    have z12 : a g 1 2 = 0 := (mul_eq_zero.1 (hz g 1 2)).resolve_left hd4
    have e0 : m 0 = s * s * m 2 := by rw [← hs]; field_simp
    rw [ha]
    fin_cases i <;> fin_cases j <;>
      simp [wt, wt1, z01, z21, z10, z12, e0, zpow_ofNat, h1', h2', hs0] <;> left <;> field_simp

theorem UpperTheory.V.U3.conjBy_tor_of_iso :
    ∀ {G κ : Type} [Group G] [Field κ] [IsAlgClosed κ] (η : G →* ℤˣ) (r r' : G →* GG 3 κ) (c g₁ : G), (2 : κ) ≠ 0 → HasMult η r → HasMult η r' →
      η c = -1 → η g₁ = 1 → Normalised c g₁ r → Normalised c g₁ r' → zeta c g₁ r ≠ 0 → zeta c g₁ r' ≠ 0 → zeta c g₁ r' ≠ -zeta c g₁ r →
      (TypeI η r ∨ TypeII η r) → MatIso η.ker (mats r) (mats r') → ∃ t : κˣ, r' = conjBy (tor κ t) r := by
  intro G κ _ _ _ η r r' c g₁ h2 hr hr' hc hg hN hN' hz hz' hne _ hiso
  obtain ⟨M, hM⟩ := hiso
  have hstar : ∀ g, η g = 1 → η (gstar c g) = 1 := by
    intro g h
    simp [gstar, hc, h]
  have hZ : (M : Matrix (Fin 3) (Fin 3) κ) * zmat c g₁ r = zmat c g₁ r' * M := by
    have e1 := hM g₁ hg
    have e2 := hM (gstar c g₁) (hstar g₁ hg)
    unfold mats at e1 e2
    rw [zmat, zmat, Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  rw [zmat_diag r c g₁ h2.isUnit ((hr c).trans hc) ((hr g₁).trans hg) hN,
    zmat_diag r' c g₁ h2.isUnit ((hr' c).trans hc) ((hr' g₁).trans hg) hN'] at hZ
  have hoff := offdiag_zero _ _ _ hz hz' hne hZ
  have hdiag : (M : Matrix (Fin 3) (Fin 3) κ) = Matrix.diagonal fun i => M i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  have hm : ∀ i, (M : Matrix (Fin 3) (Fin 3) κ) i i ≠ 0 := by
    have hdet : (M : Matrix (Fin 3) (Fin 3) κ).det ≠ 0 := M.det_ne_zero
    rw [hdiag, Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hdet
    exact fun i => hdet i (Finset.mem_univ i)
  have h1 : ∀ g, η g = 1 → ∀ i j, M i i * (r g).mat i j = (r' g).mat i j * M j j := by
    intro g h i j
    have e := hM g h
    rw [hdiag] at e
    have e' := congrFun (congrFun e i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at e'
  have hJ : ∀ (X : Matrix (Fin 3) (Fin 3) κ) (i j : Fin 3),
      (Jmat κ 3 * Xᵀ * Jmat κ 3) j.rev i.rev = X i j := by
    intro X i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]
  have h2' : ∀ g, η g = 1 → ∀ i j : Fin 3,
      M j.rev j.rev * (r g).mat i j = (r' g).mat i j * M i.rev i.rev := by
    intro g h i j
    have e := h1 _ (hstar g h) j.rev i.rev
    rwa [(mat_gstar r c g hN.atc ((hr c).trans hc) ((hr g).trans h)).1,
      (mat_gstar r' c g hN'.atc ((hr' c).trans hc) ((hr' g).trans h)).1, hJ, hJ] at e
  obtain ⟨t, ht⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator (ι := η.ker) (fun i => M i i) hm (fun g => (r g).mat)
    (fun g => (r' g).mat) (fun g => h1 g g.2) (fun g => h2' g g.2)
  obtain ⟨k1, k2, k3, -⟩ := conjBy_tor r t
  refine ⟨t, ?_⟩
  have hker : ∀ g, η g = 1 → r' g = conjBy (tor κ t) r g := by
    intro g h
    refine SemidirectProduct.ext (Units.ext ?_) (by rw [k2, hr g, hr' g])
    ext i j
    exact (ht ⟨g, h⟩ i j).trans (k1 g i j).symm
  have hcc : r' c = conjBy (tor κ t) r c :=
    SemidirectProduct.ext (Units.ext (hN'.atc.trans (k3 c g₁ hN).atc.symm))
      (by rw [k2, hr c, hr' c])
  refine MonoidHom.ext fun g => ?_
  rcases Int.units_eq_one_or (η g) with h | h
  · exact hker g h
  · have e : g = g * c⁻¹ * c := by simp
    rw [e, map_mul r' _ c, map_mul _ _ c, hcc, hker (g * c⁻¹) (by simp [h, hc])]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.NormEx
section
open Matrix UpperTheory.V.U3

section SlopeTestRemainingChoices

open IsLocalRing

variable {R : Type} [CommRing R]

private theorem quad_root [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (a b c : R)
    (hb : IsUnit b) (hc : residue R c = 0) : ∃ x, residue R x = 0 ∧ a * x ^ 2 + b * x + c = 0 := by
  have hcm : c ∈ maximalIdeal R := (residue_eq_zero_iff c).1 hc
  have hH : HenselianRing R (maximalIdeal R) := inferInstance
  obtain ⟨w, hw, hw'⟩ := hH.is_henselian
    (Polynomial.X ^ 2 + (Polynomial.C b * Polynomial.X + Polynomial.C (a * c)))
    (Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_linear_le (by norm_num))) (-b)
    (by
      have : Polynomial.eval (-b) (Polynomial.X ^ 2 + (Polynomial.C b * Polynomial.X +
          Polynomial.C (a * c))) = a * c := by simp; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hcm)
    (by
      have : Polynomial.eval (-b) (Polynomial.derivative (Polynomial.X ^ 2 +
          (Polynomial.C b * Polynomial.X + Polynomial.C (a * c)))) = -b := by simp; ring
      rw [this]; exact hb.neg.map _)
  have hw0 : w ^ 2 + (b * w + a * c) = 0 := by simpa using hw
  have hwu : IsUnit w := by
    by_contra hn
    have h1 : w ∈ maximalIdeal R := hn
    have h2 : b ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hw' h1
      simpa using this
    exact h2 hb
  obtain ⟨k, hk⟩ := hwu.exists_right_inv
  refine ⟨c * k, by simp [hc], ?_⟩
  linear_combination c * k ^ 2 * hw0 - (c * (w * k + 1) + b * c * k) * hk

private theorem unit_of_res [IsLocalRing R] {x : R} (h : IsUnit (residue R x)) : IsUnit x :=
  (residue_ne_zero_iff_isUnit x).1 h.ne_zero

private theorem stageA (s q p u t v w : R) (hw : w ^ 2 * u = 1) :
    !![1, -q * w ^ 2, 0; 0, w, 0; 0, -t * w ^ 2, 1] * !![s, q, p; q, u, t; p, t, v] *
      (!![1, -q * w ^ 2, 0; 0, w, 0; 0, -t * w ^ 2, 1])ᵀ =
    !![s - q ^ 2 * w ^ 2, 0, p - q * t * w ^ 2; 0, 1, 0; p - q * t * w ^ 2, 0, v - t ^ 2 * w ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind

private theorem stageB (s p v x k e : R) (hx : v * x ^ 2 + 2 * p * x + s = 0)
    (hk : (p + x * v) * k = 1) (he : 2 * e = 1) :
    !![1, 0, x; 0, 1, 0; -k * (v * k * e), 0, k * (1 - v * k * e * x)] * !![s, 0, p; 0, 1, 0; p, 0, v] *
      (!![1, 0, x; 0, 1, 0; -k * (v * k * e), 0, k * (1 - v * k * e * x)])ᵀ = Jmat R 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev] <;> grind

private theorem symm_norm [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (h2 : IsUnit (2 : R))
    (S : Matrix (Fin 3) (Fin 3) R) (hS : Sᵀ = S) (hr : S.map (residue R) = Jmat _ 3) :
    ∃ h : Matrix (Fin 3) (Fin 3) R, h.map (residue R) = 1 ∧ h * S * hᵀ = Jmat R 3 := by
  have hsy : ∀ i j, S j i = S i j := fun i j => congrFun (congrFun hS i) j
  have hre : ∀ i j, residue R (S i j) = Jmat _ 3 i j := fun i j => congrFun (congrFun hr i) j
  obtain ⟨s, q, p, u, t, v, rfl⟩ : ∃ s q p u t v, S = !![s, q, p; q, u, t; p, t, v] := by
    refine ⟨S 0 0, S 0 1, S 0 2, S 1 1, S 1 2, S 2 2, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> exact hsy _ _
  have hs : residue R s = 0 := by simpa [Jmat, Fin.rev] using hre 0 0
  have hq : residue R q = 0 := by simpa [Jmat, Fin.rev] using hre 0 1
  have hp : residue R p = 1 := by simpa [Jmat, Fin.rev] using hre 0 2
  have hu : residue R u = 1 := by simpa [Jmat, Fin.rev] using hre 1 1
  have ht : residue R t = 0 := by simpa [Jmat, Fin.rev] using hre 1 2
  have hv : residue R v = 0 := by simpa [Jmat, Fin.rev] using hre 2 2
  have huu : IsUnit u := unit_of_res (by rw [hu]; exact isUnit_one)
  obtain ⟨e, he⟩ := h2.exists_right_inv
  obtain ⟨y, hy0, hy⟩ := quad_root u (2 * u) (u - 1) (h2.mul huu) (by simp [hu])
  have hw : (1 + y) ^ 2 * u = 1 := by linear_combination hy
  have hw1 : residue R (1 + y) = 1 := by simp [hy0]
  generalize 1 + y = w at hw hw1
  have hA := stageA s q p u t v w hw
  obtain ⟨x, hx0, hx⟩ := quad_root (v - t ^ 2 * w ^ 2) (2 * (p - q * t * w ^ 2)) (s - q ^ 2 * w ^ 2)
    (h2.mul (unit_of_res (by simp [hp, hq]))) (by simp [hs, hq])
  obtain ⟨k, hk⟩ := (unit_of_res (x := (p - q * t * w ^ 2) + x * (v - t ^ 2 * w ^ 2))
    (by simp [hp, hq, hx0])).exists_right_inv
  have hk1 : residue R k = 1 := by simpa [hp, hq, hx0] using congrArg (residue R) hk
  have hB := stageB _ _ _ x k e hx hk he
  refine ⟨_ * _, ?_, by rw [← hB, ← hA, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]; rfl⟩
  rw [Matrix.map_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hq, ht, hv, hw1, hx0, hk1]

private theorem anti_norm [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (h2 : IsUnit (2 : R))
    (a b d : R) (ha : IsUnit a) (hb : residue R b = 0) (hd : residue R d = 0) :
    ∃ h : Matrix (Fin 3) (Fin 3) R, h.map (residue R) = 1 ∧ h * (Jmat R 3 * hᵀ * Jmat R 3) = 1 ∧
      (h * !![a, b, 0; d, 0, -b; 0, -d, -a] * (Jmat R 3 * hᵀ * Jmat R 3)) 0 1 = 0 ∧
      (h * !![a, b, 0; d, 0, -b; 0, -d, -a] * (Jmat R 3 * hᵀ * Jmat R 3)) 1 0 = 0 := by
  obtain ⟨e, he⟩ := h2.exists_right_inv
  obtain ⟨y, hy0, hy⟩ := quad_root (-b * e) a d ha hd
  obtain ⟨k, hk⟩ := (unit_of_res (x := a - b * y) (by simpa [hb] using ha.map (residue R))).exists_right_inv
  obtain ⟨x, hx0, hx⟩ : ∃ x, residue R x = 0 ∧ x * (a - b * y) = b :=
    ⟨b * k, by simp [hb], by linear_combination b * hk⟩
  clear hk
  refine ⟨!![1, x, -x ^ 2 * e; 0, 1, -x; 0, 0, 1] * !![1, 0, 0; y, 1, 0; -y ^ 2 * e, -y, 1], ?_, ?_, ?_, ?_⟩
  · rw [Matrix.map_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hx0, hy0]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev] <;> grind
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]; grind
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]; grind

private theorem conj_left {G : Type} [Group G] {m : ℕ} (h : GL (Fin m) R) (r : G →* GG m R) (g : G) :
    (conjBy h r g).left = h * (r g).left * sgnAct m R (r g).right h⁻¹ := by
  simp [conjBy, SemidirectProduct.mul_left, SemidirectProduct.inv_left]

private theorem conj_right {G : Type} [Group G] {m : ℕ} (h : GL (Fin m) R) (r : G →* GG m R) (g : G) :
    (conjBy h r g).right = (r g).right := by
  simp [conjBy]

private theorem conj_mat_one {G : Type} [Group G] {m : ℕ} (h : GL (Fin m) R) (r : G →* GG m R) (g : G)
    (hg : (r g).right = 1) :
    (conjBy h r g).mat = (h : Matrix _ _ R) * (r g).mat * ((h⁻¹ : GL (Fin m) R) : Matrix _ _ R) := by
  simp only [GG.mat, conj_left, hg, sgnAct_one, Units.val_mul]

private theorem conj_mat_neg {G : Type} [Group G] {m : ℕ} (h : GL (Fin m) R) (r : G →* GG m R) (g : G)
    (hg : (r g).right = -1) :
    (conjBy h r g).mat = (h : Matrix _ _ R) * (r g).mat *
      (Jmat R m * (h : Matrix (Fin m) (Fin m) R)ᵀ * Jmat R m) := by
  simp only [GG.mat, conj_left, hg, sgnAct_neg_one, Units.val_mul, theta_val, inv_inv]

private theorem conj_conj {G : Type} [Group G] {m : ℕ} (h h' : GL (Fin m) R) (r : G →* GG m R) :
    conjBy (h * h') r = conjBy h (conjBy h' r) := by
  ext1 g
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    _root_.mul_inv_rev, mul_assoc, MulAut.mul_apply]

private theorem sym_of_sq {m : ℕ} (x : GG m R) (hx : x * x = 1) (hr : x.right = -1) :
    (x.mat * Jmat R m)ᵀ = x.mat * Jmat R m := by
  have h1 : x.left * theta x.left = 1 := by
    have := congrArg SemidirectProduct.left hx
    simpa [hr] using this
  have h2 : x.left = (theta x.left)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : x.mat = Jmat R m * x.matᵀ * Jmat R m := by
    unfold GG.mat
    rw [← theta_inv_val, ← h2]
  rw [Matrix.transpose_mul, Jmat_transpose]
  conv_rhs => rw [h3, Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]

private theorem anti_shape (M : Matrix (Fin 3) (Fin 3) R) :
    M - Jmat R 3 * Mᵀ * Jmat R 3 = !![M 0 0 - M 2 2, M 0 1 - M 1 2, 0; M 1 0 - M 2 1, 0, -(M 0 1 - M 1 2);
      0, -(M 1 0 - M 2 1), -(M 0 0 - M 2 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

end SlopeTestRemainingChoices

theorem UpperTheory.V.U3.exists_normalised :
    ∀ {G R : Type} [Group G] [CommRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
      (η : G →* ℤˣ) (Ψ : G →* (IsLocalRing.ResidueField R)ˣ) (c g₁ : G) (r : G →* GG 3 R), IsUnit (2 : R) → Marks η Ψ c g₁ →
      (GG.map (IsLocalRing.residue R)).comp r = r0 η Ψ →
    ∃ h : GL (Fin 3) R, CongOne (IsLocalRing.maximalIdeal R) h ∧ Normalised c g₁ (conjBy h r) := by
  intro G R _ _ _ _ η Ψ c g₁ r h2 hM hr
  have hr' : ∀ g, GG.map (IsLocalRing.residue R) (r g) = r0 η Ψ g := fun g => DFunLike.congr_fun hr g
  have hright : ∀ g, (r g).right = η g := fun g => congrArg SemidirectProduct.right (hr' g)
  have hmat : ∀ g, (r g).mat.map (IsLocalRing.residue R) = (tor _ (Ψ g) : Matrix (Fin 3) (Fin 3) _) :=
    fun g => congrArg GG.mat (hr' g)
  have hc : (r c).right = -1 := (hright c).trans hM.ηc
  have hg : (r g₁).right = 1 := (hright g₁).trans hM.ηg
  obtain ⟨H₁, hH₁, hH₁'⟩ := symm_norm h2 ((r c).mat * Jmat R 3)
    (sym_of_sq _ (by rw [← map_mul, hM.csq, map_one]) hc)
    (by rw [Matrix.map_mul, hmat, hM.Ψc, Jmat_map]; simp)
  have e1 : H₁ * (r c).mat * (Jmat R 3 * H₁ᵀ * Jmat R 3) = 1 := by
    rw [← Jmat_mul_Jmat (R := R) 3]
    conv_rhs => rw [← hH₁']
    conv_rhs => enter [2]; rw [hH₁']
    simp only [Matrix.mul_assoc]
  obtain ⟨h₁, rfl⟩ : IsUnit H₁ :=
    IsUnit.of_mul_eq_one _ ((Matrix.mul_assoc _ _ _).symm.trans e1)
  have hi : ((h₁⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map (IsLocalRing.residue R) = 1 := by
    have := congrArg (fun X : Matrix (Fin 3) (Fin 3) R => X.map (IsLocalRing.residue R)) h₁.mul_inv
    simp only [Matrix.map_mul, hH₁, Matrix.one_mul] at this
    simpa using this
  have hc1 : (conjBy h₁ r c).right = -1 := (conj_right _ _ _).trans hc
  have hg1 : (conjBy h₁ r g₁).right = 1 := (conj_right _ _ _).trans hg
  have hcm : (conjBy h₁ r c).mat = 1 := (conj_mat_neg _ _ _ hc).trans e1
  have hgm : (conjBy h₁ r g₁).mat.map (IsLocalRing.residue R) =
      (tor _ (Ψ g₁) : Matrix (Fin 3) (Fin 3) _) := by
    rw [conj_mat_one _ _ _ hg, Matrix.map_mul, Matrix.map_mul, hH₁, hi, hmat]; simp
  obtain ⟨hs, hs'⟩ := mat_gstar (conjBy h₁ r) c g₁ hcm hc1 hg1
  have hcc := fun h => conj_conj h h₁ r
  generalize conjBy h₁ r = r₁ at hc1 hg1 hcm hgm hs hs' hcc
  have hent : ∀ i j, IsLocalRing.residue R ((r₁ g₁).mat i j) = _ := fun i j => congrFun (congrFun hgm i) j
  obtain ⟨H₂, hH₂, e2, z1, z2⟩ := anti_norm h2 ((r₁ g₁).mat 0 0 - (r₁ g₁).mat 2 2)
    ((r₁ g₁).mat 0 1 - (r₁ g₁).mat 1 2) ((r₁ g₁).mat 1 0 - (r₁ g₁).mat 2 1)
    (unit_of_res (by
      have := hM.Ψg.mul (Ψ g₁)⁻¹.isUnit
      rw [map_sub, hent, hent]
      convert this using 1
      simp [tor_val, wt1, sub_mul, pow_two]))
    (by rw [map_sub, hent, hent]; simp [tor_val]) (by rw [map_sub, hent, hent]; simp [tor_val])
  obtain ⟨h₂, rfl⟩ : IsUnit H₂ := IsUnit.of_mul_eq_one _ e2
  have hinv : ((h₂⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      Jmat R 3 * (h₂ : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3 := Units.inv_eq_of_mul_eq_one_right e2
  have hz : zmat c g₁ (conjBy h₂ r₁) = (h₂ : Matrix (Fin 3) (Fin 3) R) *
      ((r₁ g₁).mat - Jmat R 3 * (r₁ g₁).matᵀ * Jmat R 3) *
      (Jmat R 3 * (h₂ : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3) := by
    rw [zmat, conj_mat_one _ _ _ hg1, conj_mat_one _ _ _ hs', hs, hinv, Matrix.mul_sub, Matrix.sub_mul]
  rw [anti_shape] at hz
  refine ⟨h₂ * h₁, ?_, ?_⟩
  · intro a b
    rw [← IsLocalRing.residue_eq_zero_iff]
    have : ((h₂ * h₁ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map (IsLocalRing.residue R) = 1 := by
      rw [Units.val_mul, Matrix.map_mul, hH₁, hH₂, Matrix.one_mul]
    have h' := congrFun (congrFun this a) b
    rw [Matrix.map_apply] at h'
    rw [Matrix.sub_apply, map_sub, h']
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · rw [hcc]
    exact ⟨by rw [conj_mat_neg _ _ _ hc1, hcm, Matrix.mul_one, e2], hz ▸ z1, hz ▸ z2⟩
end

