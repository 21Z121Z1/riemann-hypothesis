import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianBlockDiagonal
section
private lemma ad_mul {S : Type} [CommRing S] (τ : S →+* S) {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) S) (B : Matrix (Fin b) (Fin c) S) :
    ((A * B).map τ).transpose = (B.map τ).transpose * (A.map τ).transpose := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

private lemma ad_add {S : Type} [CommRing S] (τ : S →+* S) {a b : ℕ}
    (A B : Matrix (Fin a) (Fin b) S) :
    ((A + B).map τ).transpose = (A.map τ).transpose + (B.map τ).transpose := by
  ext i j
  simp

private lemma ad_ad {S : Type} [CommRing S] (τ : S →+* S) (hτ : ∀ x, τ (τ x) = x) {a b : ℕ}
    (A : Matrix (Fin a) (Fin b) S) :
    (((A.map τ).transpose).map τ).transpose = A := by
  ext i j
  simp [hτ]

private lemma ad_one {S : Type} [CommRing S] (τ : S →+* S) {a : ℕ} :
    (((1 : Matrix (Fin a) (Fin a) S)).map τ).transpose = 1 := by
  rw [Matrix.map_one τ (map_zero τ) (map_one τ), Matrix.transpose_one]

private lemma ad_diag_mul {S : Type} [CommRing S] (τ : S →+* S) {r : ℕ} (u v : Fin r → S)
    (h : ∀ i, τ (u i) * v i = 1) :
    ((Matrix.diagonal u).map τ).transpose * Matrix.diagonal v = 1 := by
  rw [Matrix.diagonal_map (map_zero τ), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact h i

theorem UpperTheory.hermitian_block_diagonal :
    ∀ {S : Type} [CommRing S] (τ : S →+* S), (∀ x, τ (τ x) = x) → ∀ {n r : ℕ}
        (J g P m : Matrix (Fin n) (Fin n) S) (X Y : Matrix (Fin n) (Fin r) S)
        (C : Matrix (Fin r) (Fin r) S) (Xd Yd : Matrix (Fin r) (Fin n) S) (d e : Fin r → S),
        (J.map τ).transpose = J → IsUnit J.det →
        Xd = (X.map τ).transpose * J → Yd = (Y.map τ).transpose * J →
        Xd * X = 0 → Yd * Y = 0 → Xd * Y = 1 →
        (g.map τ).transpose * J * g = J →
        Xd * g = C * Xd →
        (∀ i, τ (e i) * d i = 1) →
        P = 1 - X * Yd - Y * Xd →
        m = (X * Matrix.diagonal d) * Yd + (Y * Matrix.diagonal e) * Xd + P * g * P →
        IsUnit m.det ∧ (m.map τ).transpose * J * m = J ∧
          m * X = X * Matrix.diagonal d ∧ m * Y = Y * Matrix.diagonal e := by
  intro S _ τ hτ n r J g P m X Y C Xd Yd d e hJ hdet hXd hYd hXX hYY hXY hg hC hde hP hm
  have adXd : (Xd.map τ).transpose = J * X := by rw [hXd, ad_mul, hJ, ad_ad τ hτ]
  have adYd : (Yd.map τ).transpose = J * Y := by rw [hYd, ad_mul, hJ, ad_ad τ hτ]
  have hYX : Yd * X = 1 := by
    have h := congrArg (fun A => (A.map τ).transpose) hXY
    simp only [ad_mul, adXd, ad_one] at h
    rw [hYd, Matrix.mul_assoc, h]
  have hed : ((Matrix.diagonal e).map τ).transpose * Matrix.diagonal d = 1 :=
    ad_diag_mul τ e d hde
  have hdeD : ((Matrix.diagonal d).map τ).transpose * Matrix.diagonal e = 1 :=
    ad_diag_mul τ d e (fun i => by
      have h := congrArg τ (hde i)
      rw [map_mul, hτ, map_one, mul_comm] at h
      exact h)
  have XX : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Xd * (X * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have YY : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Yd * (Y * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, hYY, Matrix.zero_mul]
  have XY : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Xd * (Y * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have YX : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), Yd * (X * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hYX, Matrix.one_mul]
  have PX : P * X = 0 := by
    rw [hP]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hYX, hXX, Matrix.mul_one,
      Matrix.mul_zero, sub_self, sub_zero]
  have PY : P * Y = 0 := by
    rw [hP]
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hYY, hXY, Matrix.mul_one,
      Matrix.mul_zero, sub_zero, sub_self]
  have XdP : Xd * P = 0 := by
    rw [hP]
    simp only [Matrix.mul_sub, Matrix.mul_one, XX, XY, sub_zero, sub_self]
  have YdP : Yd * P = 0 := by
    rw [hP]
    simp only [Matrix.mul_sub, Matrix.mul_one, YX, YY, sub_zero, sub_self]
  have PP : P * P = P := by
    calc P * P = (1 - X * Yd - Y * Xd) * P := by rw [← hP]
      _ = P := by
        simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, YdP, XdP, Matrix.mul_zero,
          sub_zero]
  have PX' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), P * (X * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, PX, Matrix.zero_mul]
  have PY' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S), P * (Y * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, PY, Matrix.zero_mul]
  have XdP' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), Xd * (P * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, XdP, Matrix.zero_mul]
  have YdP' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), Yd * (P * A) = 0 := fun A => by
    rw [← Matrix.mul_assoc, YdP, Matrix.zero_mul]
  have PP' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), P * (P * A) = P * A := fun A => by
    rw [← Matrix.mul_assoc, PP]
  have hed' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S),
      ((Matrix.diagonal e).map τ).transpose * (Matrix.diagonal d * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hed, Matrix.one_mul]
  have hde' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S),
      ((Matrix.diagonal d).map τ).transpose * (Matrix.diagonal e * A) = A := fun A => by
    rw [← Matrix.mul_assoc, hdeD, Matrix.one_mul]
  have hmX : m * X = X * Matrix.diagonal d := by
    rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hYX, hXX, PX, Matrix.mul_one, Matrix.mul_zero,
      add_zero]
  have hmY : m * Y = Y * Matrix.diagonal e := by
    rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hYY, hXY, PY, Matrix.mul_one, Matrix.mul_zero,
      add_zero, zero_add]
  have hPJ : (P.map τ).transpose * J = J * P := by
    have hPe : P + X * Yd + Y * Xd = 1 := by rw [hP]; abel
    have h := congrArg (fun A => (A.map τ).transpose) hPe
    simp only [ad_add, ad_mul, adXd, adYd, ad_one] at h
    have h2 : (P.map τ).transpose = 1 - (J * Y) * (X.map τ).transpose
        - (J * X) * (Y.map τ).transpose := by
      rw [← h]; abel
    rw [h2, hP]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
      ← hXd, ← hYd]
    abel
  have hPJ' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S),
      (P.map τ).transpose * (J * A) = J * (P * A) := fun A => by
    rw [← Matrix.mul_assoc, hPJ, Matrix.mul_assoc]
  have hg' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S),
      (g.map τ).transpose * (J * (g * A)) = J * A := fun A => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg]
  have hgX : (g.map τ).transpose * (J * X) = J * (X * (C.map τ).transpose) := by
    have h := congrArg (fun A => (A.map τ).transpose) hC
    simp only [ad_mul, adXd] at h
    rw [h, Matrix.mul_assoc]
  have hgX' : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) S),
      (g.map τ).transpose * (J * (X * A)) = J * (X * ((C.map τ).transpose * A)) := fun A => by
    rw [← Matrix.mul_assoc J X A, ← Matrix.mul_assoc, hgX]
    simp only [Matrix.mul_assoc]
  have hC' : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S), Xd * (g * A) = C * (Xd * A) := fun A => by
    rw [← Matrix.mul_assoc, hC, Matrix.mul_assoc]
  have hmid : (g.map τ).transpose * (J * (P * (g * P))) =
      J * P - J * (X * ((C.map τ).transpose * (Yd * (g * P)))) := by
    have hexp : ∀ {k : ℕ} (A : Matrix (Fin n) (Fin k) S),
        P * A = A - X * (Yd * A) - Y * (Xd * A) := fun A => by
      rw [hP]
      simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [hexp (g * P)]
    simp only [Matrix.mul_sub, hg', hgX', hC', XdP, Matrix.mul_zero, sub_zero]
  have hadm : (m.map τ).transpose =
      (J * Y) * (((Matrix.diagonal d).map τ).transpose * (X.map τ).transpose)
        + (J * X) * (((Matrix.diagonal e).map τ).transpose * (Y.map τ).transpose)
        + (P.map τ).transpose * ((g.map τ).transpose * (P.map τ).transpose) := by
    rw [hm]
    simp only [ad_add, ad_mul, adXd, adYd, Matrix.mul_assoc]
  have hiso : (m.map τ).transpose * J * m = J := by
    have hmJ : (m.map τ).transpose * J =
        J * (Y * (((Matrix.diagonal d).map τ).transpose * Xd))
          + J * (X * (((Matrix.diagonal e).map τ).transpose * Yd))
          + (P.map τ).transpose * ((g.map τ).transpose * (J * P)) := by
      rw [hadm, hXd, hYd]
      simp only [Matrix.add_mul, Matrix.mul_assoc, hPJ]
    rw [hmJ]
    conv_lhs => rw [hm]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, XX, XY, YX, YY, XdP', YdP',
      PX', PY', PP', XdP, YdP, hed', hde', Matrix.mul_zero, add_zero, zero_add, hmid,
      Matrix.mul_sub, hPJ', PP]
    conv_rhs => rw [show J = J * (1 : Matrix (Fin n) (Fin n) S) from (Matrix.mul_one J).symm]
    rw [show (1 : Matrix (Fin n) (Fin n) S) = P + X * Yd + Y * Xd by rw [hP]; abel]
    simp only [Matrix.mul_add]
    abel
  refine ⟨?_, hiso, hmX, hmY⟩
  have h := congrArg Matrix.det hiso
  rw [Matrix.det_mul] at h
  rw [← h] at hdet
  exact isUnit_of_mul_isUnit_right hdet
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianBlockTriangular
section
theorem UpperTheory.hermitian_block_triangular :
    ∀ {S : Type} [CommRing S] (τ : S →+* S), (∀ x, τ (τ x) = x) → ∀ {n r : ℕ}
        (J g : Matrix (Fin n) (Fin n) S) (X Y : Matrix (Fin n) (Fin r) S)
        (B : Matrix (Fin r) (Fin r) S) (Xd Yd : Matrix (Fin r) (Fin n) S),
        (J.map τ).transpose = J →
        Xd = (X.map τ).transpose * J → Yd = (Y.map τ).transpose * J →
        Xd * Y = 1 →
        (g.map τ).transpose * J * g = J →
        B.BlockTriangular id → g * X = X * B →
        Yd * X = 1 ∧ Yd * g * X = B ∧ Xd * g = (Xd * g * Y) * Xd ∧
          ∀ i, τ ((Xd * g * Y) i i) * B i i = 1 := by
  intro S _ τ hτ n r J g X Y B Xd Yd hJ hXd hYd hXY hg hB hgX
  classical
  have star_mul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) S) (Q : Matrix (Fin b) (Fin c) S),
      ((P * Q).map τ).transpose = (Q.map τ).transpose * (P.map τ).transpose := by
    intro a b c P Q
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have star_star : ∀ {a b : ℕ} (P : Matrix (Fin a) (Fin b) S),
      (((P.map τ).transpose).map τ).transpose = P := by
    intro a b P
    ext i j
    simp [hτ]
  have star_one : (((1 : Matrix (Fin r) (Fin r) S)).map τ).transpose = 1 := by
    rw [Matrix.map_one τ (map_zero τ) (map_one τ), Matrix.transpose_one]
  have h1 : Yd * X = 1 := by
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) S => (M.map τ).transpose) hXY
    simp only [star_one] at h
    rw [star_mul, hXd, star_mul, star_star, hJ, ← Matrix.mul_assoc, ← hYd] at h
    exact h
  have h2 : Yd * g * X = B := by
    rw [Matrix.mul_assoc, hgX, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hs : (X.map τ).transpose * (g.map τ).transpose
      = (B.map τ).transpose * (X.map τ).transpose := by
    rw [← star_mul, ← star_mul, hgX]
  have hD : (B.map τ).transpose * (Xd * g) = Xd := by
    calc (B.map τ).transpose * (Xd * g)
        = ((B.map τ).transpose * (X.map τ).transpose) * J * g := by
          rw [hXd]; simp only [Matrix.mul_assoc]
      _ = (X.map τ).transpose * ((g.map τ).transpose * J * g) := by
          rw [← hs]; simp only [Matrix.mul_assoc]
      _ = Xd := by rw [hg, hXd]
  have hC : (B.map τ).transpose * (Xd * g * Y) = 1 := by
    rw [← Matrix.mul_assoc, hD, hXY]
  have hC' : (Xd * g * Y) * (B.map τ).transpose = 1 := mul_eq_one_comm.mp hC
  have h3 : Xd * g = (Xd * g * Y) * Xd := by
    calc Xd * g = ((Xd * g * Y) * (B.map τ).transpose) * (Xd * g) := by
          rw [hC', Matrix.one_mul]
      _ = (Xd * g * Y) * ((B.map τ).transpose * (Xd * g)) := by rw [Matrix.mul_assoc]
      _ = (Xd * g * Y) * Xd := by rw [hD]
  have h4 : ((Xd * g * Y).map τ).transpose * B = 1 := by
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) S => (M.map τ).transpose) hC
    simp only [star_one] at h
    rwa [star_mul, star_star] at h
  refine ⟨h1, h2, h3, fun i => ?_⟩
  letI : Invertible B := invertibleOfLeftInverse B _ h4
  have hinv : (B⁻¹) = ((Xd * g * Y).map τ).transpose := Matrix.inv_eq_left_inv h4
  have htri : (B⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  have h5 := congrFun (congrFun h4 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h5
  · simpa only [Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq] using h5
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have : (B⁻¹) i k = 0 := htri hlt
      rw [hinv] at this
      rw [this, zero_mul]
    · have : B k i = 0 := hB hgt
      rw [this, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianDiagonalisation
section
open Matrix in

private def Dz {E ι : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι E) : Prop :=
  ∃ g : Matrix ι ι E, g.det ≠ 0 ∧ ∃ D : ι → E, gᴴ * T * g = diagonal D

open Matrix in
private theorem Dz.of_submatrix {E ι κ : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {T : Matrix κ κ E}
    (h : Dz (T.submatrix e e)) : Dz T := by
  obtain ⟨g, hg, D, hD⟩ := h
  refine ⟨g.submatrix e.symm e.symm, ?_, D ∘ e.symm, ?_⟩
  · rw [det_submatrix_equiv_self]; exact hg
  · have h1 : (g.submatrix e.symm e.symm)ᴴ * T * g.submatrix e.symm e.symm
        = (gᴴ * T.submatrix e e * g).submatrix e.symm e.symm := by
      rw [← submatrix_mul_equiv _ _ _ e.symm _, ← submatrix_mul_equiv _ _ _ e.symm _]
      simp [conjTranspose_submatrix]
    rw [h1, hD]
    ext a b
    simp [diagonal_apply]

open Matrix in
private theorem Dz.of_congr {E ι : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    {T P : Matrix ι ι E} (hP : P.det ≠ 0) (h : Dz (Pᴴ * T * P)) : Dz T := by
  obtain ⟨g, hg, D, hD⟩ := h
  refine ⟨P * g, ?_, D, ?_⟩
  · rw [det_mul]; exact mul_ne_zero hP hg
  · rw [← hD, conjTranspose_mul]; simp only [Matrix.mul_assoc]

open Matrix in
private theorem Dz.sum {E A B : Type} [Field E] [StarRing E] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (hA : ∀ X : Matrix A A E, X.IsHermitian → Dz X)
    (hB : ∀ X : Matrix B B E, X.IsHermitian → Dz X)
    (T : Matrix (A ⊕ B) (A ⊕ B) E) (hT : T.IsHermitian) (hdet : T.toBlocks₁₁.det ≠ 0) :
    Dz T := by
  obtain ⟨X, Y, Z, W, rfl⟩ : ∃ X Y Z W, T = fromBlocks X Y Z W :=
    ⟨_, _, _, _, (fromBlocks_toBlocks T).symm⟩
  rw [toBlocks_fromBlocks₁₁] at hdet
  obtain ⟨h1, h2, h3, h4⟩ := (isHermitian_fromBlocks_iff).1 hT
  have hu : IsUnit X.det := isUnit_iff_ne_zero.2 hdet
  have hXX : X * X⁻¹ = 1 := mul_nonsing_inv X hu
  have hXi : X⁻¹ᴴ = X⁻¹ := by rw [conjTranspose_nonsing_inv, h1.eq]
  have hZ : Yᴴ = Z := h2
  subst hZ
  set U : Matrix (A ⊕ B) (A ⊕ B) E := fromBlocks 1 (-(X⁻¹ * Y)) 0 1 with hU
  have hUdet : U.det ≠ 0 := by
    rw [hU, det_fromBlocks_zero₂₁]; simp
  set S : Matrix B B E := W - Yᴴ * X⁻¹ * Y with hS
  have hSH : S.IsHermitian := by
    rw [IsHermitian, hS, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, hXi, h4.eq, Matrix.mul_assoc]
  have key : Uᴴ * fromBlocks X Y Yᴴ W * U = fromBlocks X 0 0 S := by
    rw [hU, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [conjTranspose_one, conjTranspose_zero, conjTranspose_neg, conjTranspose_mul, hXi,
      h1.eq]
    have hXX' : X⁻¹ * X = 1 := nonsing_inv_mul X hu
    congr 1
    · simp
    · have hY : X * (X⁻¹ * Y) = Y := by rw [← Matrix.mul_assoc, hXX, Matrix.one_mul]
      simp [hY]
    · simp [Matrix.mul_assoc, hXX']
    · simp [Matrix.mul_assoc, hXX, hXX', hS, Matrix.add_mul, Matrix.mul_add]
      abel
  refine Dz.of_congr hUdet ?_
  rw [key]
  obtain ⟨gA, hgA, DA, hDA⟩ := hA X h1
  obtain ⟨gB, hgB, DB, hDB⟩ := hB S hSH
  refine ⟨fromBlocks gA 0 0 gB, ?_, Sum.elim DA DB, ?_⟩
  · rw [det_fromBlocks_zero₂₁]; exact mul_ne_zero hgA hgB
  · rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_diagonal]
    simp [hDA, hDB]

open Matrix in
private theorem Dz.pivot {E ι : Type} [Field E] [StarRing E] [Fintype ι] [DecidableEq ι]
    (ih : ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ < Fintype.card ι →
      ∀ X : Matrix κ κ E, X.IsHermitian → Dz X)
    (T : Matrix ι ι E) (hT : T.IsHermitian) (i : ι) (hi : T i i ≠ 0) : Dz T := by
  let e : {a // a = i} ⊕ {a // ¬ a = i} ≃ ι := Equiv.sumCompl _
  refine Dz.of_submatrix e ?_
  refine Dz.sum ?_ (ih _ ?_) _ (hT.submatrix e) ?_
  · intro X _
    refine ⟨1, by simp, fun a => X a a, ?_⟩
    ext a b
    have : a = b := Subsingleton.elim _ _
    subst this
    simp
  · exact Fintype.card_subtype_lt (x := i) (by simp)
  · have : Unique {a // a = i} := ⟨⟨⟨i, rfl⟩⟩, fun a => Subtype.ext a.2⟩
    rw [det_unique]
    have hdef : (((default : {a // a = i})) : ι) = i := (default : {a // a = i}).2
    simpa [e, toBlocks₁₁, hdef] using hi

open Matrix in
private theorem Dz.all {E : Type} [Field E] [StarRing E] [CharZero E] :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
      ∀ T : Matrix ι ι E, T.IsHermitian → Dz T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ _ hcard T hT
  have ih : ∀ (κ : Type) [Fintype κ] [DecidableEq κ], Fintype.card κ < Fintype.card ι →
      ∀ X : Matrix κ κ E, X.IsHermitian → Dz X :=
    fun κ _ _ h X hX => IH _ (hcard ▸ h) κ rfl X hX
  by_cases hd : ∃ i, T i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    exact Dz.pivot ih T hT i hi
  push_neg at hd
  by_cases h0 : T = 0
  · subst h0
    exact ⟨1, by simp, 0, by simp⟩
  obtain ⟨i, j, hij⟩ : ∃ i j, T i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (by ext a b; simpa using hc a b)
  have hne : j ≠ i := by
    rintro rfl
    exact hij (hd _)
  set c := (T i j)⁻¹ with hc
  set P : Matrix ι ι E := 1 + single j i c with hP
  have hPdet : P.det ≠ 0 := by
    have : P = transvection j i c := rfl
    rw [this, det_transvection_of_ne _ _ hne]
    exact one_ne_zero
  have hji : T j i = star (T i j) := (hT.apply j i).symm
  have hval : (Pᴴ * T * P) i i = 2 := by
    have hPH : Pᴴ = 1 + single i j (star c) := by
      rw [hP, conjTranspose_add, conjTranspose_one, conjTranspose_single]
    rw [hPH, hP]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.add_apply,
      Matrix.mul_assoc, single_mul_apply_same, mul_single_apply_same]
    have h1 : T i j * c = 1 := mul_inv_cancel₀ hij
    have h2 : star c * T j i = 1 := by
      rw [hji, ← star_mul', mul_comm, h1, star_one]
    rw [h1, h2, hd i, hd j]
    norm_num
  refine Dz.of_congr hPdet (Dz.pivot ?_ _ ?_ i ?_)
  · exact ih
  · exact isHermitian_conjTranspose_mul_mul P hT
  · rw [hval]; exact two_ne_zero

theorem UpperTheory.hermitian_diagonalisation :
    ∀ {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → (∀ x, σ x = x → x ∈ (algebraMap F E).range) → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), (∀ i j, σ (T j i) = T i j) → T.det ≠ 0 → ∃ (g : GL (Fin n) E) (D : Fin n → Fˣ), Matrix.transpose ((g : Matrix (Fin n) (Fin n) E).map σ) * T * (g : Matrix (Fin n) (Fin n) E) = Matrix.diagonal fun i => algebraMap F E (D i : F) := by
  intro F E _ _ _ _ σ hσ hfix n T hT hdet
  letI : StarRing E :=
    { star := σ
      star_involutive := hσ
      star_mul := fun a b => by
        show σ (a * b) = σ b * σ a
        rw [map_mul, mul_comm]
      star_add := map_add σ }
  have hstar : ∀ x : E, star x = σ x := fun _ => rfl
  have hH : T.IsHermitian := by
    ext i j
    exact hT i j
  obtain ⟨g, hg, D, hD⟩ := Dz.all n (Fin n) (by simp) T hH
  have hct : Matrix.transpose (g.map σ) = Matrix.conjTranspose g := rfl
  have hDH : (Matrix.diagonal D).IsHermitian := by
    rw [← hD]
    have := Matrix.isHermitian_conjTranspose_mul_mul g hH
    exact this
  have hfixD : ∀ i, σ (D i) = D i := by
    intro i
    have := hDH.apply i i
    simpa [hstar] using this
  have hdD : ∀ i, D i ≠ 0 := by
    intro i h0
    have h1 : (Matrix.diagonal D).det = 0 := by
      rw [Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [← hD, Matrix.det_mul, Matrix.det_mul] at h1
    have h2 : (Matrix.conjTranspose g).det ≠ 0 := by
      rw [Matrix.det_conjTranspose]
      intro h3
      exact hg (by simpa using h3)
    exact mul_ne_zero (mul_ne_zero h2 hdet) hg h1
  choose d hd using fun i => hfix (D i) (hfixD i)
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h0
    apply hdD i
    rw [← hd, h0, map_zero]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hg, fun i => Units.mk0 (d i) (hd0 i), ?_⟩
  have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero g hg : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) = g := rfl
  rw [hcoe, hct, hD]
  congr 1
  ext i
  simp [hd]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HoExistsPrime
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj17.Pl :
    Type :=
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)

theorem UpperTheory.Reformulated.B.Qj17.ho_exists_prime :
    ∀ (v : UpperTheory.Reformulated.B.Qj17.Pl) (n : ℕ),
      n ≠ (0 : ℕ) →
        (↑n : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal →
          ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  intro v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    rw [Nat.cast_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro h0 h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul h0) h
      exact ⟨p, hp, hd.mul_right b, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul h0) h
      exact ⟨p, hp, hd.mul_left a, hm⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomologyFiniteShortExact
section
open CategoryTheory

namespace UpperTheory

universe v u w

private lemma finite_middle {R : Type u} [Ring R] {M₁ M₂ M₃ : Type v}
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (h : Function.Exact f g)
    [IsNoetherianRing R] [Module.Finite R M₁] [Module.Finite R M₃] :
    Module.Finite R M₂ := by
  have hk : Module.Finite R (LinearMap.ker g) := by
    rw [LinearMap.exact_iff.1 h]
    exact Module.Finite.range f
  have : IsNoetherian R M₃ := isNoetherian_of_isNoetherianRing_of_finite R M₃
  have hq : Module.Finite R (M₂ ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

theorem homology_finite_short_exact {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)} (hS : S.ShortExact) (i : ι) :
    (Finite (S.X₁.homology i) → Finite (S.X₃.homology i) → Finite (S.X₂.homology i)) ∧
    (IsNoetherianRing R → Module.Finite R (S.X₁.homology i) →
      Module.Finite R (S.X₃.homology i) → Module.Finite R (S.X₂.homology i)) := by
  have hE := hS.homology_exact₂ i
  refine ⟨fun h₁ h₃ ↦ ?_, fun _ h₁ h₃ ↦ ?_⟩
  · exact AddCommGrpCat.isFinite.prop_X₂_of_exact
      (hE.map (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})) h₁ h₃
  · exact finite_middle _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hE)

end UpperTheory
end

