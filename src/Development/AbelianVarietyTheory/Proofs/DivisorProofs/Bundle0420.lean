import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0394
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFracOfAdjoinEqTop

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegRel
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

def SiegRel {g n L : ℕ} {B : Type} [CommRing B] {ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp R} {sc : S ⟶ Sp B}
    (f : (Fin g ⊕ Fin g → ℤ) →ₗ[ℤ] D.La) (k d : ℕ) (o : Obj b L s) (c : SiegPre g n ζ sc) : Prop :=
  ∃ (χ : o.A ⟶ c.A) (χ' : c.A ⟶ o.A), IsMonHom χ ∧ IsMonHom χ' ∧ χ ≫ χ' = (𝟙 o.A) ^ k ∧
    χ' ≫ χ = (𝟙 c.A) ^ k ∧ LBIso (c.P.pull (χ ⊗ₘ χ).left) (lbPow o.P k) ∧
    (∀ a, c.lev a = (o.eta (f a) ^ d) ≫ χ) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : D.La),
      toUnit (Over.mk x) ≫ ((o.eta y ^ (d * n)) ≫ χ) = 1 ↔ ∃ a, y = f a

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainCoboundaryOfClassZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

namespace GlobalTheory.CechOne

theorem cobd_of_isCls_zero : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (s : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F), IsCls s (0 : H R E F ((1 : ℕ) : ℤ)) → ∃ t : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, s = cobd t := by
  intro R _ F E s hs
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, hz0, hz⟩ := hs
  rw [CohomologyClass.mk_eq_zero_iff] at hz0
  obtain ⟨m, hm, β, hβ⟩ := hz0
  obtain rfl : m = 0 := by push_cast at hm; omega
  have hzv : ∀ (p q : ℤ) (hpq : p + ((1 : ℕ) : ℤ) = q),
      (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)).v p q hpq =
        (Cochain.single (p := -((1 : ℕ) : ℤ)) (q := 0)
          ((chainsXIso R E 1).hom ≫ s ≫ resι R F) ((1 : ℕ) : ℤ)).v p q hpq := by
    intro p q hpq
    rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)) = z.1 from rfl, hz]
  let b := β.v 0 0 (by omega)
  have hb : b ≫ (res R F).d 0 1 = 0 := by
    have e := Cochain.congr_v hβ 0 1 (by norm_num)
    rw [δ_v 0 _ (by norm_num) β 0 1 _ 0 1 (by omega) rfl,
      (hpos E 1 (by norm_num)).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero, hzv,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)] at e
    exact e
  haveI : Mono (ShortComplex.mk _ _ w).f := hmono
  let t' : ((chains R).obj E).X 0 ⟶ F := hex.lift b hb
  have ht' : t' ≫ resι R F = b := hex.lift_f b hb
  have e := Cochain.congr_v hβ (-((1 : ℕ) : ℤ)) 0 (by omega)
  have h1 : β.v (-((1 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
  rw [δ_v 0 _ (by norm_num) β _ 0 _ (-1) 0 (by omega) (by norm_num), h1,
    zero_comp, zero_add, hzv, Cochain.single_v] at e
  rw [show β.v 0 0 (by omega) = b from rfl, ← ht'] at e
  let D : (free R).obj (E.obj (op ⦋1⦌)) ⟶ (free R).obj (E.obj (op ⦋0⦌)) :=
    ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)
  have hd : ((chains R).obj E).d (-((1 : ℕ) : ℤ)) 0 = (chainsXIso R E 1).hom ≫ D ≫ (chainsXIso R E 0).inv :=
    GlobalTheory.EtC.ClsBasic.chains_d (R := R) E 0
  rw [hd] at e
  have hs : s = (((1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E 0).inv ≫ t') := by
    apply (cancel_epi (chainsXIso R E 1).hom).1
    apply (cancel_mono (resι R F)).1
    rw [Category.assoc, ← e]
    simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  refine ⟨(((1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E 0).inv ≫ t'), ?_⟩
  rw [hs]
  simp only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum,
    smul_smul, Category.assoc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

end GlobalTheory.CechOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveEtaleLocallyHasSections
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smooth_surjective_loc_sections : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f] (U : Scheme.{0}) (y : U ⟶ X), Loc U fun V g => ∃ x : V ⟶ Y, x ≫ f = g ≫ y := by
  intro Y X f _ _ U y
  refine (loc_iff_etale_affine_points U (fun V g => ∃ x : V ⟶ Y, x ≫ f = g ≫ y) ?_).2 ?_
  · rintro V W g k ⟨x, hx⟩
    exact ⟨k ≫ x, by simp [Category.assoc, hx]⟩
  · intro u
    obtain ⟨V, s, hE, hu⟩ := GlobalTheory.T.exists_etale_quasiSection_of_smooth_scheme_hom f (y u) (f.surjective (y u))
    obtain ⟨v, hv⟩ := hu
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback v u hv
    let W := pullback (s ≫ f) y
    obtain ⟨z, hz⟩ := W.affineCover.covers w
    haveI := hE
    have hEt : Etale (pullback.snd (s ≫ f) y) := inferInstance
    refine ⟨_, W.affineCover.f (W.affineCover.idx w) ≫ pullback.snd (s ≫ f) y, inferInstance, inferInstance, ⟨z, ?_⟩, ?_⟩
    · simp [hz, hw2]
    · refine ⟨W.affineCover.f (W.affineCover.idx w) ≫ pullback.fst (s ≫ f) y ≫ s, ?_⟩
      simp only [Category.assoc]
      rw [show pullback.fst (s ≫ f) y ≫ s ≫ f = pullback.snd (s ≫ f) y ≫ y from pullback.condition]

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulInvMulPosSemidefUniformBound
section
open scoped ComplexOrder Matrix

namespace GlobalTheory

namespace WeightedInverseBound

theorem wls_fintype {ι : Type} [Fintype ι] [DecidableEq ι] {g : ℕ} (L : Matrix ι (Fin g) ℝ)
    (hL : L.rank = g) : ∃ K : ℝ, ∀ (D : ι → ℝ) (b : ι → ℝ), (∀ k, 0 < D k) →
      ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖
        ≤ K * ‖b‖ := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hr : (L.submatrix e (Equiv.refl (Fin g))).rank = g := by
    rw [Matrix.rank_submatrix]; exact hL
  obtain ⟨K, hK⟩ := GlobalTheory.T.exists_norm_weighted_least_squares_le _ g _ hr
  refine ⟨K, fun D b hD => ?_⟩
  have h := hK (D ∘ e) (b ∘ e) (fun k => hD _)
  have h1 : (L.submatrix e (Equiv.refl (Fin g))).transpose * Matrix.diagonal (D ∘ e) *
      (L.submatrix e (Equiv.refl (Fin g))) = L.transpose * Matrix.diagonal D * L := by
    ext i j
    simp only [Matrix.mul_apply (M := _ * Matrix.diagonal _), Matrix.mul_diagonal,
      Matrix.transpose_apply, Matrix.submatrix_apply, Equiv.refl_apply, Function.comp]
    exact e.sum_comp (fun k => L k i * D k * L k j)
  have h2 : ((L.submatrix e (Equiv.refl (Fin g))).transpose * Matrix.diagonal (D ∘ e)).mulVec
      (b ∘ e) = (L.transpose * Matrix.diagonal D).mulVec b := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal,
      Matrix.transpose_apply, Matrix.submatrix_apply, Equiv.refl_apply, Function.comp]
    exact e.sum_comp (fun k => L k i * D k * b k)
  have h3 : ‖b ∘ e‖ = ‖b‖ := e.surjective.pi_norm_comp b
  rw [h1, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, h2, h3] at h
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  exact h

theorem dot_le_card_mul_norm_mul_norm {g : ℕ} (x y : Fin g → ℝ) : x ⬝ᵥ y ≤ g * (‖x‖ * ‖y‖) := by
  calc x ⬝ᵥ y = ∑ k, x k * y k := rfl
    _ ≤ ∑ _k : Fin g, ‖x‖ * ‖y‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        exact mul_le_mul (norm_le_pi_norm x k) (norm_le_pi_norm y k) (abs_nonneg _)
          (norm_nonneg _)
    _ = g * (‖x‖ * ‖y‖) := by simp

theorem norm_sq_le_dot {g : ℕ} (x : Fin g → ℝ) : ‖x‖ * ‖x‖ ≤ x ⬝ᵥ x := by
  have h0 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have : ‖x‖ ≤ Real.sqrt (x ⬝ᵥ x) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun k => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    rw [sq]
    exact Finset.single_le_sum (f := fun k => x k * x k) (fun k _ => mul_self_nonneg _)
      (Finset.mem_univ k)
  calc ‖x‖ * ‖x‖ ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (x ⬝ᵥ x) :=
        mul_le_mul this this (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = x ⬝ᵥ x := Real.mul_self_sqrt h0

theorem norm_le_of_coercive {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y.mulVec x) (z : Fin g → ℝ) :
    ‖z‖ ≤ g / c * ‖Y.mulVec z‖ := by
  rcases (norm_nonneg z).eq_or_lt with h | h
  · rw [← h]; positivity
  have h1 := hY z
  have h2 := dot_le_card_mul_norm_mul_norm z (Y.mulVec z)
  have h3 := norm_sq_le_dot z
  have h4 : ‖z‖ * (c * ‖z‖) ≤ ‖z‖ * (g * ‖Y.mulVec z‖) := by nlinarith
  have h5 := le_of_mul_le_mul_left h4 h
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith

theorem isUnit_det_of_coercive {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y.mulVec x) : IsUnit Y.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h := norm_le_of_coercive hc hY (x - y)
  rw [Matrix.mulVec_sub, hxy, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

theorem norm_mulVec_le {m : Type} [Fintype m] {g : ℕ} {Y : Matrix m (Fin g) ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ j k, |Y j k| ≤ C) (z : Fin g → ℝ) :
    ‖Y.mulVec z‖ ≤ g * C * ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  calc ‖Y.mulVec z j‖ = |∑ k, Y j k * z k| := rfl
    _ ≤ ∑ k, |Y j k * z k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin g, C * ‖z‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul (h j k) (norm_le_pi_norm z k) (abs_nonneg _) hC
    _ = g * C * ‖z‖ := by simp [mul_assoc]

theorem abs_entry_le {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {C : ℝ} (hs : Y.IsSymm)
    (h0 : ∀ x, 0 ≤ x ⬝ᵥ Y.mulVec x) (h1 : ∀ x, x ⬝ᵥ Y.mulVec x ≤ C * (x ⬝ᵥ x)) (j k : Fin g) :
    |Y j k| ≤ |C| := by
  have a := h1 (Pi.single j 1)
  have b := h1 (Pi.single k 1)
  have p := h0 (Pi.single j 1 + Pi.single k 1)
  have q := h0 (Pi.single j 1 - Pi.single k 1)
  have s : Y k j = Y j k := hs.apply j k
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub, single_dotProduct, Matrix.mulVec_single_one, one_mul,
    Matrix.col_apply, Pi.single_eq_same, mul_one] at a b p q
  have := le_abs_self C
  rw [abs_le]
  constructor <;> linarith

theorem bound_one_add {g a : ℕ} (B : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (hB : ∀ i, (B i).PosSemidef) : ∃ K : ℝ, ∀ t : Fin a → ℝ, (∀ i, 0 < t i) → ∀ i x,
      ‖(1 + ∑ l, t l • B l)⁻¹.mulVec ((t i • B i).mulVec x)‖ ≤ K * ‖x‖ := by
  classical
  have hR : ∀ i, ∃ R : Matrix (Fin g) (Fin g) ℝ, B i = R.transpose * R := by
    intro i
    open scoped MatrixOrder in
    obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 (hB i).nonneg
    exact ⟨R, by rw [hR]; rfl⟩
  choose R hR using hR
  let L : Matrix (Fin g ⊕ (Fin a × Fin g)) (Fin g) ℝ :=
    Matrix.fromRows 1 (Matrix.of fun p j => R p.1 p.2 j)
  have hL : L.rank = g := by
    refine le_antisymm (by simpa using L.rank_le_card_width) ?_
    have h1 : (Matrix.fromCols (1 : Matrix (Fin g) (Fin g) ℝ)
        (0 : Matrix (Fin g) (Fin a × Fin g) ℝ)) * L = 1 := by
      simp [L, Matrix.fromCols_mul_fromRows]
    have h2 := Matrix.rank_mul_le_right (Matrix.fromCols (1 : Matrix (Fin g) (Fin g) ℝ)
        (0 : Matrix (Fin g) (Fin a × Fin g) ℝ)) L
    rw [h1, Matrix.rank_one, Fintype.card_fin] at h2
    exact h2
  obtain ⟨K, hK⟩ := wls_fintype L hL
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ i j k, |R i j k| ≤ A :=
    ⟨‖fun i j k => R i j k‖, norm_nonneg _, fun i j k =>
      ((norm_le_pi_norm _ k).trans (norm_le_pi_norm (fun j k => R i j k) j)).trans
        (norm_le_pi_norm (fun i j k => R i j k) i)⟩
  refine ⟨|K| * (g * A), fun t ht i x => ?_⟩
  let D : Fin g ⊕ (Fin a × Fin g) → ℝ := Sum.elim (fun _ => 1) (fun p => t p.1)
  let b : Fin g ⊕ (Fin a × Fin g) → ℝ :=
    Sum.elim (fun _ => 0) (fun p => if p.1 = i then (R i).mulVec x p.2 else 0)
  have hD : ∀ k, 0 < D k := by
    rintro (k | p)
    · exact one_pos
    · exact ht _
  have h := hK D b hD
  have h1 : L.transpose * Matrix.diagonal D * L = 1 + ∑ l, t l • B l := by
    ext j k
    simp only [Matrix.mul_apply (M := _ * Matrix.diagonal _), Matrix.mul_diagonal,
      Matrix.transpose_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, L, D,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Sum.elim_inl, Sum.elim_inr,
      Matrix.of_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, hR,
      Matrix.mul_apply (N := R _), smul_eq_mul, Finset.mul_sum]
    congr 1
    · simp [Matrix.one_apply, eq_comm]
    · exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring
  have h2 : (L.transpose * Matrix.diagonal D).mulVec b = (t i • B i).mulVec x := by
    rw [hR i, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec x]
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal,
      Matrix.transpose_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, L, D, b,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Sum.elim_inl, Sum.elim_inr,
      Matrix.of_apply, Pi.smul_apply, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i]
    · simp only [if_true]
      rw [Finset.mul_sum Finset.univ _ (t i)]
      exact Finset.sum_congr rfl fun m _ => by ring
    · intro l _ hl
      simp [hl]
    · simp
  have h3 : ‖b‖ ≤ g * A * ‖x‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
    rintro (k | p)
    · simp only [b, Sum.elim_inl, norm_zero]; positivity
    · simp only [b, Sum.elim_inr]
      split_ifs
      · exact (norm_le_pi_norm _ _).trans (norm_mulVec_le hA0 (hA i) x)
      · simp only [norm_zero]; positivity
  rw [h1, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, h2] at h
  calc _ ≤ K * ‖b‖ := h
    _ ≤ |K| * ‖b‖ := mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _)
    _ ≤ |K| * (g * A * ‖x‖) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = _ := by ring

end WeightedInverseBound

open WeightedInverseBound in

theorem smul_inv_mul_posSemidef_uniform_bound : ∀ (g a : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (c C : ℝ), 0 < c → (∀ i, (B i).PosSemidef) → ∃ W : ℝ, ∀ (Y' : Matrix (Fin g) (Fin g) ℝ) (t : Fin a → ℝ), Y'.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y'.mulVec x) → (∀ x, x ⬝ᵥ Y'.mulVec x ≤ C * (x ⬝ᵥ x)) → (∀ i, 0 < t i) → ∀ i x, ‖(t i • ((Y' + ∑ l, t l • B l)⁻¹ * B i)).mulVec x‖ ≤ W * ‖x‖ := by
  intro g a B c C hc hB
  obtain ⟨K, hK⟩ := bound_one_add B hB
  refine ⟨(1 + g / c * (1 + g * |C|)) * K, fun Y' t hs hlo hhi ht i x => ?_⟩
  have hw := hK t ht i x
  set P := ∑ l, t l • B l with hP
  have hP0 : ∀ z, 0 ≤ z ⬝ᵥ P.mulVec z := by
    intro z
    have : P.PosSemidef := Matrix.posSemidef_sum _ fun l _ => (hB l).smul (ht l).le
    simpa using this.dotProduct_mulVec_nonneg z
  have hY : ∀ z, c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Y' + P).mulVec z := by
    intro z
    rw [Matrix.add_mulVec, dotProduct_add]
    linarith [hlo z, hP0 z]
  have hZ : ∀ z, 1 * (z ⬝ᵥ z) ≤ z ⬝ᵥ (1 + P).mulVec z := by
    intro z
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec]
    linarith [hP0 z]
  have hYu := isUnit_det_of_coercive hc hY
  have hZu := isUnit_det_of_coercive one_pos hZ
  set v := (t i • B i).mulVec x with hv
  set w := (1 + P)⁻¹.mulVec v with hwdef
  have hu : (t i • ((Y' + P)⁻¹ * B i)).mulVec x = (Y' + P)⁻¹.mulVec v := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_smul]
  rw [hu]
  set u := (Y' + P)⁻¹.mulVec v with hudef
  have e1 : (Y' + P).mulVec u = v := by
    rw [hudef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hYu, Matrix.one_mulVec]
  have e2 : (1 + P).mulVec w = v := by
    rw [hwdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hZu, Matrix.one_mulVec]
  have e3 : (Y' + P).mulVec (u - w) = w - Y'.mulVec w := by
    rw [Matrix.mulVec_sub, e1, ← e2, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    abel
  have h0 : ∀ z, 0 ≤ z ⬝ᵥ Y'.mulVec z := fun z =>
    le_trans (mul_nonneg hc.le (le_trans (mul_self_nonneg _) (norm_sq_le_dot z))) (hlo z)
  have b1 := norm_mulVec_le (abs_nonneg C) (abs_entry_le hs h0 hhi) w
  have b2 := norm_le_of_coercive hc hY (u - w)
  rw [e3] at b2
  have b3 : ‖w - Y'.mulVec w‖ ≤ (1 + g * |C|) * ‖w‖ := by
    have := norm_sub_le w (Y'.mulVec w)
    linarith
  have b4 : ‖u‖ ≤ ‖w‖ + ‖u - w‖ := by
    have := norm_add_le w (u - w)
    rwa [add_sub_cancel] at this
  have hgc : (0 : ℝ) ≤ g / c := by positivity
  have b5 := mul_le_mul_of_nonneg_left b3 hgc
  calc ‖u‖ ≤ (1 + g / c * (1 + g * |C|)) * ‖w‖ := by linarith
    _ ≤ (1 + g / c * (1 + g * |C|)) * (K * ‖x‖) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = _ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanDLiftClearDenominators
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.span_D_lift_clear_denominators : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] (B : Subalgebra k K) [Algebra.FiniteType k B] (Q : Ideal B), Q.IsPrime → ∀ s : B, s ∈ Q → s ≠ 0 → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → ∀ (m : ℕ) (y : Fin m → B), IsTranscendenceBasis k (fun j => Ideal.Quotient.mk Q (y j)) → ∀ v : B, ∃ r : B, r ∉ Q ∧ ∃ c : Fin (m + 1) → B, algebraMap K L (r : K) • D k L (algebraMap K L (v : K)) = ∑ l, algebraMap K L (c l : K) • (Fin.cons (D k L (algebraMap K L (s : K))) (fun j => D k L (algebraMap K L (y j : K))) : Fin (m + 1) → Ω[L⁄k]) l := by
  intro k K L _ _ _ _ _ _ _ _ B _ Q hQ s hsQ hs0 hgen m y hy v
  classical
  let R := Localization.AtPrime Q
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  haveI : IsNoetherianRing R := IsLocalization.isNoetherianRing Q.primeCompl R inferInstance
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R Q.primeCompl_le_nonZeroDivisors
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {algebraMap B R s} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro z hz
      obtain ⟨c, r, hr, hrc⟩ := hgen z hz
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      refine ⟨IsLocalization.mk' R c (⟨r, hr⟩ : Q.primeCompl), ?_⟩
      have hu := IsLocalization.map_units R (⟨r, hr⟩ : Q.primeCompl)
      apply hu.mul_left_cancel
      rw [← mul_assoc, IsLocalization.mk'_spec', ← map_mul, ← map_mul]
      exact congrArg _ hrc.symm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hsQ
  have hs0' : algebraMap B R s ≠ 0 := fun h => hs0 (hinj (by rw [h, map_zero]))
  have hnf : ¬ IsField R := by
    intro hf
    have h1 := IsLocalRing.isField_iff_maximalIdeal_eq.1 hf
    rw [hmax, Ideal.span_singleton_eq_bot] at h1
    exact hs0' h1
  have hprin : Submodule.IsPrincipal (IsLocalRing.maximalIdeal R) := ⟨⟨_, hmax⟩⟩
  haveI : IsDiscreteValuationRing R := ((IsDiscreteValuationRing.TFAE R hnf).out 0 4).2 hprin
  have hirr : Irreducible (algebraMap B R s) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : Nontrivial (B ⧸ Q) := IsDomain.toNontrivial
  haveI : Algebra.IsAlgebraic (B ⧸ Q) Q.ResidueField :=
    IsLocalization.isAlgebraic (R := B ⧸ Q) (S := Q.ResidueField) (M := nonZeroDivisors (B ⧸ Q))
  haveI : FaithfulSMul (B ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective _ _)
  have htb : IsTranscendenceBasis k (fun j => IsLocalRing.residue R (algebraMap B R (y j))) := by
    have h2 := hy.algebraMap_comp (A := Q.ResidueField)
    convert h2 using 1
    funext j
    simp only [Function.comp_apply, Ideal.algebraMap_quotient_residueField_mk]
    rfl
  have hspan := GlobalTheory.span_D_uniformizer_transcendenceBasis k R (algebraMap B R s) hirr m
    (fun j => algebraMap B R (y j)) htb
  have hunit : ∀ z : Q.primeCompl, IsUnit (algebraMap B K z) := fun z => by
    refine isUnit_iff_ne_zero.2 fun h => z.2 ?_
    have hz : (z : B) = 0 := Subtype.ext h
    rw [hz]; exact Q.zero_mem
  let ψ : R →+* K := IsLocalization.lift hunit
  letI : Algebra R L := ((algebraMap K L).comp ψ).toAlgebra
  have hRL : ∀ x : B, algebraMap R L (algebraMap B R x) = algebraMap K L (x : K) := fun x => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  haveI : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k B R, hRL, IsScalarTower.algebraMap_apply k K L]
    rfl
  haveI : SMulCommClass k R L := inferInstance
  let Φ := KaehlerDifferential.map k k R L
  let g : Fin (m + 1) → Ω[R⁄k] := Fin.cons (D k R (algebraMap B R s)) (fun j => D k R (algebraMap B R (y j)))
  have hDv : D k R (algebraMap B R v) ∈ Submodule.span R (Set.range g) := by
    rw [Fin.range_cons, hspan]; exact Submodule.mem_top
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hDv
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples Q.primeCompl (Finset.univ : Finset (Fin (m + 1))) c'
  have hb' : ∀ l, ∃ x : B, algebraMap B R x = algebraMap B R (b : B) * c' l := fun l => by
    obtain ⟨x, hx⟩ := hb l (Finset.mem_univ l)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose c hc using hb'
  have hΦD : ∀ x : B, Φ (D k R (algebraMap B R x)) = D k L (algebraMap K L (x : K)) := fun x => by
    rw [KaehlerDifferential.map_D, hRL]
  have hΦg : ∀ l, Φ (g l) = (Fin.cons (D k L (algebraMap K L (s : K))) (fun j => D k L (algebraMap K L (y j : K))) : Fin (m + 1) → Ω[L⁄k]) l := by
    intro l
    refine Fin.cases ?_ (fun j => ?_) l
    · simp only [g, Fin.cons_zero]; exact hΦD s
    · simp only [g, Fin.cons_succ]; exact hΦD (y j)
  refine ⟨b, b.2, c, ?_⟩
  rw [← hRL, ← hΦD, algebraMap_smul, ← map_smul, ← hc', Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← hRL, ← hΦg, algebraMap_smul L (algebraMap B R (c l)) (Φ (g l)), ← map_smul Φ]
  congr 1
  rw [hc, mul_smul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfStableOfIsFractionRingStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_eq_top_of_stable_of_isFractionRing' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k K] [Algebra F K] [FiniteDimensional F K] (B : Subalgebra k K) [IsFractionRing B K] (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Submodule.span K S = ⊤ → Submodule.span F S = ⊤ := by
  first | (exact @GlobalTheory.span_eq_top_of_stable_of_isFractionRing) | (exact GlobalTheory.span_eq_top_of_stable_of_isFractionRing) | (intros; apply GlobalTheory.span_eq_top_of_stable_of_isFractionRing  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapSmoothSurjectiveOfIsSeparableStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_and_surjective_spec_map_of_isSeparable : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L], Smooth (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧ Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  first | exact @GlobalTheory.spec_map_smooth_surjective_of_isSeparable | exact GlobalTheory.spec_map_smooth_surjective_of_isSeparable | (intros; apply GlobalTheory.spec_map_smooth_surjective_of_isSeparable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecWidePushoutIsLimitWidePullbackStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_widePushout_isLimit_widePullback : ∀ (n : ℕ) (C D A : Type) [CommRing C] [CommRing D] [CommRing A] (a : C →+* D) (b : C →+* A) (l : Fin n → (D →+* A)) (hl : ∀ i, (l i).comp a = b), (∀ (B : Type) [CommRing B] (g : Fin n → (D →+* B)) (c : C →+* B), (∀ i, (g i).comp a = c) → ∃! u : A →+* B, u.comp b = c ∧ ∀ i, u.comp (l i) = g i) → Nonempty (IsLimit (WidePullbackCone.mk (f := fun _ : Fin n => Spec.map (CommRingCat.ofHom a)) (Spec.map (CommRingCat.ofHom b)) (fun i => Spec.map (CommRingCat.ofHom (l i))) (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i]))) := by
  first | exact @GlobalTheory.spec_widePushout_isLimit | exact GlobalTheory.spec_widePushout_isLimit | (intros; apply GlobalTheory.spec_widePushout_isLimit; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquiv
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

set_option autoImplicit false in
open KaehlerDifferential in

theorem _root_.GlobalTheory.PD.rA_single_polyEquiv : ∀ (k : Type) [Field k] (F : Type) [Field F]
    [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), _root_.GlobalTheory.PD.IsPd k x →
    ∀ i : Fin (d + 1), ∃ e : MvPolynomial (Fin d) k ≃ₐ[k] _root_.GlobalTheory.PD.rA k x {i},
      ∀ j, (e (MvPolynomial.X j) : F) = x (i.succAbove j) / x i := by
  intro k _ F _ _ d x hP i
  refine ⟨_root_.GlobalTheory.PD.Model.chartEquiv k x hP i, fun j => ?_⟩
  simp [_root_.GlobalTheory.PD.Model.chartEquiv, _root_.GlobalTheory.PD.Model.yc,
    AlgebraicIndependent.aevalEquiv_apply_coe]

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoetheStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ I : Finset (Fin (d + 1)), I.Nonempty → IsFractionRing (rA k x I) F ∧ IsNoetherianRing (rA k x I) := by
  first | (exact @GlobalTheory.PD.rA_isFractionRing_isNoetherianRing) | (exact GlobalTheory.PD.rA_isFractionRing_isNoetherianRing) | (intros; apply GlobalTheory.PD.rA_isFractionRing_isNoetherianRing  <;> assumption)
end

