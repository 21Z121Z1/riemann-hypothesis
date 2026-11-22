import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Bundle0001
import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDpOfCompOnGens
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0009
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterlacingSignatureParity
section
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame.SignWord

variable {n : ℕ}

def sg (b : Bool) : ℤ := cond b 1 (-1)

theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

theorem step_sign (a b c e : Bool) (k : ℕ) (h : Xor' (a = b) (c = e)) :
    sg c * sg a * (-1 : ℤ) ^ k = sg e * sg b * (-1 : ℤ) ^ (k + 1) := by
  cases a <;> cases b <;> cases c <;> cases e <;> simp_all [Xor', sg, pow_succ]

theorem sign_left (b : Bool) (k : ℕ) (h : sg b * sg true * (-1 : ℤ) ^ k = 1) :
    b = true ↔ Even k := by
  rcases Nat.even_or_odd k with hk | hk
  · cases b <;> simp_all [sg, hk.neg_one_pow]
  · have hk' : ¬ Even k := Nat.not_even_iff_odd.2 hk
    cases b <;> simp_all [sg, hk.neg_one_pow]

theorem sign_right (b : Bool) (k : ℕ) (h : sg b * sg false * (-1 : ℤ) ^ k = 1) :
    b = true ↔ ¬ Even k := by
  rcases Nat.even_or_odd k with hk | hk
  · cases b <;> simp_all [sg, hk.neg_one_pow]
  · have hk' : ¬ Even k := Nat.not_even_iff_odd.2 hk
    cases b <;> simp_all [sg, hk.neg_one_pow]

theorem sum_neg_one_pow (n : ℕ) : ∑ p ∈ range (2 * n + 1), (-1 : ℤ) ^ p = 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    have h : (-1 : ℤ) ^ (2 * k + 1) = -1 := (odd_two_mul_add_one k).neg_one_pow
    have h' : (-1 : ℤ) ^ (2 * k + 1 + 1) = 1 := by rw [pow_succ, h]; norm_num
    rw [h, h']; norm_num

theorem above_lt_of_lt (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) {r : ℝ}
    (x : Fin (n + 1) ⊕ Fin n) (h : r < Sum.elim d d' x) :
    above d d' (Sum.elim d d' x) < above d d' r := by
  unfold above
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨x, ?_, ?_⟩
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact h.trans hz
  · simpa using h
  · simp

theorem above_lt_card (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (x : Fin (n + 1) ⊕ Fin n) :
    above d d' (Sum.elim d d' x) < 2 * n + 1 := by
  have h : above d d' (Sum.elim d d' x) < (univ : Finset (Fin (n + 1) ⊕ Fin n)).card := by
    unfold above
    apply Finset.card_lt_card
    exact Finset.filter_ssubset.2 ⟨x, mem_univ _, by simp⟩
  have h2 : (univ : Finset (Fin (n + 1) ⊕ Fin n)).card = 2 * n + 1 := by
    simp [Finset.card_univ, Fintype.card_sum]; ring
  omega

theorem above_injective (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    Function.Injective fun x => above d d' (Sum.elim d d' x) := by
  intro x y hxy
  simp only at hxy
  rcases lt_trichotomy (Sum.elim d d' x) (Sum.elim d d' y) with h | h | h
  · have := above_lt_of_lt d d' y h
    omega
  · exact hv h
  · have := above_lt_of_lt d d' x h
    omega

theorem above_image (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    (univ : Finset (Fin (n + 1) ⊕ Fin n)).image (fun x => above d d' (Sum.elim d d' x)) =
      range (2 * n + 1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨x, -, rfl⟩ := mem_image.1 hp
    exact mem_range.2 (above_lt_card d d' x)
  · rw [Finset.card_image_of_injective _ (above_injective d d' hv)]
    simp [Finset.card_univ, Fintype.card_sum]
    omega

theorem sum_above (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (hv : Function.Injective (Sum.elim d d')) :
    ∑ x : Fin (n + 1) ⊕ Fin n, (-1 : ℤ) ^ above d d' (Sum.elim d d' x) = 1 := by
  have h := sum_neg_one_pow n
  rw [← above_image d d' hv,
    Finset.sum_image (fun x _ y _ h => above_injective d d' hv h)] at h
  exact h

theorem sum_signs (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (e : Fin n ⊕ Unit ≃ Fin (n + 1))
    (hf : PositivityTheory.UnitaryDecomposition.Fits ε ε' e) :
    ∑ x : Fin (n + 1) ⊕ Fin n, sg (Sum.elim ε ε' x) * sg x.isLeft = 1 := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i, sg (ε i) = ∑ a, sg (ε' a) + 1 := by
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    have h0 : sg (ε (e (Sum.inr ()))) = 1 := by
      have : ε (e (Sum.inr ())) = true := hf.1
      simp [this, sg]
    simp [hf.2, h0]
  have hl : sg true = 1 := rfl
  have hr : sg false = -1 := rfl
  simp [hl, hr, h1]

theorem step_letters (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (hv : Function.Injective (Sum.elim d d'))
    (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') (x y : Fin (n + 1) ⊕ Fin n)
    (hxy : above d d' (Sum.elim d d' y) = above d d' (Sum.elim d d' x) + 1) :
    sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) =
      sg (Sum.elim ε ε' y) * sg y.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' y) := by
  have hlt : Sum.elim d d' y < Sum.elim d d' x := by
    rcases lt_trichotomy (Sum.elim d d' y) (Sum.elim d d' x) with h | h | h
    · exact h
    · rw [h] at hxy; omega
    · have := above_lt_of_lt d d' y h
      omega
  have hno : ∀ z, ¬ (Sum.elim d d' y < Sum.elim d d' z ∧ Sum.elim d d' z < Sum.elim d d' x) := by
    rintro z ⟨h1, h2⟩
    have a1 := above_lt_of_lt d d' z h1
    have a2 := above_lt_of_lt d d' x h2
    omega
  have := hw x y hlt hno
  rw [hxy]
  exact step_sign _ _ _ _ _ (by
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩)

theorem const_letters (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (hv : Function.Injective (Sum.elim d d'))
    (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') :
    ∃ T : ℤ, ∀ x : Fin (n + 1) ⊕ Fin n,
      sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) = T := by
  have him := above_image d d' hv
  have hsurj : ∀ p < 2 * n + 1, ∃ x : Fin (n + 1) ⊕ Fin n, above d d' (Sum.elim d d' x) = p := by
    intro p hp
    have : p ∈ (univ : Finset (Fin (n + 1) ⊕ Fin n)).image
        (fun x => above d d' (Sum.elim d d' x)) := by
      rw [him]; exact mem_range.2 hp
    obtain ⟨x, -, hx⟩ := mem_image.1 this
    exact ⟨x, hx⟩
  obtain ⟨x0, hx0⟩ := hsurj 0 (by omega)
  refine ⟨sg (Sum.elim ε ε' x0) * sg x0.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x0), ?_⟩
  have key : ∀ p : ℕ, ∀ x : Fin (n + 1) ⊕ Fin n, above d d' (Sum.elim d d' x) = p →
      sg (Sum.elim ε ε' x) * sg x.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) =
        sg (Sum.elim ε ε' x0) * sg x0.isLeft * (-1 : ℤ) ^ above d d' (Sum.elim d d' x0) := by
    intro p
    induction p with
    | zero =>
      intro x hx
      have : x = x0 := above_injective d d' hv (by simp only [hx, hx0])
      rw [this]
    | succ k ih =>
      intro x hx
      have hk : k < 2 * n + 1 := by
        have := above_lt_card d d' x
        omega
      obtain ⟨y, hy⟩ := hsurj k hk
      rw [← ih y hy]
      exact (step_letters ε d ε' d' hv hw y x (by rw [hx, hy])).symm
  exact fun x => key _ x rfl

theorem heSign (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool)
    (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (hf : PositivityTheory.UnitaryDecomposition.Fits ε ε' e)
    (hv : Function.Injective (Sum.elim d d')) (hw : PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d') :
    (∀ i, (ε i = true ↔ Even (above d d' (d i)))) ∧
      ∀ j, (ε' j = true ↔ ¬ Even (above d d' (d' j))) := by
  obtain ⟨T, hT⟩ := const_letters ε d ε' d' hv hw
  have hsum : T = 1 := by
    have h1 : ∀ x : Fin (n + 1) ⊕ Fin n, sg (Sum.elim ε ε' x) * sg x.isLeft =
        T * (-1 : ℤ) ^ above d d' (Sum.elim d d' x) := by
      intro x
      rw [← hT x]
      have hp : ((-1 : ℤ) ^ above d d' (Sum.elim d d' x)) *
          ((-1 : ℤ) ^ above d d' (Sum.elim d d' x)) = 1 := by
        rw [← mul_pow]; simp
      rw [mul_assoc, hp, mul_one]
    have h2 := sum_signs ε ε' e hf
    simp_rw [h1] at h2
    rw [← Finset.mul_sum, sum_above d d' hv] at h2
    simpa using h2
  subst hsum
  refine ⟨fun i => sign_left _ _ (by simpa using hT (Sum.inl i)),
    fun j => sign_right _ _ (by simpa using hT (Sum.inr j))⟩

end GlobalTheory.CompanionTheory.RgHeFrame.SignWord
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftUnique
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ChartBc

section Ring
variable {R R' D : Type} [CommRing R] [CommRing R'] [CommRing D] [Algebra R R'] [Algebra R D]

theorem left_right (r : R) : (algebraMap R R' r) ⊗ₜ[R] (1 : D) = (1 : R') ⊗ₜ[R] (algebraMap R D r) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem dp_right {I : Ideal R} {I' : Ideal R'} {γ : DividedPowers I} {γ' : DividedPowers I'} {J : Ideal D}
    (δ : DividedPowers J)
    (δ' : DividedPowers (I'.map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D)))
    (hJ : J = I.map (algebraMap R D)) (hδ : IsDPMorphism γ δ (algebraMap R D))
    (hδ' : IsDPMorphism γ' δ' (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D))
    (hσ : IsDPMorphism γ γ' (algebraMap R R')) :
    IsDPMorphism δ δ' (Algebra.TensorProduct.includeRight : D →ₐ[R] R' ⊗[R] D).toRingHom := by
  have key : ∀ r : R, (Algebra.TensorProduct.includeRight : D →ₐ[R] R' ⊗[R] D).toRingHom (algebraMap R D r) =
      (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D) (algebraMap R R' r) := fun r =>
    (left_right r).symm
  refine IsDPMorphism.on_span δ δ' (S := algebraMap R D '' I) (by rw [hJ]; rfl) ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [key]
    exact Ideal.mem_map_of_mem _ (hσ.1 (Ideal.mem_map_of_mem _ ha))
  · rintro n _ ⟨a, ha, rfl⟩
    rw [hδ.2 a ha, key, key, hδ'.2 _ (hσ.1 (Ideal.mem_map_of_mem _ ha)), hσ.2 a ha]

theorem lift_unique {I' : Ideal R'} {J : Ideal D} {B : Type} [CommRing B]
    (hle : J ≤ (I'.map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D)).comap
      (Algebra.TensorProduct.includeRight : D →ₐ[R] R' ⊗[R] D).toRingHom)
    (a : R' ⧸ I' →+* B) (b : D ⧸ J →+* B)
    (hab : ∀ r, a (Ideal.Quotient.mk I' (algebraMap R R' r)) = b (Ideal.Quotient.mk J (algebraMap R D r))) :
    ∃! φ : (R' ⊗[R] D) ⧸ I'.map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D) →+* B,
      φ.comp (Ideal.quotientMap _ (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D)
        Ideal.le_comap_map) = a ∧
      φ.comp (Ideal.quotientMap _ (Algebra.TensorProduct.includeRight : D →ₐ[R] R' ⊗[R] D).toRingHom hle) = b := by
  letI : Algebra R B := ((a.comp (Ideal.Quotient.mk I')).comp (algebraMap R R')).toAlgebra
  let f1 : R' →ₐ[R] B := { a.comp (Ideal.Quotient.mk I') with commutes' := fun _ => rfl }
  let f2 : D →ₐ[R] B := { b.comp (Ideal.Quotient.mk J) with commutes' := fun r => (hab r).symm }
  let Φ : R' ⊗[R] D →ₐ[R] B := Algebra.TensorProduct.productMap f1 f2
  have hΦ : ∀ r x, Φ (r ⊗ₜ[R] x) = a (Ideal.Quotient.mk I' r) * b (Ideal.Quotient.mk J x) := fun r x => by
    simp only [Φ, Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  have hker : I'.map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[R] D) ≤ RingHom.ker Φ.toRingHom := by
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change Φ (x ⊗ₜ[R] 1) = 0
    rw [hΦ, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, zero_mul]
  let φ := Ideal.Quotient.lift _ Φ.toRingHom fun z hz => hker hz
  have hφ : ∀ r x, φ (Ideal.Quotient.mk _ (r ⊗ₜ[R] x)) = a (Ideal.Quotient.mk I' r) * b (Ideal.Quotient.mk J x) :=
    fun r x => by
      rw [Ideal.Quotient.lift_mk]
      exact hΦ r x
  refine ⟨φ, ⟨?_, ?_⟩, ?_⟩
  · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
    change φ (Ideal.Quotient.mk _ (r ⊗ₜ[R] 1)) = a (Ideal.Quotient.mk I' r)
    rw [hφ, map_one, map_one, mul_one]
  · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    change φ (Ideal.Quotient.mk _ ((1 : R') ⊗ₜ[R] x)) = b (Ideal.Quotient.mk J x)
    rw [hφ, map_one, map_one, one_mul]
  · rintro φ₂ ⟨h1, h2⟩
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun w => ?_)
    refine TensorProduct.induction_on w (by simp) (fun r x => ?_) (fun u v hu hv => ?_)
    · have t : r ⊗ₜ[R] x = (r ⊗ₜ[R] (1 : D)) * ((1 : R') ⊗ₜ[R] x) := by simp
      have e1 := RingHom.congr_fun h1 (Ideal.Quotient.mk I' r)
      have e2 := RingHom.congr_fun h2 (Ideal.Quotient.mk J x)
      change φ₂ (Ideal.Quotient.mk _ (r ⊗ₜ[R] 1)) = _ at e1
      change φ₂ (Ideal.Quotient.mk _ ((1 : R') ⊗ₜ[R] x)) = _ at e2
      change φ₂ (Ideal.Quotient.mk _ (r ⊗ₜ[R] x)) = φ (Ideal.Quotient.mk _ (r ⊗ₜ[R] x))
      rw [hφ, t, map_mul, map_mul, e1, e2]
    · simp only [RingHom.comp_apply, map_add] at hu hv ⊢
      rw [hu, hv]

end Ring

theorem chart_bc : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q κ' σ) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O)
    (hnil : p = 0 → IsNilpotent I') {V : X.Opens} {d : ℕ}
    (c : Chart γ p q κ V d),
    letI := σ.toAlgebra
    letI := c.D.i.toAlgebra
    ∃ (c' : Chart γ' p q κ' V d) (e : c.D ⟶ (m.mor p).functor.obj c'.D), (∀ i, e.φ (c.t i) = c'.t i) ∧
      (FlatT c.D → FlatT c'.D) ∧
      ∃ f : R' ⊗[R] c.D.B ≃+* c'.D.B, (∀ r, f (r ⊗ₜ 1) = c'.D.i r) ∧ ∀ x, f (1 ⊗ₜ x) = e.φ x := by
  intro O R R' _ _ _ I I' γ γ' p X q κ κ' σ m hu hg hnil V d c
  letI a1 : Algebra R R' := σ.toAlgebra
  letI a2 : Algebra R c.D.B := c.D.i.toAlgebra
  let iL : R' →+* R' ⊗[R] c.D.B := Algebra.TensorProduct.includeLeftRingHom
  let iR : c.D.B →+* R' ⊗[R] c.D.B := (Algebra.TensorProduct.includeRight : c.D.B →ₐ[R] R' ⊗[R] c.D.B).toRingHom
  have hcomm : ∀ r, iR (c.D.i r) = iL (σ r) := fun r => (left_right (R := R) (R' := R') (D := c.D.B) r).symm
  have hEt : (MvPolynomial.eval₂Hom iL (fun i => (1 : R') ⊗ₜ[R] c.t i) :
      MvPolynomial (Fin d) R' →+* R' ⊗[R] c.D.B).Etale :=
    GlobalTheory.CompanionTheory.ChartAlg.etale_tensor (O := R) (R := R') (G := c.D.B) c.t c.etale
  haveI hF : Module.Flat R' (R' ⊗[R] c.D.B) := GlobalTheory.CompanionTheory.ChartAlg.flat_of_etale _ hEt
  obtain ⟨δ', hδ'⟩ : ∃ δ' : DividedPowers (I'.map iL), IsDPMorphism γ' δ' iL :=
    GlobalTheory.CompanionTheory.JLiftDP.dpFlat R' (R' ⊗[R] c.D.B) I' γ'
  have hle : c.D.J ≤ (I'.map iL).comap iR := by
    rw [c.J_eq]
    refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
    change iR (c.D.i x) ∈ I'.map iL
    rw [hcomm]
    exact Ideal.mem_map_of_mem iL (m.hI.1 (Ideal.mem_map_of_mem σ hx))
  let h : c.D.B ⧸ c.D.J →+* (R' ⊗[R] c.D.B) ⧸ I'.map iL := Ideal.quotientMap _ iR hle
  let ψ : R' ⧸ I' →+* (R' ⊗[R] c.D.B) ⧸ I'.map iL := Ideal.quotientMap _ iL Ideal.le_comap_map
  let y₀ : PtOver X q κ (c.D.B ⧸ c.D.J) := c.D.y
  have hw : ∀ r, y₀.1.1 (Ideal.Quotient.mk I r) = Ideal.Quotient.mk c.D.J (c.D.i r) := c.D.w
  have hhy : h.comp y₀.1.1 = ψ.comp m.bar := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
    change h (y₀.1.1 (Ideal.Quotient.mk I r)) = Ideal.Quotient.mk _ (iL (σ r))
    rw [hw, ← hcomm]
    rfl
  have hκ' : m.bar.comp κ = κ' := by
    have := m.bar_κ
    rw [hg, RingHom.comp_id] at this
    exact this
  let y' : PtOver X q κ' ((R' ⊗[R] c.D.B) ⧸ I'.map iL) :=
    ⟨(ψ, Spec.map (CommRingCat.ofHom h) ≫ pt c.D), by
      change (Spec.map (CommRingCat.ofHom h) ≫ pt c.D) ≫ q = _
      have e0 : pt c.D ≫ q = Spec.map (CommRingCat.ofHom (y₀.1.1.comp κ)) := y₀.2
      rw [Category.assoc, e0, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hhy,
        RingHom.comp_assoc, hκ']⟩
  let D' : Thick (nlFun γ' p X q κ') := mkT (R' ⊗[R] c.D.B) iL (I'.map iL) δ'
    ⟨fun hp => by
      have h1 : IsNilpotent (p : c.D.B) := c.D.adm.1 hp
      have h2 := h1.map iR
      rwa [map_natCast] at h2,
     fun hp => by
      obtain ⟨n, hn⟩ := hnil hp
      exact ⟨n, by rw [← Ideal.map_pow, hn]; exact Ideal.map_bot⟩⟩ hδ' y' (fun r => rfl)
  have hin : InU V D' := fun x _ => c.inV (show Spec.map (CommRingCat.ofHom h) x ∈ (⊤ : (Spec (CommRingCat.of (c.D.B ⧸ c.D.J))).Opens) from trivial)
  let c' : Chart γ' p q κ' V d :=
    { D := D'
      t := fun k => (1 : R') ⊗ₜ[R] c.t k
      etale := hEt
      J_eq := rfl
      inV := hin
      rep := fun B z hz => by
        let y0 : PtOver X q κ B := ⟨(z.1.1.comp m.bar, z.1.2), by
          rw [z.2, RingHom.comp_assoc, hκ']⟩
        obtain ⟨φ, hφ, hun⟩ := c.rep B y0 hz
        have hφ1 : φ.comp y₀.1.1 = z.1.1.comp m.bar := congrArg (fun w : PtOver X q κ B => w.1.1) hφ
        have hφ2 : Spec.map (CommRingCat.ofHom φ) ≫ pt c.D = z.1.2 :=
          congrArg (fun w : PtOver X q κ B => w.1.2) hφ
        have hab : ∀ r, z.1.1 (Ideal.Quotient.mk I' (algebraMap R R' r)) =
            φ (Ideal.Quotient.mk c.D.J (algebraMap R c.D.B r)) := fun r => by
          have e1 := RingHom.congr_fun hφ1 (Ideal.Quotient.mk I r)
          change φ (y₀.1.1 (Ideal.Quotient.mk I r)) = _ at e1
          rw [hw] at e1
          exact e1.symm
        obtain ⟨φ', ⟨h1, h2⟩, hu'⟩ := lift_unique (R := R) (R' := R') (D := c.D.B) hle z.1.1 φ hab
        refine ⟨φ', ?_, fun φ₂ hφ₂ => hu' φ₂ ?_⟩
        · refine Subtype.ext (Prod.ext h1 ?_)
          change Spec.map (CommRingCat.ofHom φ') ≫ (Spec.map (CommRingCat.ofHom h) ≫ pt c.D) = z.1.2
          rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          have e2 : φ'.comp h = φ := h2
          rw [e2, hφ2]
        · have ha : φ₂.comp ψ = z.1.1 := congrArg (fun w : PtOver X q κ' B => w.1.1) hφ₂
          have hb : Spec.map (CommRingCat.ofHom φ₂) ≫ (Spec.map (CommRingCat.ofHom h) ≫ pt c.D) = z.1.2 :=
            congrArg (fun w : PtOver X q κ' B => w.1.2) hφ₂
          refine ⟨ha, hun (φ₂.comp h) (Subtype.ext (Prod.ext ?_ ?_))⟩
          · change (φ₂.comp h).comp y₀.1.1 = z.1.1.comp m.bar
            rw [RingHom.comp_assoc, hhy, ← RingHom.comp_assoc, ha]
          · change Spec.map (CommRingCat.ofHom (φ₂.comp h)) ≫ pt c.D = z.1.2
            rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
            exact hb }
  let e : c.D ⟶ (m.mor p).functor.obj c'.D :=
    mkH (T' := (m.mor p).functor.obj c'.D) iR hcomm
      (dp_right (R := R) (R' := R') (D := c.D.B) c.D.δ δ' c.J_eq c.D.compat hδ' m.hI) hle
      (Subtype.ext (Prod.ext hhy (by
        change Spec.map (CommRingCat.ofHom h) ≫ pt c.D = (Spec.map (CommRingCat.ofHom h) ≫ pt c.D) ≫ m.u
        rw [hu, Category.comp_id])))
  exact ⟨c', e, fun _ => rfl, fun _ => RingHom.flat_algebraMap_iff.2 hF, RingEquiv.refl _, fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.CompanionTheory.ChartBc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

variable {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}

def secs {E : X.Modules} (S : Subobject E) (V : X.Opens) : Set Γ(E, V) :=
  Set.range (S.arrow.app V)

def Killed (J : X.IdealSheafData) {E : X.Modules} (S : Subobject E) : Prop :=
  ∀ (U : X.affineOpens) (a : Γ(X, U)), a ∈ J.ideal U → ∀ x : Γ(E, U), a • x ∈ secs S U

variable [X.Over (Spec (.of A))]

def powSub (E : X.Modules) (n : ℕ) : Subobject E := Subobject.mk (idealPowι I E n)

def PropSupp (A : Type) [CommRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] {E : X.Modules}
    (S : Subobject E) : Prop :=
  ∃ T : X.IdealSheafData, IsProper (T.subschemeι ≫ (X ↘ Spec (.of A))) ∧
    Scheme.Modules.SupportedIn (cokernel S.arrow) (T.support : Set X)

structure ClosedSys (E : X.Modules) (S : ℕ → Subobject E) : Prop where
  qcoh : ∀ e, (S e : X.Modules).IsQuasicoherent
  pow_le : ∀ e, powSub I E (e + 1) ≤ S e
  succ : ∀ e, S e = S (e + 1) ⊔ powSub I E (e + 1)

def Alg (E : X.Modules) (S : ℕ → Subobject E) : Prop :=
  ∃ B : Subobject E, (B : X.Modules).IsQuasicoherent ∧ PropSupp A B ∧
    ∀ e, B ⊔ powSub I E (e + 1) = S e

def Statement (J : X.IdealSheafData) : Prop :=
  ∀ (E : X.Modules), IsCoherent E → ∀ S : ℕ → Subobject E, ClosedSys I E S →
    (∀ e, Killed J (S e)) → PropSupp A (S 0) → Alg I E S

def restrictSys {E : X.Modules} (D : Subobject E) (S : ℕ → Subobject E) (c e : ℕ) :
    Subobject (D : X.Modules) :=
  (Subobject.pullback D.arrow).obj (S (e + c)) ⊔ powSub I (D : X.Modules) (e + 1)

lemma powSub_succ_le (E : X.Modules) (n : ℕ) : powSub I E (n + 1) ≤ powSub I E n :=
  Subobject.mk_le_mk_of_comm (idealPowSucc I E n) (idealPowSucc_ι I E n)

theorem closedSys_pow (E : X.Modules) [E.IsQuasicoherent] :
    ClosedSys I E (fun e => powSub I E (e + 1)) where
  qcoh e := (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (idealPowι I E (e + 1))).symm inferInstance
  pow_le _ := le_rfl
  succ e := (sup_eq_right.2 (powSub_succ_le I E (e + 1))).symm

end GlobalTheory.CompanionTheory.GE
end
end

