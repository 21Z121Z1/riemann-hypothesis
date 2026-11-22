import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfNormNeZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalNormApproxOfLocalPadicNorm
section
open scoped TensorProduct Classical

namespace GlobalTheory.LocalApprox

theorem isUnit_of_isUnit_one_tmul (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (b : E) (hb : IsUnit ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b)) : IsUnit b := by
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] E) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap ℚ ℚ_[ℓ]).injective
  have h1 : Function.Injective (LinearMap.mulLeft ℚ b) := by
    intro x y hxy
    apply hinj
    have h := congrArg (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] E) hxy
    simp only [LinearMap.mulLeft_apply, map_mul] at h
    exact hb.mul_left_cancel h
  obtain ⟨w, hw⟩ := LinearMap.injective_iff_surjective.1 h1 1
  have hw' : b * w = 1 := hw
  exact ⟨⟨b, w, hw', by rw [mul_comm]; exact hw'⟩, rfl⟩

theorem exists_rat_mul_unit (ℓ : ℕ) [Fact ℓ.Prime] (u : ℚ_[ℓ]ˣ) :
    ∃ c : ℚ, c ≠ 0 ∧ ∃ r : ℤ_[ℓ]ˣ, (u : ℚ_[ℓ]) = algebraMap ℚ ℚ_[ℓ] c * ((r : ℤ_[ℓ]) : ℚ_[ℓ]) := by
  have hu : 0 < ‖(u : ℚ_[ℓ])‖ := norm_pos_iff.2 u.ne_zero
  obtain ⟨c, hc⟩ := Padic.rat_dense ℓ (u : ℚ_[ℓ]) hu
  have hn : ‖(c : ℚ_[ℓ])‖ = ‖(u : ℚ_[ℓ])‖ := by
    have h : (c : ℚ_[ℓ]) = (u : ℚ_[ℓ]) + -((u : ℚ_[ℓ]) - c) := by ring
    have hlt : ‖-((u : ℚ_[ℓ]) - c)‖ < ‖(u : ℚ_[ℓ])‖ := by rwa [norm_neg]
    rw [h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]
  have hc0 : (c : ℚ_[ℓ]) ≠ 0 := norm_pos_iff.1 (hn ▸ hu)
  have h1 : ‖(u : ℚ_[ℓ]) / c‖ = 1 := by rw [norm_div, hn, div_self hu.ne']
  refine ⟨c, fun h => hc0 (by simp [h]), PadicInt.mkUnits h1, ?_⟩
  rw [PadicInt.mkUnits_eq, eq_ratCast, mul_div_cancel₀ _ hc0]

theorem main : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (τ : E →ₐ[ℚ] E) (ℓ : ℕ) [Fact ℓ.Prime]
    (a : E) (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] E)ˣ), IsUnit a →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] E) (u : ℚ_[ℓ]) *
      ((z : ℚ_[ℓ] ⊗[ℚ] E) * Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ (z : ℚ_[ℓ] ⊗[ℚ] E)) →
    ∃ (c : ℚ) (b x y : E), c ≠ 0 ∧ IsUnit b ∧ a = x * (algebraMap ℚ E c * (b * τ b)) ∧
      algebraMap ℚ E c * (b * τ b) = y * a ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y) := by
  intro E _ _ _ τ ℓ _ a u z ha hau
  set S := ℚ_[ℓ] ⊗[ℚ] E
  set τℓ : S →ₐ[ℚ_[ℓ]] S := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ with hτℓ
  set ι : E →ₐ[ℚ] S := Algebra.TensorProduct.includeRight with hι
  have hιapp : ∀ w : E, ι w = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w := fun w => rfl
  have hτι : ∀ w : E, τℓ (ι w) = ι (τ w) := fun w => by
    show Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τ ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] τ w
    rw [Algebra.TensorProduct.map_tmul]; rfl
  have hιq : ∀ q : ℚ, ι (algebraMap ℚ E q) = algebraMap ℚ_[ℓ] S (algebraMap ℚ ℚ_[ℓ] q) := fun q => by
    rw [ι.commutes, IsScalarTower.algebraMap_apply ℚ ℚ_[ℓ] S]
  have hint : ∀ t : ℤ_[ℓ], IsIntegral ℤ_[ℓ] (algebraMap ℚ_[ℓ] S (t : ℚ_[ℓ])) := fun t => by
    rw [show (t : ℚ_[ℓ]) = algebraMap ℤ_[ℓ] ℚ_[ℓ] t from rfl, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  have hτint : ∀ w : S, IsIntegral ℤ_[ℓ] w → IsIntegral ℤ_[ℓ] (τℓ w) := fun w hw =>
    hw.map (τℓ.restrictScalars ℤ_[ℓ])
  obtain ⟨c, hc0, r, hur⟩ := exists_rat_mul_unit ℓ u
  obtain ⟨b, s, hs, hb⟩ := GlobalTheory.T.exists_approx_unit_padic_tensor E ℓ z
  obtain ⟨ρ, hρ, hρint⟩ := GlobalTheory.T.exists_integral_inv_one_add_prime_mul_padic ℓ S s hs
  set v : S := 1 + (ℓ : S) * s with hv
  have hvint : IsIntegral ℤ_[ℓ] v := by
    refine isIntegral_one.add (IsIntegral.mul ?_ hs)
    rw [show (ℓ : S) = algebraMap ℤ_[ℓ] S ℓ by simp]
    exact isIntegral_algebraMap
  have hbU : IsUnit b := isUnit_of_isUnit_one_tmul E ℓ b (by
    rw [hb]; exact z.isUnit.mul ⟨⟨_, ρ, hρ, by rw [mul_comm]; exact hρ⟩, rfl⟩)
  set m : E := algebraMap ℚ E c * (b * τ b) with hm
  have hmU : IsUnit m := ((isUnit_iff_ne_zero.2 hc0).map (algebraMap ℚ E)).mul (hbU.mul (hbU.map τ))
  obtain ⟨mi, hmi⟩ : ∃ mi : E, m * mi = 1 := ⟨_, hmU.mul_val_inv⟩
  obtain ⟨ai, hai⟩ : ∃ ai : E, a * ai = 1 := ⟨_, ha.mul_val_inv⟩

  set R : S := algebraMap ℚ_[ℓ] S ((r : ℤ_[ℓ]) : ℚ_[ℓ]) with hR
  set Ri : S := algebraMap ℚ_[ℓ] S (((r⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) with hRi
  set C : S := algebraMap ℚ_[ℓ] S (algebraMap ℚ ℚ_[ℓ] c) with hC
  set U : S := algebraMap ℚ_[ℓ] S (u : ℚ_[ℓ]) with hU
  have hUCR : U = C * R := by rw [hU, hur, map_mul]
  have hRRi : R * Ri = 1 := by
    rw [hR, hRi, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      PadicInt.coe_one, map_one]
  have h1 : ι a = U * ((z : S) * τℓ z) := hau
  have h2 : ι m = C * (((z : S) * v) * (τℓ z * τℓ v)) := by
    rw [hm, map_mul, map_mul, hιq, hτι b |>.symm, hιapp b, hb, map_mul]
  have h4 : v * ρ = 1 := hρ
  have h5 : τℓ v * τℓ ρ = 1 := by rw [← map_mul, h4, map_one]
  have h3 : ι m * ι mi = 1 := by rw [← map_mul, hmi, map_one]
  have h3' : ι a * ι ai = 1 := by rw [← map_mul, hai, map_one]
  have hx : ι (a * mi) = R * ρ * τℓ ρ := by
    have hK : R * ρ * τℓ ρ * ι m = ι a := by
      rw [h2, h1, hUCR]
      linear_combination (C * R * (z : S) * τℓ z * τℓ v * τℓ ρ) * h4 + (C * R * (z : S) * τℓ z) * h5
    rw [map_mul]
    linear_combination (-ι mi) * hK + (R * ρ * τℓ ρ) * h3
  have hy : ι (m * ai) = Ri * v * τℓ v := by
    have hK : Ri * v * τℓ v * ι a = ι m := by
      rw [h2, h1, hUCR]
      linear_combination (C * (z : S) * v * τℓ z * τℓ v) * hRRi
    rw [map_mul]
    linear_combination (-ι ai) * hK + (Ri * v * τℓ v) * h3'
  obtain ⟨d1, hd1, hx1⟩ := GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral E ℓ (a * mi) (by
    rw [← hιapp, hx]
    exact ((hint _).mul hρint).mul (hτint _ hρint))
  obtain ⟨d2, hd2, hy2⟩ := GlobalTheory.T.exists_coprime_mul_isIntegral_of_padic_integral E ℓ (m * ai) (by
    rw [← hιapp, hy]
    exact ((hint _).mul hvint).mul (hτint _ hvint))
  refine ⟨c, b, a * mi, m * ai, hc0, hbU, ?_, ?_, d1 * d2, ?_, ?_, ?_⟩
  · linear_combination (-a) * hmi
  · linear_combination (-m) * hai
  · intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : ℓ.Prime)).1 h with h | h
    · exact hd1 h
    · exact hd2 h
  · have : ((d1 * d2 : ℕ) : E) * (a * mi) = (d2 : E) * ((d1 : E) * (a * mi)) := by push_cast; ring
    rw [this]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d2 : ℤ))).mul hx1
  · have : ((d1 * d2 : ℕ) : E) * (m * ai) = (d1 : E) * ((d2 : E) * (m * ai)) := by push_cast; ring
    rw [this]
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (d1 : ℤ))).mul hy2

end GlobalTheory.LocalApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfNormNeZeroStatement
section
open GlobalTheory.UnitLemma Polynomial Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianModel_of_norm_ne_zero : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (x : B.Aˣ), Module.finrank K.E B.A = n → B.σ (x : B.A) = x → B.N x ≠ 0 → ∃ (γ : Matrix (Fin n) (Fin n) K.E) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by
  first | exact @GlobalTheory.InertUnitOrb.ModelOfN.exists_model | exact GlobalTheory.InertUnitOrb.ModelOfN.exists_model | (intros; apply GlobalTheory.InertUnitOrb.ModelOfN.exists_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomAffineHilbertBaseSectionRingHomStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_affineHilbertBaseSectionRingHom : ∀ (Z : Scheme.{0}) (C : Type) [CommRing C] (Φ : C →+* Γ(Z, ⊤)), ∃ h : Z ⟶ Spec (CommRingCat.of C), GlobalTheory.HilbAff.secAlg C h ⊤ = Φ := by
  first | (exact @GlobalTheory.HilbAff.exists_hom_secAlg_top) | (exact GlobalTheory.HilbAff.exists_hom_secAlg_top) | (intros; apply GlobalTheory.HilbAff.exists_hom_secAlg_top  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomJet
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SquareLiftLemmas

open CategoryTheory GlobalTheory.AnPer GlobalTheory.AnPer.Charts

def liftSq {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) : TrivSqZeroExt O (Fin g → O) →+* C where
  toFun x := ρ x.fst + ∑ a, ρ (x.snd a) * n a
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, Pi.add_apply, map_add, add_mul,
      Finset.sum_add_distrib]
    ring
  map_mul' x y := by
    have h0 : (∑ a, ρ (x.snd a) * n a) * (∑ b, ρ (y.snd b) * n b) = 0 := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun b _ ↦ ?_
      rw [mul_mul_mul_comm, hn, mul_zero]
    have h1 : ∀ a, ρ ((x * y).snd a) * n a =
        ρ x.fst * (ρ (y.snd a) * n a) + (ρ (x.snd a) * n a) * ρ y.fst := fun a ↦ by
      have : (x * y).snd a = x.fst * y.snd a + x.snd a * y.fst := by
        simp [TrivSqZeroExt.snd_mul, mul_comm]
      rw [this, map_add, map_mul, map_mul]; ring
    rw [add_mul, mul_add, mul_add, h0, add_zero, TrivSqZeroExt.fst_mul, map_mul]
    simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring

theorem liftSq_apply {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (x : TrivSqZeroExt O (Fin g → O)) :
    liftSq ρ n hn x = ρ x.fst + ∑ a, ρ (x.snd a) * n a := rfl

theorem liftSq_inl {g : ℕ} {O C : Type} [CommRing O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (h : O) : liftSq ρ n hn (TrivSqZeroExt.inl h) = ρ h := by
  simp [liftSq_apply]

theorem liftSq_sec {g : ℕ} {O C : Type} [CommRing O] [Algebra ℂ O] [CommRing C] (ρ : O →+* C) (n : Fin g → C)
    (hn : ∀ a b, n a * n b = 0) (D : Fin g → Derivation ℂ O O) (h : O) :
    liftSq ρ n hn (tszeSec D h) = ρ h + ∑ a, ρ (D a h) * n a := by
  rw [liftSq_apply, fst_tszeSec]
  simp only [snd_tszeSec]

theorem exists_hom_jet {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C)
    (hdeg : Hom.deg f₁ = Hom.deg f₂) (hJ : ∀ a, n a ∈ T.J) (hn : ∀ a b, n a * n b = 0)
    (h : ∀ x : Hol (K.W k), Hom.φ f₂ x = Hom.φ f₁ x + ∑ a, Hom.φ f₁ (dw a x) * n a) :
    ∃ χ : K.jet k ⟶ T, Hom.deg χ = Hom.deg f₁ ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        Hom.φ χ x = Hom.φ f₁ x.fst + ∑ a, Hom.φ f₁ (x.snd a) * n a := by
  let ρ : Hol (K.W k) →+* T.C := (Hom.φ f₁ : (K.triv k).C →+* T.C)
  letI := (K.jet k).alg
  letI := (K.triv k).alg
  let φ : (K.jet k).C →ₐ[Hol F.V] T.C :=
    { liftSq ρ n hn with
      commutes' := fun f ↦ (liftSq_inl ρ n hn (K.cst k f)).trans ((Hom.φ f₁).commutes f) }
  have hφ : ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)), φ x = liftSq ρ n hn x := fun _ ↦ rfl
  have hcomp : (φ : (K.jet k).C →+* T.C).comp (K.jet k).ρ = (Hom.φ f₁ : (K.triv k).C →+* T.C).comp (K.triv k).ρ :=
    RingHom.ext fun x ↦ liftSq_inl ρ n hn x
  let χ : K.jet k ⟶ T :=
    { φ := φ
      deg := Hom.deg f₁
      le := Hom.le f₁
      mem := fun c hc ↦ by
        have hc' : TrivSqZeroExt.fst c = 0 := hc
        rw [hφ, liftSq_apply, hc', map_zero, zero_add]
        exact T.J.sum_mem fun a _ ↦ T.J.mul_mem_left _ (hJ a)
      close := by rw [hcomp]; exact Hom.close f₁ }
  refine ⟨χ, rfl, hom_ext (fun c ↦ ?_) (zero_add _), hom_ext (fun c ↦ ?_) ((zero_add _).trans hdeg), fun _ ↦ rfl⟩
  · change liftSq ρ n hn (TrivSqZeroExt.inl (sh (K.le_refl k) c)) = _
    rw [sh_refl, liftSq_inl]; rfl
  · change liftSq ρ n hn (tszeSec dw c) = _
    refine Eq.trans ?_ (h c).symm
    exact liftSq_sec ρ n hn dw c

end GlobalTheory.SquareLiftLemmas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousIdealOverReesAlgebra
section
open MvPolynomial

namespace GlobalTheory.ReesHomogeneous

variable {σ : Type} {R : Type} [CommRing R]

theorem homogeneousComponent_mul_of_homogeneous_left {S : Type} [CommRing S] {k : ℕ} (n : ℕ)
    {P : MvPolynomial σ S} (hP : P.IsHomogeneous k) (Q : MvPolynomial σ S) :
    homogeneousComponent n (P * Q) = if k ≤ n then P * homogeneousComponent (n - k) Q else 0 := by
  classical
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := S)
  have h := DirectSum.coe_decompose_mul_of_left_mem (homogeneousSubmodule σ S) (a := P) (b := Q) n
    ((mem_homogeneousSubmodule k P).2 hP)
  have e : ∀ (m : ℕ) (T : MvPolynomial σ S),
      ((DirectSum.decompose (homogeneousSubmodule σ S) T m : homogeneousSubmodule σ S m) :
        MvPolynomial σ S) = homogeneousComponent m T :=
    fun m T => MvPolynomial.decomposition.decompose'_apply T m
  rw [e, e] at h
  exact h

noncomputable def piece (I : Ideal R) (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) :
    MvPolynomial σ R :=
  ∑ m ∈ F.support, monomial m (((coeff m F : reesAlgebra I) : Polynomial R).coeff e)

variable {I : Ideal R}

@[simp] theorem coeff_piece (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    coeff m (piece I e F) = (coeff m F).1.coeff e := by
  classical
  simp only [piece, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h]; rfl

@[simp] theorem piece_zero (e : ℕ) : piece I e (0 : MvPolynomial σ (reesAlgebra I)) = 0 := by
  ext m; simp

@[simp] theorem piece_add (e : ℕ) (F G : MvPolynomial σ (reesAlgebra I)) :
    piece I e (F + G) = piece I e F + piece I e G := by
  ext m; simp

theorem piece_X_mul (e : ℕ) (i : σ) (F : MvPolynomial σ (reesAlgebra I)) :
    piece I e (X i * F) = X i * piece I e F := by
  classical
  ext m
  rw [coeff_piece, coeff_X_mul', coeff_X_mul']
  split_ifs <;> simp

theorem piece_C_mul (e : ℕ) (r : reesAlgebra I) (F : MvPolynomial σ (reesAlgebra I)) :
    piece I e (C r * F) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal e, C ((r : Polynomial R).coeff p.1) * piece I p.2 F := by
  ext m
  simp [coeff_sum, coeff_C_mul, Polynomial.coeff_mul]

theorem piece_isHomogeneous (e : ℕ) {d : ℕ} {F : MvPolynomial σ (reesAlgebra I)}
    (hF : F.IsHomogeneous d) : (piece I e F).IsHomogeneous d := by
  intro m hm
  apply hF
  intro h
  apply hm
  rw [coeff_piece, h]
  simp

theorem coeff_piece_mem (e : ℕ) (F : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    coeff m (piece I e F) ∈ I ^ e := by
  rw [coeff_piece]
  exact (mem_reesAlgebra_iff I _).1 (coeff m F).2 e

end GlobalTheory.ReesHomogeneous

namespace GlobalTheory.ReesHomogeneous

variable {σ : Type} {R : Type} [CommRing R] {I : Ideal R}

theorem C_mul_mem_of_pow (J : ℕ → Ideal (MvPolynomial σ R))
    (H : ∀ (e t : ℕ) (a : R) (F : MvPolynomial σ R), a ∈ I → F.IsHomogeneous t →
      (∀ m, coeff m F ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) :
    ∀ (k : ℕ) (b : R), b ∈ I ^ k → ∀ (l t : ℕ) (P : MvPolynomial σ R), P.IsHomogeneous t →
      (∀ m, coeff m P ∈ I ^ l) → P ∈ J l → C b * P ∈ J (l + k) := by
  intro k
  induction k with
  | zero =>
    intro b _ l t P _ _ hP
    simpa using (J l).mul_mem_left (C b) hP
  | succ k ih =>
    intro b hb l t P hPh hPc hP
    rw [pow_succ] at hb
    refine Submodule.mul_induction_on hb ?_ ?_
    · intro x hx y hy
      have h1 := ih x hx l t P hPh hPc hP
      have h2 : ∀ m, coeff m (C x * P) ∈ I ^ (l + k) := by
        intro m
        rw [coeff_C_mul, pow_add, mul_comm (I ^ l)]
        exact Ideal.mul_mem_mul hx (hPc m)
      have h3 := H (l + k) t y (C x * P) hy (hPh.C_mul x) h2 h1
      rw [show C (x * y) * P = C y * (C x * P) by rw [C_mul]; ring]
      simpa [add_assoc] using h3
    · intro x y hx hy
      rw [C_add, add_mul]
      exact add_mem hx hy

def reesIdeal (I : Ideal R) (J : ℕ → Ideal (MvPolynomial σ R))
    (H : ∀ (e t : ℕ) (a : R) (F : MvPolynomial σ R), a ∈ I → F.IsHomogeneous t →
      (∀ m, coeff m F ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) :
    Ideal (MvPolynomial σ (reesAlgebra I)) where
  carrier := {F | ∀ d e, piece I e (homogeneousComponent d F) ∈ J e}
  zero_mem' := by intro d e; simp
  add_mem' := by
    intro F G hF hG d e
    rw [map_add, piece_add]
    exact add_mem (hF d e) (hG d e)
  smul_mem' := by
    intro c F hF
    rw [smul_eq_mul]
    revert F
    induction c using MvPolynomial.induction_on with
    | C r =>
      intro F hF d e
      rw [homogeneousComponent_C_mul, piece_C_mul]
      refine Ideal.sum_mem _ fun p hp => ?_
      have hpe : p.2 + p.1 = e := by rw [add_comm]; exact Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      rw [← hpe]
      exact C_mul_mem_of_pow J H p.1 _ ((mem_reesAlgebra_iff I _).1 r.2 p.1) p.2 d _
        (piece_isHomogeneous p.2 (homogeneousComponent_isHomogeneous d F))
        (coeff_piece_mem p.2 _) (hF d p.2)
    | add p q hp hq =>
      intro F hF d e
      rw [add_mul, map_add, piece_add]
      exact add_mem (hp hF d e) (hq hF d e)
    | mul_X p i hp =>
      intro F hF
      rw [mul_assoc]
      apply hp
      intro d e
      rw [homogeneousComponent_mul_of_homogeneous_left d (isHomogeneous_X _ i)]
      split_ifs
      · rw [piece_X_mul]
        exact (J e).mul_mem_left _ (hF _ e)
      · simp

end GlobalTheory.ReesHomogeneous

namespace GlobalTheory.ReesHomogeneous

theorem exists_homogeneous_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, coeff m F ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ 𝔞 : Ideal (MvPolynomial (Fin (n + 1)) (reesAlgebra I)), (∀ F ∈ 𝔞, ∀ d, homogeneousComponent d F ∈ 𝔞) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) (reesAlgebra I)), F.IsHomogeneous t → (F ∈ 𝔞 ↔ ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R), (∀ m, coeff m G = (coeff m F).1.coeff e) → G ∈ J e) := by
  intro R _ I n J H
  refine ⟨reesIdeal I J H, ?_, ?_⟩
  · intro F hF d d' e
    show piece I e (homogeneousComponent d' (homogeneousComponent d F)) ∈ J e
    rw [homogeneousComponent_of_mem (homogeneousComponent_mem d F)]
    split_ifs
    · exact hF d e
    · simp
  · intro t F hFt
    have hG : ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R),
        (∀ m, coeff m G = (coeff m F).1.coeff e) → G = piece I e F := by
      intro e G hG
      ext m
      rw [hG, coeff_piece]
    constructor
    · intro hF e G hGc
      rw [hG e G hGc]
      have := hF t e
      rwa [homogeneousComponent_eq_self hFt] at this
    · intro h d e
      show piece I e (homogeneousComponent d F) ∈ J e
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule t F).2 hFt)]
      split_ifs
      · exact h e _ fun m => coeff_piece e F m
      · simp

end GlobalTheory.ReesHomogeneous
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafComapEqOfOpenCoverStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheaf_comap_eq_of_openCover : ∀ {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : X, ∃ i y, f i y = x) →
    ∀ (J : ∀ i, (V i).IdealSheafData),
    (∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') →
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i := by
  first | (exact @GlobalTheory.IdealGlue.exists_comap_eq) | (exact GlobalTheory.IdealGlue.exists_comap_eq) | (intros; apply GlobalTheory.IdealGlue.exists_comap_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitDetKrylovMatrixOfSeparable
section
open Matrix Polynomial

namespace GlobalTheory.LeviDesc.Krylov

theorem exists_isUnit_det_krylov_of_separable {F : Type} [Field F] {r : ℕ}
    (y : Matrix (Fin r) (Fin r) F) (hs : y.charpoly.Separable) :
    ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field y hs
  exact ⟨v, isUnit_iff_ne_zero.2 hv⟩

example : ∀ {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F), y.charpoly.Separable → ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det :=
  @exists_isUnit_det_krylov_of_separable

end GlobalTheory.LeviDesc.Krylov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMulSubMemJacobsonOfFiniteResidueFielStatement
section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_mul_involution_sub_mem_jacobson : ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] (τ : A →+* A), (∀ a, τ (τ a) = a) → ∀ θ : A, IsUnit (θ - τ θ) → ∀ a : A, IsUnit a → τ a = a → ∃ t : A, IsUnit t ∧ t * τ t - a ∈ (⊥ : Ideal A).jacobson := by
  first | (exact @GlobalTheory.exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField) | (exact GlobalTheory.exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField) | (intros; apply GlobalTheory.exists_isUnit_mul_sub_mem_jacobson_of_finite_residueField  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeRelativeLengthOfSmulLeStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeRelativeLength_of_smul_le : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → ∀ (X' X : Submodule (Int0 v) M), X' ≤ X → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ c : Int0 v, c ≠ 0 → (∀ x ∈ X, c • x ∈ X') → ∃ r : ℝ, RelLen v X' X r := by
  first | exact @GlobalTheory.SubLen.exists_relLen_of_smul_le | exact GlobalTheory.SubLen.exists_relLen_of_smul_le | (intros; apply GlobalTheory.SubLen.exists_relLen_of_smul_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftToCompleteDvrOfFiniteStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_to_complete_dvr_of_finite' : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R], Function.Injective (algebraMap A R) →
    Module.Finite A R → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ρ : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ ρ.comp (algebraMap A R) = f.comp h := by
  first | exact @GlobalTheory.exists_lift_to_complete_dvr_of_finite | exact GlobalTheory.exists_lift_to_complete_dvr_of_finite | (intros; apply GlobalTheory.exists_lift_to_complete_dvr_of_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsOfSeparableStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lifts_of_separable_reduction : ∀ (D : ℕ) (P : Polynomial (MvPowerSeries (Fin D) ℂ)), P.Monic → (P.map (MvPowerSeries.constantCoeff (σ := Fin D) (R := ℂ))).Separable → ∃ θ : Fin P.natDegree → MvPowerSeries (Fin D) ℂ, Function.Injective θ ∧ ∀ j, P.IsRoot (θ j) := by
  first | exact @GlobalTheory.HenselSplitPS.exists_lifts_of_separable | exact GlobalTheory.HenselSplitPS.exists_lifts_of_separable | (intros; apply GlobalTheory.HenselSplitPS.exists_lifts_of_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalPushoutUnramifiedCharZeroStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_pushout_unramified_charZero : ∀ (A V V' : Type) [CommRing A] [CommRing V] [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (f : A →+* V) (f' : A →+* V'), f'.Flat → (maximalIdeal V).comap f = (maximalIdeal V').comap f' → ((maximalIdeal V).comap f).map f = maximalIdeal V → ((maximalIdeal V').comap f').map f' = maximalIdeal V' → CharZero (ResidueField V) → ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (g : V →+* B) (g' : V' →+* B), g.comp f = g'.comp f' ∧ g.Flat ∧ (maximalIdeal V).map g = maximalIdeal B ∧ (maximalIdeal V').map g' = maximalIdeal B := by
  first | exact @GlobalTheory.UnramPushout.exists_local_pushout | exact GlobalTheory.UnramPushout.exists_local_pushout | (intros; apply GlobalTheory.UnramPushout.exists_local_pushout <;> assumption)
end

