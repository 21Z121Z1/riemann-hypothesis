import Mathlib
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0006
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

private theorem sum_smul_cols_eq_mul_vec {C R X : Type} [Field C] [CommRing R] [Algebra R C]
    [Fintype X] (B : Matrix X X C) (c : X → R) :
    (∑ j, c j • fun x => B x j) = B *ᵥ fun j => algebraMap R C (c j) := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply]
  simp only [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]

theorem mem_span_cols_iff {C R X : Type} [Field C] [CommRing R] [Algebra R C] [Fintype X]
    [DecidableEq X] (B : Matrix X X C) (hB : IsUnit B.det) (u : X → C) :
    u ∈ Submodule.span R (Set.range fun j x => B x j) ↔
      ∀ j, ∃ r : R, algebraMap R C r = (B⁻¹ *ᵥ u) j := by
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hinv' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ j
    refine ⟨c j, ?_⟩
    rw [sum_smul_cols_eq_mul_vec, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  · intro h
    choose c hc using h
    refine ⟨c, ?_⟩
    have e : (fun j => algebraMap R C (c j)) = B⁻¹ *ᵥ u := funext hc
    rw [sum_smul_cols_eq_mul_vec, e, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]

theorem exists_denominator {C R X : Type} [Field C] [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) (hv : v.Integers R) [Fintype X] [Nonempty X] (w : X → C) :
    ∃ c : R, c ≠ 0 ∧ ∀ d : R,
      (∀ j, ∃ r : R, algebraMap R C r = algebraMap R C d * w j) ↔ d ∈ Ideal.span {c} := by
  classical
  by_cases hall : ∀ j, v (w j) ≤ 1
  · have h10 : (1 : R) ≠ 0 := by
      intro h
      have h' := congrArg (algebraMap R C) h
      simp at h'
    refine ⟨1, h10, fun d => ?_⟩
    constructor
    · intro _
      simp [Ideal.span_singleton_one]
    · intro _ j
      apply hv.exists_of_le_one
      rw [map_mul]
      calc v (algebraMap R C d) * v (w j) ≤ 1 * 1 := mul_le_mul' (hv.map_le_one d) (hall j)
        _ = 1 := one_mul 1
  · push Not at hall
    obtain ⟨j1, hj1⟩ := hall
    obtain ⟨j0, -, hj0⟩ :=
      Finset.exists_max_image Finset.univ (fun j => v (w j)) Finset.univ_nonempty
    have hgt : 1 < v (w j0) := lt_of_lt_of_le hj1 (hj0 j1 (Finset.mem_univ _))
    have hw0 : w j0 ≠ 0 := by
      intro h
      simp [h] at hgt
    have hinvle : v (w j0)⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ hgt.le
    obtain ⟨c, hc⟩ := hv.exists_of_le_one hinvle
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact inv_ne_zero hw0 hc.symm
    refine ⟨c, hc0, fun d => ?_⟩
    rw [Ideal.mem_span_singleton, hv.dvd_iff_le, hc]
    constructor
    · intro h
      obtain ⟨r, hr⟩ := h j0
      have e : algebraMap R C d = (algebraMap R C d * w j0) * (w j0)⁻¹ :=
        (mul_inv_cancel_right₀ hw0 _).symm
      rw [e, map_mul, ← hr]
      exact mul_le_of_le_one_left zero_le (hv.map_le_one r)
    · intro h j
      apply hv.exists_of_le_one
      rw [map_mul]
      calc v (algebraMap R C d) * v (w j) ≤ v (w j0)⁻¹ * v (w j0) :=
            mul_le_mul' h (hj0 j (Finset.mem_univ _))
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hw0, map_one]

private theorem smul_algebra_map_char_eq {C R F : Type} [Field C] [CommRing R] [Algebra R C] [Field F]
    (χ : MulChar F R) (c : R) :
    (c • fun a => algebraMap R C (χ a)) = fun a => algebraMap R C (c * χ a) := by
  funext a
  simp only [Pi.smul_apply, Algebra.smul_def, map_mul]

theorem eig_rank_one : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ χ : MulChar F R, (∃ c : R, c ≠ 0 ∧ xIdeal AA.carrier χ = Ideal.span {c}) ∧ ∀ g, g ∈ eig AA.carrier χ ↔ ∃ c ∈ xIdeal AA.carrier χ, g = fun a => algebraMap R C (c * χ a) := by
  intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ AA _ χ
  obtain ⟨B, hB, hM⟩ := AA.lat
  have key : ∀ d : R, d ∈ xIdeal AA.carrier χ ↔
      (d • fun a => algebraMap R C (χ a)) ∈ AA.carrier := fun d => by
    simp only [xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc0, hc⟩ := exists_denominator v hv (B⁻¹ *ᵥ fun a => algebraMap R C (χ a))
    refine ⟨c, hc0, ?_⟩
    ext d
    rw [key, hM, mem_span_cols_iff B hB, ← hc d]
    refine forall_congr' fun j => exists_congr fun r => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
  · intro g
    constructor
    · rintro ⟨hgM, hg⟩
      have hint : ∀ x, ∃ r : R, algebraMap R C r = g x := AA.le_int hgM
      obtain ⟨r, hr⟩ := hint 1
      have hgf : g = fun a => algebraMap R C (r * χ a) := by
        funext a
        have h := hg a 1
        rw [smul_eq_mul, mul_one] at h
        rw [h, ← hr, map_mul]
        exact mul_comm _ _
      refine ⟨r, ?_, hgf⟩
      rw [key, smul_algebra_map_char_eq, ← hgf]
      exact hgM
    · rintro ⟨c, hc, rfl⟩
      rw [key, smul_algebra_map_char_eq] at hc
      refine ⟨hc, fun a x => ?_⟩
      simp only [smul_eq_mul, map_mul]
      ring

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegralStatement
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_generator_dual_integral : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (E : Type) [Field E] [NumberField E] (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → Submodule.span A {algebraMap A K d} = Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} → algebraMap A K d ≠ 0 ∧ (∀ k, algebraMap A K d * σ (dualInt E k) ∈ (algebraMap A K).range) ∧ ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A, ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt | exact GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualFamilyIsBasisStatement
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_family_is_basis : ∀ (V : Type) [CommRing V] (L : Type) [AddCommGroup L] [Module V L] (n : ℕ) (b : Module.Basis (Fin n) V L) (u : Fin n → L) (f : Fin n → (L →ₗ[V] V)) (N : V), IsUnit N → (∀ i j, f j (u i) = if i = j then N else 0) → LinearIndependent V u ∧ Submodule.span V (Set.range u) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit | exact GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit | (intros; apply GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNegStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_degree_neg : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (B : V →ₗ[K] V' →ₗ[K] K), IsBun C L → Function.Bijective B → IsBun C (dualLat C L B) ∧ deg C (dualLat C L B) = - deg C L ∧ dualLat C (dualLat C L B) B.flip = L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual | exact GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsTotallyRealEvenNegPlacesLocalNorm
section
namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

theorem exists_smul_mem_of_mem_span_val {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) {V : Type} [AddCommGroup V] [Module C V]
    [Module O V] [IsScalarTower O C V] (L : Submodule O V) {u : V}
    (hu : u ∈ Submodule.span C (L : Set V)) : ∃ c : C, c ≠ 0 ∧ c • u ∈ L := by
  have key : ∀ (a b : C) (x : V), b ≠ 0 → v a ≤ v b → b • x ∈ L → a • x ∈ L := by
    intro a b x hb hab hx
    have hvb : 0 < v b := (Valuation.pos_iff v).2 hb
    have h1 : v (a / b) ≤ 1 := by
      rw [map_div₀]
      exact (div_le_one hvb).2 hab
    obtain ⟨o, ho⟩ := hv.exists_of_le_one h1
    have h2 : a • x = o • (b • x) := by
      rw [← IsScalarTower.algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ hb]
    rw [h2]
    exact L.smul_mem o hx
  induction hu using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    rcases le_total (v a) (v b) with h | h
    · exact ⟨a, ha, by rw [smul_add]; exact L.add_mem hx (key a b y hb h hy)⟩
    · exact ⟨b, hb, by rw [smul_add]; exact L.add_mem (key b a x ha h hx) hy⟩
  | smul d x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    by_cases hd : d = 0
    · exact ⟨1, one_ne_zero, by simp [hd]⟩
    · exact ⟨a / d, div_ne_zero ha hd, by rw [smul_smul, div_mul_cancel₀ _ hd]; exact hx⟩

theorem latIn_isLattice : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (L : Submodule O V) (U : Submodule C V), L.FG → U ≤ Submodule.span C (L : Set V) → (latIn L U).IsLattice C := by
  intro C _ v O _ _ hv V _ _ _ _ L U hL hU
  have hfg := GlobalTheory.CompanionTheory.Ar.HT.fg_inf_restrictScalars_of_integers C v O hv V L U hL
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (U.subtype.restrictScalars O) := Subtype.val_injective
    apply Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars O) hinj
    convert hfg using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  · rw [eq_top_iff]
    intro u _
    obtain ⟨c, hc, hcu⟩ := exists_smul_mem_of_mem_span_val hv L (hU u.2)
    have h1 : c • u ∈ Submodule.span C (latIn L U : Set U) := Submodule.subset_span hcu
    have h2 := Submodule.smul_mem _ c⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulPStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_lattice_degree_mul_p : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)), IsBun C L → IsBun C (frobLat C p L) ∧ deg C (frobLat C p L) = p * deg C L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat | exact GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.DegFrob.deg_frobLat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionId
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem indOrder_id_eq_of_isHopfOrder : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → indOrder (MonoidHom.id T) A = A :=
  PositivityTheory.HtPt.Mh.ind_id

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderInductionInjectiveStatement
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_induction_injective : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (H : Type) [CommGroup H] (ι : H →* T), Function.Injective ι → ∀ A : Subalgebra R (H → R), IsHopfOrder A → IsHopfOrder (indOrder ι A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Induced.isHopfOrder_indOrder | exact GlobalTheory.CompanionTheory.Ar.BT.Induced.isHopfOrder_indOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Induced.isHopfOrder_indOrder <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtension
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem ext_tensor_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (A : Subalgebra R (T → R)), IsHopfOrder A → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) → IsHopfOrder (extOrder (algebraMap R R') A) ∧ ∃ e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A, ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) :=
  PositivityTheory.HtPt.Mh.ext_tensor

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealDescendingOneDimQuotientStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_descending_one_dim_quotient : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Finite A] (χ : A →ₐ[k] k) (e : A) (J : Ideal A), IsIdempotentElem e → χ e = 1 → (∀ t ∈ RingHom.ker χ, IsNilpotent (e * t)) → J ≤ Ideal.span {e} → J ≠ ⊥ → ∃ (J₁ : Ideal A) (t : A) (l : A →ₗ[k] k), J₁ < J ∧ t ∈ J ∧ (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) ∧ (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) ∧ (∀ a ∈ J₁, l a = 0) ∧ l t = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one | exact GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.StepIdeal.exists_colength_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralClosurePlaceRingsDataStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_section_associated_global_element : ∀ (F Ω X : Type) [Field F] [NumberField F] [Field Ω] (φ : F →+* Ω) (R : X → Subring Ω) (s : X → Ω) (pl : X → Option (HeightOneSpectrum (𝓞 F))) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ), (∀ x, ∀ z : Ω, IsIntegral (R x) z → z ∈ R x) → (∀ x, pl x = none → (∀ a : F, φ a ∈ R x) ∧ s x ∈ R x ∧ s x ≠ 0 ∧ (s x)⁻¹ ∈ R x) → (∀ x v, pl x = some v → (∀ a : F, v.valuation F a ≤ 1 → φ a ∈ R x) ∧ ∃ (m : ℕ) (n : ℤ) (π : F), 0 < m ∧ (n : ℚ) = m * r v ∧ v.valuation F π = WithZero.exp (-1 : ℤ) ∧ s x ≠ 0 ∧ s x ^ m / φ π ^ n ∈ R x ∧ φ π ^ n / s x ^ m ∈ R x) → ∃ (M : ℕ) (α : F), 0 < M ∧ α ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ n : ℤ, (n : ℚ) = M * r v ∧ v.valuation F α = WithZero.exp (-n)) ∧ ∀ x, s x ^ M / φ α ∈ R x ∧ φ α / s x ^ M ∈ R x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_global_generator | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_global_generator | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_global_generator <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelGraphBaseChangeHoldsStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_graph_base_change_holds : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (∀ i, (D.bc RC).kk τ i = spanOver RC (bcMap Ω C _ '' D.kk τ i)) ∧ ∀ i, (D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (Prod.map (algebraMap Ω C) (bcMap Ω C _) '' D.stepGraph τ (χ τ) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change | exact GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change <;> assumption)
end

