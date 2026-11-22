import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0574
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtCoeffFockColumnSubstitutionExpStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_coeff_fockColumnSubstitution_exp : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a)
    (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
    HasDerivAt (fun h : ℝ => MvPolynomial.coeff m (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R))
      (MvPolynomial.coeff m (GlobalTheory.ColLie.colDer τ S R)) 0 := by
  first | exact @GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp | exact GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp | (intros; apply GlobalTheory.ColLie.hasDerivAt_coeff_colSub_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinMovedPointStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_hilbertEisenstein_movedPoint : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (z : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → (∀ i, 1 + z i * c ≠ 0 ∧ 0 < (τ + t * z i / (1 + z i * c)).im) → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  first | exact @GlobalTheory.HilbFam.hasSum_movedPoint | exact GlobalTheory.HilbFam.hasSum_movedPoint | (intros; apply GlobalTheory.HilbFam.hasSum_movedPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCommOfIrreducibleMultiplicityLeOne
section
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

section
variable {H : Type} [Group H] (U : Subgroup H) [Fintype U] (χ : H → ℂ)

def heckeIdem {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V) : Module.End ℂ V :=
  ((Fintype.card U : ℂ))⁻¹ • ∑ u : U, χ (u : H)⁻¹ • τ (u : H)

theorem heckeIdem_apply {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V) (v : V) :
    heckeIdem U χ τ v = ((Fintype.card U : ℂ))⁻¹ • ∑ u : U, χ (u : H)⁻¹ • τ (u : H) v := by
  simp [heckeIdem, LinearMap.sum_apply]

theorem heckeIdem_mem (hm : ∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y)
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V) (v : V) :
    heckeIdem U χ τ v ∈ eig τ (U : Set H) χ := by
  rw [heckeIdem_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [mem_eig]
  intro g hg
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : U)) _ _ ?_
  intro u
  have h1 : χ (u : H)⁻¹ = χ g * χ (g * u)⁻¹ := by
    rw [← hm (g) hg _ (U.inv_mem (U.mul_mem hg u.2))]
    have h2 := hm _ (U.inv_mem (U.mul_mem hg u.2)) g hg
    have h3 := hm (g) hg _ (U.inv_mem (U.mul_mem hg u.2))
    rw [h3, mul_comm (χ g), ← h2]
    simp
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_smul, smul_smul, map_mul, h1]
  rfl

theorem heckeIdem_of_mem (hm : ∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y) (h1 : χ 1 = 1)
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V) (v : V)
    (hv : v ∈ eig τ (U : Set H) χ) : heckeIdem U χ τ v = v := by
  rw [heckeIdem_apply]
  rw [mem_eig] at hv
  have : ∀ u : U, χ (u : H)⁻¹ • τ (u : H) v = v := by
    intro u
    rw [hv u u.2, smul_smul, ← hm _ (U.inv_mem u.2) _ u.2, inv_mul_cancel, h1, one_smul]
  simp only [this, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]

theorem heckeIdem_sub {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V)
    (W : Subrepresentation τ) (w : W.toSubmodule) :
    ((heckeIdem U χ W.toRepresentation w : W.toSubmodule) : V) = heckeIdem U χ τ w := by
  rw [heckeIdem_apply, heckeIdem_apply]
  simp [Subrepresentation.toRepresentation]

theorem heckeIdem_comm_of_le_one (hm : ∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ H V)
    (hr : finrank ℂ (eig τ (U : Set H) χ) ≤ 1) (g h : H) (v : V) :
    heckeIdem U χ τ (τ g (heckeIdem U χ τ (τ h (heckeIdem U χ τ v)))) =
      heckeIdem U χ τ (τ h (heckeIdem U χ τ (τ g (heckeIdem U χ τ v)))) := by
  obtain ⟨w0, hw0⟩ := finrank_le_one_iff.mp hr
  have key : ∀ x, ∃ c : ℂ, heckeIdem U χ τ x = c • (w0 : V) := by
    intro x
    obtain ⟨c, hc⟩ := hw0 ⟨_, heckeIdem_mem U χ hm τ x⟩
    exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
  obtain ⟨c, hc⟩ := key v
  obtain ⟨a, ha⟩ := key (τ g w0)
  obtain ⟨b, hb⟩ := key (τ h w0)
  simp only [hc, map_smul, ha, hb, smul_smul]
  congr 1
  ring

theorem heckeIdem_comm [Finite H] (hm : ∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y)
    (hirr : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ H W),
      τ.IsIrreducible → finrank ℂ (eig τ (U : Set H) χ) ≤ 1) (g h : H) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ H V),
      finrank ℂ V = n → ∀ v : V,
    heckeIdem U χ τ (τ g (heckeIdem U χ τ (τ h (heckeIdem U χ τ v)))) =
      heckeIdem U χ τ (τ h (heckeIdem U χ τ (τ g (heckeIdem U χ τ v)))) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ τ hn v
    by_cases hi : τ.IsIrreducible
    · exact heckeIdem_comm_of_le_one U χ hm τ (hirr V τ hi) g h v
    rcases subsingleton_or_nontrivial V with hs | hs
    · exact Subsingleton.elim _ _
    have hex : ∃ W : Subrepresentation τ, W ≠ ⊥ ∧ W ≠ ⊤ := by
      by_contra hc
      push Not at hc
      apply hi
      haveI : Nontrivial (Subrepresentation τ) := ⟨⊥, ⊤, fun e => by
        have := congrArg Subrepresentation.toSubmodule e
        exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) this⟩
      exact ⟨fun W => by
        by_cases hW : W = ⊥
        · exact Or.inl hW
        · exact Or.inr (hc W hW)⟩
    obtain ⟨W, hb, ht⟩ := hex
    haveI : NeZero (Nat.card H : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
    have hss : τ.IsSemisimpleRepresentation := inferInstance
    obtain ⟨W', hW'⟩ := hss.exists_isCompl W
    have ht' : W' ≠ ⊤ := by
      rintro rfl
      exact hb (by simpa using hW'.disjoint)
    have sub : ∀ X : Subrepresentation τ, X ≠ ⊤ → ∀ v ∈ X.toSubmodule,
        heckeIdem U χ τ (τ g (heckeIdem U χ τ (τ h (heckeIdem U χ τ v)))) =
      heckeIdem U χ τ (τ h (heckeIdem U χ τ (τ g (heckeIdem U χ τ v)))) := by
      intro X hX v hv
      have hlt : finrank ℂ X.toSubmodule < n := by
        rw [← hn]
        refine Submodule.finrank_lt ?_
        intro e
        exact hX (Subrepresentation.toSubmodule_injective e)
      have := congrArg Subtype.val (ih _ hlt X.toSubmodule X.toRepresentation rfl ⟨v, hv⟩)
      have hτ : ∀ (k : H) (x : X.toSubmodule), ((X.toRepresentation k x : X.toSubmodule) : V) = τ k x :=
        fun _ _ => rfl
      simpa only [heckeIdem_sub, hτ] using this
    have hsup : W.toSubmodule ⊔ W'.toSubmodule = ⊤ :=
      congrArg Subrepresentation.toSubmodule hW'.sup_eq_top
    have hv : v ∈ W.toSubmodule ⊔ W'.toSubmodule := hsup ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp hv
    simp only [map_add, sub W ht a ha, sub W' ht' b hb']

end

theorem exists_idem_hecke_comm : ∀ (H : Type) [Group H] [Finite H] (U : Subgroup H) (χ : H → ℂ), (∀ x ∈ U, ∀ y ∈ U, χ (x * y) = χ x * χ y) → χ 1 = 1 → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ H W), τ.IsIrreducible → finrank ℂ (eig τ (U : Set H) χ) ≤ 1) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ H V), ∃ e : Module.End ℂ V, e * e = e ∧ (∀ v ∈ eig τ (U : Set H) χ, e v = v) ∧ (∀ T : Module.End ℂ V, (∀ g, Commute T (τ g)) → Commute T e) ∧ ∀ g h : H, e * τ g * e * τ h * e = e * τ h * e * τ g * e := by
  intro H _ _ U χ hm h1 hirr V _ _ _ τ
  letI : Fintype U := Fintype.ofFinite U
  refine ⟨heckeIdem U χ τ, ?_, heckeIdem_of_mem U χ hm h1 τ, ?_, ?_⟩
  · ext v
    exact heckeIdem_of_mem U χ hm h1 τ _ (heckeIdem_mem U χ hm τ v)
  · intro T hT
    exact Commute.smul_right (Commute.sum_right _ _ _ fun u _ => Commute.smul_right (hT _) _) _
  · intro g h
    ext v
    exact heckeIdem_comm U χ hm hirr g h _ V τ rfl v

end GlobalTheory.FinGL.LeviWh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegralNonzeroIntegerStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ α : 𝓞 K, α ≠ 0 → Integrable (GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K))) ∧ 2 ^ Fintype.card I * ∫ y, GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.wt φ n (α : K) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℂ) ^ (-s) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y‖ = (∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2)) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) ^ (-s.re) := by
  first | exact @GlobalTheory.HeckeMellinOne.mellin_term | exact GlobalTheory.HeckeMellinOne.mellin_term | (intros; apply GlobalTheory.HeckeMellinOne.mellin_term <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLe
section
open NumberField IsDedekindDomain

namespace GlobalTheory.TjCount

theorem Tj_complex_ne_zero_iff {L : Type} [Field L] (n : ℕ) (O : Subring L) (ϖ : L) (j : ℕ)
    (g : GL (Fin n) L) : Formalism.UG.Tj ℂ n O ϖ j g ≠ 0 ↔ Formalism.UG.Tj ℤ n O ϖ j g ≠ 0 := by
  unfold Formalism.UG.Tj
  rw [Set.indicator_apply_ne_zero, Set.indicator_apply_ne_zero]
  simp

theorem prod_le_pow (q n j : ℕ) (hq : 2 ≤ q) (hj : j ≤ n) :
    0 < ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) ∧
    ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) ≤ (q : ℤ) ^ (n * j) := by
  have hq1 : (1 : ℤ) < q := by exact_mod_cast (by omega : 1 < q)
  have hpos : ∀ i ∈ Finset.range j, (0 : ℤ) < (q : ℤ) ^ (n - i) - 1 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have : (1 : ℤ) < (q : ℤ) ^ (n - i) := one_lt_pow₀ hq1 (by omega)
    linarith
  refine ⟨Finset.prod_pos hpos, ?_⟩
  calc ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1)
      ≤ ∏ _i ∈ Finset.range j, (q : ℤ) ^ n := by
        apply Finset.prod_le_prod (fun i hi => (hpos i hi).le)
        intro i hi
        have : (q : ℤ) ^ (n - i) ≤ (q : ℤ) ^ n := pow_le_pow_right₀ hq1.le (Nat.sub_le n i)
        linarith
    _ = (q : ℤ) ^ (n * j) := by rw [Finset.prod_const, Finset.card_range, ← pow_mul]

theorem one_le_prod (q j : ℕ) (hq : 2 ≤ q) : 1 ≤ ∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1) := by
  have hq1 : (1 : ℤ) < q := by exact_mod_cast (by omega : 1 < q)
  have h1 : ∀ i ∈ Finset.range j, (1 : ℤ) ≤ (q : ℤ) ^ (i + 1) - 1 := by
    intro i _
    have : (q : ℤ) ≤ (q : ℤ) ^ (i + 1) := by
      calc (q : ℤ) = (q : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ (q : ℤ) ^ (i + 1) := pow_le_pow_right₀ hq1.le (by omega)
    linarith
  calc (1 : ℤ) = ∏ _i ∈ Finset.range j, (1 : ℤ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) h1

end GlobalTheory.TjCount

open GlobalTheory.TjCount in

theorem GlobalTheory.TjCount.tj_cosets_finite_card_le : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), Formalism.UG.IsUnifV E w ϖ → ∀ j ≤ n, {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n | Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0}.Finite ∧ Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n // Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} ≤ Formalism.UG.qV E w ^ (n * j) := by
  intro E _ _ w n ϖ hϖ j hj
  have h := Formalism.UG.P.Tj_double_coset_decomposition E w n ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ j hj
  have hq : 2 ≤ Formalism.UG.qV E w := GlobalTheory.LFun.one_lt_absNorm w
  have hcard : Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} =
      Nat.card {x : GL (Fin n) (w.adicCompletion E) ⧸ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov E w) |
        Formalism.UG.Tj ℤ n (Formalism.UG.Ov E w) ϖ j x.out ≠ 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Tj_complex_ne_zero_iff _ _ _ _ _)
  obtain ⟨hP, hB⟩ := prod_le_pow (Formalism.UG.qV E w) n j hq hj
  have hA := one_le_prod (Formalism.UG.qV E w) j hq
  rw [← hcard] at h
  set C := Nat.card {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} with hC
  have hCpos : 0 < C := by
    rcases Nat.eq_zero_or_pos C with h0 | h0
    · rw [h0] at h; simp at h; linarith
    · exact h0
  have hle : (C : ℤ) ≤ (Formalism.UG.qV E w : ℤ) ^ (n * j) := by
    have : (C : ℤ) ≤ (C : ℤ) * ∏ i ∈ Finset.range j, ((Formalism.UG.qV E w : ℤ) ^ (i + 1) - 1) :=
      le_mul_of_one_le_right (by positivity) hA
    linarith
  refine ⟨?_, by exact_mod_cast hle⟩
  have : Finite {q : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w n //
      Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j q.out ≠ 0} := Nat.finite_of_card_ne_zero hCpos.ne'
  exact Set.finite_coe_iff.mp (by exact this)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTnScalarUniformiserSingleTranslation
section
open NumberField IsDedekindDomain

namespace GlobalTheory.LFun

theorem tn_single (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V)
    (ϖ : w.adicCompletion E) (hϖ : Formalism.UG.IsUnifV E w ϖ) :
    ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w n), ∃ g,
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n) x = ρ g x := by
  classical
  intro x hx
  have h0 : ϖ ≠ 0 := Formalism.UG.P.tjcosets_ne_zero w ϖ hϖ
  set g := Formalism.UG.P.tjcosets_dG n n ϖ h0 with hg
  have hdiag : Formalism.UG.diagJ n ϖ n = ϖ • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    unfold Formalism.UG.diagJ
    ext i j
    by_cases h : i = j
    · subst h; simp [i.2]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hcomm : ∀ a : GL (Fin n) (w.adicCompletion E), g * a = a * g := fun a => by
    ext : 1
    rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val, hdiag]
    simp
  have hT : Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ n = Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL w n) g := by
    unfold Formalism.UG.Tj Formalism.UG.dosetInd
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b, hb, Units.ext (by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]; exact e)⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, by rw [Units.val_mul, Units.val_mul, hg, Formalism.UG.P.tjcosets_dG_val]⟩
  refine ⟨g, ?_⟩
  rw [hT, GlobalTheory.LFun.heckeVec_dosetInd hx (R := {g})]
  · simp
  · intro γ hγ
    rw [Finset.mem_singleton.1 hγ]
    exact DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hy
    refine ⟨g, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    have : g⁻¹ * (a * g * b) = a * b := by
      rw [← hcomm a]; group
    rw [this]
    exact (GlobalTheory.LFun.KGL w n).mul_mem ha hb

end GlobalTheory.LFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HensIsLocalRingAndIsLocalHomOfStatement
section
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalRing_hens_and_isLocalHom_of : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsLocalRing (Hens R) ∧ ∀ i : EtNbhd R, IsLocalHom (Hens.of i) := by
  first | exact @GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of | exact GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of | (intros; apply GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDiffUnitSpecialises
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem hom_diff_unit_specialises : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∀ t s : S, s ∈ closure {t} → (∀ x : A.left, A.hom x = t → (u * v⁻¹).left x = (η[B]).left t) → ∀ x : A.left, A.hom x = s → (u * v⁻¹).left x = (η[B]).left s := by
  intro S A B _ _ _ _ u v hA hB hu hv t s hst H x hx
  haveI := hA.smooth
  haveI := hB.proper
  have hη : (η[B]).left ≫ B.hom = 𝟙 S := by simpa using Over.w (η[B])
  have hid : IsClosedImmersion (𝟙 S) := inferInstance
  haveI : IsClosedImmersion ((η[B]).left ≫ B.hom) := by rw [hη]; exact hid
  haveI : IsClosedImmersion (η[B]).left := IsClosedImmersion.of_comp _ B.hom
  have hF : IsClosed ((u * v⁻¹).left ⁻¹' Set.range (η[B]).left) :=
    (η[B]).left.isClosedEmbedding.isClosed_range.preimage (u * v⁻¹).left.continuous
  have hcl : x ∈ closure (A.hom ⁻¹' {t}) := by
    rw [mem_closure_iff]
    intro U hU hxU
    have hO : IsOpen (A.hom '' U) := A.hom.isOpenMap U hU
    obtain ⟨_, ⟨y, hyU, rfl⟩, hyt⟩ := mem_closure_iff.mp hst _ hO ⟨x, hxU, hx⟩
    exact ⟨y, hyU, hyt⟩
  have hmem : x ∈ (u * v⁻¹).left ⁻¹' Set.range (η[B]).left :=
    closure_minimal (fun z (hz : z ∈ A.hom ⁻¹' {t}) =>
      (⟨t, (H z hz).symm⟩ : (u * v⁻¹).left z ∈ Set.range (η[B]).left)) hF hcl
  obtain ⟨y, hy⟩ := hmem
  have hys : y = s := by
    have e1 := congrArg B.hom hy
    rw [← Scheme.Hom.comp_apply, hη, ← Scheme.Hom.comp_apply, Over.w] at e1
    simpa [hx] using e1
  subst hys
  exact hy.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixFunctorMapVal
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomFixGlue

variable {S : Scheme.{0}}

def cmp (X : Over S) {T T' : Scheme.{0}} (c : T' ⟶ T) (t : T ⟶ S) :
    pullback X.hom (c ≫ t) ⟶ pullback X.hom t :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ c) (by rw [pullback.condition, Category.assoc])

@[reassoc (attr := simp)]
theorem cmp_fst (X : Over S) {T T' : Scheme.{0}} (c : T' ⟶ T) (t : T ⟶ S) :
    cmp X c t ≫ pullback.fst X.hom t = pullback.fst X.hom (c ≫ t) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cmp_snd (X : Over S) {T T' : Scheme.{0}} (c : T' ⟶ T) (t : T ⟶ S) :
    cmp X c t ≫ pullback.snd X.hom t = pullback.snd X.hom (c ≫ t) ≫ c := pullback.lift_snd _ _ _

variable (A B : Over S) [GrpObj A] [GrpObj B]

def baseHom {T T' : Scheme.{0}} (c : T' ⟶ T) (t : T ⟶ S)
    (Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B) :
    (Over.pullback (c ≫ t)).obj A ⟶ (Over.pullback (c ≫ t)).obj B :=
  Over.homMk (pullback.lift (cmp A c t ≫ Φ.left ≫ pullback.fst B.hom t) (pullback.snd A.hom (c ≫ t)) (by
    have h1 : Φ.left ≫ pullback.snd B.hom t = pullback.snd A.hom t := Over.w Φ
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Φ.left, h1, cmp_snd_assoc]))
    (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
theorem baseHom_fst {T T' : Scheme.{0}} (c : T' ⟶ T) (t : T ⟶ S)
    (Φ : (Over.pullback t).obj A ⟶ (Over.pullback t).obj B) :
    (baseHom A B c t Φ).left ≫ pullback.fst B.hom (c ≫ t) = cmp A c t ≫ Φ.left ≫ pullback.fst B.hom t :=
  pullback.lift_fst _ _ _

abbrev Pair (T : Scheme.{0}) : Type := Σ t : T ⟶ S, (Over.pullback t).obj A ⟶ (Over.pullback t).obj B

theorem pair_ext {T : Scheme.{0}} {t₁ t₂ : T ⟶ S} (h : t₁ = t₂)
    (Φ₁ : (Over.pullback t₁).obj A ⟶ (Over.pullback t₁).obj B)
    (Φ₂ : (Over.pullback t₂).obj A ⟶ (Over.pullback t₂).obj B)
    (hΦ : Φ₁.left ≫ pullback.fst B.hom t₁ =
      pullback.map A.hom t₁ A.hom t₂ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h]) ≫ Φ₂.left ≫ pullback.fst B.hom t₂) :
    (⟨t₁, Φ₁⟩ : Pair A B T) = ⟨t₂, Φ₂⟩ := by
  subst h
  have e : pullback.map A.hom t₁ A.hom t₁ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    apply pullback.hom_ext <;> simp
  rw [e, Category.id_comp] at hΦ
  congr 1
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact hΦ
  · exact (Over.w Φ₁).trans (Over.w Φ₂).symm

abbrev basePair {T T' : Scheme.{0}} (c : T' ⟶ T) (p : Pair A B T) : Pair A B T' :=
  ⟨c ≫ p.1, baseHom A B c p.1 p.2⟩

theorem basePair_id {T : Scheme.{0}} (p : Pair A B T) : basePair A B (𝟙 T) p = p := by
  obtain ⟨t, Φ⟩ := p
  refine pair_ext A B (Category.id_comp t) _ _ ?_
  simp only [basePair, baseHom_fst]
  congr 1

theorem basePair_comp {T T' T'' : Scheme.{0}} (c : T' ⟶ T) (c' : T'' ⟶ T') (p : Pair A B T) :
    basePair A B (c' ≫ c) p = basePair A B c' (basePair A B c p) := by
  obtain ⟨t, Φ⟩ := p
  refine pair_ext A B (Category.assoc c' c t) _ _ ?_
  have e : pullback.map A.hom ((c' ≫ c) ≫ t) A.hom (c' ≫ c ≫ t) (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      cmp A c' (c ≫ t) ≫ cmp A c t = cmp A (c' ≫ c) t := by
    apply pullback.hom_ext
    · simp [pullback.map]
      exact pullback.lift_fst _ _ _
    · simp [pullback.map]
      exact pullback.lift_snd_assoc _ _ _ _
  simp only [basePair, baseHom_fst, baseHom_fst_assoc]
  rw [← e]
  simp only [Category.assoc]

variable (L : LB A.left) (M : LB B.left)

def Good {T : Scheme.{0}} (p : Pair A B T) : Prop :=
  IsMonHom p.2 ∧ LBIso (L.pull (pullback.fst A.hom p.1)) ((M.pull (pullback.fst B.hom p.1)).pull p.2.left)

def Good' {T : Scheme.{0}} (p : Pair A B T) : Prop :=
  ∀ (T' : Scheme.{0}) (c : T' ⟶ T), Good A B L M (basePair A B c p)

theorem good'_basePair {T T' : Scheme.{0}} (c : T' ⟶ T) {p : Pair A B T} (h : Good' A B L M p) :
    Good' A B L M (basePair A B c p) := fun T'' c' => by
  rw [← basePair_comp]; exact h T'' (c' ≫ c)

def homFixFunctor : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := {p : Pair A B T.unop // Good' A B L M p}
  map c := TypeCat.ofHom fun p => ⟨basePair A B c.unop p.1, good'_basePair A B L M c.unop p.2⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro p
    exact Subtype.ext (basePair_id A B p.1)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    exact Subtype.ext (basePair_comp A B f.unop g.unop p.1)

@[simp]
theorem homFixFunctor_map_val {T T' : Scheme.{0}ᵒᵖ} (c : T ⟶ T') (p : (homFixFunctor A B L M).obj T) :
    ((homFixFunctor A B L M).map c p).1 = basePair A B c.unop p.1 := rfl

def homFixProj : homFixFunctor A B L M ⟶ yoneda.obj S where
  app T := TypeCat.ofHom fun p => p.1.1

end GlobalTheory.EndLoc.HomFixGlue

namespace GlobalTheory.EndLoc.HomFixGlue
@[simp]
theorem homFixProj_app {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)
    {T : Scheme.{0}ᵒᵖ} (p : (homFixFunctor A B L M).obj T) : (homFixProj A B L M).app T p = p.1.1 := rfl
end GlobalTheory.EndLoc.HomFixGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOfStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf L c τ → (∀ z, c * z ∈ L.lattice ↔ z ∈ (tauPair τ).lattice) ∧ (∀ z, L.weierstrassP (c * z) = (c ^ 2)⁻¹ * (tauPair τ).weierstrassP z) ∧ (∀ z, L.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * (tauPair τ).derivWeierstrassP z) ∧ s2 L = (c ^ 2)⁻¹ * s2 (tauPair τ) ∧ area L = ‖c‖ ^ 2 * area (tauPair τ) := by
  first | exact @GlobalTheory.WpFam.homogeneity_of_isTauOf | exact GlobalTheory.WpFam.homogeneity_of_isTauOf | (intros; apply GlobalTheory.WpFam.homogeneity_of_isTauOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterOfProductStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_character_of_product : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (χ : (∀ i, G i) → ℂ), IsIrrChar ℂ ℂ χ → ∃ ψ : ∀ i, G i → ℂ, (∀ i, IsIrrChar ℂ ℂ (ψ i)) ∧ ∀ x, χ x = ∏ i, ψ i (x i) := by
  first | exact @GlobalTheory.irrChar_pi_eq_prod | exact GlobalTheory.irrChar_pi_eq_prod | (intros; apply GlobalTheory.irrChar_pi_eq_prod <;> assumption)
end

