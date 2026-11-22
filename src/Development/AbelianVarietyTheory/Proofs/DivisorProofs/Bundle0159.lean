import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinConstantTermPartialZeta
section
open scoped nonZeroDivisors
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

namespace GlobalTheory.EisConstTerm

theorem eisTerm_pair_zero (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (s : ℕ) (z : Emb F → ℂ) (a : F) :
    eisTerm (2 * s) 0 z (a, 0) = ((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
      ((|((Algebra.norm ℚ a : ℚ) : ℝ)| : ℝ) : ℂ)⁻¹ ^ (2 * s) := by
  have hcard : Fintype.card (Emb F) = Module.finrank ℚ F := by
    rw [← NumberField.Embeddings.card F ℂ]
    refine Fintype.card_of_bijective (f := fun τ : Emb F => (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
    · intro τ τ' hτ
      ext y
      have := DFunLike.congr_fun hτ y
      simpa using this
    · intro φ
      have hr : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
      exact ⟨hr.embedding, by ext y; simp⟩
  have hprod : ∏ τ, latPt z (a, 0) τ = (2 * (Real.pi : ℂ) * Complex.I) ^ Module.finrank ℚ F * ((Algebra.norm ℚ a : ℚ) : ℂ) := by
    rw [← prod_emb, ← hcard, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [latPt]
  unfold eisTerm
  rw [hprod, mul_zero, Complex.cpow_zero, mul_one, mul_inv, mul_pow, inv_pow ((2 * (Real.pi : ℂ) * Complex.I) ^ Module.finrank ℚ F), ← pow_mul, mul_comm (Module.finrank ℚ F)]
  congr 1
  rw [← Complex.ofReal_ratCast, inv_pow, inv_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, (even_two_mul s).pow_abs]

theorem spanSingleton_mul_le_one (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F) (ha : a ∈ latM 𝔞) :
    FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) *
      (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≤ 1 := by
  set cD : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hcD : cD ≠ 0 := by
    simp only [cD, ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have h := FractionalIdeal.spanSingleton_le_iff_mem.2 ha
  calc _ ≤ latM 𝔞 * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by gcongr
    _ = (cD⁻¹ * cD) * (((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) * 𝔞) := by rw [latM]; ring
    _ = 1 := by rw [inv_mul_cancel₀ hcD, Units.inv_mul, one_mul]

theorem mem_latM_of_le_one (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F)
    (ha : FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) *
      (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≤ 1) : a ∈ latM 𝔞 := by
  set cD : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  have hcD : cD ≠ 0 := by
    simp only [cD, ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  calc FractionalIdeal.spanSingleton (𝓞 F)⁰ a
      = FractionalIdeal.spanSingleton (𝓞 F)⁰ a * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * latM 𝔞 := by
        rw [latM, show ∀ X : FractionalIdeal (𝓞 F)⁰ F, X * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * (cD⁻¹ * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)) =
          X * (cD * cD⁻¹) * ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)) from fun X => by ring,
          mul_inv_cancel₀ hcD, Units.mul_inv, mul_one, mul_one]
    _ ≤ 1 * latM 𝔞 := by gcongr
    _ = latM 𝔞 := one_mul _

theorem absNorm_of_spanSingleton (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (a : F) (J : Ideal (𝓞 F))
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a *
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    (Ideal.absNorm J : ℝ) = |((Algebra.norm ℚ a : ℚ) : ℝ)| * (dF F * nrm 𝔞) := by
  have h := congrArg FractionalIdeal.absNorm hJ
  have e1 : FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 F)⁰ F) = Ideal.absNorm J := FractionalIdeal.coeIdeal_absNorm J
  have e2 : FractionalIdeal.absNorm ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = Ideal.absNorm (differentIdeal ℤ (𝓞 F)) :=
    FractionalIdeal.coeIdeal_absNorm _
  rw [e1, map_mul, map_mul, FractionalIdeal.absNorm_span_singleton (𝓞 F), e2, absNorm_differentIdeal F (𝓞 F)] at h
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_abs] at h'
  rw [h', dF, nrm, mul_assoc]
  congr 2
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem mk0_eq_of_spanSingleton (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (D : (Ideal (𝓞 F))⁰) (a : F) (ha : a ≠ 0)
    (J : (Ideal (𝓞 F))⁰) (hJ : ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ClassGroup.mk0 J = ClassGroup.mk0 D * ClassGroup.mk F 𝔞 := by
  have hu : FractionalIdeal.mk0 F J = toPrincipalIdeal (𝓞 F) F (Units.mk0 a ha) * FractionalIdeal.mk0 F D * 𝔞 := by
    apply Units.ext
    simp only [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.coe_mk0, Units.val_mk0]
    exact hJ
  have hp : ClassGroup.mk F (toPrincipalIdeal (𝓞 F) F (Units.mk0 a ha)) = 1 :=
    ClassGroup.mk_eq_one_iff.2 ⟨⟨a, by rw [coe_toPrincipalIdeal, Units.val_mk0, FractionalIdeal.coe_spanSingleton]⟩⟩
  rw [← ClassGroup.mk_mk0 F, hu, map_mul, map_mul, hp, one_mul, ClassGroup.mk_mk0]

theorem exists_spanSingleton_of_mk0_eq (F : Type) [Field F] [NumberField F] (𝔞 : Frac F) (D : (Ideal (𝓞 F))⁰)
    (J : (Ideal (𝓞 F))⁰) (hJ : ClassGroup.mk0 J = ClassGroup.mk0 D * ClassGroup.mk F 𝔞) :
    ∃ a : F, a ≠ 0 ∧ ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ a * ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := by
  set u := FractionalIdeal.mk0 F J * (FractionalIdeal.mk0 F D * 𝔞)⁻¹ with hu_def
  have h1 : ClassGroup.mk F u = 1 := by
    rw [hu_def, map_mul, map_inv, map_mul, ClassGroup.mk_mk0, ClassGroup.mk_mk0, hJ, mul_inv_cancel]
  obtain ⟨⟨x, hx⟩⟩ := ClassGroup.mk_eq_one_iff.1 h1
  have hu : (u : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    show ((u : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) = ((FractionalIdeal.spanSingleton (𝓞 F)⁰ x : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)
    rw [FractionalIdeal.coe_spanSingleton]
    exact hx
  have hx0 : x ≠ 0 := by
    intro h; apply Units.ne_zero u; rw [hu, h, FractionalIdeal.spanSingleton_zero]
  refine ⟨x, hx0, ?_⟩
  have e : FractionalIdeal.mk0 F J = u * (FractionalIdeal.mk0 F D * 𝔞) := by
    rw [hu_def, inv_mul_cancel_right]
  have e' := congrArg Units.val e
  simp only [Units.val_mul, FractionalIdeal.coe_mk0] at e'
  rw [e', hu, mul_assoc]

theorem hasSum_constTerm : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (s : ℕ), 1 ≤ s →
  ∀ (D : (Ideal (NumberField.RingOfIntegers F))⁰), (D : Ideal (NumberField.RingOfIntegers F)) = differentIdeal ℤ (NumberField.RingOfIntegers F) →
  ∀ Z : ℂ → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk0 D * ClassGroup.mk F 𝔞) Z →
  ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    HasSum (fun c : {c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) // c.out.1.2 = 0} => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisClass 𝔞 𝔟 (2 * s) 0 z c)
      (((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F * GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℝ) : ℂ) ^ (2 * s) * Z ((2 * s : ℕ) : ℂ)) := by
  intro F _ _ _ 𝔞 𝔟 s hs D hD Z hZ z hz
  classical
  set C := ClassGroup.mk0 D * ClassGroup.mk F 𝔞 with hC
  let S := {c : Quotient (latRel 𝔞 𝔟) // c.out.1.2 = 0}
  let T := {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C}
  let cD : FractionalIdeal (𝓞 F)⁰ F := ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
  let Jf : F → FractionalIdeal (𝓞 F)⁰ F := fun a => FractionalIdeal.spanSingleton (𝓞 F)⁰ a * cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F)
  have hcD : cD ≠ 0 := by
    simp only [cD, ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have hX : cD * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := mul_ne_zero hcD (Units.ne_zero 𝔞)
  have hne : ∀ c : S, c.1.out.1.1 ≠ 0 := fun c h => c.1.out.2.2.2 (Prod.ext h c.2)
  have hle : ∀ c : S, Jf c.1.out.1.1 ≤ 1 := fun c => spanSingleton_mul_le_one F 𝔞 _ c.1.out.2.1
  let Jof : S → Ideal (𝓞 F) := fun c => Classical.choose (FractionalIdeal.le_one_iff_exists_coeIdeal.1 (hle c))
  have hJof : ∀ c : S, ((Jof c : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = Jf c.1.out.1.1 := fun c =>
    Classical.choose_spec (FractionalIdeal.le_one_iff_exists_coeIdeal.1 (hle c))
  have hJnz : ∀ c : S, Jof c ∈ (Ideal (𝓞 F))⁰ := by
    intro c
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h0
    have := hJof c
    rw [h0, Submodule.zero_eq_bot, FractionalIdeal.coeIdeal_bot] at this
    simp only [Jf, mul_assoc] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact hne c (FractionalIdeal.spanSingleton_eq_zero_iff.1 h)
    · exact hX h
  have hDc : ((D : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = cD := by simp only [cD, hD]
  let f : S → T := fun c => ⟨⟨Jof c, hJnz c⟩, mk0_eq_of_spanSingleton F 𝔞 D _ (hne c) _ (by rw [hDc]; exact hJof c)⟩
  have hsp : ∀ (a : F) (ε : (𝓞 F)ˣ), FractionalIdeal.spanSingleton (𝓞 F)⁰ (((ε : 𝓞 F) : F) * a) = FractionalIdeal.spanSingleton (𝓞 F)⁰ a := by
    intro a ε
    refine (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨ε, ?_⟩).symm
    rw [Units.smul_def, Algebra.smul_def]
  have hf : Function.Bijective f := by
    constructor
    · intro c c' h
      have h1 : Jof c = Jof c' := congrArg (fun J : T => (J.1 : Ideal (𝓞 F))) h
      have h2 : Jf c.1.out.1.1 = Jf c'.1.out.1.1 := by rw [← hJof, ← hJof, h1]
      have h3 : FractionalIdeal.spanSingleton (𝓞 F)⁰ c.1.out.1.1 = FractionalIdeal.spanSingleton (𝓞 F)⁰ c'.1.out.1.1 := by
        simp only [Jf, mul_assoc] at h2
        exact mul_right_cancel₀ hX h2
      obtain ⟨ε, hε⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h3
      apply Subtype.ext
      rw [← Quotient.out_eq c.1, ← Quotient.out_eq c'.1]
      apply Quotient.sound
      refine ⟨ε, ?_, ?_⟩
      · rw [← hε, Units.smul_def, Algebra.smul_def]
      · rw [c.2, c'.2, mul_zero]
    · rintro ⟨J, hJ⟩
      obtain ⟨a, ha, hJa⟩ := exists_spanSingleton_of_mk0_eq F 𝔞 D J hJ
      have hJle : Jf a ≤ 1 := by
        have h := FractionalIdeal.coeIdeal_le_one (I := (J : Ideal (𝓞 F))) (S := (𝓞 F)⁰) (P := F)
        rwa [hJa, hDc] at h
      let p : LatPair 𝔞 𝔟 := ⟨(a, 0), mem_latM_of_le_one F 𝔞 a hJle, Submodule.zero_mem _, fun h => ha (congrArg Prod.fst h)⟩
      obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r p (Quotient.mk (latRel 𝔞 𝔟) p).out := Quotient.exact (Quotient.out_eq _).symm
      have h2' : (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2 = 0 := by rw [h2]; simp [p]
      refine ⟨⟨Quotient.mk _ p, h2'⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show Jof _ = (J : Ideal (𝓞 F))
      refine FractionalIdeal.coeIdeal_injective (K := F) ?_
      show ((Jof _ : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = ((J : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)
      rw [hJof, hJa, hDc]
      show Jf (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1 = Jf a
      rw [h1]
      simp only [Jf, hsp]
      rfl
  let e : S ≃ T := Equiv.ofBijective f hf
  have hZ2 := hZ.2 ((2 * s : ℕ) : ℂ) (by simp; norm_cast; omega)
  rw [← e.hasSum_iff] at hZ2
  have key : (fun c : S => eisClass 𝔞 𝔟 (2 * s) 0 z c.1) = fun c => (((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
        ((dF F * nrm 𝔞 : ℝ) : ℂ) ^ (2 * s)) * ((fun J : T => ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-((2 * s : ℕ) : ℂ))) ∘ e) c := by
    funext c
    have hN := absNorm_of_spanSingleton F 𝔞 c.1.out.1.1 (Jof c) (hJof c)
    simp only [Function.comp_apply, e, Equiv.ofBijective_apply, f]
    unfold eisClass
    rw [← Prod.mk.eta (p := c.1.out.1), c.2, eisTerm_pair_zero, Complex.cpow_neg, Complex.cpow_natCast]
    have hX0 : ((dF F * nrm 𝔞 : ℝ) : ℂ) ≠ 0 := by
      have h1 : dF F ≠ 0 := by
        unfold dF; rw [abs_ne_zero]; exact_mod_cast NumberField.discr_ne_zero F
      have h2 : nrm 𝔞 ≠ 0 := by
        unfold nrm; rw [Rat.cast_ne_zero, ne_eq, FractionalIdeal.absNorm_eq_zero_iff]; exact Units.ne_zero 𝔞
      exact_mod_cast mul_ne_zero h1 h2
    rw [← Complex.ofReal_natCast, hN, Complex.ofReal_mul (|_|)]
    have gen : ∀ (K y X : ℂ) (n : ℕ), X ≠ 0 → K * y⁻¹ ^ n = K * X ^ n * ((y * X) ^ n)⁻¹ := by
      intro K y X n hX
      rw [mul_pow, mul_inv, inv_pow, mul_assoc K, mul_comm ((y ^ n)⁻¹), ← mul_assoc (X ^ n), mul_inv_cancel₀ (pow_ne_zero _ hX), one_mul]
    exact gen _ _ _ _ hX0
  rw [key]
  exact hZ2.mul_left _

end GlobalTheory.EisConstTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasseJetVanishingMemPow
section
open Polynomial

namespace GlobalTheory

theorem hasseJet_vanishing_mem_pow (k A : Type) [Field k] [IsAlgClosed k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k)
    (hN : 2 ≤ N) (h01 : Δ 0 1 = 1)
    (hL : ∀ l < N, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ p u * Δ (l - p) w)
    (hπ : ∃ π : A, Δ 1 π = 1) :
    ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧
      ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  classical
  obtain ⟨π, hπ⟩ := hπ
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  have hmul0 : ∀ u w : A, Δ 0 (u * w) = Δ 0 u * Δ 0 w := by
    intro u w
    have := hL 0 hN0 u w
    simpa using this
  let φ : A →+* k :=
    { toFun := Δ 0
      map_one' := h01
      map_mul' := hmul0
      map_zero' := map_zero _
      map_add' := map_add _ }
  have hφ : ∀ u, φ u = Δ 0 u := fun _ => rfl
  have halg : ∀ l c, Δ l (algebraMap k A c) = c * Δ l 1 := by
    intro l c
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨algebraMap k A c, ?_⟩
    rw [hφ, halg, h01, mul_one]
  set Q : Ideal A := RingHom.ker φ with hQdef
  have hQmax : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  have hQmem : ∀ u, u ∈ Q ↔ Δ 0 u = 0 := fun u => RingHom.mem_ker
  have h11 : Δ 1 (1 : A) = 0 := by
    have := hL 1 hN1 1 1
    rw [Finset.sum_range_succ, Finset.sum_range_one] at this
    norm_num [h01] at this
    first | exact this | linear_combination -this
  have hvan : ∀ j, ∀ u ∈ Q ^ j, ∀ l < N, l < j → Δ l u = 0 := by
    intro j
    induction j with
    | zero => intro u _ l _ hl; omega
    | succ j ih =>
      intro u hu
      rw [pow_succ] at hu
      refine Submodule.mul_induction_on (C := fun r => ∀ l < N, l < j + 1 → Δ l r = 0) hu ?_ ?_
      · intro a ha b hb l hl hlj
        rw [hL l hl]
        refine Finset.sum_eq_zero fun p hp => ?_
        have hp' : p < l + 1 := Finset.mem_range.mp hp
        by_cases hpj : p < j
        · rw [ih a ha p (by omega) hpj, zero_mul]
        · have : l - p = 0 := by omega
          rw [this, (hQmem b).mp hb, mul_zero]
      · intro a b ha hb l hl hlj
        rw [map_add, ha l hl hlj, hb l hl hlj, add_zero]
  set x : A := π - algebraMap k A (Δ 0 π) with hx
  have hx0 : Δ 0 x = 0 := by rw [hx, map_sub, halg, h01, mul_one, sub_self]
  have hx1 : Δ 1 x = 1 := by rw [hx, map_sub, halg, h11, mul_zero, sub_zero, hπ]
  have hxQ : x ∈ Q := (hQmem x).mpr hx0
  have hxpow : ∀ j < N, Δ j (x ^ j) = 1 := by
    intro j
    induction j with
    | zero => intro _; simpa using h01
    | succ j ih =>
      intro hj
      rw [pow_succ, hL (j + 1) hj, Finset.sum_eq_single j]
      · rw [ih (by omega), show j + 1 - j = 1 by omega, hx1, one_mul]
      · intro p hp hpj
        have hp' := Finset.mem_range.mp hp
        by_cases hlt : p < j
        · rw [hvan j (x ^ j) (Ideal.pow_mem_pow hxQ j) p (by omega) hlt, zero_mul]
        · have : p = j + 1 := by omega
          subst this
          rw [Nat.sub_self, hx0, mul_zero]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
  have hxQ2 : x ∉ Q ^ 2 := by
    intro h
    have := hvan 2 x h 1 hN1 (by norm_num)
    rw [hx1] at this
    exact one_ne_zero this
  obtain ⟨J, hJ⟩ : Q ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)
  have hJQ : Q ⊔ J = ⊤ := by
    by_contra hne
    have hle : J ≤ Q := by
      have := hQmax.eq_of_le hne le_sup_left
      rw [this]
      exact le_sup_right
    apply hxQ2
    have : Ideal.span {x} ≤ Q ^ 2 := by
      rw [hJ, sq]
      exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self x)
  have hdec : ∀ j, Q ^ j ≤ Ideal.span {x ^ j} ⊔ Q ^ (j + 1) := by
    intro j
    have htop : J ^ j ⊔ Q = ⊤ := by
      rw [sup_comm]
      exact Ideal.sup_pow_eq_top hJQ
    calc Q ^ j = Q ^ j * (J ^ j ⊔ Q) := by rw [htop, Ideal.mul_top]
      _ = Q ^ j * J ^ j ⊔ Q ^ j * Q := Ideal.mul_sup _ _ _
      _ = Ideal.span {x ^ j} ⊔ Q ^ (j + 1) := by
        rw [← mul_pow, ← hJ, Ideal.span_singleton_pow, pow_succ]
      _ ≤ _ := le_rfl
  refine ⟨Q, hQmax, hQmem, fun f hf => ?_⟩
  have key : ∀ j ≤ N, f ∈ Q ^ j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hdec j (ih (by omega)))
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      have hzv : Δ j z = 0 := hvan (j + 1) z hz j (by omega) (by omega)
      have hfj : Δ j f = 0 := hf j (by omega)
      have ha : Δ 0 a = 0 := by
        rw [← hyz, map_add, hzv, add_zero, mul_comm a, hL j (by omega),
          Finset.sum_eq_single j] at hfj
        · rwa [hxpow j (by omega), Nat.sub_self, one_mul] at hfj
        · intro p hp hpj
          have hp' := Finset.mem_range.mp hp
          rw [hvan j (x ^ j) (Ideal.pow_mem_pow hxQ j) p (by omega) (by omega), zero_mul]
        · intro h
          exact absurd (Finset.mem_range.mpr (by omega)) h
      rw [← hyz]
      refine Ideal.add_mem _ ?_ hz
      rw [pow_succ, mul_comm a]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hxQ j) ((hQmem a).mpr ha)
  exact key N le_rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOneContractionOfEtalePrime
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_one_contraction_of_etale_prime : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (a : A), a ≠ 0 → algebraMap A (Localization.AtPrime Q) a ∈ P → P.height ≤ 1 →
    (P.comap (algebraMap A (Localization.AtPrime Q))).height = 1 ∧
      P.comap (algebraMap A[X] (Localization.AtPrime Q)) =
        (P.comap (algebraMap A (Localization.AtPrime Q))).map (Polynomial.C : A →+* A[X]) := by
  first | (exact @GlobalTheory.EtaleHeightOne.height_one_and_comap_eq_map_C) | (exact GlobalTheory.EtaleHeightOne.height_one_and_comap_eq_map_C) | (intros; apply GlobalTheory.EtaleHeightOne.height_one_and_comap_eq_map_C  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil

theorem hasFDerivAt_of_norming {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {X : Type} (l : X → B →L[ℂ] ℂ) (h1 : ∀ x b, ‖l x b‖ ≤ ‖b‖)
    (h2 : ∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) (F : V → B) (A : V → V →L[ℝ] B) (hA : Continuous A)
    (hF : ∀ x v, HasFDerivAt (fun w => l x (F w)) (((l x).restrictScalars ℝ).comp (A v)) v) (v : V) :
    HasFDerivAt F (A v) v := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.1 (hA.continuousAt (x := v)) c hc
  filter_upwards [Metric.ball_mem_nhds v hδ] with w hw
  refine h2 _ _ (by positivity) fun x => ?_
  have := (convex_ball v δ).norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ) (C := c)
    (φ := ((l x).restrictScalars ℝ).comp (A v))
    (fun u _ => (hF x u).hasFDerivWithinAt) (fun u hu => ?_) (Metric.mem_ball_self hδ) hw
  · simpa only [map_sub, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] using this
  · refine ContinuousLinearMap.opNorm_le_bound _ hc.le fun z => ?_
    have e : (((l x).restrictScalars ℝ).comp (A u) - ((l x).restrictScalars ℝ).comp (A v)) z = l x ((A u - A v) z) := by
      simp
    rw [e]
    refine (h1 _ _).trans (((A u - A v).le_opNorm z).trans ?_)
    have := hb hu
    rw [dist_eq_norm] at this
    gcongr

theorem sm_of_weak_deriv_closed : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ)
    (ρ : V → B →L[ℂ] B), IsHeis (fun x y => om x y) ρ → ∀ (X : Type) (l : X → B →L[ℂ] ℂ), (∀ x b, ‖l x b‖ ≤ ‖b‖) →
    (∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) →
    (∀ x v, ∃ (a : ℂ) (x' : X), ∀ b, l x (ρ v b) = a * l x' b) → ∀ Θ : Set B,
    (∀ f ∈ Θ, ∀ x, Differentiable ℝ fun v => l x (ρ v f)) →
    (∀ f ∈ Θ, ∀ z : V, ∃ f' ∈ Θ, ∀ x, HasDerivAt (fun t : ℝ => l x (ρ (t • z) f)) (l x f') 0) →
    ∀ f ∈ Θ, Sm ρ f := by
  intro V _ _ _ B _ _ _ om ρ h X l h1 h2 h3 Θ hd hc
  have sep : ∀ b b' : B, (∀ x, l x b = l x b') → b = b' := fun b b' hb => by
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    exact h2 _ 0 le_rfl fun x => by rw [map_sub, hb, sub_self, norm_zero]
  have lsm : ∀ x (r : ℝ) (b : B), l x (r • b) = r • l x b := fun x r b => ((l x).restrictScalars ℝ).map_smul r b
  have key : ∀ f ∈ Θ, ∃ D : V →L[ℝ] B, (∀ z, D z ∈ Θ) ∧
      ∀ v, HasFDerivAt (fun w => ρ w f) (((ρ v).restrictScalars ℝ).comp D -
        (om v).smulRight (((π : ℂ) * I) • ρ v f)) v := by
    intro f hf
    choose g hg hg' using hc f hf
    have hgd : ∀ x z, l x (g z) = fderiv ℝ (fun v => l x (ρ v f)) 0 z := by
      intro x z
      refine (hg' z x).unique ?_
      have a1 : HasDerivAt (fun t : ℝ => t • z) z 0 := by simpa using (hasDerivAt_id (0 : ℝ)).smul_const z
      have a2 : HasFDerivAt (fun v => l x (ρ v f)) (fderiv ℝ (fun v => l x (ρ v f)) 0) ((0 : ℝ) • z) := by
        rw [zero_smul]; exact (hd f hf x 0).hasFDerivAt
      exact a2.comp_hasDerivAt (0 : ℝ) a1
    let D0 : V →ₗ[ℝ] B :=
      { toFun := g
        map_add' := fun z z' => sep _ _ fun x => by rw [map_add, hgd, hgd, hgd, map_add]
        map_smul' := fun r z => sep _ _ fun x => by rw [RingHom.id_apply, lsm, hgd, hgd, map_smul] }
    let D : V →L[ℝ] B := LinearMap.toContinuousLinearMap D0
    have hD : ∀ z, D z = g z := fun z => rfl
    refine ⟨D, fun z => hg z, hasFDerivAt_of_norming l h1 h2 _ _ ?_ ?_⟩
    · refine continuous_clm_apply.2 fun z => ?_
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply]
      have a1 := h.2.2.2 (D z)
      have a2 := h.2.2.2 f
      exact a1.sub ((om.continuous.clm_apply continuous_const).smul (a2.const_smul _))
    · intro x v
      obtain ⟨a, x', hx⟩ := h3 x v
      have e : (fun w => l x (ρ w f)) =
          fun w => cexp (-(π * I) * (om v (w - v) : ℝ)) * (a * l x' (ρ (w - v) f)) := by
        funext w
        rw [← hx, h.2.1, add_sub_cancel, map_smul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
        simp
      have b0 : HasFDerivAt (fun w : V => w - v) (ContinuousLinearMap.id ℝ V) v := (hasFDerivAt_id v).sub_const v
      have b1 : HasFDerivAt (fun w => l x' (ρ (w - v) f)) (fderiv ℝ (fun v => l x' (ρ v f)) 0) v := by
        have a2 : HasFDerivAt (fun v => l x' (ρ v f)) (fderiv ℝ (fun v => l x' (ρ v f)) 0) (v - v) := by
          rw [sub_self]; exact (hd f hf x' 0).hasFDerivAt
        simpa [Function.comp_def] using HasFDerivAt.comp (f := fun w : V => w - v) v a2 b0
      have b2 : HasFDerivAt (fun w : V => ((om v (w - v) : ℝ) : ℂ)) (Complex.ofRealCLM.comp (om v)) v := by
        simpa [Function.comp_def] using (Complex.ofRealCLM.comp (om v)).hasFDerivAt.comp v b0
      have b3 := ((b2.const_mul (-(π * I) : ℂ)).cexp).mul (b1.const_mul a)
      rw [e]
      refine b3.congr_fderiv ?_
      ext z
      simp [← hgd, h.1, hD, lsm, hx]
      ring
  have ind : ∀ n : ℕ, ∀ f ∈ Θ, ContDiff ℝ n fun v => ρ v f := by
    intro n
    induction n with
    | zero => intro f _; exact contDiff_zero.2 (h.2.2.2 f)
    | succ n ih =>
      intro f hf
      obtain ⟨D, hD, hF⟩ := key f hf
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
      refine ⟨fun v => (hF v).differentiableAt, by simp, fun z => ?_⟩
      simp only [(hF _).fderiv, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply]
      exact (ih _ (hD z)).sub ((om.contDiff.clm_apply contDiff_const).smul ((ih f hf).const_smul _))
  intro f hf
  exact contDiff_infty.2 fun n => ind n f hf

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianEndoMatrixRationalInLatticeBasisStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_endo_matrix_rational_in_lattice_basis : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₁.mulVec (star (e l))).im) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₂.mulVec (star (e l))).im) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    ∃ Tq : Matrix (Fin n) (Fin n) ℚ,
      Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) := by
  first | exact @GlobalTheory.herm_endo_matrix_rat | exact GlobalTheory.herm_endo_matrix_rat | (intros; apply GlobalTheory.herm_endo_matrix_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFlagComplementPosDefFactorizationStatement
section
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_flag_complement_posDef_factorization : ∀ (n r : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ), J.conjTranspose = J → (J * θ).PosDef →
    ∀ (X Y : Matrix (Fin n) (Fin r) ℂ), X.conjTranspose * J * Y = 1 →
    ∀ (l d : ℕ) (h : l + d ≤ r) (u₁ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin l) (Fin d) ℂ),
      let X₁ : Matrix (Fin n) (Fin l) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Xb : Matrix (Fin n) (Fin d) ℂ := X.submatrix id fun j => ⟨l + j.val, by omega⟩
      let X₂ : Matrix (Fin n) (Fin (l + d)) ℂ := X.submatrix id fun j => ⟨j.val, by omega⟩
      let Yb : Matrix (Fin n) (Fin d) ℂ := Y.submatrix id fun j => ⟨l + j.val, by omega⟩
      let Y₂ : Matrix (Fin n) (Fin (l + d)) ℂ := Y.submatrix id fun j => ⟨j.val, by omega⟩
      θ * X₂ = u₁ * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) → X₁.conjTranspose * (J * θ) * (Xb + X₁ * A) = 0 →
      θ * (Xb + X₁ * A) = u₁ * Yb * (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)) ∧
        (Xb.conjTranspose * (J * θ) * (Xb + X₁ * A)).PosDef := by
  first | exact @GlobalTheory.schur_complement_step_cpx | exact GlobalTheory.schur_complement_step_cpx | (intros; apply GlobalTheory.schur_complement_step_cpx <;> assumption)
end

