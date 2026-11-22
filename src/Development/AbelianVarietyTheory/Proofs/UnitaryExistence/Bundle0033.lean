import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_letter_equiv {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (p q r : ℕ) (hr : r = p + q)
    (ρ : (E →+* ℂ) → (E →+* ℂ)) (hρ : Function.Bijective ρ) (m : (E →+* ℂ) → ℕ)
    (hp : ∀ τ, ρ τ ∈ Ψ → m τ = p) (hq : ∀ τ, ρ τ ∉ Ψ → m τ = q) :
    ∃ f : (Σ τ, Fin (m τ)) ≃ Ψ × Fin r, ∀ s,
      (ρ s.1 ∈ Ψ ∧ (f s).1.1 = ρ s.1 ∧ ((f s).2 : ℕ) = q + s.2) ∨
      (ρ s.1 ∉ Ψ ∧ (f s).1.1 = ComplexEmbedding.conjugate (ρ s.1) ∧ ((f s).2 : ℕ) = q - 1 - s.2 ∧ (s.2 : ℕ) < q) := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  have hf : ∀ s : Σ τ, Fin (m τ), ∃ t : Ψ × Fin r,
      (ρ s.1 ∈ Ψ ∧ t.1.1 = ρ s.1 ∧ (t.2 : ℕ) = q + s.2) ∨
      (ρ s.1 ∉ Ψ ∧ t.1.1 = ComplexEmbedding.conjugate (ρ s.1) ∧ (t.2 : ℕ) = q - 1 - s.2 ∧ (s.2 : ℕ) < q) := by
    rintro ⟨τ, i⟩
    have hi := i.2
    by_cases h : ρ τ ∈ Ψ
    · have := hp τ h
      exact ⟨(⟨ρ τ, h⟩, ⟨q + i, by omega⟩), Or.inl ⟨h, rfl, rfl⟩⟩
    · have := hq τ h
      have h' : ComplexEmbedding.conjugate (ρ τ) ∈ Ψ := by
        by_contra h'
        exact h ((hΨ _).2 h')
      exact ⟨(⟨_, h'⟩, ⟨q - 1 - i, by omega⟩), Or.inr ⟨h, rfl, rfl, by show (i : ℕ) < q; omega⟩⟩
  choose f hf using hf
  have hext : ∀ s s' : Σ τ, Fin (m τ), ρ s.1 = ρ s'.1 → (s.2 : ℕ) = s'.2 → s = s' := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ h1 h2
    obtain rfl : τ = τ' := hρ.1 h1
    obtain rfl : i = i' := Fin.ext h2
    rfl
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro s s' hss
    have h1 := hf s
    have h2 := hf s'
    rw [← hss] at h2
    rcases h1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩ <;> rcases h2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
    · exact hext _ _ (b1.symm.trans b2) (by omega)
    · omega
    · omega
    · refine hext _ _ ?_ (by omega)
      rw [← hcc (ρ s.1), ← b1, b2, hcc]
  · rintro ⟨⟨τ, hτ⟩, j⟩
    have hj := j.2
    by_cases h : (j : ℕ) < q
    · obtain ⟨τ0, h0⟩ := hρ.2 (ComplexEmbedding.conjugate τ)
      have hn : ρ τ0 ∉ Ψ := h0 ▸ (hΨ τ).1 hτ
      have := hq τ0 hn
      refine ⟨⟨τ0, ⟨q - 1 - j, by omega⟩⟩, ?_⟩
      rcases hf ⟨τ0, ⟨q - 1 - j, by omega⟩⟩ with ⟨a, -⟩ | ⟨-, b, c, -⟩
      · exact absurd a hn
      · refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · rw [b]; show ComplexEmbedding.conjugate (ρ τ0) = τ; rw [h0, hcc]
        · rw [c]; show q - 1 - (q - 1 - j) = j; omega
    · obtain ⟨τ0, h0⟩ := hρ.2 τ
      have hn : ρ τ0 ∈ Ψ := h0 ▸ hτ
      have := hp τ0 hn
      refine ⟨⟨τ0, ⟨j - q, by omega⟩⟩, ?_⟩
      rcases hf ⟨τ0, ⟨j - q, by omega⟩⟩ with ⟨-, b, c⟩ | ⟨a, -⟩
      · refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · rw [b]; exact h0
        · rw [c]; show q + (j - q) = j; omega
      · exact absurd hn a

theorem letter_column_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, (∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, (∀ j, relab c σ (e j).1 = if ((idx j).2 : ℕ) < (F.Di k).q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧ (∀ j, ((idx j).2 : ℕ) = if ((idx j).2 : ℕ) < (F.Di k).q then (F.Di k).q - 1 - (e j).2 else (F.Di k).q + (e j).2) ∧ ∀ (x : Frame (M.X k).Ψ r) (v : Fin r → E) j, perFr (M.X k) x v (relab c σ (e j).1) (e j).2 = if ((idx j).2 : ℕ) < (F.Di k).q then hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v) else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2) ∧ (M.X k).p0 = (F.Di k).q ∧ r = (F.Di k).p + (F.Di k).q ∧ cc (-(M.X k).ξ0) = -(-(M.X k).ξ0) ∧ (∀ τ ∈ (M.X k).Ψ, 0 < (τ (-(M.X k).ξ0)).im) ∧ ∀ φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E), (∀ a, φ a = (M.φ k a : Fin r → E)) → LinearMap.range φ = (M.X k).Λ ∧ (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc ((M.X k).Gm a b) = (M.X k).Gm b a) ∧ (M.X k).Gm.det ≠ 0 ∧ ∀ x y, (((F.Di k).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (φ x) (φ y))) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hσ hB hN k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp, hq⟩ := F.sig k
  obtain ⟨hp0, hty⟩ := hB.type k
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  refine ⟨?_, hp0.trans hq.symm, by rw [hp, hq]; exact hB.rank, ?_, ?_, ?_⟩
  · obtain ⟨f, hf⟩ := exists_letter_equiv (M.X k).Ψ (M.X k).cmType Dw.p Dw.q r hB.rank (relab c σ) hbij Dw.mult
      (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
      (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
    obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, ∀ j,
        (relab c σ (e j).1 ∈ (M.X k).Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
        (relab c σ (e j).1 ∉ (M.X k).Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
          ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
    rw [hq]
    refine ⟨idx, fun j => ?_, fun j => ?_, fun x v j => ?_⟩
    · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
      · rw [if_neg (by omega), b]
      · rw [if_pos (by omega), b, hcc]
    · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
      · rw [if_neg (by omega), c']
      · rw [if_pos (by omega), c']
    · have h := hi j
      generalize idx j = t at h ⊢
      obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
      dsimp only at h ⊢
      rw [← hp0] at h ⊢
      rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
      · rw [if_neg (by omega)]
        unfold perFr
        rw [dif_pos a, dif_pos hn]
      · rw [if_pos (by omega)]
        unfold perFr
        rw [dif_neg a, dif_pos (show conjEmb (relab c σ (e j).1) ∈ (M.X k).Ψ from hτ), dif_pos hn]
        rfl
  · have h := (M.X k).ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  · intro τ hτ
    have := hN k τ hτ
    rw [map_neg, Complex.neg_im]
    linarith
  · intro φ hφ
    have hrange : LinearMap.range φ = (M.X k).Λ := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        rw [hφ]
        exact (M.φ k a).2
      · intro hy
        exact ⟨(M.φ k).symm ⟨y, hy⟩, by rw [hφ, LinearEquiv.apply_symm_apply]⟩
    refine ⟨hrange, ?_, ?_, (M.X k).Gm_herm, (M.X k).Gm_det, fun x y => ?_⟩
    · intro a b hab
      rw [hφ, hφ] at hab
      exact (M.φ k).injective (Subtype.ext hab)
    · rw [← LinearMap.coe_range, hrange]
      exact (M.X k).Λ_span
    · rw [hφ, hφ]
      exact hB.ef k x y

end GlobalTheory.FrameUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspPairingIntIffHermitianExponentIntegral
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ExponentTrace

section

variable {E : Type} [Field E] [NumberField E]

noncomputable abbrev dif (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)

theorem mem_mul_inv_iff {A B : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0) (x : E) :
    x ∈ B * A⁻¹ ↔ ∀ y ∈ A, x * y ∈ B := by
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hA]

theorem mem_one_iff_range (x : E) :
    x ∈ Set.range (algebraMap (𝓞 E) E) ↔ x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_one_iff]; rfl

theorem trace_dual_iff {A : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0) (y : E) :
    (∀ a ∈ A, ∃ n : ℤ, Algebra.trace ℚ E (y * a) = n) ↔ y ∈ (dif E)⁻¹ * A⁻¹ := by
  rw [mem_mul_inv_iff hA]
  constructor
  · intro h a ha
    rw [mem_inv_different_iff]
    intro o ho
    have hm : a * o ∈ A := by
      have := FractionalIdeal.mul_mem_mul ha (mem_one_fractionalIdeal_iff.2 ho)
      rwa [mul_one] at this
    rw [mul_assoc]
    exact h _ hm
  · intro h a ha
    simpa using mem_inv_different_iff.1 (h a ha) 1 isIntegral_one

theorem coord_iff {A : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0) (u : E) :
    (∀ y : E, (∀ a ∈ A, ∃ n : ℤ, Algebra.trace ℚ E (y * a) = n) →
      u * y ∈ Set.range (algebraMap (𝓞 E) E)) ↔ u ∈ dif E * A := by
  have hd : dif E ≠ 0 := coe_different_ne_zero
  have h0 : (dif E)⁻¹ * A⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hd) (inv_ne_zero hA)
  have e : dif E * A = 1 * ((dif E)⁻¹ * A⁻¹)⁻¹ := by rw [mul_inv, inv_inv, inv_inv, one_mul]
  rw [e, mem_mul_inv_iff h0]
  simp only [trace_dual_iff hA, mem_one_iff_range]

variable [IsCMField E]

noncomputable def pairIdeal (N : ℕ) (A B : FractionalIdeal (𝓞 E)⁰ E) : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * A * (dif E * conjFrac B)

theorem pairIdeal_ne_zero {N : ℕ} (hN : 0 < N) {A B : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0)
    (hB : B ≠ 0) : pairIdeal N A B ≠ 0 :=
  mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2
    (Nat.cast_ne_zero.2 hN.ne')) hA) (mul_ne_zero coe_different_ne_zero (conjFrac_ne_zero hB))

theorem ccm (a b : E) : cc (a * b) = cc a * cc b := map_mul _ a b
theorem cca (a b : E) : cc (a + b) = cc a + cc b := map_add _ a b
theorem ccc (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

theorem conj_mem_pairIdeal {N : ℕ} {A B : FractionalIdeal (𝓞 E)⁰ E} {s : E}
    (hs : s ∈ pairIdeal N A B) : cc s ∈ pairIdeal N B A := by
  have e : pairIdeal N B A = conjFrac (pairIdeal N A B) := by
    have hN : cc (N : E) = N := map_natCast _ N
    unfold pairIdeal
    rw [map_mul, map_mul, map_mul, conjFrac_conjFrac, conjFrac_spanSingleton, hN,
      conjFrac_different]
    ring
  rw [e]
  exact cc_mem_conjFrac.2 hs

theorem entry_iff (N : ℕ) (A : FractionalIdeal (𝓞 E)⁰ E) {B : FractionalIdeal (𝓞 E)⁰ E}
    (hB : B ≠ 0) (s : E) :
    (∀ y : E, (∀ a' ∈ B, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) →
      ∃ z ∈ A, s * y = (N : E) * z) ↔ s ∈ pairIdeal N A B := by
  have hd : dif E ≠ 0 := coe_different_ne_zero
  have hB' := conjFrac_ne_zero hB
  have h0 : (dif E)⁻¹ * (conjFrac B)⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hd) (inv_ne_zero hB')
  have e : pairIdeal N A B = (FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * A) *
      ((dif E)⁻¹ * (conjFrac B)⁻¹)⁻¹ := by
    rw [mul_inv, inv_inv, inv_inv]; rfl
  rw [e, mem_mul_inv_iff h0]
  refine forall_congr' fun y => imp_congr ?_ FractionalIdeal.mem_singleton_mul.symm
  rw [← trace_dual_iff hB']
  constructor
  · intro h a ha
    have := h _ (mem_conjFrac.1 ha)
    rwa [ccc] at this
  · intro h a ha
    exact h _ (cc_mem_conjFrac.2 ha)

theorem pair_iff {N : ℕ} (hN : 0 < N) {A B : FractionalIdeal (𝓞 E)⁰ E} (hA : A ≠ 0)
    (hB : B ≠ 0) (x : E) :
    (∀ s ∈ pairIdeal N A B, ∃ n : ℤ, Algebra.trace ℚ E (x * s) = n) ↔
      ∀ u ∈ dif E * A, ∀ m ∈ dif E * B,
        (N : E) * (u * x * cc m) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  have hd : dif E ≠ 0 := coe_different_ne_zero
  have hB' := conjFrac_ne_zero hB
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hN'
  have hc : conjFrac (dif E * B) = dif E * conjFrac B := by rw [map_mul, conjFrac_different]
  have e : (dif E)⁻¹ * (pairIdeal N A B)⁻¹ =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E)⁻¹ *
        (1 * (dif E * conjFrac B)⁻¹ * (dif E * A)⁻¹) := by
    rw [← FractionalIdeal.spanSingleton_inv]
    unfold pairIdeal
    simp only [mul_inv]
    ring
  rw [trace_dual_iff (pairIdeal_ne_zero hN hA hB), e, FractionalIdeal.mem_singleton_mul]
  simp only [mem_mul_inv_iff (mul_ne_zero hd hA), mem_mul_inv_iff (mul_ne_zero hd hB')]
  constructor
  · rintro ⟨y, hy, rfl⟩ u hu m hm
    have := hy u hu (cc m) (hc ▸ cc_mem_conjFrac.2 hm)
    convert this using 1
    field_simp
  · intro h
    refine ⟨(N : E) * x, fun u hu m hm => ?_, by field_simp⟩
    have := h u hu (cc m) (mem_conjFrac.1 (hc ▸ hm))
    rw [ccc] at this
    convert this using 1
    ring

theorem prE_int_iff {r ρ : ℕ} (X : Data E r) (χ β : Matrix (Fin ρ) (Fin ρ) E) :
    (∃ n : ℤ, FJ.prE X χ β = n) ↔
      ∃ n : ℤ, Algebra.trace ℚ E (∑ a, ∑ b, χ a b * (β a b / X.ξ0)) = 2 * n := by
  have h1 : FJ.prE X χ β =
      (Algebra.trace ℚ E (Matrix.trace (χ.transpose * β) / (X.κ0 / 2)) : ℝ) / 2 := by
    rw [← X.re_sum_Psi, Complex.re_sum]; rfl
  have h2 : Matrix.trace (χ.transpose * β) / X.ξ0 = ∑ a, ∑ b, χ a b * (β a b / X.ξ0) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_div, mul_div_assoc]
    rw [Finset.sum_comm]
  rw [h1, ← h2]
  have key : ∀ (q : ℚ) (n : ℤ), (q : ℝ) / 2 = n ↔ q = 2 * n := fun q n => by
    rw [div_eq_iff two_ne_zero, mul_comm]
    exact_mod_cast Iff.rfl
  simp only [key]
  rcases X.κ0_xi with h | h
  · rw [h, mul_div_cancel_left₀ _ two_ne_zero]
  · rw [h, neg_div, mul_div_cancel_left₀ _ two_ne_zero, div_neg, map_neg]
    constructor <;> rintro ⟨n, hn⟩ <;> exact ⟨-n, by push_cast; linarith⟩

theorem skew_iff (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {r ρ : ℕ} (X : Data E r)
    (I : Fin ρ → Fin ρ → FractionalIdeal (𝓞 E)⁰ E) (hI : ∀ a b, ∀ s ∈ I a b, cc s ∈ I b a)
    (χ : Matrix (Fin ρ) (Fin ρ) E) (hχ : FJ.IsHermE χ) :
    (∀ β, FJ.IsSkew β → (∀ a b, β a b / X.ξ0 ∈ I a b) → ∃ n : ℤ, FJ.prE X χ β = n) ↔
      ∀ a b, ∀ s ∈ I a b, ∃ n : ℤ, Algebra.trace ℚ E (χ a b * s) = n := by
  have hξ := X.ξ0_ne
  have hc0 : cc (0 : E) = 0 := map_zero _
  simp only [prE_int_iff]
  constructor
  · intro h a b s hs
    let S : Matrix (Fin ρ) (Fin ρ) E := Matrix.of fun i j =>
      (if a = i ∧ b = j then s else 0) + (if b = i ∧ a = j then cc s else 0)
    have hS : ∀ i j, (X.ξ0 • S) i j / X.ξ0 = S i j := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_div_cancel_left₀ _ hξ]
    obtain ⟨n, hn⟩ := h (X.ξ0 • S) (fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul, S, Matrix.of_apply, ccm, cca, X.ξ0_im,
        apply_ite cc, ccc, hc0, and_comm (a := a = j), and_comm (a := b = j)]
      ring) (fun i j => by
      rw [hS]
      refine Submodule.add_mem (I i j : Submodule (𝓞 E) E) ?_ ?_
      · split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h; exact hs
        · exact zero_mem _
      · split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h; exact hI _ _ s hs
        · exact zero_mem _)
    refine ⟨n, ?_⟩
    have e : ∑ i, ∑ j, χ i j * ((X.ξ0 • S) i j / X.ξ0) = χ a b * s + cc (χ a b * s) := by
      simp only [hS]
      simp only [S, Matrix.of_apply, mul_add, Finset.sum_add_distrib, ite_and, mul_ite, mul_zero]
      rw [ccm, hχ a b]
      simp
    rw [e, map_add, trace_cc] at hn
    linarith
  · intro h β hβ hm
    have hreal : cc (∑ a, ∑ b, χ a b * (β a b / X.ξ0)) = ∑ a, ∑ b, χ a b * (β a b / X.ξ0) := by
      have h1 : ∀ a b, IsCMField.complexConj E (χ a b) = χ b a := hχ
      have h2 : ∀ a b, IsCMField.complexConj E (β a b) = -β b a := hβ
      have h3 : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
      simp only [cc, map_sum, map_mul, map_div₀, h1, h2, h3, neg_div_neg_eq]
      rw [Finset.sum_comm]
    have := (DiagDifferent.trace_even_real_iff E H 1 _ (fun a ha =>
      mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 ha))) hreal).2
      (fun o ho => ?_) 1 (FractionalIdeal.one_mem_one _) (map_one _)
    · rwa [mul_one] at this
    · have hh : ∀ a b, ∃ n : ℤ, Algebra.trace ℚ E (χ a b * (β a b / X.ξ0 * o)) = n := fun a b =>
        h a b _ (by
          have := FractionalIdeal.mul_mem_mul (hm a b) ho
          rwa [mul_one] at this)
      choose k hk using hh
      refine ⟨∑ a, ∑ b, k a b, ?_⟩
      simp only [Finset.sum_mul, map_sum, mul_assoc, hk]
      push_cast
      rfl

end

theorem prE_int_iff_values_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E) (χ : Matrix (Fin ρ) (Fin ρ) E), 0 < N → (∀ b, cc' b ≠ 0) → FJ.IsHermE χ → ((∀ β, FJ.IsSkew β → (∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z) → ∃ n : ℤ, FJ.prE X χ β = n) ↔ ∀ u m : Fin ρ → E, (∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → u a * y ∈ Set.range (algebraMap (𝓞 E) E)) → (∀ a (y : E), (∀ a' ∈ cc' a, ∃ n : ℤ, Algebra.trace ℚ E (y * a') = n) → m a * y ∈ Set.range (algebraMap (𝓞 E) E)) → (N : E) * ∑ i, ∑ k, u i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E)) := by
  intro E _ _ _ H r ρ X N cc' χ hN hc hχ
  have h1 := skew_iff H X (fun a b => pairIdeal N (cc' a) (cc' b))
    (fun a b s hs => conj_mem_pairIdeal hs) χ hχ
  simp only [entry_iff N _ (hc _), coord_iff (hc _)]
  rw [h1]
  simp only [pair_iff hN (hc _) (hc _), mem_one_iff_range]
  constructor
  · intro h u m hu hm
    simp only [Finset.mul_sum]
    exact Submodule.sum_mem ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) fun i _ =>
      Submodule.sum_mem _ fun k _ => h i k _ (hu i) _ (hm k)
  · intro h a b u hu m hm
    have hc0 : cc (0 : E) = 0 := map_zero _
    have hs : ∀ (a : Fin ρ) (u : E), u ∈ dif E * cc' a →
        ∀ i, (Pi.single a u : Fin ρ → E) i ∈ dif E * cc' i := fun a u hu i => by
      by_cases hi : i = a
      · subst hi; simpa using hu
      · rw [Pi.single_eq_of_ne hi]; exact FractionalIdeal.zero_mem _
    have := h _ _ (hs a u hu) (hs b m hm)
    simpa [Pi.single_apply, apply_ite cc, hc0] using this

end GlobalTheory.ExponentTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DerivativeAlongTangentCombinationModuliStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_along_tangent_combination_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), (∀ i, IsTanAt x (v i)) → IsCombAt x v a w → ∀ (U : Xo.univ.t.G.left.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hv : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U) (f : Γ(Xo.univ.t.G.left, U)), TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom ((w.appLE U ⊤ h).hom f)) = ∑ i, a i * TrivSqZeroExt.snd (show DualNumber S from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber S))).hom.hom (((v i).appLE U ⊤ (hv i)).hom f)) := by
  first | exact @GlobalTheory.TanDeriv.deriv_comb | exact GlobalTheory.TanDeriv.deriv_comb | (intros; apply GlobalTheory.TanDeriv.deriv_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetEqOneOfTrivialOnHalf
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix nonZeroDivisors TensorProduct

namespace GlobalTheory.HalfLevelDet

theorem det_baseChange_eq {E : Type} [Field E] [NumberField E] {r : ℕ} {L : Type}
    [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] (hr : Module.finrank (𝓞 E) L = r)
    (φ : L →ₗ[𝓞 E] (Fin r → E)) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (f : L →ₗ[𝓞 E] L) (g : Matrix (Fin r) (Fin r) E) (hg : ∀ a, φ (f a) = g *ᵥ φ a) :
    LinearMap.det (LinearMap.baseChange E f) = g.det := by
  have hb := TensorProduct.isBaseChange (𝓞 E) L E
  have hl := (isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E _).2 hb
  have h1 : Module.finrank E (E ⊗[𝓞 E] L) = Module.finrank E (Fin r → E) := by
    rw [IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl,
      IsLocalizedModule.finrank_eq (𝓞 E)⁰ (TensorProduct.mk (𝓞 E) E L 1) le_rfl, hr]
    simp
  let F : E ⊗[𝓞 E] L →ₗ[E] (Fin r → E) := φ.liftBaseChange E
  have hF : ∀ (c : E) (a : L), F (c ⊗ₜ a) = c • φ a := fun c a => by simp [F]
  have hsurj : Function.Surjective F := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨1 ⊗ₜ a, by rw [hF, one_smul]⟩
  have hinj : Function.Injective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h1).2 hsurj
  let e : (E ⊗[𝓞 E] L) ≃ₗ[E] (Fin r → E) := LinearEquiv.ofBijective F ⟨hinj, hsurj⟩
  have hc : ∀ x, e (LinearMap.baseChange E f x) = g *ᵥ e x := by
    intro x
    change F _ = g *ᵥ F x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a => rw [LinearMap.baseChange_tmul, hF, hF, hg, Matrix.mulVec_smul]
    | add x y hx hy => rw [map_add, map_add, map_add, Matrix.mulVec_add, hx, hy]
  rw [← LinearMap.det_conj (LinearMap.baseChange E f) e, ← LinearMap.det_toLin']
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [hc]

theorem det_eq_one_of_trivial_on_half : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (γ : Dw.La ≃ₗ[𝓞 E] Dw.La), (∀ a b, Dw.EF (γ a) (γ b) = Dw.EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ e, γ a = a + l.M • e) → LinearMap.det (LinearMap.baseChange E (γ : Dw.La →ₗ[𝓞 E] Dw.La)) = 1 := by
  intro E _ _ _ H Dw l γ hiso hhalf
  have := Dw.fin
  have hfull := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H Dw l γ hiso hhalf
  obtain ⟨ξ, hξ0, hξ⟩ : ∃ δ : E, δ ≠ 0 ∧ cc δ = -δ := by
    have hne : IsCMField.complexConj E ≠ 1 := IsCMField.complexConj_ne_one E
    obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
      by_contra h
      push Not at h
      exact hne (AlgEquiv.ext h)
    refine ⟨x - IsCMField.complexConj E x, sub_ne_zero.mpr hx.symm, ?_⟩
    unfold cc
    rw [map_sub, IsCMField.complexConj_apply_apply]
    ring
  obtain ⟨Gm, φ, hM⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw ξ hξ hξ0 _ rfl
  obtain ⟨g, hgu, hg⟩ :=
    GlobalTheory.IsoExt.exists_unitary_of_isometry E H Dw Dw _ ξ Gm φ φ γ hξ hM hM hiso
  rw [det_baseChange_eq Dw.rank φ hM.2.1 (γ : Dw.La →ₗ[𝓞 E] Dw.La) g hg]
  refine GlobalTheory.CongruenceDet.det_eq_one E _ l.M Gm (LinearMap.range φ) g hM.2.2.2.1
    (Submodule.fg_range φ) hM.2.1 l.three_le ⟨hgu, fun x => ⟨?_, ?_⟩⟩ ?_
  · rintro ⟨a, rfl⟩
    exact ⟨γ a, hg a⟩
  · rintro ⟨a, ha⟩
    refine ⟨γ.symm a, ?_⟩
    have h := hg (γ.symm a)
    rw [LinearEquiv.apply_symm_apply, ha] at h
    have h' := congrArg (fun v => (g⁻¹ : GL _ E).1 *ᵥ v) h
    simpa [Matrix.mulVec_mulVec] using h'.symm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨e, he⟩ := hfull a
    exact ⟨φ e, ⟨e, rfl⟩, by rw [← hg, he, map_add, map_nsmul]⟩

end GlobalTheory.HalfLevelDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameRingOverTestRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameRing_over_testRing : ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (p : TRing K), ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), FrameRing m π X s := by
  first | exact @GlobalTheory.exists_frameRing_testRing | exact GlobalTheory.exists_frameRing_testRing | (intros; apply GlobalTheory.exists_frameRing_testRing <;> assumption)
end

