import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleTwistedCoboundary
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformEigenvalueEqCharMulConj
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisMReal

theorem qs_smul (c : ℂ) (a : ℕ → ℂ) : qs (fun n => c * a n) = fun τ => c * qs a τ := by
  funext τ
  unfold qs
  rw [← tsum_mul_left]
  congr 1
  funext n
  ring

theorem pet_smul_right (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ h (fun τ => c * f τ) = c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  ring

theorem pet_smul_left (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ (fun τ => c * h τ) f = conj c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  simp only [map_mul]
  ring

theorem eig_conj : ∀ (k N q : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g →
    q.Prime → ¬ q ∣ N → g q = ch χ q * conj (g q) := by
  intro k N q χ g hk hN hg hq hqN
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_gammaZeroPartitionWeight N hN
  have hT : To k (ch χ q) q g = fun n => g q * g n := hg.eig q hq hqN
  have hadj := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k N N q χ ρ g g hk hN dvd_rfl hq hqN hρ hg.cf hg.cf.1
  have hne : g ≠ 0 := by
    intro h0
    have := hg.one
    rw [h0] at this
    simp at this
  have hP := GlobalTheory.T.halfPeterssonIntegral_self_ne_zero_cuspForm k N N χ ρ g hk hN dvd_rfl hρ hg.cf hne
  rw [hT, qs_smul, pet_smul_right, pet_smul_left] at hadj
  exact mul_right_cancel₀ hP (hadj.trans (by ring) : g q * pet k ρ (qs g) (qs g) = ch χ q * conj (g q) * pet k ρ (qs g) (qs g))

end GlobalTheory.EisMReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixingMulFrobAt
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ Matrix

namespace GlobalTheory.KZ

theorem exists_fixing_mul_frobAt :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (E0 : Finset Ω) (S : Finset ℕ),
      ∃ (s' : Ω ≃ₐ[ℚ] Ω) (q : ℕ), (∀ x ∈ E0, s' x = x) ∧ q.Prime ∧ q ∉ S ∧ FrobAt q (s * s') := by
  intro Ω _ _ _ s E0 S
  have : IsGalois ℚ Ω := {}
  let K : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (E0 : Set Ω)
  have : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hKo : IsOpen (K.fixingSubgroup : Set (G ℚ Ω)) := IntermediateField.fixingSubgroup_isOpen K
  let V : Set (G ℚ Ω) := {φ | s⁻¹ * φ ∈ K.fixingSubgroup}
  have hVo : IsOpen V := hKo.preimage (continuous_mul_left s⁻¹)
  have hVne : V.Nonempty := ⟨s, by simp [V, K.fixingSubgroup.one_mem]⟩
  let T : ℕ := ∏ p ∈ S.filter (· ≠ 0), p
  have hT : T ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (Finset.mem_filter.1 hp).2
  have hS : {v : HeightOneSpectrum (𝓞 ℚ) | (T : 𝓞 ℚ) ∈ v.asIdeal}.Finite :=
    (Ideal.finite_factors (I := Ideal.span {(T : 𝓞 ℚ)}) (by simpa using hT)).subset
      fun _ hv => Ideal.dvd_span_singleton.2 hv
  obtain ⟨φ, hφV, v, hv, hd, B, hB, hφ⟩ :=
    (GlobalTheory.Published.ChebotarevDegreeOne.dense (F := ℚ) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS).inter_open_nonempty
      V hVo hVne
  have h2 : Ideal.absNorm v.asIdeal = normV v := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hmem : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := h2 ▸ Ideal.absNorm_mem v.asIdeal
  have hq : (normV v).Prime := by
    rw [← h2]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified ℚ).1 v).2 hd
  refine ⟨s⁻¹ * φ, normV v, ?_, hq, ?_, ?_⟩
  · intro x hx
    exact (mem_fixingSubgroup_iff _).1 hφV x (IntermediateField.subset_adjoin ℚ _ (by simpa using hx))
  · intro hqS
    apply hv
    show (T : 𝓞 ℚ) ∈ v.asIdeal
    have hdvd : normV v ∣ T := Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hqS, hq.ne_zero⟩)
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  · rw [mul_inv_cancel_left]
    have hqB : B.valuation ((normV v : ℕ) : Ω) < 1 := by
      have := (hB ((normV v : ℕ) : 𝓞 ℚ)).2 hmem
      simpa using this
    refine ⟨B, (ValuationSubring.mem_nonunits_iff _).2 hqB, fun x hx => ?_⟩
    have hx1 : B.valuation x ≤ 1 := (B.valuation_le_one_iff x).2 hx
    have hlt := hφ.2 x hx1
    refine ⟨?_, hlt⟩
    have hxq : x ^ normV v ∈ B := pow_mem hx _
    have hd' : φ x - x ^ normV v ∈ B := (B.valuation_le_one_iff _).1 hlt.le
    simpa using add_mem hd' hxq

end GlobalTheory.KZ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalOfDepletedEigenform
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eigF_of_prim : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (α β : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → Prim k N χ g → Wt (N * l) ρ → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (k - 1) → ∃ (B : ℕ) (c : ℕ → ℂ), EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = pet k ρ (qs (Vo l fun n => conj (g n))) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs fun n => conj (g n)) (qs a) := by
  intro k N l χ g ρ α β hk hN hl hlN hg hρ hab hαβ
  haveI : NeZero N := ⟨by omega⟩
  set h : ℕ → ℂ := fun n => conj (g n) with hh_def
  have hNl : 0 < N * l := Nat.mul_pos hN hl.pos
  have hdvd : N ∣ N * l := dvd_mul_right N l
  have hP : Prim k N χ⁻¹ h := (GlobalTheory.T.cuspForm_conjugate_coefficients_inv_char k N χ g).2 hg
  have hMFh : MF k N (ch χ⁻¹) h := hP.cf.1
  have lin := GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) (ch χ⁻¹)
  have hCFh : CF k (N * l) (ch χ⁻¹) h := (GlobalTheory.T.modularFormCoeffSeq_linear_structure k N (ch χ⁻¹)).2.2.2.2.2 (N * l) h hdvd hP.cf
  have hCFV : CF k (N * l) (ch χ⁻¹) (Vo l h) := (GlobalTheory.T.coeffHeckeVOperator_raises_level k N l (ch χ⁻¹) h hl.pos).2 hP.cf
  have petlin := GlobalTheory.T.halfPeterssonIntegralWeighted_linear_forms k (N * l) (N * l) N χ⁻¹ ρ hk hNl hdvd hρ

  have hsc : ∀ (h' a : ℕ → ℂ) (x : ℂ), CF k (N * l) (ch χ⁻¹) h' → MF k (N * l) (ch χ⁻¹) a →
      pet k ρ (qs (x • h')) (qs a) = conj x * pet k ρ (qs h') (qs a) := by
    intro h' a x hh' ha
    have e : qs (x • h') = fun τ => x * qs h' τ + 0 * qs h' τ := by
      rw [(lin.2.2.1 x h' hh'.1).2]; funext τ; simp
    rw [e, petlin.2 h' h' a x 0 hh' hh' ha.1]; simp
  have hconj : ∀ x : ZMod N, conj (χ x) = χ⁻¹ x := fun x => MulChar.star_apply' χ x
  have hch : ∀ n : ℕ, ch χ⁻¹ (n : ℤ) = χ⁻¹ (n : ZMod N) := by intro n; simp [ch]
  set φ : (ℕ → ℂ) → ℂ := fun a => pet k ρ (qs (Vo l h)) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs h) (qs a) with hφ_def
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_sturmBound_isModularFormCoeffSeq k (N * l) N χ⁻¹ hNl hdvd
  obtain ⟨c, hc⟩ := GlobalTheory.T.linearFunctional_eq_coeffLinearCombinationFinite {a | MF k (N * l) (ch χ⁻¹) a} B φ lin.1
    (by
      intro a ha b hb
      refine ⟨(lin.2.1 a b ha hb).1, ?_⟩
      have e1 := petlin.1 (Vo l h) a b 1 1 hCFV ha.1 hb.1
      have e2 := petlin.1 h a b 1 1 hCFh ha.1 hb.1
      simp only [one_smul, one_mul] at e1 e2
      simp only [hφ_def, e1, e2]; ring)
    (by
      intro x a ha
      refine ⟨(lin.2.2.1 x a ha).1, ?_⟩
      have e1 := petlin.1 (Vo l h) a a x 0 hCFV ha.1 ha.1
      have e2 := petlin.1 h a a x 0 hCFh ha.1 ha.1
      simp only [zero_smul, add_zero, zero_mul] at e1 e2
      simp only [hφ_def, e1, e2]; ring)
    hB
  have hφ : ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = φ a := fun a ha => (hc a ha).symm
  refine ⟨B, c, ⟨?_, ?_⟩, hφ⟩
  ·
    intro a ha q hq hqNl
    have hqN : ¬ q ∣ N := fun d => hqNl (dvd_mul_of_dvd_left d l)
    have hql : q ≠ l := fun e => hqNl (e ▸ dvd_mul_left q N)
    have hcop : q.Coprime l := (Nat.coprime_primes hq hl).2 hql
    have hTa := GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ⁻¹ a hk hdvd hq hqNl ha
    rw [hφ _ hTa, hφ _ ha]
    have eigh : To k (ch χ⁻¹ q) q h = h q • h := by
      rw [hP.eig q hq hqN]; funext n; simp
    have eigV : To k (ch χ⁻¹ q) q (Vo l h) = h q • Vo l h := by
      rw [(GlobalTheory.T.coeffHecke_UV_cauchyProduct_identities ℂ l hl.pos).2.2.2.2.1 k q _ h hcop hq.pos, eigh]
      funext n; simp only [Vo, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
    have adj0 := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k (N * l) N q χ⁻¹ ρ h a hk hNl hdvd hq hqNl hρ hCFh ha
    have adj1 := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k (N * l) N q χ⁻¹ ρ (Vo l h) a hk hNl hdvd hq hqNl hρ hCFV ha
    rw [eigh, hsc h a _ hCFh ha] at adj0
    rw [eigV, hsc (Vo l h) a _ hCFV ha] at adj1
    have hgq : conj (h q) = g q := by simp [hh_def]
    simp only [hφ_def]
    rw [adj0, adj1]
    simp only [hgq, hch]
    ring
  ·
    intro a ha
    have hper : ∀ d : ℤ, ch χ⁻¹ (d + ((N * l : ℕ) : ℤ)) = ch χ⁻¹ d := by
      intro d; simp only [ch]; congr 1; push_cast; simp
    have hUa := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ⁻¹) a hk hl (dvd_mul_left l N) hper ha).1
    rw [hφ _ hUa, hφ _ ha]
    have adjU0 := GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint k (N * l) N l χ⁻¹ ρ h a hk hNl hdvd hl (dvd_mul_left l N) hlN hρ hCFh ha
    have adjU1 := GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint k (N * l) N l χ⁻¹ ρ (Vo l h) a hk hNl hdvd hl (dvd_mul_left l N) hlN hρ hCFV ha
    have tr0 := GlobalTheory.T.sum_slash_heckeRepLowerLevel_eq_pow_mul_heckeV k N l χ⁻¹ h hk hl.pos hMFh
    have eigl : To k (ch χ⁻¹ l) l h = h l • h := by
      rw [hP.eig l hl hlN]; funext n; simp
    have tr1 := GlobalTheory.T.sum_slash_heckeRepLower_heckeV_eigenform k N l χ⁻¹ h (h l) hk hN hl hlN hMFh eigl
    have f0 : (fun τ => ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ)
        = fun τ => ((l : ℂ) ^ k) * qs (Vo l h) τ + 0 * qs (Vo l h) τ := by
      funext τ; rw [tr0]; ring
    have f1 : (fun τ => ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ)
        = fun τ => (ch χ⁻¹⁻¹ l * h l) * qs (Vo l h) τ + (-(ch χ⁻¹⁻¹ l * (l : ℂ)⁻¹)) * qs h τ := by
      funext τ; rw [tr1]; ring
    rw [f0, petlin.2 (Vo l h) (Vo l h) a _ 0 hCFV hCFV ha.1] at adjU0
    rw [f1, petlin.2 (Vo l h) h a _ _ hCFV hCFh ha.1] at adjU1
    have e1 : conj (ch χ⁻¹⁻¹ (l : ℤ)) = χ⁻¹ (l : ZMod N) := by
      rw [inv_inv]; simp only [ch, Int.cast_natCast]; exact hconj _
    have hgl : conj (h l) = g l := by simp [hh_def]
    have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
    have key : (l : ℂ) ^ (k - 1) / (l : ℂ) ^ k = (l : ℂ)⁻¹ := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]; field_simp
    simp only [map_mul, map_neg, map_inv₀, map_pow, Complex.conj_natCast, map_zero, e1, hgl, zero_mul, add_zero] at adjU0 adjU1
    simp only [hφ_def, adjU0, adjU1]
    set P0 := pet k ρ (qs h) (qs a)
    set P1 := pet k ρ (qs (Vo l h)) (qs a)
    have hcan : (l : ℂ) ^ k / (l : ℂ) ^ k = 1 := div_self (pow_ne_zero _ hl0)
    linear_combination (-P1) * hab + (P0 / (l : ℂ) ^ k) * hαβ + (χ⁻¹ (l : ZMod N) * P0) * key + (-β * P1) * hcan

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqEisensteinProductParity
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem zmf_congr_cop {k l : ℕ} (u v : ℤ → ℂ) (F G : ℕ → ℕ → ℂ)
    (h : ∀ x y : ℕ, ¬ l ∣ x → ¬ l ∣ y → F x y = G x y) : Zm k l u v F = Zm k l u v G := by
  funext n
  unfold Zm
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  split_ifs with hp
  · rfl
  · push_neg at hp
    rw [Nat.mem_divisorsAntidiagonal] at hx hy
    have hx' : ¬ l ∣ x.1 := fun hd => hp.1 (hx.1 ▸ dvd_mul_of_dvd_left hd _)
    have hy' : ¬ l ∣ y.2 := fun hd => hp.2 (hy.1 ▸ dvd_mul_of_dvd_right hd _)
    rw [h _ _ hx' hy']

theorem zmf_sum_smul {ι : Type*} (s : Finset ι) (k l : ℕ) (u v : ℤ → ℂ) (c : ι → ℂ) (G : ι → ℕ → ℕ → ℂ) :
    Zm k l u v (fun x y => ∑ i ∈ s, c i * G i x y) = ∑ i ∈ s, c i • Zm k l u v (G i) := by
  funext n
  simp only [Zm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem zmf_mf_sum {ι : Type*} (s : Finset ι) (k L : ℕ) (χ : ℤ → ℂ) (g : ι → ℕ → ℂ)
    (h : ∀ i ∈ s, MF k L χ (g i)) : MF k L χ (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).2.1 _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).1

theorem zm_fun_mf : ∀ (k N l m : ℕ) (ε θ ν : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ), 3 ≤ k → Odd k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → ε = θ⁻¹ * ν → ν (-1) = -θ (-1) → (∀ x, f (-x) = θ (-1) * f x) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) := by
  intro k N l m ε θ ν f hk hodd hN hl hm hlN hε hν hf
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  set φ : ℂ := ((l ^ m).totient : ℂ) with hφ
  have hφ0 : φ ≠ 0 := by
    rw [hφ]; exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (pow_ne_zero _ hl.ne_zero))).ne'
  set c : DirichletCharacter ℂ (l ^ m) → ℂ := fun ψ => φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * ψ⁻¹ u with hc
  have hinv : ∀ (ψ : DirichletCharacter ℂ (l ^ m)) (u : (ZMod (l ^ m))ˣ),
      ψ⁻¹ (u : ZMod (l ^ m)) = ψ ((u : ZMod (l ^ m))⁻¹) := by
    intro ψ u; rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
  have hexp : ∀ w : (ZMod (l ^ m))ˣ, f w = ∑ ψ, c ψ * ψ w := by
    intro w
    calc f w = φ⁻¹ * (f w * φ) := by field_simp
      _ = φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * (if (u : ZMod (l ^ m)) = w then φ else 0) := by
          congr 1
          simp only [Units.val_inj, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq']; simp
      _ = φ⁻¹ * ∑ u : (ZMod (l ^ m))ˣ, f u * ∑ ψ : DirichletCharacter ℂ (l ^ m), ψ ((u : ZMod (l ^ m))⁻¹) * ψ w := by
          congr 1
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ u.isUnit]
      _ = ∑ ψ, c ψ * ψ w := by
          simp only [hc, hinv, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun ψ _ => Finset.sum_congr rfl fun u _ => ?_
          ring
  have hquo : Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) = Zm k l (hat θ) (ch ν)
      (fun x y => ∑ ψ : DirichletCharacter ℂ (l ^ m), c ψ * (ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ 0)) := by
    apply zmf_congr_cop
    intro x y hx hy
    have cx : Nat.Coprime x (l ^ m) := (Nat.Coprime.pow_left m ((hl.coprime_iff_not_dvd).2 hx)).symm
    have cy : Nat.Coprime y (l ^ m) := (Nat.Coprime.pow_left m ((hl.coprime_iff_not_dvd).2 hy)).symm
    set ux := ZMod.unitOfCoprime x cx
    set uy := ZMod.unitOfCoprime y cy
    have ex : ((x : ℤ) : ZMod (l ^ m)) = ux := by simp [ux, ZMod.coe_unitOfCoprime]
    have ey : ((y : ℤ) : ZMod (l ^ m)) = uy := by simp [uy, ZMod.coe_unitOfCoprime]
    have ex' : (x : ZMod (l ^ m)) = ux := by simp [ux, ZMod.coe_unitOfCoprime]
    have ey' : (y : ZMod (l ^ m)) = uy := by simp [uy, ZMod.coe_unitOfCoprime]
    simp only [ch, ex, ey, ex', ey', pow_zero, mul_one, hinv]
    rw [ZMod.inv_coe_unit, ← Units.val_mul, hexp]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [← map_mul, ← Units.val_mul]
  rw [hquo, zmf_sum_smul]
  apply zmf_mf_sum
  intro ψ _
  have hsq : ∀ {M : ℕ} (χ : DirichletCharacter ℂ M), χ (-1) * χ (-1) = 1 := by
    intro M χ; rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hh := (GlobalTheory.T.dirichletCharFiniteFourierTransform_properties).1 N θ hN
  by_cases hψ : ψ (-1) = θ (-1)
  · have h1 : ψ (-1) * θ (-1) = (-1) ^ (k - 1 - 0) := by
      obtain ⟨r, rfl⟩ := hodd
      rw [hψ, hsq, show 2 * r + 1 - 1 - 0 = 2 * r by omega, pow_mul]; norm_num
    have h2 : ψ (-1) * ν (-1) = (-1) ^ (0 + 1) := by
      rw [hψ, hν, mul_neg, hsq]; norm_num
    exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k _ (ch ε)).2.2.1 (c ψ) _
      (GlobalTheory.T.muModelProduct_isModularFormCoeffSeq_locallyAlgebraic k 0 N l m ε (hat θ) θ ν ψ (by omega) hN hl hm hlN hh.1 hh.2.1 hε h1 h2)).1
  · have hc0 : c ψ = 0 := by
      have hpm : ∀ {M : ℕ} (χ : DirichletCharacter ℂ M), χ (-1) = 1 ∨ χ (-1) = -1 := by
        intro M χ
        have := hsq χ
        have h' : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination this
        rcases mul_eq_zero.1 h' with h | h
        · left; linear_combination h
        · right; linear_combination h
      have hprod : θ (-1) * ψ⁻¹ (-1) = -1 := by
        have hi : ψ⁻¹ (-1) = ψ (-1) := by
          rw [MulChar.inv_apply, show (-1 : ZMod (l ^ m)) = ((-1 : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) by simp, Ring.inverse_unit, inv_neg_one]
        rw [hi]
        rcases hpm θ with h | h <;> rcases hpm ψ with h' | h' <;> rw [h, h'] at hψ ⊢
        all_goals first | exact absurd rfl hψ | norm_num
      set S := ∑ u : (ZMod (l ^ m))ˣ, f u * ψ⁻¹ u with hS
      have hS' : S = - S := by
        calc S = ∑ u : (ZMod (l ^ m))ˣ, f ((-u : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) * ψ⁻¹ ((-u : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) :=
              (Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)).symm
          _ = ∑ u : (ZMod (l ^ m))ˣ, (θ (-1) * ψ⁻¹ (-1)) * (f u * ψ⁻¹ u) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [Units.val_neg, hf, neg_eq_neg_one_mul (u : ZMod (l ^ m)), map_mul]
              ring
          _ = - S := by rw [← Finset.mul_sum, hprod, neg_one_mul]
      have : S = 0 := by linear_combination hS' / 2
      simp [hc, ← hS, this]
    rw [hc0, zero_smul]
    exact (GlobalTheory.T.modularFormCoeffSeq_linear_structure k _ (ch ε)).1

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleTwistedCoboundaryStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cocycle_twisted_coboundary : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k : ℕ) (χ κ : Gal p Ω → ZMod (p ^ k)), IsKum T k (Ggeo p Ω) (T.qq k) κ →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω) a → IsTwistedOneCocycle 0 k (Ggeo p Ω) χ a →
      ∃ o : Ω, IsInt p o ∧ (∀ g ∈ Ggeo p Ω, g o = o) ∧
        IsTwistedOneCoboundary 0 k (Ggeo p Ω) χ (fun g => (p : Ω) ^ c * a g - o * ((κ g).val : Ω))) ∧
  (∀ o : Ω, IsInt p o → (∀ g ∈ Ggeo p Ω, g o = o) →
      IsTwistedOneCoboundary 0 k (Ggeo p Ω) χ (fun g => o * ((κ g).val : Ω)) → Cong p k ((p : Ω) ^ c * o) 0) := by
  first | exact @GlobalTheory.K5.TopGeo.top | exact GlobalTheory.K5.TopGeo.top | (intros; apply GlobalTheory.K5.TopGeo.top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReLatSelf
section
noncomputable section

namespace GlobalTheory.VolRatioCompare

open NumberField Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def reLat (V : HSpace E) (L : Submodule (𝓞 E) V.V) (h1 : Submodule.IsLattice E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) : HSpace E :=
  { V with L0 := L, standardTuple_isLattice := h1, baseLattice_isUnimodular := h2 }

end GlobalTheory.VolRatioCompare
end
end

