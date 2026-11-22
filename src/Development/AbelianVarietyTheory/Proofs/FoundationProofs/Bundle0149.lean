import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0144
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Formalism.FormalDegreeBessel.StatementRP

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EllipticPointsStabilizer
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.EllipticZero

lemma denom_mul_SL (g h : SL(2, ℤ)) (z : ℍ) :
    denom ((g * h : SL(2, ℤ)) : GL (Fin 2) ℝ) z
      = denom (g : GL (Fin 2) ℝ) ((h • z : ℍ) : ℂ) * denom (h : GL (Fin 2) ℝ) z := by
  have hd : 0 < ((h : GL (Fin 2) ℝ)).det.val := by simp
  have := denom_cocycle (g : GL (Fin 2) ℝ) (h : GL (Fin 2) ℝ) z.im_ne_zero
  rw [← coe_smul_of_det_pos hd, ← ModularGroup.sl_moeb] at this
  rw [← this, map_mul, map_mul]

lemma conj_fix (γ u : SL(2, ℤ)) (σ : ℍ) (hu : u • σ = σ) :
    (γ * u * γ⁻¹) • (γ • σ) = γ • σ ∧
      denom ((γ * u * γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) ((γ • σ : ℍ) : ℂ)
        = denom (u : GL (Fin 2) ℝ) σ := by
  refine ⟨by rw [mul_smul, mul_smul, inv_smul_smul, hu], ?_⟩
  have h1 := denom_mul_SL (γ * u * γ⁻¹) γ σ
  have h2 := denom_mul_SL γ u σ
  rw [inv_mul_cancel_right, h2, hu, mul_comm] at h1
  exact (mul_right_cancel₀ (denom_ne_zero _ _) h1).symm

lemma eq_zero_of_fix {k : ℤ} (f : ModularForm 𝒮ℒ k) (u : SL(2, ℤ)) (σ : ℍ) (hu : u • σ = σ)
    (hk : denom (u : GL (Fin 2) ℝ) σ ^ k ≠ 1) : f σ = 0 := by
  have h : f (u • σ) = denom u σ ^ k * f σ :=
    SlashInvariantForm.slash_action_eqn'' f (by simp) σ
  rw [hu] at h
  have : (denom (u : GL (Fin 2) ℝ) σ ^ k - 1) * f σ = 0 := by linear_combination -h
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hk)

lemma exists_four : ∃ (σ : ℍ) (u : SL(2, ℤ)), u • σ = σ ∧
    IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) σ) 4 := by
  refine ⟨UpperHalfPlane.I, ModularGroup.S, ?_, ?_⟩
  · rw [modular_S_smul]; ext1; simp
  · rw [ModularGroup.denom_S]; exact Complex.isPrimitiveRoot_I

lemma exists_six : ∃ (σ : ℍ) (u : SL(2, ℤ)), u • σ = σ ∧
    IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) σ) 6 := by
  have hp := Complex.isPrimitiveRoot_exp 6 (by norm_num)
  set μ := Complex.exp (2 * Real.pi * Complex.I / (6 : ℕ)) with hμ
  have him : 0 < μ.im := by
    have : μ = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
      rw [hμ]; congr 1; push_cast; ring
    rw [this, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]
    positivity
  have h6 : μ ^ 6 = 1 := hp.pow_eq_one
  have h3 : μ ^ 3 - 1 ≠ 0 := sub_ne_zero.2 (hp.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
  have h1 : μ + 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    exact him.ne' this
  have hq : μ ^ 2 - μ + 1 = 0 := by
    have : (μ ^ 3 - 1) * ((μ + 1) * (μ ^ 2 - μ + 1)) = 0 := by linear_combination h6
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h3)).resolve_left h1
  have h0 : μ ≠ 0 := hp.ne_zero (by norm_num)
  refine ⟨⟨μ, him⟩, ModularGroup.T * ModularGroup.S, ?_, ?_⟩
  · rw [mul_smul, modular_S_smul, modular_T_smul]
    ext1
    simp only [coe_vadd]
    push_cast
    field_simp
    linear_combination -hq
  · rw [denom_mul_SL, ModularGroup.denom_S]
    have : ∀ z : ℍ, denom ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ) z = 1 := fun z => by
      rw [ModularGroup.denom_apply]; simp [ModularGroup.T]
    rw [this, one_mul]
    exact hp

theorem elliptic_of_zero : ∀ τ₀ : ℍ,
    (E₆ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧ IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 4) ∧
    (E₄ τ₀ = 0 → ∃ u : SL(2, ℤ), u • τ₀ = τ₀ ∧
      IsPrimitiveRoot (denom (u : GL (Fin 2) ℝ) τ₀) 6) := by
  intro τ₀
  constructor
  · intro h
    obtain ⟨σ, u, hu, hp⟩ := exists_four
    have h0 : E₆ σ = 0 := eq_zero_of_fix E₆ u σ hu (by
      rw [Ne, hp.zpow_eq_one_iff_dvd]; norm_num)
    obtain ⟨γ, rfl⟩ := GlobalTheory.T.j_invariant_equal_sl2_orbit τ₀ σ (by rw [h, h0]; ring)
    obtain ⟨h1, h2⟩ := conj_fix γ u σ hu
    exact ⟨_, h1, h2 ▸ hp⟩
  · intro h
    obtain ⟨σ, u, hu, hp⟩ := exists_six
    have h0 : E₄ σ = 0 := eq_zero_of_fix E₄ u σ hu (by
      rw [Ne, hp.zpow_eq_one_iff_dvd]; norm_num)
    obtain ⟨γ, rfl⟩ := GlobalTheory.T.j_invariant_equal_sl2_orbit τ₀ σ (by rw [h, h0]; ring)
    obtain ⟨h1, h2⟩ := conj_fix γ u σ hu
    exact ⟨_, h1, h2 ▸ hp⟩

end GlobalTheory.EllipticZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjugateFamilyOfInjective
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN.Lag

theorem mdiff_of_hasQ {N : ℕ} (hN : 0 < N) {f : ℍ → ℂ} (h : ∃ a, HasQ N f a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  obtain ⟨a, ha⟩ := h
  exact (GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ N f a hN ha).1

theorem hasQ_of_qConj {g : ℂ ≃+* ℂ} {N : ℕ} {f f' : ℍ → ℂ} (h : QConj g N f f') :
    (∃ a, HasQ N f a) ∧ ∃ a, HasQ N f' a := by
  obtain ⟨a, ha, hb⟩ := h
  exact ⟨⟨a, ha⟩, ⟨_, hb⟩⟩

theorem qConj_refl {N : ℕ} {f : ℍ → ℂ} (h : ∃ a, HasQ N f a) : QConj (RingEquiv.refl ℂ) N f f := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha, by simpa using ha⟩

theorem hasQ_zero (N : ℕ) : HasQ N (0 : ℍ → ℂ) (fun _ => 0) := by
  intro τ
  simp only [zero_mul, Pi.zero_apply]
  exact hasSum_zero

theorem qConj_ne_zero {g : ℂ ≃+* ℂ} {N : ℕ} (hN : 0 < N) {f f' : ℍ → ℂ} (h : QConj g N f f') (hf : f ≠ 0) :
    f' ≠ 0 := by
  obtain ⟨a, ha, hb⟩ := h
  rintro rfl
  have h1 := (GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique).1 N 0 _ _ hN hb (hasQ_zero N)
  have h2 : a = fun _ => 0 := funext fun n => by
    have := congrFun h1 n
    simpa using this
  subst h2
  exact hf ((GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique).2 N f 0 _ ha (hasQ_zero N))

theorem prod_ne_zero {N : ℕ} (hN : 0 < N) {κ : Type} (s : Finset κ) (u : κ → ℍ → ℂ)
    (hu : ∀ l ∈ s, u l ≠ 0 ∧ ∃ a, HasQ N (u l) a) : (fun τ => ∏ l ∈ s, u l τ) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro h
    have := congrFun h UpperHalfPlane.I
    simp at this
  | insert x s hx ih =>
    have hs : ∀ l ∈ s, u l ≠ 0 ∧ ∃ a, HasQ N (u l) a := fun l hl => hu l (Finset.mem_insert_of_mem hl)
    have hQ : ∃ b, HasQ N (fun τ => ∏ l ∈ s, u l τ) b :=
      (hasQ_of_qConj ((GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure (RingEquiv.refl ℂ) N hN).2.2.2.2.2 κ s u u
        fun l hl => qConj_refl (hs l hl).2).2).1
    intro h
    have hprod : ∀ τ, u x τ * (∏ l ∈ s, u l τ) = 0 := fun τ => by
      have := congrFun h τ
      simpa [Finset.prod_insert hx] using this
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff (u x) _ (mdiff_of_hasQ hN (hu x (Finset.mem_insert_self x s)).2)
      (mdiff_of_hasQ hN hQ) hprod with h1 | h1
    · exact (hu x (Finset.mem_insert_self x s)).1 h1
    · exact ih hs h1

end GlobalTheory.FN.Lag

namespace GlobalTheory.FN.Lag

open Finset in

theorem conj_family_of_injective : ∀ (g : ℂ ≃+* ℂ) (ι : Type) [Fintype ι] (act act' : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t t' F : ι → ℍ → ℂ), 0 < N → ActBij act → ActBij act' → IsFam act m t → IsFam act' m t' → IsFam act k F → Function.Injective t → (∀ i, QConj g N (t i) (t' i)) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ F' : ι → ℍ → ℂ, IsFam act' k F' ∧ ∀ i, QConj g N (F i) (F' i) := by
  intro g ι _ act act' m k N t t' F hN hb hb' ht ht' hF hinj htt' hFq
  classical
  have hR := GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure g N hN
  have hRr := GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure (RingEquiv.refl ℂ) N hN
  have hA := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act'

  obtain ⟨c, hc, hlag⟩ := GlobalTheory.T.modular_form_symmetric_function_decomp ι act m k N t F hN hb ht hF (fun i => (hasQ_of_qConj (htt' i)).1) hFq
  choose c' hc' using fun j => GlobalTheory.T.exists_qConj_level_one_invariant g (k + m * j) N (c j) hN (hc j).1 (hc j).2

  obtain ⟨s, hs, hmin⟩ := GlobalTheory.T.permutedModularFamily_monic_poly_coeff_invariant ι act k N F ⊤ hN hb hF
    (fun i => let ⟨a, ha⟩ := hFq i; ⟨a, ha, fun _ => Subring.mem_top _⟩)
  choose s' hs' using fun j : Fin (Fintype.card ι) => GlobalTheory.T.exists_qConj_level_one_invariant g (k * (Fintype.card ι - j)) N (s j) hN (hs j).1
    (let ⟨a, ha, _⟩ := (hs j).2; ⟨a, ha⟩)

  obtain ⟨D, hD⟩ : ∃ D : ι → ℍ → ℂ, ∀ i, D i = fun τ => ∏ l ∈ univ.erase i, (t i τ - t l τ) := ⟨_, fun _ => rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D' : ι → ℍ → ℂ, ∀ i, D' i = fun τ => ∏ l ∈ univ.erase i, (t' i τ - t' l τ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨A, hAd⟩ : ∃ A : ι → ℍ → ℂ, ∀ i, A i = fun τ =>
      ∑ j ∈ range (Fintype.card ι), c j τ * t i τ ^ (Fintype.card ι - 1 - j) := ⟨_, fun _ => rfl⟩
  obtain ⟨A', hA'd⟩ : ∃ A' : ι → ℍ → ℂ, ∀ i, A' i = fun τ =>
      ∑ j ∈ range (Fintype.card ι), c' j τ * t' i τ ^ (Fintype.card ι - 1 - j) := ⟨_, fun _ => rfl⟩
  have hDD : ∀ i, QConj g N (D i) (D' i) := fun i => by
    rw [hD i, hD' i]
    exact (hR.2.2.2.2.2 ι (univ.erase i) (fun l τ => t i τ - t l τ) (fun l τ => t' i τ - t' l τ)
      (fun l _ => hR.2.2.1 _ _ _ _ (htt' i) (htt' l))).2
  have hAA : ∀ i, QConj g N (A i) (A' i) := fun i => by
    rw [hAd i, hA'd i]
    exact (hR.2.2.2.2.2 ℕ (range (Fintype.card ι)) (fun j τ => c j τ * t i τ ^ (Fintype.card ι - 1 - j))
      (fun j τ => c' j τ * t' i τ ^ (Fintype.card ι - 1 - j))
      (fun j _ => hR.2.2.2.1 _ _ _ _ (hc' j).2 (hR.2.2.2.2.1 _ _ _ (htt' i)))).1
  have hDne : ∀ i, D i ≠ 0 := fun i => by
    rw [hD i]
    refine prod_ne_zero hN (univ.erase i) (fun l τ => t i τ - t l τ) fun l hl => ⟨?_, ?_⟩
    · intro h
      apply Finset.ne_of_mem_erase hl
      apply hinj
      funext τ
      have := congrFun h τ
      simp only [Pi.zero_apply] at this
      exact (sub_eq_zero.mp this).symm
    · exact (hasQ_of_qConj (hRr.2.2.1 _ _ _ _ (qConj_refl (hasQ_of_qConj (htt' i)).1)
        (qConj_refl (hasQ_of_qConj (htt' l)).1))).1
  have hD'ne : ∀ i, D' i ≠ 0 := fun i => qConj_ne_zero hN (hDD i) (hDne i)

  choose F' hF'1 hF'2 using fun i => GlobalTheory.T.exists_coeffwiseConjugate_of_integral_quotient g N (Fintype.card ι) (F i) (D i) (D' i) (A i) (A' i) s s' hN
    (hFq i) (hDD i) (hAA i) (fun j => (hs' j).2) (hDne i)
    (fun τ => by simp only [hD, hAd]; exact hlag i τ) (fun τ => hmin i τ)
  refine ⟨F', ?_, hF'1⟩

  have hv := (GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values ι act' m t').1 ht'
  have hD'fam : IsFam act' ((m * (Fintype.card ι - 1) : ℕ) : ℤ) D' := by
    rw [GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values]
    intro i γ τ
    simp only [hD', hv]
    set X : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)
    have e : ∀ l ∈ univ.erase i, X ^ (m : ℤ) * t' (act' i γ) τ - X ^ (m : ℤ) * t' (act' l γ) τ =
        X ^ (m : ℤ) * (t' (act' i γ) τ - t' (act' l γ) τ) := fun _ _ => by ring
    rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (mem_univ _),
      Finset.card_univ]
    congr 1
    · rw [← zpow_natCast, ← zpow_mul]
      push_cast
      ring_nf
    · apply Finset.prod_nbij (fun l => act' l γ)
      · intro l hl
        exact Finset.mem_erase.mpr ⟨fun h => Finset.ne_of_mem_erase hl ((hb' γ).1 h), mem_univ _⟩
      · intro l _ l' _ h
        exact (hb' γ).1 h
      · intro y hy
        obtain ⟨l, hl⟩ := (hb' γ).2 y
        refine ⟨l, ?_, hl⟩
        refine Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨fun h => ?_, mem_univ _⟩)
        subst h
        exact Finset.ne_of_mem_erase (Finset.mem_coe.mp hy) hl.symm
      · intro l _
        rfl
  have hA'fam : IsFam act' ((k + m * (Fintype.card ι - 1) : ℕ) : ℤ) A' := by
    have e : A' = fun i τ => ∑ j ∈ range (Fintype.card ι), (fun j i τ => c' j τ * t' i τ ^ (Fintype.card ι - 1 - j)) j i τ := by
      funext i τ
      rw [hA'd i]
    rw [e]
    refine hA.2.2.2.2.2.1 ℕ _ _ _ fun j hj => ?_
    have hj' : j < Fintype.card ι := Finset.mem_range.mp hj
    have hw : ((k + m * j : ℕ) : ℤ) + ((Fintype.card ι - 1 - j : ℕ) : ℤ) * (m : ℤ) =
        ((k + m * (Fintype.card ι - 1) : ℕ) : ℤ) := by
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.le_sub_one_of_lt hj')
      rw [hr, show j + r - j = r by omega]
      push_cast
      ring
    rw [← hw]
    exact hA.2.2.2.1 _ _ (fun _ => c' j) (fun i τ => t' i τ ^ (Fintype.card ι - 1 - j))
      (fun _ γ => (hc' j).1 γ) (hA.2.2.2.2.1 _ _ _ ht')
  intro i γ
  have e1 : (F' i ∣[(k : ℤ)] γ) * (D' i ∣[((m * (Fintype.card ι - 1) : ℕ) : ℤ)] γ) =
      A' i ∣[((k + m * (Fintype.card ι - 1) : ℕ) : ℤ)] γ := by
    rw [show ((k + m * (Fintype.card ι - 1) : ℕ) : ℤ) = (k : ℤ) + ((m * (Fintype.card ι - 1) : ℕ) : ℤ) by push_cast; ring,
      ← ModularForm.mul_slash_SL2]
    congr 1
    funext τ
    exact hF'2 i τ
  rw [hD'fam i γ, hA'fam i γ] at e1
  have hz : ∀ τ, ((F' i ∣[(k : ℤ)] γ) τ - F' (act' i γ) τ) * D' (act' i γ) τ = 0 := fun τ => by
    have := congrFun e1 τ
    simp only [Pi.mul_apply] at this
    rw [sub_mul, this, hF'2, sub_self]
  have hol1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F' i ∣[(k : ℤ)] γ) := by
    rw [ModularForm.SL_slash]
    exact MDifferentiable.slash (mdiff_of_hasQ hN (hasQ_of_qConj (hF'1 i)).2) _ _
  rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ (hol1.sub (mdiff_of_hasQ hN (hasQ_of_qConj (hF'1 (act' i γ))).2))
    (mdiff_of_hasQ hN (hasQ_of_qConj (hDD (act' i γ))).2) hz with h | h
  · funext τ
    exact sub_eq_zero.mp (congrFun h τ)
  · exact absurd h (hD'ne _)

end GlobalTheory.FN.Lag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteEtaleLocalSurjectiveOfIsSeparable
section
namespace GlobalTheory

open Polynomial IsLocalRing

open Polynomial IsLocalRing in
private lemma mem_smul_top_iff_of_linearEquiv_pi {V M ι : Type*} [CommRing V] [AddCommGroup M]
    [Module V M] [Fintype ι] [DecidableEq ι] (e : M ≃ₗ[V] (ι → V)) (J : Ideal V) (x : M) :
    x ∈ J • (⊤ : Submodule V M) ↔ ∀ i, e x i ∈ J := by
  constructor
  · intro hx
    have hle : J • (⊤ : Submodule V M) ≤
        (Submodule.pi Set.univ (fun _ : ι => J)).comap e.toLinearMap := by
      refine Submodule.smul_le.mpr fun r hr m _ => ?_
      simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
        LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact fun i => J.mul_mem_right _ hr
    intro i
    have := hle hx
    simp only [Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearEquiv.coe_coe] at this
    exact this i
  · intro hx
    have hsum : x = ∑ i, e x i • e.symm (fun j => if i = j then 1 else 0) := by
      apply e.injective
      simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
      exact pi_eq_sum_univ (e x)
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

open Polynomial IsLocalRing in
private lemma ideal_smul_top_eq_self {V : Type*} [CommRing V] (J : Ideal V) :
    J • (⊤ : Submodule V V) = J := by
  rw [smul_eq_mul, Ideal.mul_top]

open Polynomial IsLocalRing in
private lemma isAdicComplete_of_linearEquiv_pi {V M ι : Type*} [CommRing V] [AddCommGroup M]
    [Module V M] [Fintype ι] (e : M ≃ₗ[V] (ι → V)) (J : Ideal V) [IsAdicComplete J V] :
    IsAdicComplete J M := by
  classical
  have key : ∀ (n : ℕ) (x y : M), x ≡ y [SMOD J ^ n • (⊤ : Submodule V M)] ↔
      ∀ i, e x i ≡ e y i [SMOD J ^ n • (⊤ : Submodule V V)] := by
    intro n x y
    simp only [SModEq.sub_mem, mem_smul_top_iff_of_linearEquiv_pi e, map_sub, Pi.sub_apply,
      ideal_smul_top_eq_self]
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · apply e.injective
    funext i
    rw [map_zero]
    exact IsHausdorff.haus' (I := J) (e x i) fun n => by
      simpa using (key n x 0).1 (hx n) i
  · choose L hL using fun i => IsPrecomplete.prec' (I := J) (fun n => e (f n) i)
      (fun {m n} hmn => (key m _ _).1 (hf hmn) i)
    refine ⟨e.symm L, fun n => (key n _ _).2 fun i => ?_⟩
    simpa using hL i n

open Polynomial IsLocalRing in

theorem _root_.GlobalTheory.unramExt : _root_.ReciprocityTheory.ChartRestriction.G.Out.UnramExtSt := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.UnramExtSt
  intro V _ _ _ _ k' _ _ _ _
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element (ResidueField V) k'
  have hint : IsIntegral (ResidueField V) θ := .of_finite _ _
  obtain ⟨μ, hμmap, hμdeg, hμ⟩ := lifts_and_degree_eq_and_monic
    (map_surjective _ (residue_surjective (R := V)) (minpoly (ResidueField V) θ))
    (minpoly.monic hint)
  letI : Algebra V k' := ((algebraMap (ResidueField V) k').comp (residue V)).toAlgebra
  haveI : IsScalarTower V (ResidueField V) k' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hroot : eval₂ (algebraMap V k') θ μ = 0 := by
    rw [show algebraMap V k' = (algebraMap (ResidueField V) k').comp (residue V) from rfl,
      ← eval₂_map, hμmap]
    exact minpoly.aeval _ _
  let φ : AdjoinRoot μ →+* k' := AdjoinRoot.lift (algebraMap V k') θ hroot
  have hφ : ∀ g : V[X], φ (AdjoinRoot.mk μ g) = aeval θ g := fun g => by
    simp [φ, AdjoinRoot.lift_mk, aeval_def]
  have hadj : Algebra.adjoin (ResidueField V) {θ} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ]; rfl
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : y ∈ Algebra.adjoin (ResidueField V) {θ} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := map_surjective _ (residue_surjective (R := V)) p
    refine ⟨AdjoinRoot.mk μ q, ?_⟩
    rw [hφ]
    simp [aeval_def, eval₂_map, IsScalarTower.algebraMap_eq V (ResidueField V) k']
  haveI : Nontrivial (AdjoinRoot μ) := φ.domain_nontrivial
  have hnon : ∀ w : AdjoinRoot μ, w ∈ nonunits (AdjoinRoot μ) ↔ φ w = 0 := by
    intro w
    refine ⟨fun hw => ?_, fun hw hu => (hu.map φ).ne_zero hw⟩
    by_contra hne
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective w
    rw [hφ] at hne
    exact hw (_root_.GlobalTheory.isUnit_adjoinRoot_mk_of_aeval_ne_zero hint hμ hμmap hne)
  haveI : IsLocalRing (AdjoinRoot μ) := IsLocalRing.of_nonunits_add fun a b ha hb => by
    rw [hnon] at ha hb ⊢
    rw [map_add, ha, hb, add_zero]
  have hmax : maximalIdeal (AdjoinRoot μ) = RingHom.ker φ := by
    ext w
    rw [mem_maximalIdeal, hnon, RingHom.mem_ker]
  have hCm : (AdjoinRoot.mk μ).comp C = algebraMap V (AdjoinRoot μ) := rfl
  have hker : RingHom.ker φ = (maximalIdeal V).map (algebraMap V (AdjoinRoot μ)) := by
    apply le_antisymm
    · intro w hw
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective w
      rw [RingHom.mem_ker, hφ] at hw
      have hdvd : minpoly (ResidueField V) θ ∣ g.map (residue V) := by
        apply minpoly.dvd
        rw [← IsLocalRing.ResidueField.algebraMap_eq, aeval_map_algebraMap]
        exact hw
      obtain ⟨h', hh'⟩ := hdvd
      obtain ⟨h, rfl⟩ := map_surjective _ (residue_surjective (R := V)) h'
      have hcoeff : ∀ n, (g - μ * h).coeff n ∈ maximalIdeal V := by
        intro n
        rw [← residue_eq_zero_iff, ← coeff_map, Polynomial.map_sub, Polynomial.map_mul, hμmap,
          hh', sub_self, coeff_zero]
      have hmk : AdjoinRoot.mk μ g = AdjoinRoot.mk μ (g - μ * h) := by
        simp [AdjoinRoot.mk_self]
      rw [hmk, ← hCm, ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_C_iff.2 hcoeff)
    · rw [Ideal.map_le_iff_le_comap]
      intro v hv
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hCm, RingHom.comp_apply, hφ, aeval_C,
        IsScalarTower.algebraMap_apply V (ResidueField V) k',
        IsLocalRing.ResidueField.algebraMap_eq, (residue_eq_zero_iff v).2 hv, map_zero]
  have hmW : maximalIdeal (AdjoinRoot μ) = (maximalIdeal V).map (algebraMap V (AdjoinRoot μ)) :=
    hmax.trans hker
  let pb := AdjoinRoot.powerBasis' hμ
  haveI : Module.Finite V (AdjoinRoot μ) := pb.finite
  haveI : Module.Free V (AdjoinRoot μ) := Module.Free.of_basis pb.basis
  haveI : IsNoetherianRing (AdjoinRoot μ) := inferInstance
  have hinj : Function.Injective (algebraMap V (AdjoinRoot μ)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    rw [← hCm, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at hv
    by_contra hne
    have hle := degree_le_of_dvd hv (C_ne_zero.2 hne)
    rw [degree_C hne, hμdeg] at hle
    exact absurd hle (not_le.2 (minpoly.degree_pos hint))
  haveI hlh : IsLocalHom (algebraMap V (AdjoinRoot μ)) := by
    refine ⟨fun v hv => ?_⟩
    by_contra hnu
    have hvm : v ∈ maximalIdeal V := (mem_maximalIdeal v).2 hnu
    have := Ideal.mem_map_of_mem (algebraMap V (AdjoinRoot μ)) hvm
    rw [← hmW] at this
    exact (mem_maximalIdeal _).1 this hv
  let e : ResidueField (AdjoinRoot μ) ≃+* k' :=
    (Ideal.quotEquivOfEq hmax).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have he : ∀ w, e (residue (AdjoinRoot μ) w) = φ w := fun w => rfl
  have he' : ∀ v : V, e (residue (AdjoinRoot μ) (algebraMap V (AdjoinRoot μ) v)) =
      algebraMap (ResidueField V) k' (residue V v) := by
    intro v
    rw [he, ← hCm, RingHom.comp_apply, hφ, aeval_C]
    rfl
  let eAlg : ResidueField (AdjoinRoot μ) →ₐ[ResidueField V] k' :=
    { e.toRingHom with
      commutes' := fun r => by
        obtain ⟨v, rfl⟩ := residue_surjective r
        simpa using he' v }
  haveI : Algebra.IsSeparable (ResidueField V) (ResidueField (AdjoinRoot μ)) :=
    Algebra.IsSeparable.of_algHom _ _ eAlg
  haveI : Algebra.FormallyUnramified V (AdjoinRoot μ) :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmW.symm
  obtain ⟨hdom, hdvr⟩ := _root_.GlobalTheory.exists_isDiscreteValuationRing_of_flat V (AdjoinRoot μ) hmW.symm
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top)
  have hcompl : IsAdicComplete (maximalIdeal (AdjoinRoot μ)) (AdjoinRoot μ) := by
    rw [hmW, IsAdicComplete.map_algebraMap_iff]
    exact isAdicComplete_of_linearEquiv_pi pb.basis.equivFun _
  exact ⟨AdjoinRoot μ, inferInstance, hdom, hdvr, hcompl, inferInstance, pb.finite, hinj, hlh,
    inferInstance, e, he'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevMulVecOutside
section
open Matrix Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.LevelStabiliser

open GlobalTheory.LevelUnitary

variable (k i r' : ℕ)

theorem liftVec_eq (v : Fin (2 * r' + k + 1) → ℂ) : liftVec k i r' v = incl k i r' *ᵥ v := by
  ext p
  have h := incl_mul k i r' (Matrix.of fun a (_ : Unit) => v a) p ()
  exact h.symm

end GlobalTheory.LevelStabiliser
end
end

