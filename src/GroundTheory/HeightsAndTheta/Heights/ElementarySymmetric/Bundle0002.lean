import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.FlatDegree.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymPerturbation
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace AntisymPerturbation

variable {T : Type} [Fintype T] [DecidableEq T] {N j : ℕ}

omit [Fintype T] [DecidableEq T] in

theorem rename_mul_eq_or_neg {R : MvPolynomial (T × Fin N) ℝ} {σ ρ : Equiv.Perm (T × Fin N)}
    (hσ : rename σ R = R ∨ rename σ R = -R) (hρ : rename ρ R = R ∨ rename ρ R = -R) :
    rename ⇑(σ * ρ) R = R ∨ rename ⇑(σ * ρ) R = -R := by
  rw [Equiv.Perm.coe_mul, ← rename_rename]
  rcases hρ with h | h
  · rw [h]; exact hσ
  · rw [h, map_neg]
    rcases hσ with h' | h'
    · right; rw [h']
    · left; rw [h', neg_neg]

theorem rename_swap_eq_or_neg {R : MvPolynomial (T × Fin N) ℝ} (hR : R ∈ antisymSpace T N j)
    (τ : T) (a c : Fin N) (hac : a.val ≤ c.val) (hblk : c.val < j ∨ j ≤ a.val) :
    rename ⇑(Equiv.swap (τ, a) (τ, c)) R = R ∨ rename ⇑(Equiv.swap (τ, a) (τ, c)) R = -R := by
  have hR' : ∀ σ, IsBlockSimpleSwap T N j σ → rename σ R = -R := hR.2
  suffices H : ∀ k : ℕ, ∀ c : Fin N, c.val = a.val + k → (c.val < j ∨ j ≤ a.val) →
      rename ⇑(Equiv.swap (τ, a) (τ, c)) R = R ∨ rename ⇑(Equiv.swap (τ, a) (τ, c)) R = -R from
    H (c.val - a.val) c (by omega) hblk
  intro k
  induction k with
  | zero =>
    intro c hc _
    have hca : c = a := Fin.ext (by omega)
    subst hca
    left
    rw [Equiv.swap_self, Equiv.coe_refl, rename_id_apply]
  | succ k ih =>
    intro c hc hb
    have hc' : a.val + k < N := by omega
    have hsimple : rename ⇑(Equiv.swap (τ, (⟨a.val + k, hc'⟩ : Fin N)) (τ, c)) R = -R :=
      hR' _ ⟨τ, ⟨a.val + k, hc'⟩, c, by simp only; omega, by simp only; omega, rfl⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have hca : (⟨a.val + 0, hc'⟩ : Fin N) = a := Fin.ext (by simp)
      rw [hca] at hsimple
      exact Or.inr hsimple
    · have hprev := ih ⟨a.val + k, hc'⟩ rfl (by simp only; omega)
      have h1 : (τ, a) ≠ (τ, (⟨a.val + k, hc'⟩ : Fin N)) := by
        simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff]; omega
      have h2 : (τ, a) ≠ (τ, c) := by
        simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff]; omega
      have e := Equiv.swap_mul_swap_mul_swap h1 h2
      rw [Equiv.swap_comm (τ, c) (τ, a)] at e
      rw [← e]
      exact rename_mul_eq_or_neg (rename_mul_eq_or_neg (Or.inr hsimple) hprev) (Or.inr hsimple)

omit [Fintype T] [DecidableEq T] in

theorem image_comp_perm (σ : Equiv.Perm (T × Fin N)) (τ : T) {a b a' b' : Fin N}
    (hσa : σ (τ, a) = (τ, a')) (hσb : σ (τ, b) = (τ, b')) {K : Set (T × Fin N → ℝ)}
    (hKc : IsCompact K) (hKH : K ⊆ diagHyperplane T N τ a' b')
    (hKO : ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a' b').Nonempty ∧
      O ∩ diagHyperplane T N τ a' b' ⊆ K) :
    IsCompact ((fun y => y ∘ ⇑σ) '' K) ∧ (fun y => y ∘ ⇑σ) '' K ⊆ diagHyperplane T N τ a b ∧
      ∃ O : Set (T × Fin N → ℝ), IsOpen O ∧ (O ∩ diagHyperplane T N τ a b).Nonempty ∧
        O ∩ diagHyperplane T N τ a b ⊆ (fun y => y ∘ ⇑σ) '' K := by
  have hinv_a : σ⁻¹ (τ, a') = (τ, a) := by rw [← hσa]; simp
  have hinv_b : σ⁻¹ (τ, b') = (τ, b) := by rw [← hσb]; simp
  refine ⟨hKc.image (continuous_pi fun p => continuous_apply _), ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    show y (σ (τ, a)) = y (σ (τ, b))
    rw [hσa, hσb]
    exact hKH hy
  · obtain ⟨O, hO, ⟨y0, hy0O, hy0H⟩, hOK⟩ := hKO
    refine ⟨(fun x => x ∘ ⇑σ⁻¹) ⁻¹' O, hO.preimage (continuous_pi fun p => continuous_apply _),
      ⟨y0 ∘ ⇑σ, ?_, ?_⟩, ?_⟩
    · have e : (y0 ∘ ⇑σ) ∘ ⇑σ⁻¹ = y0 := by funext p; simp
      show (y0 ∘ ⇑σ) ∘ ⇑σ⁻¹ ∈ O
      rw [e]
      exact hy0O
    · show y0 (σ (τ, a)) = y0 (σ (τ, b))
      rw [hσa, hσb]
      exact hy0H
    · rintro x ⟨hxO, hxH⟩
      refine ⟨x ∘ ⇑σ⁻¹, hOK ⟨hxO, ?_⟩, ?_⟩
      · show x (σ⁻¹ (τ, a')) = x (σ⁻¹ (τ, b'))
        rw [hinv_a, hinv_b]
        exact hxH
      · funext p; simp

end AntisymPerturbation

theorem AntisymPerturbation.proof (hStab : AntisymStability.Statement) :
    AntisymPerturbation.Statement := by
  intro T _ _ N j hj hjN h K hK
  let jm : Fin N := ⟨j - 1, by omega⟩
  let jp : Fin N := ⟨j, hjN⟩
  let σ : T → Fin N → Fin N → Equiv.Perm (T × Fin N) := fun τ a b =>
    Equiv.swap (τ, a) (τ, jm) * Equiv.swap (τ, b) (τ, jp)
  have hσa : ∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val → σ τ a b (τ, a) = (τ, jm) := by
    intro τ a b ha hb
    have e1 : Equiv.swap (τ, b) (τ, jp) (τ, a) = (τ, a) := Equiv.swap_apply_of_ne_of_ne
      (by simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff]; omega)
      (by simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff, jp]; omega)
    simp only [σ, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [e1, Equiv.swap_apply_left]
  have hσb : ∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val → σ τ a b (τ, b) = (τ, jp) := by
    intro τ a b ha hb
    simp only [σ, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne
      (by simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff, jp]; omega)
      (by simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff, jp, jm]; omega)
  have hsign : ∀ R ∈ antisymSpace T N j, ∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val →
      rename ⇑(σ τ a b) R = R ∨ rename ⇑(σ τ a b) R = -R := by
    intro R hR τ a b ha hb
    refine AntisymPerturbation.rename_mul_eq_or_neg
      (AntisymPerturbation.rename_swap_eq_or_neg hR τ a jm (by simp only [jm]; omega)
        (Or.inl (by simp only [jm]; omega))) ?_
    rw [Equiv.swap_comm]
    exact AntisymPerturbation.rename_swap_eq_or_neg hR τ jp b (by simp only [jp]; omega)
      (Or.inr (by simp only [jp]; omega))
  obtain ⟨C, hC⟩ := hStab T N j (fun τ a b => (fun y => y ∘ ⇑(σ τ a b)) '' K τ)
    (fun τ a b ha hb => AntisymPerturbation.image_comp_perm (σ τ a b) τ (hσa τ a b ha hb)
      (hσb τ a b ha hb) (hK τ).1 (hK τ).2.1 (hK τ).2.2.1)
  rcases isEmpty_or_nonempty T with hT | ⟨⟨τ0⟩⟩
  · refine ⟨0, fun P v ε hR _ => ?_⟩
    obtain ⟨l, hl, hb⟩ := hC _ hR
    exact ⟨l, hl, fun m => by simpa using hb 0 le_rfl (fun τ => isEmptyElim τ) m⟩
  · refine ⟨C, fun P v ε hR hε => ?_⟩
    obtain ⟨l, hl, hb⟩ := hC _ hR
    refine ⟨l, hl, hb ε ?_ ?_⟩
    · obtain ⟨O, _, ⟨y, hyO, hyH⟩, hOK⟩ := (hK τ0).2.2.1
      exact (abs_nonneg _).trans (hε τ0 y (hOK ⟨hyO, hyH⟩))
    · rintro τ a b ha hb x ⟨y, hy, rfl⟩
      have hyh : eval y h = 0 := (hK τ).2.2.2 y hy
      have hyP := hε τ y hy
      show |eval (y ∘ ⇑(σ τ a b)) (P - v • h)| ≤ ε
      rw [← eval_rename]
      rcases hsign _ hR τ a b ha hb with e | e
      · rw [e]; simpa [hyh] using hyP
      · rw [e, map_neg, abs_neg]; simpa [hyh] using hyP

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PAntisymStability
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def antisymEvalOn {T : Type*} {N : ℕ} (Ω : Set (T × Fin N → ℝ)) :
    MvPolynomial (T × Fin N) ℝ →ₗ[ℝ] C(Ω, ℝ) where
  toFun p := ⟨fun x => eval (x : T × Fin N → ℝ) p, (continuous_eval p).comp continuous_subtype_val⟩
  map_add' p q := by ext x; simp
  map_smul' c p := by ext x; simp

@[simp] lemma antisymEvalOn_apply {T : Type*} {N : ℕ} (Ω : Set (T × Fin N → ℝ))
    (p : MvPolynomial (T × Fin N) ℝ) (x : Ω) : antisymEvalOn Ω p x = eval (x : T × Fin N → ℝ) p :=
  rfl

lemma abs_coeff_le_sum_abs_coeff {σ : Type*} (p : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    |coeff m p| ≤ ∑ m' ∈ p.support, |coeff m' p| := by
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (f := fun m' => |coeff m' p|) (fun _ _ => abs_nonneg _) hm
  · rw [notMem_support_iff.1 hm, abs_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma exists_uniform_coeff_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {σ : Type*} (G : E →ₗ[ℝ] MvPolynomial σ ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : E) (m : σ →₀ ℕ), |coeff m (G y)| ≤ C * ‖y‖ := by
  let b := Module.finBasis ℝ E
  let c : Fin (Module.finrank ℝ E) → (E →L[ℝ] ℝ) := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖c i‖ * ∑ m' ∈ (G (b i)).support, |coeff m' (G (b i))|,
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _), fun y m => ?_⟩
  have hy : G y = ∑ i, b.repr y i • G (b i) := by
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp only [map_smul]
  rw [hy, coeff_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [coeff_smul, smul_eq_mul, abs_mul]
  have h1 : |b.repr y i| ≤ ‖c i‖ * ‖y‖ := by
    have := (c i).le_opNorm y
    simpa [c, Real.norm_eq_abs] using this
  calc |b.repr y i| * |coeff m (G (b i))|
      ≤ (‖c i‖ * ‖y‖) * ∑ m' ∈ (G (b i)).support, |coeff m' (G (b i))| :=
        mul_le_mul h1 (abs_coeff_le_sum_abs_coeff _ _) (abs_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖c i‖ * (∑ m' ∈ (G (b i)).support, |coeff m' (G (b i))|) * ‖y‖ := by ring

theorem AntisymStability.proof (hB1 : AntisymDivisible.Statement) : AntisymStability.Statement := by
  intro T _ _ N j Om hOm
  set Ω : Set (T × Fin N → ℝ) :=
    ⋃ (τ : T) (a : Fin N) (b : Fin N) (_ : a.val < j ∧ j ≤ b.val), Om τ a b with hΩdef
  have hΩc : IsCompact Ω :=
    isCompact_iUnion fun τ => isCompact_iUnion fun a => isCompact_iUnion fun b =>
      isCompact_iUnion fun h => (hOm τ a b h.1 h.2).1
  have : CompactSpace Ω := isCompact_iff_compactSpace.mp hΩc
  have : FiniteDimensional ℝ (homogeneousSubmodule (T × Fin N) ℝ (antisymDegree T N + 1)) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  have : FiniteDimensional ℝ (antisymSpace T N j) :=
    Submodule.finiteDimensional_of_le (fun P hP => hP.1)
  let Φ : antisymSpace T N j →ₗ[ℝ] C(Ω, ℝ) := (antisymEvalOn Ω).comp (antisymSpace T N j).subtype
  obtain ⟨g, hg⟩ := Φ.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict Φ)
  obtain ⟨C, hC0, hC⟩ := exists_uniform_coeff_bound (E := LinearMap.range Φ) ((antisymSpace T N j).subtype.comp g)
  refine ⟨C, fun P hP => ?_⟩
  let P' : antisymSpace T N j := ⟨P, hP⟩
  let y := Φ.rangeRestrict P'
  let Q : antisymSpace T N j := g y
  have hQ : Φ Q = Φ P' := by
    have h1 : Φ.rangeRestrict Q = y := LinearMap.congr_fun hg y
    exact congrArg Subtype.val h1
  have hker : Φ (P' - Q) = 0 := by rw [map_sub, hQ, sub_self]
  have hvan : ∀ x ∈ Ω, eval x ((P' - Q : antisymSpace T N j) : MvPolynomial (T × Fin N) ℝ) = 0 := by
    intro x hx
    have := congrArg (fun f : C(Ω, ℝ) => f ⟨x, hx⟩) hker
    simpa [Φ] using this
  obtain ⟨l, hl, hPl⟩ := hB1 T N j _ (P' - Q).2 (fun τ a b ha hb => by
    obtain ⟨_, _, O, hO, hne, hOsub⟩ := hOm τ a b ha hb
    refine ⟨O, hO, hne, fun x hx => hvan x ?_⟩
    exact Set.mem_iUnion.2 ⟨τ, Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨b,
      Set.mem_iUnion.2 ⟨⟨ha, hb⟩, hOsub hx⟩⟩⟩⟩)
  refine ⟨l, hl, fun M hM hbd m => ?_⟩
  have hPQ : P - antisymDelta T N * l = (Q : MvPolynomial (T × Fin N) ℝ) := by
    rw [← hPl, Submodule.coe_sub]
    simp [P']
  rw [hPQ]
  have hy : ‖y‖ ≤ M := by
    have e : ‖y‖ = ‖Φ P'‖ := rfl
    rw [e, ContinuousMap.norm_le _ hM]
    rintro ⟨x, hx⟩
    have hx' := hx
    simp only [hΩdef, Set.mem_iUnion] at hx'
    obtain ⟨τ, a, b, ⟨ha, hb⟩, hxO⟩ := hx'
    simpa [Φ, P', Real.norm_eq_abs] using hbd τ a b ha hb x hxO
  calc |coeff m (Q : MvPolynomial (T × Fin N) ℝ)| ≤ C * ‖y‖ := hC y m
    _ ≤ C * M := mul_le_mul_of_nonneg_left hy hC0

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFlatDegreeBoundX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlatTheorem

open NumberField

theorem FlatDegreeBound.one_le_rootDiscr (K : Type) [Field K] [NumberField K] :
    1 ≤ rootDiscr K := by
  rw [rootDiscr_def]
  have h : (1 : ℝ) ≤ ((|discr K| : ℤ) : ℝ) := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  exact Real.one_le_rpow h (by positivity)

theorem FlatDegreeBound.rootDiscr_le_rootDiscr (K E : Type) [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] : rootDiscr K ≤ rootDiscr E := by
  have key := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) E (𝓞 E)
  have hE0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have hN : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at key
    exact hE0 key
  have hle : (discr K).natAbs ^ Module.finrank K E ≤ (discr E).natAbs := by
    rw [key]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hN)
  set n := Module.finrank ℚ K with hn
  set m := Module.finrank K E with hm
  have hnE : Module.finrank ℚ E = n * m := (Module.finrank_mul_finrank ℚ K E).symm
  have hnpos : 0 < n := Module.finrank_pos
  have hmpos : 0 < m := Module.finrank_pos
  have habsK : ((|discr K| : ℤ) : ℝ) = ((discr K).natAbs : ℝ) := (Nat.cast_natAbs _).symm
  have habsE : ((|discr E| : ℤ) : ℝ) = ((discr E).natAbs : ℝ) := (Nat.cast_natAbs _).symm
  rw [rootDiscr_def, rootDiscr_def, habsK, habsE, hnE]
  have hleR : (((discr K).natAbs : ℝ)) ^ (m : ℝ) ≤ ((discr E).natAbs : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hle
  have h0 : (0 : ℝ) ≤ ((discr K).natAbs : ℝ) := Nat.cast_nonneg _
  calc ((discr K).natAbs : ℝ) ^ (n : ℝ)⁻¹
      = (((discr K).natAbs : ℝ) ^ (m : ℝ)) ^ (((n * m : ℕ) : ℝ)⁻¹) := by
        rw [← Real.rpow_mul h0]
        congr 1
        push_cast
        field_simp
    _ ≤ ((discr E).natAbs : ℝ) ^ (((n * m : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hleR (by positivity)

theorem FlatDegreeBound.proof : FlatDegreeBound.Statement := by
  intro K E _ _ _ _ _ p q logΩ c hc
  subst hc
  have h1 := FlatDegreeBound.one_le_rootDiscr K
  have h2 := FlatDegreeBound.rootDiscr_le_rootDiscr K E
  have hlK : 0 ≤ Real.log (rootDiscr K) := Real.log_nonneg h1
  have hlKE : Real.log (rootDiscr K) ≤ Real.log (rootDiscr E) :=
    Real.log_le_log (by linarith) h2
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have ha := mul_nonneg hq hlK
  have hb := mul_nonneg hq (sub_nonneg.mpr hlKE)
  rw [abs_le]
  constructor <;> nlinarith

end GroundTheory.Heights₂.Heights.FlatTheorem
end

