import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.PPieceCoefficientsHolomorphic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Matrix Filter Topology

theorem coeff_finset_prod_differentiableAt {d : ℕ} {ι : Type*} (S : Finset ι)
    (P : ι → (Fin d → ℂ) → Polynomial ℂ) (y₀ : Fin d → ℂ)
    (hP : ∀ i ∈ S, ∀ k, DifferentiableAt ℂ (fun y => (P i y).coeff k) y₀) :
    ∀ k, DifferentiableAt ℂ (fun y => (∏ i ∈ S, P i y).coeff k) y₀ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro k
    simp only [Finset.prod_empty]
    exact differentiableAt_const _
  | insert a S ha ih =>
    intro k
    have ih' := ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha, Polynomial.coeff_mul]
    exact DifferentiableAt.fun_sum fun p _ =>
      (hP a (Finset.mem_insert_self a S) p.1).mul (ih' p.2)

theorem coeff_X_sub_C_differentiableAt {d : ℕ} (a : (Fin d → ℂ) → ℂ) (y₀ : Fin d → ℂ)
    (ha : DifferentiableAt ℂ a y₀) (k : ℕ) :
    DifferentiableAt ℂ (fun y => (Polynomial.X - Polynomial.C (a y)).coeff k) y₀ := by
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  by_cases hk : k = 0
  · subst hk
    simpa using ha.neg
  · simp only [hk, if_false]
    exact differentiableAt_const _

theorem PieceCoefficientsHolomorphic.proof : PieceCoefficientsHolomorphic.Statement := by
  classical
  intro n d N A Z c Q O F hcov hO hF hXOF i y₀ hy₀
  have hy₀' : eval y₀ Q ≠ 0 := hy₀
  obtain ⟨hfin, hcard, hsec⟩ := hcov y₀ hy₀'
  choose! U V g hU hyU hV hxV hg hgy hAg hZV using hsec
  set T : Finset (Fin n → ℂ) := hfin.toFinset with hT
  have hmemT : ∀ x, x ∈ T ↔ x ∈ Z ∧ A *ᵥ x = y₀ := fun x => by simp [T]
  have hTcard : T.card = N := by rw [← hcard, Set.ncard_eq_toFinset_card _ hfin]
  have hgd : ∀ x ∈ T, DifferentiableAt ℂ (g x) y₀ := fun x hx =>
    (hg x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2).differentiableAt
      ((hU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2).mem_nhds
        (hyU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2))
  have hgc : ∀ x ∈ T, Tendsto (g x) (𝓝 y₀) (𝓝 x) := fun x hx => by
    have := (hgd x hx).continuousAt
    rw [ContinuousAt, hgy x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2] at this
    exact this
  have hQopen : IsOpen {y : Fin d → ℂ | eval y Q ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval Q) continuous_const
  have hev : ∀ᶠ w in 𝓝 y₀, eval w Q ≠ 0 ∧ (∀ x ∈ T, w ∈ U x) ∧
      (∀ x ∈ T, ∀ x' ∈ T, x ≠ x' → g x w ≠ g x' w) ∧
      (∀ x ∈ T, x ∈ O → g x w ∈ O) ∧ (∀ x ∈ T, x ∉ O → g x w ∉ F) := by
    refine Filter.Eventually.and (hQopen.mem_nhds hy₀') (Filter.Eventually.and ?_
      (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_)))
    · exact (eventually_all_finset T).2 fun x hx =>
        (hU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2).mem_nhds (hyU x ((hmemT x).1 hx).1 ((hmemT x).1 hx).2)
    · refine (eventually_all_finset T).2 fun x hx => (eventually_all_finset T).2 fun x' hx' => ?_
      by_cases hxx : x = x'
      · exact Filter.Eventually.of_forall fun w h => absurd hxx h
      · exact ((hgc x hx).prodMk_nhds (hgc x' hx')).eventually
          ((isOpen_ne_fun continuous_fst continuous_snd).eventually_mem
            (show (x, x') ∈ {p : (Fin n → ℂ) × (Fin n → ℂ) | p.1 ≠ p.2} from hxx)) |>.mono
          fun w hw _ => hw
    · refine (eventually_all_finset T).2 fun x hx => ?_
      by_cases hxO : x ∈ O
      · exact ((hgc x hx).eventually (hO.eventually_mem hxO)).mono fun w hw _ => hw
      · exact Filter.Eventually.of_forall fun w h => absurd h hxO
    · refine (eventually_all_finset T).2 fun x hx => ?_
      by_cases hxO : x ∈ O
      · exact Filter.Eventually.of_forall fun w h => absurd hxO h
      · have hxF : x ∉ F := by
          intro hxF
          have hX : x ∈ {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ F :=
            ⟨⟨((hmemT x).1 hx).1, by rw [((hmemT x).1 hx).2]; exact hy₀'⟩, hxF⟩
          rw [← hXOF] at hX
          exact hxO hX.2
        exact ((hgc x hx).eventually (hF.isOpen_compl.eventually_mem hxF)).mono fun w hw _ => hw
  have heq : (fun y => (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
        (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i) =ᶠ[𝓝 y₀]
      (fun y => (∏ x ∈ T.filter (· ∈ O),
        (Polynomial.X - Polynomial.C (∑ j, c j * g x y j))).coeff i) := by
    filter_upwards [hev] with w ⟨hwQ, hwU, hwinj, hwO, hwF⟩
    have hinj : Set.InjOn (fun x => g x w) T := fun x hx x' hx' h => by
      by_contra hne
      exact hwinj x hx x' hx' hne h
    have hgZ : ∀ x ∈ T, g x w ∈ Z ∧ A *ᵥ g x w = w := fun x hx => by
      have h1 := ((hmemT x).1 hx).1
      have h2 := ((hmemT x).1 hx).2
      refine ⟨?_, hAg x h1 h2 w (hwU x hx)⟩
      have hmem : g x w ∈ g x '' U x := ⟨w, hwU x hx, rfl⟩
      rw [← hZV x h1 h2] at hmem
      exact hmem.1
    obtain ⟨hfinw, hcardw, -⟩ := hcov w hwQ
    have hfull : ((T.image fun x => g x w : Finset _) : Set (Fin n → ℂ)) =
        {x | x ∈ Z ∧ A *ᵥ x = w} := by
      apply Set.eq_of_subset_of_ncard_le _ _ hfinw
      · intro z hz
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        exact hgZ x hx
      · rw [hcardw, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, hTcard]
    have hset : {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = w} =
        (((T.filter (· ∈ O)).image fun x => g x w : Finset _) : Set (Fin n → ℂ)) := by
      ext z
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨hzZ, hzO, hzA⟩
        have hz : z ∈ ((T.image fun x => g x w : Finset _) : Set (Fin n → ℂ)) := by
          rw [hfull]; exact ⟨hzZ, hzA⟩
        simp only [Finset.mem_coe, Finset.mem_image] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        refine ⟨x, ⟨hx, ?_⟩, rfl⟩
        by_contra hxO
        have hX : g x w ∈ {x | x ∈ Z ∧ eval (A *ᵥ x) Q ≠ 0} ∩ O :=
          ⟨⟨hzZ, by rw [hzA]; exact hwQ⟩, hzO⟩
        rw [hXOF] at hX
        exact hwF x hx hxO hX.2
      · rintro ⟨x, ⟨hx, hxO⟩, rfl⟩
        exact ⟨(hgZ x hx).1, hwO x hx hxO, (hgZ x hx).2⟩
    have key : (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = w},
        (Polynomial.X - Polynomial.C (∑ j, c j * x j))) =
        ∏ x ∈ T.filter (· ∈ O), (Polynomial.X - Polynomial.C (∑ j, c j * g x w j)) := by
      rw [hset, finprod_mem_coe_finset, Finset.prod_image
        (fun x hx x' hx' h => hinj (Finset.mem_filter.1 hx).1 (Finset.mem_filter.1 hx').1 h)]
    exact congrArg (fun p => Polynomial.coeff p i) key
  have hd : DifferentiableAt ℂ (fun y => (∏ x ∈ T.filter (· ∈ O),
      (Polynomial.X - Polynomial.C (∑ j, c j * g x y j))).coeff i) y₀ :=
    coeff_finset_prod_differentiableAt _ _ _ (fun x hx k => coeff_X_sub_C_differentiableAt _ _
      (DifferentiableAt.fun_sum fun j _ =>
        (differentiableAt_pi.1 (hgd x (Finset.mem_filter.1 hx).1) j).const_mul (c j)) k) i
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.PPieceRootProductPolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Matrix

theorem PieceRootProductPolynomial.coeff_bound {ι : Type*} (s : Finset ι) (r : ι → ℂ) (B : ℝ)
    (hB : ∀ x ∈ s, ‖r x‖ ≤ B) (i : ℕ) :
    ‖(∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).coeff i‖ ≤ B ^ (s.card - i) * (s.card.choose i) := by
  have hm : (∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C _)
  have hdeg : (∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).natDegree = s.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C _),
      Finset.sum_congr rfl (fun x _ => Polynomial.natDegree_X_sub_C _), Finset.sum_const, smul_eq_mul, mul_one]
  have hs : Polynomial.Splits ((∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).map (RingHom.id ℂ)) := by
    rw [Polynomial.map_id]
    exact Polynomial.Splits.prod (fun x _ => Polynomial.Splits.X_sub_C _)
  have h := Polynomial.coeff_le_of_roots_le (f := RingHom.id ℂ) (B := B) i hm hs (by
    intro z hz
    rw [Polynomial.map_id] at hz
    have hz' := (Polynomial.mem_roots hm.ne_zero).1 hz
    rw [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hz'
    obtain ⟨x, hx, hx0⟩ := hz'
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hx0
    rw [hx0]
    exact hB x hx)
  rwa [Polynomial.map_id, hdeg] at h

theorem PieceRootProductPolynomial.coeff_monic_of_coeffs {R : Type*} [CommRing R] (k : ℕ) (p : ℕ → R)
    (i : ℕ) :
    (Polynomial.X ^ k + ∑ j : Fin k, Polynomial.C (p j) * Polynomial.X ^ (j : ℕ)).coeff i =
      if i < k then p i else if i = k then 1 else 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  by_cases hi : i < k
  · rw [Finset.sum_eq_single ⟨i, hi⟩, if_neg hi.ne, if_pos rfl, if_pos hi, zero_add]
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Fin.ext h.symm)
    · simp
  · rw [Finset.sum_eq_zero, if_neg hi, add_zero]
    intro j _
    rw [if_neg]
    intro h
    exact hi (h ▸ j.isLt)

theorem PieceRootProductPolynomial.proof (h1 : PieceCoefficientsHolomorphic.Statement)
    (h2 : MonicRootGrowth.Statement) (h3 : GrowthOffHypersurfacePolynomial.Statement) :
    PieceRootProductPolynomial.Statement := by
  intro n d N k A Z c m Q O F hm hQ hroot hcov hO hF hOF hk
  have hhol := h1 n d N A Z c Q O F hcov hO hF hOF
  obtain ⟨C, M, hC⟩ := h2 d m hm
  have hfin : ∀ y : Fin d → ℂ, eval y Q ≠ 0 → {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}.Finite :=
    fun y hy => (hcov y hy).1.subset (fun x hx => ⟨hx.1, hx.2.2⟩)

  have hprod : ∀ (y : Fin d → ℂ) (hy : eval y Q ≠ 0),
      (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y}, (Polynomial.X - Polynomial.C (∑ j, c j * x j))) =
        ∏ x ∈ (hfin y hy).toFinset, (Polynomial.X - Polynomial.C (∑ j, c j * x j)) :=
    fun y hy => finprod_mem_eq_finite_toFinset_prod _ (hfin y hy)
  have hcard : ∀ (y : Fin d → ℂ) (hy : eval y Q ≠ 0), (hfin y hy).toFinset.card = k :=
    fun y hy => by rw [← Set.ncard_eq_toFinset_card _ (hfin y hy), hk y hy]

  have hgrowth : ∀ (i : ℕ) (y : Fin d → ℂ), eval y Q ≠ 0 →
      ‖(∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
          (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i‖ ≤
        ((k.choose i : ℝ) * |C| ^ (k - i)) * (1 + ‖y‖) ^ (M * (k - i)) := by
    intro i y hy
    rw [hprod y hy]
    have hb := PieceRootProductPolynomial.coeff_bound (hfin y hy).toFinset (fun x => ∑ j, c j * x j)
      (|C| * (1 + ‖y‖) ^ M) (fun x hx => by
        obtain ⟨hxZ, -, hxy⟩ := (Set.Finite.mem_toFinset _).1 hx
        have h := hC y _ (hxy ▸ hroot x hxZ)
        exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))) i
    rw [hcard y hy] at hb
    calc _ ≤ _ := hb
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hp : ∀ i : ℕ, ∃ p : MvPolynomial (Fin d) ℂ, ∀ y : Fin d → ℂ, eval y Q ≠ 0 →
      (∏ᶠ x ∈ {x | x ∈ Z ∧ x ∈ O ∧ A *ᵥ x = y},
          (Polynomial.X - Polynomial.C (∑ j, c j * x j))).coeff i = eval y p :=
    fun i => h3 d Q _ _ _ hQ (hhol i) (hgrowth i)
  choose p hp using hp
  refine ⟨Polynomial.X ^ k + ∑ j : Fin k, Polynomial.C (p j) * Polynomial.X ^ (j : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_, fun y hy => ?_⟩
  · rw [Polynomial.natDegree_add_eq_left_of_degree_lt, Polynomial.natDegree_X_pow]
    rw [Polynomial.degree_X_pow]
    exact Polynomial.degree_sum_fin_lt _
  · have hmon : (∏ x ∈ (hfin y hy).toFinset, (Polynomial.X - Polynomial.C (∑ j, c j * x j))).Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C _)
    have hdeg : (∏ x ∈ (hfin y hy).toFinset,
        (Polynomial.X - Polynomial.C (∑ j, c j * x j))).natDegree = k := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C _),
        Finset.sum_congr rfl (fun x _ => Polynomial.natDegree_X_sub_C _), Finset.sum_const, smul_eq_mul,
        mul_one, hcard y hy]
    ext i
    rw [Polynomial.coeff_map, PieceRootProductPolynomial.coeff_monic_of_coeffs]
    by_cases hi : i < k
    · rw [if_pos hi, hp i y hy]
    · rw [if_neg hi, hprod y hy]
      by_cases hik : i = k
      · rw [if_pos hik, map_one, hik, ← hdeg]
        exact hmon.coeff_natDegree.symm
      · rw [if_neg hik, map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

