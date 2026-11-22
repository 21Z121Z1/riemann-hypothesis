import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsWeightMulClassLeMulSum
section
open scoped Classical

namespace GlobalTheory

theorem sum_pairs_weight_mul_class_le_mul_sum (α β : Type) (S : Finset (α × α)) (cls : α → β)
    (w : α → ℝ) (om : β → ℝ) (T₁ T₂ : Finset β) (hw : ∀ a, 0 ≤ w a) (hom : ∀ b, 0 ≤ om b)
    (hT : ∀ p ∈ S, cls p.1 ∈ T₁ ∧ cls p.2 ∈ T₂)
    (hinj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → cls p.2 = cls q.2 → p = q)
    (hsum : ∀ b, ∑ a ∈ (S.image Prod.fst).filter (fun a => cls a = b), w a ≤ 1) :
    ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2)) ≤ (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by

  have key : ∀ b ∈ T₁ ×ˢ T₂,
      ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b), w p.1 * (om (cls p.1) * om (cls p.2))
        ≤ om b.1 * om b.2 := by
    intro b _
    set F := S.filter (fun p => (cls p.1, cls p.2) = b) with hF
    have h1 : ∑ p ∈ F, w p.1 * (om (cls p.1) * om (cls p.2))
        = (∑ p ∈ F, w p.1) * (om b.1 * om b.2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      have e := (Finset.mem_filter.1 hp).2
      rw [← e]
    have h2 : ∑ p ∈ F, w p.1 = ∑ a ∈ F.image Prod.fst, w a := by
      rw [Finset.sum_image]
      intro p hp q hq hpq
      have ep := (Finset.mem_filter.1 hp).2
      have eq := (Finset.mem_filter.1 hq).2
      have hc : cls p.2 = cls q.2 := by
        have := congrArg Prod.snd (ep.trans eq.symm)
        simpa using this
      exact hinj p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 hpq hc
    have h3 : F.image Prod.fst ⊆ (S.image Prod.fst).filter (fun a => cls a = b.1) := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      have hp' := Finset.mem_filter.1 hp
      refine Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hp'.1, ?_⟩
      have := congrArg Prod.fst hp'.2
      simpa using this
    have h4 : ∑ p ∈ F, w p.1 ≤ 1 := by
      rw [h2]
      exact (Finset.sum_le_sum_of_subset_of_nonneg h3 (fun a _ _ => hw a)).trans (hsum b.1)
    rw [h1]
    have hnn : 0 ≤ om b.1 * om b.2 := mul_nonneg (hom _) (hom _)
    calc (∑ p ∈ F, w p.1) * (om b.1 * om b.2) ≤ 1 * (om b.1 * om b.2) :=
          mul_le_mul_of_nonneg_right h4 hnn
      _ = om b.1 * om b.2 := one_mul _
  calc ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2))
      = ∑ b ∈ T₁ ×ˢ T₂, ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b),
          w p.1 * (om (cls p.1) * om (cls p.2)) := by
        symm
        exact Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_product.2 (hT p hp)) _
    _ ≤ ∑ b ∈ T₁ ×ˢ T₂, om b.1 * om b.2 := Finset.sum_le_sum key
    _ = (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdFixedPlaceAverage
section
open Finset

namespace GlobalTheory

theorem sum_prod_fixed_place_average {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
    [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] {V : Type}
    [AddCommGroup V] [Module ℂ V] (a : ∀ i, G i → ℂ) (f : (∀ i, G i) → V)
    (hf : ∀ i (γ : ∀ i, G i), γ i = 1 → ∑ β : G i, a i β • f (Function.update γ i β) = f γ) :
    ∑ γ : (∀ i, G i), (∏ i, a i (γ i)) • f γ = f 1 := by
  classical
  let c : Finset ι → (∀ i, G i) → ℂ := fun S γ =>
    ∏ i, (if i ∈ S then a i (γ i) else if γ i = 1 then 1 else 0)
  have key : ∀ S : Finset ι, ∑ γ, c S γ • f γ = f 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.sum_eq_single (1 : ∀ i, G i)]
      · simp [c]
      · intro γ _ hγ
        obtain ⟨i, hi⟩ : ∃ i, γ i ≠ 1 := by
          by_contra hcon
          push_neg at hcon
          exact hγ (funext hcon)
        have : c ∅ γ = 0 := Finset.prod_eq_zero (mem_univ i) (by simp [hi])
        rw [this, zero_smul]
      · intro h; exact absurd (mem_univ _) h
    | insert j S hj ih =>
      rw [← ih]
      let h : ∀ i, G i → ℂ := fun i x => if i ∈ S then a i x else if x = 1 then 1 else 0
      have cU : ∀ (γ : ∀ i, G i) (β : G j),
          c S (Function.update γ j β) = h j β * ∏ i ∈ univ.erase j, h i (γ i) := by
        intro γ β
        show ∏ i, h i (Function.update γ j β i) = _
        rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro i hi
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have cI : ∀ γ : ∀ i, G i, c (insert j S) γ = a j (γ j) * ∏ i ∈ univ.erase j, h i (γ i) := by
        intro γ
        show ∏ i, _ = _
        rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro i hi
          have : i ≠ j := Finset.ne_of_mem_erase hi
          simp [h, this]
      have step1 : ∑ γ, c S γ • f γ
          = ∑ γ, ∑ β : G j, (c S γ * a j β) • f (Function.update γ j β) := by
        apply Finset.sum_congr rfl
        intro γ _
        by_cases hγ : γ j = 1
        · rw [← hf j γ hγ, Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro β _
          rw [mul_smul]
        · have : c S γ = 0 := Finset.prod_eq_zero (mem_univ j) (by simp [hj, hγ])
          simp [this]
      let e : (∀ i, G i) × G j ≃ (∀ i, G i) × G j :=
        { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
          invFun := fun p => (Function.update p.1 j p.2, p.1 j)
          left_inv := by intro p; simp
          right_inv := by intro p; simp }
      rw [step1, ← Fintype.sum_prod_type']
      rw [← Fintype.sum_equiv e
        (fun p => (c S (Function.update p.1 j p.2) * a j (p.1 j)) • f p.1) _ (by
          intro p
          simp [e])]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro γ _
      dsimp only
      rw [← Finset.sum_smul, ← Finset.sum_mul]
      simp_rw [cU]
      rw [← Finset.sum_mul, cI]
      have : ∑ β : G j, h j β = 1 := by simp [h, hj]
      rw [this, one_mul, mul_comm]
  have := key univ
  simpa [c] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdOfLocalChoicesBijection
section
open scoped Classical

namespace GlobalTheory

theorem prod_sum_of_local_choices {ι Q R : Type} {O : ι → Type} [CommSemiring R] [TopologicalSpace R] [∀ p, Nonempty (O p)]
    (s : Finset ι) (Φ : Q → ∀ p, O p) (Tq : Set Q) (U : ∀ p, Set (O p))
    (hU : ∀ p ∈ s, (U p).Finite)
    (hinj : ∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c')
    (hmem : ∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p)
    (hsurj : ∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p)
    (g : ∀ p, O p → R) :
    Tq.Finite ∧ (∑' c : Q, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0)
      = ∏ p ∈ s, ∑' o : O p, if o ∈ U p then g p o else 0 := by
  have hT : Tq.Finite := by
    let e : Q → ∀ p : s, O p := fun c p => Φ c p
    have hfin : (Set.pi Set.univ (fun p : s => U p)).Finite :=
      Set.Finite.pi (fun p => hU p p.2)
    refine Set.Finite.of_finite_image (f := e) (hfin.subset ?_) ?_
    · rintro _ ⟨c, hc, rfl⟩ p _
      exact hmem c hc p p.2
    · intro c hc c' hc' h
      exact hinj c hc c' hc' (fun p hp => congrFun h ⟨p, hp⟩)
  refine ⟨hT, ?_⟩
  let t : ∀ p, Finset (O p) := fun p => if h : p ∈ s then (hU p h).toFinset else ∅
  have ht : ∀ p ∈ s, ∀ o, o ∈ t p ↔ o ∈ U p := by
    intro p hp o; simp [t, hp]
  rw [tsum_eq_sum (s := hT.toFinset) (fun c hc => by
    rw [Set.Finite.mem_toFinset] at hc; simp [hc])]
  have hR : ∀ p ∈ s, (∑' o : O p, if o ∈ U p then g p o else 0) = ∑ o ∈ t p, g p o := by
    intro p hp
    rw [tsum_eq_sum (s := t p) (fun o ho => by rw [ht p hp] at ho; simp [ho])]
    refine Finset.sum_congr rfl (fun o ho => ?_)
    rw [ht p hp] at ho; simp [ho]
  rw [Finset.prod_congr rfl hR, Finset.prod_sum]
  have hL : (∑ c ∈ hT.toFinset, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0)
      = ∑ c ∈ hT.toFinset, ∏ p ∈ s, g p (Φ c p) :=
    Finset.sum_congr rfl (fun c hc => by rw [Set.Finite.mem_toFinset] at hc; simp [hc])
  rw [hL]
  refine Finset.sum_bij (fun c _ => fun p _ => Φ c p) ?_ ?_ ?_ ?_
  · intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    rw [Finset.mem_pi]
    intro p hp
    exact (ht p hp _).2 (hmem c hc p hp)
  · intro c hc c' hc' h
    rw [Set.Finite.mem_toFinset] at hc hc'
    exact hinj c hc c' hc' (fun p hp => congrFun (congrFun h p) hp)
  · intro x hx
    rw [Finset.mem_pi] at hx
    let y : ∀ p, O p := fun p => if h : p ∈ s then x p h else Classical.arbitrary (O p)
    obtain ⟨c, hc, hcy⟩ := hsurj y (fun p hp => by
      simp only [y, dif_pos hp]; exact (ht p hp _).1 (hx p hp))
    refine ⟨c, (Set.Finite.mem_toFinset hT).2 hc, ?_⟩
    funext p hp
    rw [hcy p hp]; simp [y, hp]
  · intro c _
    exact (Finset.prod_attach s (fun p => g p (Φ c p))).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SummableAndTsumLeOfBoxCount
section
open Finset

namespace GlobalTheory

theorem summable_and_tsum_le_of_box_count (ι Γ : Type) [Fintype ι] (D : Γ → ι → ℝ) (t : Γ → ℝ)
    (a A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (ha : Real.exp (-a) ≤ 1 / 2) (_hD : ∀ γ v, 0 ≤ D γ v)
    (ht : ∀ γ, 0 ≤ t γ ∧ t γ ≤ c * ∏ v, Real.exp (-(2 * a * (⌊D γ v⌋₊ : ℝ))))
    (hN : ∀ r : ι → ℝ, (∀ v, 0 ≤ r v) → {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.Finite ∧
      (({γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.ncard : ℕ) : ℝ) ≤ A * Real.exp (a * ∑ v, r v)) :
    Summable t ∧ ∑' γ, t γ ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by
  classical
  set q := Real.exp (-a) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by linarith
  have hgeom : ∀ M : ℕ, ∑ k ∈ Finset.range M, q ^ k ≤ 2 := by
    intro M
    calc ∑ k ∈ Finset.range M, q ^ k ≤ ∑' k, q ^ k :=
          (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun k _ => pow_nonneg hq0 k)
      _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1
      _ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
  have hprod : ∀ F : Finset (ι → ℕ), ∑ n ∈ F, ∏ v, q ^ (n v) ≤ 2 ^ Fintype.card ι := by
    intro F
    set M := F.sup (fun n => ∑ v, n v) + 1 with hM
    have hsub : F ⊆ Fintype.piFinset (fun _ : ι => Finset.range M) := by
      intro n hn
      rw [Fintype.mem_piFinset]
      intro v
      rw [Finset.mem_range]
      have h1 : n v ≤ ∑ w, n w :=
        Finset.single_le_sum (fun w _ => Nat.zero_le (n w)) (Finset.mem_univ v)
      have h2 : ∑ w, n w ≤ F.sup (fun n => ∑ v, n v) := Finset.le_sup (f := fun n => ∑ v, n v) hn
      omega
    calc ∑ n ∈ F, ∏ v, q ^ (n v)
        ≤ ∑ n ∈ Fintype.piFinset (fun _ : ι => Finset.range M), ∏ v, q ^ (n v) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => Finset.prod_nonneg (fun v _ => pow_nonneg hq0 _))
      _ = ∏ _v : ι, ∑ k ∈ Finset.range M, q ^ k :=
          (Finset.prod_univ_sum (fun _ => Finset.range M) (fun _ k => q ^ k)).symm
      _ ≤ ∏ _v : ι, (2 : ℝ) :=
          Finset.prod_le_prod (fun v _ => Finset.sum_nonneg (fun k _ => pow_nonneg hq0 k))
            (fun v _ => hgeom M)
      _ = 2 ^ Fintype.card ι := by simp
  have hB : 0 ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by positivity
  have hfin : ∀ s : Finset Γ, ∑ γ ∈ s, t γ ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by
    intro s
    set φ : Γ → ι → ℕ := fun γ v => ⌊D γ v⌋₊ with hφ
    set s' := s.filter (fun γ => t γ ≠ 0) with hs'
    rw [← Finset.sum_filter_ne_zero]
    rw [← Finset.sum_fiberwise_of_maps_to (t := s'.image φ) (g := φ)
      (fun γ hγ => Finset.mem_image_of_mem φ hγ)]
    have hfib : ∀ n : ι → ℕ, ∑ γ ∈ s'.filter (fun γ => φ γ = n), t γ ≤
        c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) := by
      intro n
      set Fn := s'.filter (fun γ => φ γ = n) with hFn
      set e : ℝ := c * ∏ v, Real.exp (-(2 * a * (n v : ℝ))) with he_def
      have he : 0 ≤ e := by positivity
      have h1 : ∑ γ ∈ Fn, t γ ≤ Fn.card * e := by
        calc ∑ γ ∈ Fn, t γ ≤ ∑ _γ ∈ Fn, e := by
              apply Finset.sum_le_sum
              intro γ hγ
              have hn : φ γ = n := (Finset.mem_filter.1 hγ).2
              have hfl : ∀ v, ⌊D γ v⌋₊ = n v := fun v => congrFun hn v
              have h := (ht γ).2
              simp only [hfl] at h
              exact h
          _ = Fn.card * e := by rw [Finset.sum_const, nsmul_eq_mul]
      set r : ι → ℝ := fun v => (n v : ℝ) + 1 with hr_def
      have hr : ∀ v, 0 ≤ r v := fun v => by positivity
      obtain ⟨hSf, hSc⟩ := hN r hr
      have hsub : (↑Fn : Set Γ) ⊆ {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v} := by
        intro γ hγ
        have hm := Finset.mem_filter.1 (Finset.mem_coe.1 hγ)
        have hm' := Finset.mem_filter.1 hm.1
        refine ⟨hm'.2, fun v => ?_⟩
        have hfl : ⌊D γ v⌋₊ = n v := congrFun hm.2 v
        have hl := Nat.lt_floor_add_one (D γ v)
        rw [hfl] at hl
        exact hl.le
      have hcard : (Fn.card : ℝ) ≤ A * Real.exp (a * ∑ v, r v) := by
        have hc' := Set.ncard_le_ncard hsub hSf
        rw [Set.ncard_coe_finset] at hc'
        exact le_trans (by exact_mod_cast hc') hSc
      have hS2 : ∑ v, 2 * a * (n v : ℝ) = 2 * a * ∑ v, (n v : ℝ) := by rw [Finset.mul_sum]
      have hS3 : ∑ v, (n v : ℝ) * -a = (∑ v, (n v : ℝ)) * -a := by rw [Finset.sum_mul]
      have hS1 : ∑ v, r v = ∑ v, (n v : ℝ) + Fintype.card ι := by
        simp only [hr_def, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]
      calc ∑ γ ∈ Fn, t γ ≤ Fn.card * e := h1
        _ ≤ A * Real.exp (a * ∑ v, r v) * e := mul_le_mul_of_nonneg_right hcard he
        _ = c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) := by
            rw [he_def, hq]
            simp_rw [← Real.exp_nat_mul]
            rw [← Real.exp_sum, ← Real.exp_sum, Finset.sum_neg_distrib, hS2, hS3, hS1]
            rw [show A * Real.exp (a * (∑ v, (n v : ℝ) + Fintype.card ι)) *
                  (c * Real.exp (-(2 * a * ∑ v, (n v : ℝ)))) =
                c * A * (Real.exp (a * (∑ v, (n v : ℝ) + Fintype.card ι)) *
                  Real.exp (-(2 * a * ∑ v, (n v : ℝ)))) by ring,
              show c * A * Real.exp (a * Fintype.card ι) * Real.exp ((∑ v, (n v : ℝ)) * -a) =
                c * A * (Real.exp (a * Fintype.card ι) * Real.exp ((∑ v, (n v : ℝ)) * -a)) by ring,
              ← Real.exp_add, ← Real.exp_add]
            congr 2
            ring
    calc ∑ n ∈ s'.image φ, ∑ γ ∈ s'.filter (fun γ => φ γ = n), t γ
        ≤ ∑ n ∈ s'.image φ, c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) :=
          Finset.sum_le_sum (fun n _ => hfib n)
      _ = c * A * Real.exp (a * Fintype.card ι) * ∑ n ∈ s'.image φ, ∏ v, q ^ (n v) := by
          rw [Finset.mul_sum]
      _ ≤ c * A * Real.exp (a * Fintype.card ι) * 2 ^ Fintype.card ι :=
          mul_le_mul_of_nonneg_left (hprod _) (by positivity)
      _ = c * A * (2 * Real.exp a) ^ Fintype.card ι := by
          rw [mul_pow, ← Real.exp_nat_mul, mul_comm (Fintype.card ι : ℝ) a]
          ring
  exact ⟨summable_of_sum_le (fun γ => (ht γ).1) hfin, tsum_le_of_sum_le' hB hfin⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumInvStabilizerEqTsumMulFiber
section
open scoped ENNReal

namespace GlobalTheory

open MulAction

theorem encard_fiber_orbit_mul_stabilizer {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y]
    (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x) (x : L) (y : Y) (g : Γ)
    (hg : g • π x = y) :
    ({z : L | π z = y ∧ z ∈ orbit Γ x}).encard * (stabilizer Γ x : Set Γ).encard
      = (stabilizer Γ y : Set Γ).encard := by
  classical
  have hx0 : π (g • x) = y := by rw [hπ, hg]
  have hset : (orbit (stabilizer Γ y) (g • x) : Set L) = {z : L | π z = y ∧ z ∈ orbit Γ x} := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      have hh : (h : Γ) • y = y := mem_stabilizer_iff.mp h.2
      refine ⟨?_, (h : Γ) * g, ?_⟩
      · show π ((h : Γ) • g • x) = y
        rw [hπ, hx0, hh]
      · show ((h : Γ) * g) • x = (h : Γ) • g • x
        rw [mul_smul]
    · rintro ⟨hz, k, rfl⟩
      have hk : k * g⁻¹ ∈ stabilizer Γ y := by
        rw [mem_stabilizer_iff]
        calc (k * g⁻¹) • y = (k * g⁻¹) • g • π x := by rw [hg]
          _ = π (k • x) := by rw [mul_smul, inv_smul_smul, hπ]
          _ = y := hz
      exact ⟨⟨k * g⁻¹, hk⟩, show (k * g⁻¹) • g • x = k • x by rw [mul_smul, inv_smul_smul]⟩
  have e : stabilizer (stabilizer Γ y) (g • x) ≃ stabilizer Γ x :=
    { toFun := fun s => ⟨g⁻¹ * ((s : stabilizer Γ y) : Γ) * g, by
        have hs : ((s : stabilizer Γ y) : Γ) • g • x = g • x := mem_stabilizer_iff.mp s.2
        rw [mem_stabilizer_iff, mul_smul, mul_smul, hs, inv_smul_smul]⟩
      invFun := fun t => ⟨⟨g * (t : Γ) * g⁻¹, by
          have ht : (t : Γ) • x = x := mem_stabilizer_iff.mp t.2
          rw [mem_stabilizer_iff, ← hg, mul_smul, mul_smul, inv_smul_smul, ← hπ, ht]⟩, by
          have ht : (t : Γ) • x = x := mem_stabilizer_iff.mp t.2
          show (g * (t : Γ) * g⁻¹) • g • x = g • x
          rw [mul_smul, mul_smul, inv_smul_smul, ht]⟩
      left_inv := fun s => by
        apply Subtype.ext; apply Subtype.ext
        show g * (g⁻¹ * ((s : stabilizer Γ y) : Γ) * g) * g⁻¹ = ((s : stabilizer Γ y) : Γ)
        group
      right_inv := fun t => by
        apply Subtype.ext
        show g⁻¹ * (g * (t : Γ) * g⁻¹) * g = (t : Γ)
        group }
  have key := ENat.card_congr
    (Subgroup.groupEquivQuotientProdSubgroup (s := stabilizer (stabilizer Γ y) (g • x)))
  rw [ENat.card_prod, ← ENat.card_congr (orbitEquivQuotientStabilizer (stabilizer Γ y) (g • x)),
    ENat.card_congr e] at key
  rw [← hset]
  exact key.symm

theorem encard_eq_tsum_fibers {L Q : Type} (F : Set L) (q : L → Q) :
    (F.encard : ℝ≥0∞) = ∑' o : Q, (({z | z ∈ F ∧ q z = o}).encard : ℝ≥0∞) := by
  classical
  have h1 : ∑' _ : F, (1 : ℝ≥0∞) = ∑' _ : (Σ o : Q, {z : F // q z = o}), (1 : ℝ≥0∞) :=
    ((Equiv.sigmaFiberEquiv (fun z : F => q z)).tsum_eq (fun _ => (1 : ℝ≥0∞))).symm
  rw [← ENNReal.tsum_set_one F, h1, ENNReal.tsum_sigma']
  refine tsum_congr fun o => ?_
  simp only [ENNReal.tsum_one]
  congr 1
  exact ENat.card_congr
    { toFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private lemma inv_coe_mul_mul_coe_eq_inv_coe (a b : ℕ∞) (h0 : a * b ≠ 0) (ht : a * b ≠ ⊤) :
    (((a * b : ℕ∞) : ℝ≥0∞))⁻¹ * (a : ℝ≥0∞) = (b : ℝ≥0∞)⁻¹ := by
  have ha0 : a ≠ 0 := left_ne_zero_of_mul h0
  have hb0 : b ≠ 0 := right_ne_zero_of_mul h0
  induction a using ENat.recTopCoe with
  | top => exact absurd (ENat.top_mul hb0) ht
  | coe m =>
    induction b using ENat.recTopCoe with
    | top => exact absurd (by rw [mul_comm]; exact ENat.top_mul ha0) ht
    | coe k =>
      have hm : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha0
      have hk : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb0
      rw [ENat.toENNReal_mul, ENat.toENNReal_coe, ENat.toENNReal_coe,
        ENNReal.mul_inv (Or.inl hm) (Or.inr hk), mul_comm (m : ℝ≥0∞)⁻¹, mul_assoc,
        ENNReal.inv_mul_cancel hm (ENNReal.natCast_ne_top m), mul_one]

private lemma quotient_mk_map_eq_of_mem_orbit {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y]
    (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x) {a b : L} (h : a ∈ orbit Γ b) :
    Quotient.mk (orbitRel Γ Y) (π a) = Quotient.mk (orbitRel Γ Y) (π b) := by
  obtain ⟨g, rfl⟩ := h
  apply Quotient.sound
  show π (g • b) ∈ orbit Γ (π b)
  rw [hπ]
  exact mem_orbit _ g

theorem tsum_inv_stabilizer_eq_tsum_mul_fiber {Γ L Y : Type} [Group Γ] [MulAction Γ L]
    [MulAction Γ Y] (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x)
    (hfin : ∀ y : Y, (∃ x, π x = y) → Finite (MulAction.stabilizer Γ y)) :
    (∑' o : MulAction.orbitRel.Quotient Γ L,
        (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹)
      = ∑' o : MulAction.orbitRel.Quotient Γ Y,
        (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹
          * (((π ⁻¹' {o.out}).encard : ℝ≥0∞)) := by
  classical
  set φ : orbitRel.Quotient Γ L → orbitRel.Quotient Γ Y :=
    fun o => Quotient.mk (orbitRel Γ Y) (π o.out) with hφ
  have hsplit := ((Equiv.sigmaFiberEquiv φ).tsum_eq
      (fun o : orbitRel.Quotient Γ L => (((stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹)).symm.trans
    (ENNReal.tsum_sigma' _)
  refine hsplit.trans (tsum_congr fun O => ?_)
  change ∑' o : {o // φ o = O}, (((stabilizer Γ o.1.out : Set Γ).encard : ℝ≥0∞))⁻¹ = _
  have hsupp : Function.support (fun o : orbitRel.Quotient Γ L =>
      ((({z | z ∈ π ⁻¹' {O.out} ∧ Quotient.mk (orbitRel Γ L) z = o}).encard : ℕ∞) : ℝ≥0∞))
      ⊆ {o | φ o = O} := by
    intro o ho
    obtain ⟨z, hz, hzo⟩ : ({z | z ∈ π ⁻¹' {O.out} ∧ Quotient.mk (orbitRel Γ L) z = o}).Nonempty := by
      rw [← Set.encard_pos, pos_iff_ne_zero]
      intro h0
      exact ho (by simp only [h0, ENat.toENNReal_zero])
    have hzo' : o.out ∈ orbit Γ z := by
      apply orbitRel_apply.mp
      apply Quotient.exact
      rw [Quotient.out_eq]
      exact hzo.symm
    show Quotient.mk (orbitRel Γ Y) (π o.out) = O
    rw [quotient_mk_map_eq_of_mem_orbit π hπ hzo', show π z = O.out from hz]
    exact Quotient.out_eq O
  rw [encard_eq_tsum_fibers (π ⁻¹' {O.out}) (Quotient.mk (orbitRel Γ L)),
    ← tsum_subtype_eq_of_support_subset hsupp, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun o => ?_
  have hx : Quotient.mk (orbitRel Γ Y) (π o.1.out) = Quotient.mk (orbitRel Γ Y) O.out := by
    rw [Quotient.out_eq O]
    exact o.2
  obtain ⟨h, hh⟩ : π o.1.out ∈ orbit Γ O.out := orbitRel_apply.mp (Quotient.exact hx)
  have hg : h⁻¹ • π o.1.out = O.out := by rw [← hh, inv_smul_smul]
  have hF : {z | z ∈ π ⁻¹' {O.out} ∧ Quotient.mk (orbitRel Γ L) z = o.1}
      = {z : L | π z = O.out ∧ z ∈ orbit Γ o.1.out} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    refine and_congr Iff.rfl ⟨fun hz => ?_, fun hz => ?_⟩
    · apply orbitRel_apply.mp
      apply Quotient.exact
      rw [Quotient.out_eq]
      exact hz
    · rw [← Quotient.out_eq o.1]
      exact Quotient.sound (orbitRel_apply.mpr hz)
  have hmul := encard_fiber_orbit_mul_stabilizer π hπ o.1.out O.out h⁻¹ hg
  have hfinY : Finite (stabilizer Γ O.out) := hfin O.out ⟨h⁻¹ • o.1.out, by rw [hπ, hg]⟩
  have hY0 : (stabilizer Γ O.out : Set Γ).encard ≠ 0 := by
    rw [Ne, Set.encard_eq_zero]
    exact Set.nonempty_iff_ne_empty.mp ⟨1, (stabilizer Γ O.out).one_mem⟩
  have hYt : (stabilizer Γ O.out : Set Γ).encard ≠ ⊤ := by
    rw [Ne, Set.encard_eq_top_iff, Set.not_infinite]
    exact Set.toFinite _
  rw [hF, ← hmul]
  rw [← hmul] at hY0 hYt
  exact (inv_coe_mul_mul_coe_eq_inv_coe _ _ hY0 hYt).symm

end GlobalTheory
end

