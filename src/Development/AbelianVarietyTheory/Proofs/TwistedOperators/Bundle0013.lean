import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdEqSumOfFactorwiseLinearExpansion
section
namespace GlobalTheory

open Finset in

theorem prod_eq_sum_of_factorwise_expansion : ∀ (K : Type) [Fintype K] (X : K → Type) (I : Type) (S : Finset I) (x : I → ℂ) (a : ∀ n, I → X n → ℂ) (b : K → I → ℂ) (A : ∀ n, X n → ℂ) (B : K → ℂ), (∀ n (y : I → ℂ), (∀ q, ∑ i ∈ S, y i * a n i q = 0) → ∑ i ∈ S, y i * b n i = 0) → (∀ n (y : I → ℂ), (∀ q, A n q = ∑ i ∈ S, y i * a n i q) → B n = ∑ i ∈ S, y i * b n i) → (∀ q : ∀ n, X n, ∏ n, A n (q n) = ∑ i ∈ S, x i * ∏ n, a n i (q n)) → (∀ n, Nonempty (X n)) → ∏ n, B n = ∑ i ∈ S, x i * ∏ n, b n i := by
  intro K _ X I S x a b A B h1 h2 h3 hne
  classical
  have key : ∀ T : Finset K, ∀ q : ∀ n, X n,
      ∑ i ∈ S, x i * ∏ n, (if n ∈ T then b n i else a n i (q n)) =
        ∏ n, (if n ∈ T then B n else A n (q n)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro q; simpa using (h3 q).symm
    | insert m T hm ih =>
      intro q
      obtain ⟨c, hc⟩ : ∃ c, c = ∏ n ∈ univ.erase m, (if n ∈ T then B n else A n (q n)) := ⟨_, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y : I → ℂ, y = fun i => x i * ∏ n ∈ univ.erase m,
          (if n ∈ T then b n i else a n i (q n)) := ⟨_, rfl⟩
      have hL : ∀ t, ∑ i ∈ S, y i * a m i t = A m t * c := by
        intro t
        have h := ih (Function.update q m t)
        have e1 : ∀ i, ∏ n, (if n ∈ T then b n i else a n i (Function.update q m t n)) =
            a m i t * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n)) := by
          intro i
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
          congr 1
          · simp [hm]
          · apply Finset.prod_congr rfl
            intro n hn
            have hnm : n ≠ m := Finset.ne_of_mem_erase hn
            rw [Function.update_of_ne hnm]
        have e2 : ∏ n, (if n ∈ T then B n else A n (Function.update q m t n)) = A m t * c := by
          rw [hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
          congr 1
          · simp [hm]
          · apply Finset.prod_congr rfl
            intro n hn
            have hnm : n ≠ m := Finset.ne_of_mem_erase hn
            rw [Function.update_of_ne hnm]
        rw [e2] at h
        simp only [e1] at h
        rw [← h, hy]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have e3 : ∀ i, ∏ n, (if n ∈ insert m T then b n i else a n i (q n)) =
          b m i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n)) := by
        intro i
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro n hn
          have hnm : n ≠ m := Finset.ne_of_mem_erase hn
          simp [Finset.mem_insert, hnm]
      have e4 : ∏ n, (if n ∈ insert m T then B n else A n (q n)) = B m * c := by
        rw [hc, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro n hn
          have hnm : n ≠ m := Finset.ne_of_mem_erase hn
          simp [Finset.mem_insert, hnm]
      rw [e4]
      simp only [e3]
      have hs : ∑ i ∈ S, x i * (b m i * ∏ n ∈ univ.erase m, (if n ∈ T then b n i else a n i (q n))) =
          ∑ i ∈ S, y i * b m i := by
        rw [hy]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hs]
      by_cases hc0 : c = 0
      · rw [hc0, mul_zero]
        apply h1 m y
        intro t
        rw [hL t, hc0, mul_zero]
      · have hB := h2 m (fun i => y i / c) (by
          intro t
          have : ∑ i ∈ S, y i / c * a m i t = (∑ i ∈ S, y i * a m i t) / c := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [this, hL t, mul_div_cancel_right₀ _ hc0])
        rw [hB, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
  obtain ⟨q⟩ : Nonempty (∀ n, X n) := ⟨fun n => Classical.choice (hne n)⟩
  simpa using (key Finset.univ q).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexEqOfMap
section
namespace GlobalTheory.RelIndexOfMap

theorem relIndex_eq_of_map {X P : Type} [Group X] [Group P] (φ : X →* P) (A B : Subgroup X)
    (U V : Subgroup P) (hA : A.map φ = U) (hB : ∀ a ∈ A, a ∈ B ↔ φ a ∈ V) :
    B.relIndex A = V.relIndex U := by
  rw [← hA, ← Subgroup.relIndex_comap]
  unfold Subgroup.relIndex
  congr 1
  ext a
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  exact hB a a.2

theorem index_pi_dep {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, Group (H i)]
    (V : ∀ i, Subgroup (H i)) :
    (Subgroup.pi Set.univ V).index = ∏ i, (V i).index := by
  simp only [Subgroup.index_eq_card]
  rw [← Nat.card_pi]
  let f : ((∀ i, H i) ⧸ Subgroup.pi Set.univ V) → ∀ i, H i ⧸ V i :=
    Quotient.lift (fun g i => (QuotientGroup.mk (g i) : H i ⧸ V i)) (by
      intro a b hab
      have hab' := QuotientGroup.leftRel_apply.1 hab
      funext i
      exact QuotientGroup.eq.2 (hab' i trivial))
  refine Nat.card_eq_of_bijective f ⟨?_, ?_⟩
  · intro a b
    refine Quotient.inductionOn₂ a b fun a b hab => ?_
    refine QuotientGroup.eq.2 fun i _ => ?_
    exact QuotientGroup.eq.1 (congrFun hab i)
  · intro q
    refine ⟨QuotientGroup.mk fun i => (q i).out, ?_⟩
    funext i
    exact Quotient.out_eq (q i)

theorem relIndex_pi {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, Group (H i)]
    (U V : ∀ i, Subgroup (H i)) :
    (Subgroup.pi Set.univ V).relIndex (Subgroup.pi Set.univ U) = ∏ i, (V i).relIndex (U i) := by
  let f : (∀ i, U i) →* (∀ i, H i) :=
    { toFun := fun x i => (x i : H i)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have h := relIndex_eq_of_map f ⊤ (Subgroup.pi Set.univ fun i => (V i).subgroupOf (U i))
    (Subgroup.pi Set.univ U) (Subgroup.pi Set.univ V) (by
      ext u
      constructor
      · rintro ⟨x, -, rfl⟩ i _
        exact (x i).2
      · intro hu
        exact ⟨fun i => ⟨u i, hu i trivial⟩, trivial, rfl⟩) (by
      intro a _
      exact Iff.rfl)
  rw [← h, Subgroup.relIndex_top_right]
  exact index_pi_dep (fun i => (V i).subgroupOf (U i))

theorem mem_map_conj {H : Type} [Group H] (J : Subgroup H) (h x : H) :
    x ∈ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H → MulAut H) h)) J ↔
      h⁻¹ * x * h ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨_, hx, by simp [mul_assoc]⟩

theorem main : (let d1 : {G : Type} → [inst : Group G] → (M N : Subgroup G) → Subgroup G → G → Subgroup ↥(Subgroup.subgroupOf N M) := @(fun {G : Type} [Group G] (M N K : Subgroup G) (x : G) ↦ Subgroup.comap (MonoidHom.comp (Subgroup.subtype M) (Subgroup.subtype (Subgroup.subgroupOf N M))) (Subgroup.comap (MulEquiv.toMonoidHom ((MulAut.conj : G → MulAut G) x⁻¹)) K)); ∀ {G : Type} [inst : Group G] {M N K : Subgroup G} {ι : Type} [inst_1 : Fintype ι] {H : ι → Type} [inst_2 : (i : ι) → Group (H i)] (S : Subgroup G) [Subgroup.Normal S] (L : (i : ι) → G →* H i) (J Nn : (i : ι) → Subgroup (H i)), (∀ k ∈ K, ∀ (i : ι), (L i : G → H i) k ∈ J i) → (∀ y ∈ S, (∀ (i : ι), (L i : G → H i) y ∈ J i) → y ∈ K) → S ≤ M → (∀ n ∈ N, ∀ (i : ι), (L i : G → H i) n ∈ Nn i) → (∀ y ∈ S, (∀ (i : ι), (L i : G → H i) y ∈ Nn i) → y ∈ N) → (∀ (u : (i : ι) → H i), ∃ y ∈ S, ∀ (i : ι), (L i : G → H i) y = u i) → ∀ {δ r : G}, r ∈ S → ∀ (c h : (i : ι) → H i), (∀ (i : ι), (L i : G → H i) r = c i * h i) → (∀ (i : ι), c i ∈ J i) → (∀ (i : ι) (x : H i), ((L i : G → H i) δ * c i)⁻¹ * x * ((L i : G → H i) δ * c i) ∈ Nn i ↔ x ∈ Nn i) → Subgroup.relIndex (d1 M N K (δ * r)) (d1 M N K δ) = ∏ i : ι, Subgroup.relIndex (Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H i → MulAut (H i)) (h i))) (J i)) (Nn i ⊓ J i) ∧ Subgroup.relIndex (d1 M N K δ) (d1 M N K (δ * r)) = ∏ i : ι, Subgroup.relIndex (J i) (Nn i ⊓ Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H i → MulAut (H i)) (h i))) (J i))) := by
  intro d1 G _ M N K ι _ H _ S hS L J Nn hKJ hSK hSM hNN hSN hsurj δ r hr c h hrc hc hδ
  have hd : ∀ (x : G) (n : N.subgroupOf M), n ∈ d1 M N K x ↔ x⁻¹ * ((n : M) : G) * x ∈ K := by
    intro x n
    simp [d1, Subgroup.mem_comap]
  have key : ∀ a b : G, a * b⁻¹ ∈ S → b ∈ K → (∀ i, L i a ∈ J i) → a ∈ K := by
    intro a b hab hb ha
    have : a * b⁻¹ ∈ K := hSK _ hab fun i => by
      rw [map_mul, map_inv]
      exact mul_mem (ha i) (inv_mem (hKJ b hb i))
    simpa using mul_mem this hb
  let φ : (N.subgroupOf M) →* (∀ i, H i) :=
    { toFun := fun n i => (L i δ * c i)⁻¹ * L i ((n : M) : G) * (L i δ * c i)
      map_one' := by ext i; simp
      map_mul' := by intro a b; ext i; simp [mul_assoc] }
  have hφ : ∀ n i, φ n i = (L i δ * c i)⁻¹ * L i ((n : M) : G) * (L i δ * c i) := fun _ _ => rfl
  have hφN : ∀ n i, φ n i ∈ Nn i := fun n i => (hδ i _).2 (hNN _ n.2 i)
  have h1 : ∀ n i, φ n i ∈ J i ↔ L i (δ⁻¹ * ((n : M) : G) * δ) ∈ J i := by
    intro n i
    have e : φ n i = (c i)⁻¹ * L i (δ⁻¹ * ((n : M) : G) * δ) * c i := by
      simp [hφ, mul_assoc]
    rw [e, Subgroup.mul_mem_cancel_right _ (hc i), Subgroup.mul_mem_cancel_left _ (inv_mem (hc i))]
  have h2 : ∀ n i, φ n i ∈
      Subgroup.map (MulEquiv.toMonoidHom ((MulAut.conj : H i → MulAut (H i)) (h i))) (J i) ↔
      L i ((δ * r)⁻¹ * ((n : M) : G) * (δ * r)) ∈ J i := by
    intro n i
    rw [mem_map_conj]
    have e : (h i)⁻¹ * φ n i * h i = L i ((δ * r)⁻¹ * ((n : M) : G) * (δ * r)) := by
      simp [hφ, hrc, mul_assoc]
    rw [e]
  have hs : ∀ u : ∀ i, H i, (∀ i, u i ∈ Nn i) →
      ∃ n : N.subgroupOf M, ((n : M) : G) ∈ S ∧ φ n = u := by
    intro u hu
    obtain ⟨y, hy, hyu⟩ := hsurj fun i => (L i δ * c i) * u i * (L i δ * c i)⁻¹
    have hyN : y ∈ N := hSN y hy fun i => by
      rw [← hδ i, hyu i]
      simpa [mul_assoc] using hu i
    refine ⟨⟨⟨y, hSM hy⟩, hyN⟩, hy, ?_⟩
    ext i
    rw [hφ]
    simp [hyu, mul_assoc]
  constructor
  · rw [← relIndex_pi]
    refine relIndex_eq_of_map φ _ _ _ _ ?_ ?_
    · ext u
      constructor
      · rintro ⟨n, hn, rfl⟩ i _
        exact ⟨hφN n i, (h1 n i).2 (hKJ _ ((hd _ _).1 hn) i)⟩
      · intro hu
        obtain ⟨n, hn, rfl⟩ := hs u fun i => (hu i trivial).1
        refine ⟨n, (hd _ _).2 (hSK _ ?_ fun i => (h1 n i).1 (hu i trivial).2), rfl⟩
        exact hS.conj_mem' _ hn _
    · intro a ha
      rw [hd] at ha ⊢
      constructor
      · intro hb i _
        exact (h2 a i).2 (hKJ _ hb i)
      · intro hb
        refine key _ _ ?_ ha fun i => (h2 a i).1 (hb i trivial)
        have := mul_mem (inv_mem hr) (hS.conj_mem _ hr (δ⁻¹ * ((a : M) : G) * δ))
        convert this using 1
        group
  · rw [← relIndex_pi]
    refine relIndex_eq_of_map φ _ _ _ _ ?_ ?_
    · ext u
      constructor
      · rintro ⟨n, hn, rfl⟩ i _
        exact ⟨hφN n i, (h2 n i).2 (hKJ _ ((hd _ _).1 hn) i)⟩
      · intro hu
        obtain ⟨n, hn, rfl⟩ := hs u fun i => (hu i trivial).1
        refine ⟨n, (hd _ _).2 (hSK _ ?_ fun i => (h2 n i).1 (hu i trivial).2), rfl⟩
        exact hS.conj_mem' _ hn _
    · intro a ha
      rw [hd] at ha ⊢
      constructor
      · intro hb i _
        exact (h1 a i).2 (hKJ _ hb i)
      · intro hb
        refine key _ _ ?_ ha fun i => (h1 a i).1 (hb i trivial)
        have := mul_mem (hS.conj_mem _ (inv_mem hr) (δ⁻¹ * ((a : M) : G) * δ)) hr
        convert this using 1
        group

end GlobalTheory.RelIndexOfMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqZeroOfWrongSignGaussianRelation
section
open SchwartzMap LineDeriv MeasureTheory ComplexConjugate

noncomputable section

namespace GlobalTheory.WrongSignGauss

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def sesq : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ).flip.comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)).flip

@[simp] theorem sesq_apply (u w : ℂ) : sesq u w = u * conj w := by
  simp [sesq]; ring

def mulForm (ℓ : V →ₗ[ℝ] ℝ) : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (⇑(LinearMap.toContinuousLinearMap ℓ))

theorem mulForm_apply (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    mulForm ℓ f x = (ℓ x : ℂ) * f x := by
  rw [mulForm, SchwartzMap.smulLeftCLM_apply_apply (ContinuousLinearMap.hasTemperateGrowth _)]
  simp [Complex.real_smul]

theorem lineDerivOp_mulForm (v : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (mulForm ℓ f) x = (ℓ x : ℂ) * ∂_{v} f x + (ℓ v : ℂ) * f x := by
  have e : (⇑(mulForm ℓ f)) = ⇑(LinearMap.toContinuousLinearMap ℓ) • ⇑f := by
    funext y; rw [Pi.smul_apply', mulForm_apply, Complex.real_smul]; rfl
  have h2 := ((LinearMap.toContinuousLinearMap ℓ).hasFDerivAt (x := x)).smul (f.hasFDerivAt x)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, e, h2.fderiv]
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, Complex.real_smul]

theorem lineDerivOp_comm' (u v : V) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (∂_{u} f) x = ∂_{u} (∂_{v} f) x := by
  have key : ∀ (u v : V) x, ∂_{v} (∂_{u} f) x = fderiv ℝ (fderiv ℝ f) x v u := by
    intro u v x
    have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
      ((SchwartzMap.fderivCLM ℝ _ ℂ f).differentiableAt (x := x)).hasFDerivAt
    have h1 := ((ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt (x := fderiv ℝ f x)).comp x hd
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have e : (⇑(∂_{u} f : 𝓢(V, ℂ))) = (ContinuousLinearMap.apply ℝ ℂ u) ∘ fderiv ℝ f := by
      funext y; rfl
    rw [e, h1.fderiv]
    rfl
  rw [key, key]
  exact ((f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)) _ _

def twD (a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{a} f - (2 * Real.pi * Complex.I) • mulForm ℓ f

theorem twD_apply (a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    twD a ℓ f x = ∂_{a} f x - 2 * Real.pi * Complex.I * ((ℓ x : ℂ) * f x) := by
  simp [twD, mulForm_apply]

section integrals

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

def ip (u w : 𝓢(V, ℂ)) : ℂ := ∫ x, u x * conj (w x) ∂μ

theorem integrable_ip (u w : 𝓢(V, ℂ)) : Integrable (fun x => u x * conj (w x)) μ := by
  have h := (pairing sesq u w).integrable (μ := μ)
  simpa [pairing_apply] using h

theorem ip_smul_left (c : ℂ) (u w : 𝓢(V, ℂ)) : ip μ (c • u) w = c * ip μ u w := by
  simp only [ip, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem ip_smul_right (c : ℂ) (u w : 𝓢(V, ℂ)) : ip μ u (c • w) = conj c * ip μ u w := by
  simp only [ip, SchwartzMap.smul_apply, smul_eq_mul, map_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem ip_sub_left (u v w : 𝓢(V, ℂ)) : ip μ (u - v) w = ip μ u w - ip μ v w := by
  simp only [ip, SchwartzMap.sub_apply, sub_mul]
  exact integral_sub (integrable_ip μ u w) (integrable_ip μ v w)

theorem ip_sub_right (u v w : 𝓢(V, ℂ)) : ip μ w (u - v) = ip μ w u - ip μ w v := by
  simp only [ip, SchwartzMap.sub_apply, map_sub, mul_sub]
  exact integral_sub (integrable_ip μ w u) (integrable_ip μ w v)

theorem ip_lineDerivOp (a : V) (u w : 𝓢(V, ℂ)) : ip μ (∂_{a} u) w = - ip μ u (∂_{a} w) := by
  have h := integral_bilinear_lineDerivOp_right_eq_neg_left (μ := μ) u w sesq a
  simp only [sesq_apply] at h
  simp only [ip, h, neg_neg]

theorem ip_mulForm (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) : ip μ (mulForm ℓ u) w = ip μ u (mulForm ℓ w) := by
  simp only [ip, mulForm_apply, map_mul, Complex.conj_ofReal]
  congr 1; funext x; ring

theorem ip_twD (a : V) (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) :
    ip μ (twD a ℓ u) w = - ip μ u (twD a ℓ w) := by
  simp only [twD, ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right, ip_lineDerivOp, ip_mulForm]
  simp [map_mul, Complex.conj_ofReal, map_ofNat]
  ring

end integrals

theorem lineDerivOp_twD (v a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (twD a ℓ f) x = ∂_{v} (∂_{a} f) x -
      2 * Real.pi * Complex.I * ((ℓ x : ℂ) * ∂_{v} f x + (ℓ v : ℂ) * f x) := by
  rw [twD, ← LineDeriv.lineDerivOpCLM_apply (R := ℂ), map_sub, map_smul,
    LineDeriv.lineDerivOpCLM_apply, LineDeriv.lineDerivOpCLM_apply]
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, lineDerivOp_mulForm]

theorem twD_comm (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    twD a₁ ℓ₁ (twD a₂ ℓ₂ f) - twD a₂ ℓ₂ (twD a₁ ℓ₁ f) =
      (-(2 * Real.pi * Complex.I) * ((ℓ₂ a₁ - ℓ₁ a₂ : ℝ) : ℂ)) • f := by
  ext x
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, twD_apply _ _ (twD _ _ f),
    lineDerivOp_twD]
  rw [twD_apply, twD_apply, lineDerivOp_comm' a₁ a₂ f x]
  push_cast
  ring

section main

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]

theorem ip_self (h : 𝓢(V, ℂ)) : ip μ h h = ((∫ x, ‖h x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [ip]
  first
  | rw [← integral_complex_ofReal]
  | rw [← integral_ofReal (𝕜 := ℂ)]
  congr 1; funext x
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem norm_sq_twD (f : 𝓢(V, ℂ)) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ)
    (hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f) :
    ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ = Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h1 : ip μ (twD a₁ ℓ₁ (twD a₂ ℓ₂ f)) f = -(Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f)) := by
    rw [ip_twD, hD, ip_smul_left]
  have h2 : ip μ (twD a₂ ℓ₂ (twD a₁ ℓ₁ f)) f = -(conj Complex.I * ip μ (twD a₁ ℓ₁ f) (twD a₁ ℓ₁ f)) := by
    rw [ip_twD, hD, ip_smul_right]
  have h3 := congrArg (fun u => ip μ u f) (twD_comm a₁ a₂ ℓ₁ ℓ₂ f)
  simp only [ip_sub_left, ip_smul_left, h1, h2, Complex.conj_I, ip_self] at h3
  have E : ((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) =
      ((Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) * ∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    push_cast at h3 ⊢
    linear_combination (Complex.I / 2) * h3 +
      (((∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ : ℝ) : ℂ) - Real.pi * ((ℓ₂ a₁ : ℂ) - ℓ₁ a₂) *
        ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ)) * Complex.I_sq
  exact_mod_cast E

end main

theorem vanish : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (a₁ a₂ : V) (ℓ₁ ℓ₂ : V →ₗ[ℝ] ℝ),
    (∀ y, fderiv ℝ f y a₂ + (-(2 * Real.pi * Complex.I) * (ℓ₂ y : ℂ)) * f y =
      Complex.I * (fderiv ℝ f y a₁ + (-(2 * Real.pi * Complex.I) * (ℓ₁ y : ℂ)) * f y)) →
    ℓ₂ a₁ - ℓ₁ a₂ < 0 → f = 0 := by
  intro V _ _ _ f a₁ a₂ ℓ₁ ℓ₂ hf hc
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  let μ : Measure V := Measure.addHaar
  have hD : twD a₂ ℓ₂ f = Complex.I • twD a₁ ℓ₁ f := by
    ext y
    simp only [SchwartzMap.smul_apply, smul_eq_mul, twD_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    linear_combination hf y
  have hk := norm_sq_twD μ f a₁ a₂ ℓ₁ ℓ₂ hD
  have hG : 0 ≤ ∫ x, ‖twD a₁ ℓ₁ f x‖ ^ 2 ∂μ := integral_nonneg (fun x => by positivity)
  have hF : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg (fun x => by positivity)
  have hP : Real.pi * (ℓ₂ a₁ - ℓ₁ a₂) < 0 := mul_neg_of_pos_of_neg Real.pi_pos hc
  have hF0 : ∫ x, ‖f x‖ ^ 2 ∂μ = 0 := by nlinarith
  have hint : Integrable (fun x => ‖f x‖ ^ 2) μ := by
    refine (integrable_ip μ f f).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [norm_mul, sq]
  rw [integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint] at hF0
  have hcont : Continuous (fun x => ‖f x‖ ^ 2) := f.continuous.norm.pow 2
  have h0 := (Continuous.ae_eq_iff_eq μ hcont continuous_zero).1 hF0
  ext x
  have hx := congrFun h0 x
  simpa using hx

end GlobalTheory.WrongSignGauss
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleOver
section
open scoped TensorProduct

namespace GlobalTheory.TensHead

def Stab {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (N : Submodule ℂ V) : Prop :=
  ∀ g ∈ G, ∀ x ∈ N, g x ∈ N

def SimpleOver {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (K : Submodule ℂ V) : Prop :=
  ∀ N : Submodule ℂ V, Stab G N → K ≤ N → N = K ∨ N = ⊤

def piOp {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i)) : Module.End ℂ (⨂[ℂ] j, M j) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)

def piOps {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i))) :
    Set (Module.End ℂ (⨂[ℂ] j, M j)) :=
  {f | ∃ i, ∃ g ∈ Op i, f = piOp i g}

def tensOps {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) : Set (Module.End ℂ (V₀ ⊗[ℂ] V₁)) :=
  {f | ∃ g ∈ A, f = TensorProduct.map g LinearMap.id} ∪
    {f | ∃ h ∈ B, f = TensorProduct.map LinearMap.id h}

def piKer {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (K : ∀ i, Submodule ℂ (M i)) : Submodule ℂ (⨂[ℂ] j, M j) :=
  Submodule.span ℂ {t | ∃ y : ∀ i, M i, (∃ i, y i ∈ K i) ∧ t = PiTensorProduct.tprod ℂ y}

def tensKer {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁) : Submodule ℂ (V₀ ⊗[ℂ] V₁) :=
  Submodule.span ℂ {t | ∃ (x : V₀) (y : V₁), (x ∈ K₀ ∨ y ∈ K₁) ∧ t = x ⊗ₜ[ℂ] y}

end GlobalTheory.TensHead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumFourSwap
section
namespace GlobalTheory.SumFourSwap

theorem sum_four_swap {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ a : α, ∑ c : α, ∑ b : β, ∑ e : β, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a : α, ∑ c : α, ∑ e : β, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ e : β, ∑ b : β, f a b c e := Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

end GlobalTheory.SumFourSwap
end

