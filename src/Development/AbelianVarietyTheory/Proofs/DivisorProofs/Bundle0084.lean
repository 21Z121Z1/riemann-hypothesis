import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulNormSqLeNormProjApplySqOfSpanningParts
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts
    {X Y ι : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    (T : X →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ) (hP : (⨆ k, P k) = ⊤)
    (hl : ∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) (u : Y) :
    m * ‖u‖ ^ 2 ≤ ‖LinearMap.adjoint T u‖ ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  haveI : Nontrivial Y := ⟨⟨u, 0, hu⟩⟩
  set S : Y →ₗ[ℂ] Y := T ∘ₗ LinearMap.adjoint T with hS
  have hsym : S.IsSymmetric := by
    intro a b
    simp only [hS, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right T, LinearMap.adjoint_inner_left]
  have hq : ∀ y : Y, RCLike.re ⟪S y, y⟫_ℂ = ‖LinearMap.adjoint T y‖ ^ 2 := by
    intro y
    simp only [hS, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right T, inner_self_eq_norm_sq]
  have hev : ∀ μ : ℝ, Module.End.HasEigenvalue S (μ : ℂ) → m ≤ μ := by
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    by_contra hlt
    have hlt : μ < m := not_le.mp hlt
    have hSv : S v = (μ : ℂ) • v := hv.apply_eq_smul
    have hle : ∀ k, P k ≤ (ℂ ∙ v)ᗮ := by
      intro k y hy
      obtain ⟨l, hml, hly⟩ := hl k
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      have h1 := hsym v y
      have h2 : S y = (l : ℂ) • y := hly y hy
      rw [hSv, h2, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
      have h3 : ((μ : ℂ) - (l : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        have : μ = l := by exact_mod_cast h
        linarith
      have h4 : ((μ : ℂ) - (l : ℂ)) * ⟪v, y⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
      exact (mul_eq_zero.mp h4).resolve_left h3
    have hv' : v ∈ (ℂ ∙ v)ᗮ := by
      have : (⊤ : Submodule ℂ Y) ≤ (ℂ ∙ v)ᗮ := hP ▸ iSup_le hle
      exact this Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hv'
    exact hv.2 hv'
  have h1 := hev _ hsym.hasEigenvalue_iInf_of_finiteDimensional
  have hb : BddBelow (Set.range fun x : { x : Y // x ≠ 0 } =>
      RCLike.re ⟪S x, x⟫_ℂ / ‖(x : Y)‖ ^ 2) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    simp only [hq]
    positivity
  have h2 := h1.trans (ciInf_le hb ⟨u, hu⟩)
  simp only [hq] at h2
  have hpos : 0 < ‖u‖ ^ 2 := by positivity
  rwa [le_div_iff₀ hpos] at h2

theorem mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts :
    ∀ (X Y ι : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ), 0 < m → LinearMap.adjoint e = e → (∀ y, e (e y) = e y) → (⨆ k, P k) = ⊤ → (∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) → ∀ x ∈ (LinearMap.ker (e ∘ₗ T))ᗮ, m * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 := by
  intro X Y ι _ _ _ _ _ _ T e P m hm he hee hP hl x hx
  rw [LinearMap.orthogonal_ker] at hx
  obtain ⟨w, hw⟩ := hx
  rw [LinearMap.adjoint_comp, he, LinearMap.comp_apply] at hw
  set u := e w with hu
  have h1 := mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts T P m hP hl u
  rw [hw] at h1
  have h2 : ⟪x, x⟫_ℂ = ⟪u, e (T x)⟫_ℂ := by
    have : ⟪u, e (T x)⟫_ℂ = ⟪e u, T x⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_left e, he]
    rw [this, hu, hee, ← hu, ← LinearMap.adjoint_inner_left T, hw]
  have h3 : ‖x‖ ^ 2 ≤ ‖u‖ * ‖e (T x)‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) u (e (T x))
    rw [← h2, inner_self_eq_norm_sq_to_K] at h
    simpa using h
  by_cases hx0 : x = 0
  · simp [hx0]
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  have h4 : (‖x‖ ^ 2) ^ 2 ≤ (‖u‖ * ‖e (T x)‖) ^ 2 := by gcongr
  have h5 : (m * ‖x‖ ^ 2) * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 * ‖x‖ ^ 2 := by
    calc (m * ‖x‖ ^ 2) * ‖x‖ ^ 2 = m * (‖x‖ ^ 2) ^ 2 := by ring
      _ ≤ m * (‖u‖ * ‖e (T x)‖) ^ 2 := by gcongr
      _ = ‖e (T x)‖ ^ 2 * (m * ‖u‖ ^ 2) := by ring
      _ ≤ ‖e (T x)‖ ^ 2 * ‖x‖ ^ 2 := by gcongr
  exact le_of_mul_le_mul_right h5 hpos

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTensorInjectiveOfFlatBaseChangeKerInf
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open TensorProduct

namespace GlobalTheory.TorStep

theorem mul_tensor_injective : ∀ (P R₂ B B₂ : Type) [CommRing P] [CommRing R₂] [CommRing B]
    [CommRing B₂] [Algebra P B] (K₁ : Ideal P) (f₂ : P →+* R₂) (a₂ : R₂ →+* B₂) (c₂ : B →+* B₂),
    Function.Surjective f₂ → Function.Surjective c₂ → c₂.comp (algebraMap P B) = a₂.comp f₂ →
    RingHom.ker c₂ = (RingHom.ker f₂).map (algebraMap P B) → K₁ ⊓ RingHom.ker f₂ = ⊥ →
    a₂.Flat → Function.Injective (TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype)) := by
  intro P R₂ B B₂ _ _ _ _ _ K₁ f₂ a₂ c₂ hf hc hcomp hker hK hflat
  letI := a₂.toAlgebra
  haveI : Module.Flat R₂ B₂ := hflat
  have hc' : ∀ p : P, c₂ (algebraMap P B p) = a₂ (f₂ p) := fun p => by
    simpa using congrArg (fun g : P →+* B₂ => g p) hcomp
  have hsmulB : ∀ (p : P) (b : B), c₂ (p • b) = f₂ p • c₂ b := fun p b => by
    rw [Algebra.smul_def, map_mul, hc', Algebra.smul_def, RingHom.algebraMap_toAlgebra]

  have hzero : ∀ x : P, x ∈ K₁ → f₂ x = 0 → x = 0 := fun x h1 h2 => by
    have : x ∈ K₁ ⊓ RingHom.ker f₂ := ⟨h1, h2⟩
    rw [hK] at this
    simpa using this

  have L0 : ∀ x : B, x ∈ RingHom.ker c₂ → ∀ k : K₁, (k ⊗ₜ[P] x : K₁ ⊗[P] B) = 0 := by
    intro x hx
    rw [hker, Ideal.map] at hx
    suffices H : ∀ (k : K₁) (y : B), (k ⊗ₜ[P] (y * x) : K₁ ⊗[P] B) = 0 by
      intro k; simpa using H k 1
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨κ, hκ, rfl⟩ := hz
      intro k y
      have e1 : y * algebraMap P B κ = κ • y := by rw [Algebra.smul_def, mul_comm]
      rw [e1, ← smul_tmul]
      have e2 : κ • k = 0 := by
        apply Subtype.ext
        apply hzero
        · exact (κ • k).2
        · simp only [Submodule.coe_smul, smul_eq_mul, map_mul]
          rw [RingHom.mem_ker.mp hκ, zero_mul]
      rw [e2, zero_tmul]
    | zero => intro k y; rw [mul_zero, tmul_zero]
    | add u v _ _ hu hv => intro k y; rw [mul_add, tmul_add, hu, hv, add_zero]
    | smul b u _ hu => intro k y; rw [smul_eq_mul, ← mul_assoc]; exact hu k (y * b)
  have L1 : ∀ (k : K₁) (x y : B), c₂ x = c₂ y → (k ⊗ₜ[P] x : K₁ ⊗[P] B) = k ⊗ₜ[P] y := by
    intro k x y h
    rw [← sub_eq_zero, ← tmul_sub]
    exact L0 _ (by rw [RingHom.mem_ker, map_sub, h, sub_self]) k
  let s := Function.surjInv hc
  have hs : ∀ β, c₂ (s β) = β := Function.surjInv_eq hc
  let J₂ : Ideal R₂ := K₁.map f₂
  let ej : K₁ → J₂ := fun k => ⟨f₂ k, Ideal.mem_map_of_mem f₂ k.2⟩
  have hpre : ∀ j : J₂, ∃ k : P, k ∈ K₁ ∧ f₂ k = j := fun j =>
    (Ideal.mem_map_iff_of_surjective f₂ hf).mp j.2
  let einv : J₂ → K₁ := fun j => ⟨Classical.choose (hpre j), (Classical.choose_spec (hpre j)).1⟩
  have hE' : ∀ j : J₂, f₂ (einv j) = j := fun j => (Classical.choose_spec (hpre j)).2
  have hE : ∀ (k : K₁) (j : J₂), f₂ k = j → einv j = k := by
    intro k j h
    apply Subtype.ext
    rw [← sub_eq_zero]
    apply hzero
    · exact (einv j - k).2
    · rw [map_sub, hE', h, sub_self]

  let ψ0 : K₁ →+ B →+ J₂ ⊗[R₂] B₂ :=
    AddMonoidHom.mk' (fun k => AddMonoidHom.mk' (fun b => ej k ⊗ₜ[R₂] c₂ b)
      (fun b b' => by rw [map_add, tmul_add]))
      (fun k k' => by
        ext b
        have : ej (k + k') = ej k + ej k' := Subtype.ext (by simp [ej])
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, this, add_tmul])
  let ψ : K₁ ⊗[P] B →+ J₂ ⊗[R₂] B₂ := liftAddHom ψ0 (by
    intro p k b
    simp only [ψ0, AddMonoidHom.mk'_apply]
    have : ej (p • k) = f₂ p • ej k := Subtype.ext (by simp [ej])
    rw [this, hsmulB, smul_tmul])

  let χ0 : J₂ →+ B₂ →+ K₁ ⊗[P] B :=
    AddMonoidHom.mk' (fun j => AddMonoidHom.mk' (fun β => einv j ⊗ₜ[P] s β)
      (fun β β' => by rw [← tmul_add]; exact L1 _ _ _ (by rw [map_add, hs, hs, hs])))
      (fun j j' => by
        ext β
        have : einv (j + j') = einv j + einv j' :=
          hE _ _ (by rw [Submodule.coe_add, map_add, hE', hE', Submodule.coe_add])
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, this, add_tmul])
  let χ : J₂ ⊗[R₂] B₂ →+ K₁ ⊗[P] B := liftAddHom χ0 (by
    intro r j β
    simp only [χ0, AddMonoidHom.mk'_apply]
    obtain ⟨p, rfl⟩ := hf r
    have e1 : einv (f₂ p • j) = p • einv j :=
      hE _ _ (by simp [hE'])
    rw [e1, smul_tmul]
    exact L1 _ _ _ (by rw [hsmulB, hs, hs]))
  have hχψ : ∀ t, χ (ψ t) = t := by
    intro t
    induction t with
    | zero => simp
    | add u v hu hv => rw [map_add, map_add, hu, hv]
    | tmul k b =>
      simp only [ψ, χ, liftAddHom_tmul, ψ0, χ0, AddMonoidHom.mk'_apply]
      rw [hE k (ej k) rfl]
      exact L1 _ _ _ (hs _)

  let ν : J₂ ⊗[R₂] B₂ →ₗ[R₂] B₂ :=
    (TensorProduct.lid R₂ B₂).toLinearMap ∘ₗ J₂.subtype.rTensor B₂
  have hν : Function.Injective ν :=
    (TensorProduct.lid R₂ B₂).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ J₂.injective_subtype)
  set μ := TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype) with hμ
  have key : ∀ t, ν (ψ t) = c₂ (μ t) := by
    intro t
    induction t with
    | zero => simp
    | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, map_add]
    | tmul k b =>
      simp only [ψ, liftAddHom_tmul, ψ0, AddMonoidHom.mk'_apply, ν, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply, LinearEquiv.coe_coe,
        TensorProduct.lid_tmul, hμ, TensorProduct.lift.tmul, LinearMap.coe_comp,
        LinearMap.lsmul_apply]
      rw [hsmulB]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  have h1 : ψ t = 0 := hν (by rw [key, ht, map_zero, map_zero])
  rw [← hχψ t, h1, map_zero]

end GlobalTheory.TorStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearMemSpanImagePartial
section
namespace GlobalTheory.MultilinearSpanImage

theorem multilinear_mem_span_image_partial {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module ℂ (M i)] {N : Type} [AddCommGroup N]
    [Module ℂ N] (Φ : MultilinearMap ℂ M N) (s : (i : ι) → Set (M i)) (t : Finset ι) :
    ∀ f : (i : ι) → M i, (∀ i ∈ t, f i ∈ Submodule.span ℂ (s i)) → (∀ i, i ∉ t → f i ∈ s i) →
      Φ f ∈ Submodule.span ℂ {y : N | ∃ g : (i : ι) → M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
  refine Finset.induction_on t ?_ ?_
  · intro f _ h
    exact Submodule.subset_span ⟨f, fun i => h i (by simp), rfl⟩
  · intro a t ha ih f h1 h2
    have key : ∀ x ∈ Submodule.span ℂ (s a), Φ (Function.update f a x) ∈
        Submodule.span ℂ {y : N | ∃ g : (i : ι) → M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        apply ih
        · intro i hi
          have hne : i ≠ a := by rintro rfl; exact ha hi
          simpa [hne] using h1 i (Finset.mem_insert_of_mem hi)
        · intro i hi
          by_cases h : i = a
          · subst h; simpa using hx
          · simpa [h] using h2 i (by simp [h, hi])
      | zero => rw [Φ.map_update_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Φ.map_update_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [Φ.map_update_smul]; exact Submodule.smul_mem _ c hx
    have := key (f a) (h1 a (Finset.mem_insert_self a t))
    simpa using this

theorem multilinear_apply_mem_span_image {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [inst : (i : ι) → AddCommGroup (M i)] [inst_1 : (i : ι) → Module ℂ (M i)] {N : Type}
    [inst_2 : AddCommGroup N] [inst_3 : Module ℂ N] (Φ : MultilinearMap ℂ M N)
    (s : (i : ι) → Set (M i)) (f : (i : ι) → M i) (hf : ∀ (i : ι), f i ∈ Submodule.span ℂ (s i)) :
    (Φ : ((i : ι) → M i) → N) f ∈ Submodule.span ℂ
      {y : N | ∃ (g : (i : ι) → M i), (∀ (i : ι), g i ∈ s i) ∧ y = (Φ : ((i : ι) → M i) → N) g} :=
  multilinear_mem_span_image_partial Φ s Finset.univ f (fun i _ => hf i) (fun i hi => absurd (Finset.mem_univ i) hi)

end GlobalTheory.MultilinearSpanImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearVanishOfProdVanish
section
open Finset Function

namespace GlobalTheory

theorem multilinear_vanish_of_prod_vanish_of_agree_off_finset {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M]
    [Module K M] (P : MultilinearMap K (fun i => A i) M) (S : Finset ι) :
    ∀ {D : Type} (s : Finset D) (c : D → K) (f : D → ∀ i, A i),
      (∀ i ∉ S, ∀ d ∈ s, ∀ d' ∈ s, f d i = f d' i) →
      (∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) →
      ∑ d ∈ s, c d • P (f d) = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro D s c f hconst hx
    rcases s.eq_empty_or_nonempty with rfl | ⟨d₀, hd₀⟩
    · simp
    have hf : ∀ d ∈ s, f d = f d₀ := fun d hd =>
      funext fun i => hconst i (Finset.notMem_empty i) d hd d₀ hd₀
    have hsum : ∑ d ∈ s, c d • P (f d) = (∑ d ∈ s, c d) • P (f d₀) := by
      rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]
    have hx' : ∀ x : ∀ i, X i, (∑ d ∈ s, c d) * ∏ i, (f d₀ i : X i → K) (x i) = 0 := by
      intro x; rw [Finset.sum_mul, ← hx x]
      exact Finset.sum_congr rfl fun d hd => by rw [hf d hd]
    rw [hsum]
    by_cases hc : ∑ d ∈ s, c d = 0
    · rw [hc, zero_smul]
    · by_contra hne
      have hex : ∀ i, ∃ t : X i, (f d₀ i : X i → K) t ≠ 0 := by
        intro i
        by_contra h
        push_neg at h
        apply hne
        have h0 : f d₀ i = 0 := by
          apply Subtype.ext
          funext t
          simpa using h t
        rw [P.map_coord_zero i h0, smul_zero]
      choose x hxne using hex
      have h1 := hx' x
      rw [mul_eq_zero] at h1
      rcases h1 with h | h
      · exact hc h
      · exact (Finset.prod_ne_zero_iff.mpr fun i _ => hxne i) h
  | insert i₀ S hi₀ ih =>
    intro D s c f hconst hx
    classical
    let W : Submodule K (A i₀) := Submodule.span K (↑(s.image fun d => f d i₀))
    let b := Module.finBasis K W
    have hmem : ∀ d ∈ s, f d i₀ ∈ W := fun d hd =>
      Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨d, hd, rfl⟩)
    let a : D → Fin (Module.finrank K W) → K := fun d l =>
      if hd : d ∈ s then b.repr ⟨f d i₀, hmem d hd⟩ l else 0
    have hexp : ∀ d ∈ s, f d i₀ = ∑ l, a d l • (b l : A i₀) := by
      intro d hd
      have h := congrArg Subtype.val (b.sum_repr ⟨f d i₀, hmem d hd⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      simp only [a, dif_pos hd]
      exact h.symm
    have hP : ∀ d ∈ s, P (f d) = ∑ l, a d l • P (update (f d) i₀ (b l)) := by
      intro d hd
      have e : f d = update (f d) i₀ (∑ l, a d l • (b l : A i₀)) := by
        rw [← hexp d hd, update_eq_self]
      rw [e, P.map_update_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [P.map_update_smul, update_idem]

    have hsplit : ∀ (g : ∀ i, A i) (y : ∀ i, X i), ∏ i, (g i : X i → K) (y i) =
        (g i₀ : X i₀ → K) (y i₀) * ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g y =>
      (Finset.mul_prod_erase univ (fun i => (g i : X i → K) (y i)) (mem_univ i₀)).symm
    have hupd : ∀ (g : ∀ i, A i) (v : A i₀) (y : ∀ i, X i),
        ∏ i ∈ univ.erase i₀, (update g i₀ v i : X i → K) (y i) =
          ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g v y =>
      Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
    have hupdx : ∀ (g : ∀ i, A i) (y : ∀ i, X i) (t : X i₀),
        ∏ i ∈ univ.erase i₀, (g i : X i → K) (update y i₀ t i) =
          ∏ i ∈ univ.erase i₀, (g i : X i → K) (y i) := fun g y t =>
      Finset.prod_congr rfl fun i hi => by rw [update_of_ne (Finset.ne_of_mem_erase hi)]
    have hli : LinearIndependent K (fun l => ((b l : A i₀) : X i₀ → K)) :=
      b.linearIndependent.map' ((A i₀).subtype ∘ₗ W.subtype)
        (LinearMap.ker_eq_bot_of_injective (Subtype.val_injective.comp Subtype.val_injective))

    have hB : ∀ (x : ∀ i, X i) (l : Fin (Module.finrank K W)),
        ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) = 0 := by
      intro x
      refine Fintype.linearIndependent_iff.mp hli _ ?_
      funext t
      have h := hx (update x i₀ t)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [hsplit, hupdx, update_self, hexp d hd]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    have hstep : ∑ d ∈ s, c d • P (f d) =
        ∑ l, ∑ d ∈ s, (c d * a d l) • P (update (f d) i₀ (b l)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [hP d hd, Finset.smul_sum]
      simp only [mul_smul]
    rw [hstep]
    refine Finset.sum_eq_zero fun l _ => ih s (fun d => c d * a d l)
      (fun d => update (f d) i₀ (b l)) ?_ ?_
    · intro i hi d hd d' hd'
      by_cases h : i = i₀
      · subst h; simp
      · simp only [update_of_ne h]
        exact hconst i (by simp [h, hi]) d hd d' hd'
    · intro x
      have h := hB x l
      calc ∑ d ∈ s, c d * a d l * ∏ i, (update (f d) i₀ (b l) i : X i → K) (x i)
          = ((b l : A i₀) : X i₀ → K) (x i₀) *
              ∑ d ∈ s, c d * a d l * ∏ i ∈ univ.erase i₀, (f d i : X i → K) (x i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [hsplit, hupd, update_self]
            ring
        _ = 0 := by rw [h, mul_zero]

theorem multilinear_vanish_of_prod_vanish {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M]
    [Module K M] (P : MultilinearMap K (fun i => A i) M) {D : Type} (s : Finset D) (c : D → K)
    (f : D → ∀ i, A i)
    (hx : ∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) :
    ∑ d ∈ s, c d • P (f d) = 0 :=
  multilinear_vanish_of_prod_vanish_of_agree_off_finset A P univ s c f (fun i hi => absurd (mem_univ i) hi) hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialIdealEqBotOfPderivStableNoConstants
section
namespace GlobalTheory

open MvPolynomial Finsupp

theorem mvPolynomial_ideal_eq_bot_of_pderiv_stable :
    ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) R)),
  (∀ P ∈ I, ∀ i, MvPolynomial.pderiv i P ∈ I) → (∀ a : R, MvPolynomial.C a ∈ I → a = 0) → I = ⊥ := by
  intro R _ _ _ r I hI hC
  have key : ∀ n : ℕ, ∀ P ∈ I, P.totalDegree = n → P = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro P hP h
    by_contra hne
    by_cases hn : n = 0
    · subst hn
      rw [totalDegree_eq_zero_iff_eq_C] at h
      apply hne
      rw [h] at hP ⊢
      rw [hC _ hP, C_0]
    · obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hne)
        (fun s => s.sum fun _ e => e)
      have hdeg : (m.sum fun _ e => e) = n := by rw [← h, totalDegree, hmd]
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have hm0 : m = 0 := Finsupp.ext hcon
        subst hm0
        simp at hdeg
        omega
      have hQ : pderiv i P ∈ I := hI P hP i
      have hQne : pderiv i P ≠ 0 := by
        intro h0
        have hc := coeff_pderiv (i := i) P (m - single i 1)
        rw [h0, coeff_zero, sub_add_single_one_cancel hi] at hc
        have hcm : coeff m P ≠ 0 := MvPolynomial.mem_support_iff.mp hm
        have hk : (((m - single i 1 : Fin r →₀ ℕ) i : ℕ) : R) + 1 ≠ 0 :=
          Nat.cast_add_one_ne_zero _
        exact (mul_ne_zero hcm hk) hc.symm
      have hlt : (pderiv i P).totalDegree < n := by
        have hle : (pderiv i P).totalDegree ≤ n - 1 := by
          apply Finset.sup_le
          intro s hs
          have hs' := MvPolynomial.mem_support_iff.mp hs
          rw [coeff_pderiv] at hs'
          have hsupp : s + single i 1 ∈ P.support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hs')
          have hd := le_totalDegree hsupp
          rw [Finsupp.sum_add_index' (by simp) (by intros; rfl), Finsupp.sum_single_index rfl, h] at hd
          omega
        omega
      exact hQne (ih _ hlt _ hQ rfl)
  rw [eq_bot_iff]
  intro P hP
  rw [Ideal.mem_bot]
  exact key _ P hP rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardHomologyOfShortExactMul
section
open CategoryTheory Limits

namespace GlobalTheory

theorem natCard_eq_coker_mul_ker_of_exact {R : Type} [Ring R] {A A' B D D' : Type}
    [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup D] [AddCommGroup D']
    [Module R A] [Module R A'] [Module R B] [Module R D] [Module R D']
    (f : A →ₗ[R] A') (g : A' →ₗ[R] B) (d : B →ₗ[R] D) (h : D →ₗ[R] D')
    (e₁ : LinearMap.range f = LinearMap.ker g) (e₂ : LinearMap.range g = LinearMap.ker d)
    (e₃ : LinearMap.range d = LinearMap.ker h) :
    Nat.card B = Nat.card (A' ⧸ LinearMap.range f) * Nat.card (LinearMap.ker h) := by
  have h1 : Nat.card B = Nat.card (B ⧸ LinearMap.ker d) * Nat.card (LinearMap.ker d) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker d).toAddSubgroup
  rw [h1, Nat.card_congr d.quotKerEquivRange.toEquiv, e₃, e₁,
    Nat.card_congr g.quotKerEquivRange.toEquiv, e₂, mul_comm]

theorem natCard_homology_of_shortExact_mul : ∀ (p : ℕ) (C G : CochainComplex (ModuleCat.{0} ℤ) ℕ) (π : C ⟶ G) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact → ∀ n : ℕ, Nat.card (G.homology n) = Nat.card ((C.homology n) ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : C.homology n →ₗ[ℤ] C.homology n))) * Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1)))) := by
  intro p C G π hz hS n
  have hmul0 : ∀ k, HomologicalComplex.homologyMap ((p : ℤ) • 𝟙 C) k = (p : ℤ) • 𝟙 _ := by
    intro k
    have := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) k).map_zsmul
      (f := 𝟙 C) (r := (p : ℤ))
    rw [CategoryTheory.Functor.map_id] at this
    exact this
  have hmul : ∀ k, (HomologicalComplex.homologyMap ((p : ℤ) • 𝟙 C) k).hom
      = (p : ℤ) • (LinearMap.id : C.homology k →ₗ[ℤ] C.homology k) := by
    intro k
    rw [hmul0]
    ext x
    simp
  have e2 := (hS.homology_exact₂ n).moduleCat_range_eq_ker
  have e3 := (hS.homology_exact₃ n (n+1) rfl).moduleCat_range_eq_ker
  have e1 := (hS.homology_exact₁ n (n+1) rfl).moduleCat_range_eq_ker
  dsimp only at e1 e2 e3
  rw [hmul] at e1 e2
  exact natCard_eq_coker_mul_ker_of_exact _ _ _ _ e2 e3 e1

end GlobalTheory
end

