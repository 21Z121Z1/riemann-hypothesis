import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0025
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSatakeAlmostAll

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SingleBdd
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem exists_types {G H : Type} [Group G] [Group H] (i : H →* G) (W : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ W] (hW : ∀ h, ∀ f ∈ W, (fun g => f (g * i h)) ∈ W) :
    ∃ V : Submodule ℂ (H → ℂ), FiniteDimensional ℂ V ∧ (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) ∧
      ∀ f ∈ W, ∀ g, (fun k => f (g * i k)) ∈ V := by
  let ρ : H → W →ₗ[ℂ] W := fun h => (LinearMap.funLeft ℂ ℂ fun g => g * i h).restrict (hW h)
  have hρ : ∀ k k' w, ρ (k * k') w = ρ k (ρ k' w) := fun k k' w =>
    Subtype.ext (funext fun g => by
      change w.1 (g * i (k * k')) = w.1 (g * i k * i k')
      rw [map_mul, mul_assoc])
  let m : Module.Dual ℂ W →ₗ[ℂ] W →ₗ[ℂ] (H → ℂ) :=
    LinearMap.mk₂ ℂ (fun l w k => l (ρ k w)) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => by funext k; simp) (fun _ _ _ => by funext k; simp)
  refine ⟨LinearMap.range (TensorProduct.lift m), inferInstance, ?_, fun f hf g => ?_⟩
  · rintro _ ⟨t, rfl⟩ k'
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul l w => exact ⟨l ⊗ₜ ρ k' w, funext fun k => congrArg l (hρ k k' w).symm⟩
    | add s t hs ht => rw [map_add]; exact add_mem hs ht
  · exact ⟨((LinearMap.proj g).comp W.subtype) ⊗ₜ ⟨f, hf⟩, rfl⟩

private theorem exists_types' {G H : Type} [Group G] [Group H] (i : H →* G) (C : Subgroup G) (hi : ∀ k, i k ∈ C) (f : G → ℂ)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : C => GroundTheory.Automorphic.rightTranslate (k : G) f))) :
    ∃ V : Submodule ℂ (H → ℂ), FiniteDimensional ℂ V ∧ (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) ∧
      ∀ g, (fun k => f (g * i k)) ∈ V := by
  obtain ⟨V, h1, h2, h3⟩ := exists_types i
    (Submodule.span ℂ (Set.range fun k : C => GroundTheory.Automorphic.rightTranslate (k : G) f)) (fun k ψ hψ => by
      induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨l, rfl⟩ := hψ
        exact Submodule.subset_span ⟨⟨i k, hi k⟩ * l, funext fun g => congrArg f (mul_assoc g (i k) l.1).symm⟩
      | zero => exact zero_mem _
      | add _ _ _ _ a b => exact add_mem a b
      | smul c _ _ a => exact Submodule.smul_mem _ c a)
  exact ⟨V, h1, h2, h3 f (Submodule.subset_span ⟨1, funext fun g => congrArg f (mul_one g)⟩)⟩

private theorem exists_monic {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (W : Submodule ℂ M)
    [FiniteDimensional ℂ W] (hW : ∀ x ∈ W, T x ∈ W) : UpperTheory.V.Af.Fin.AlgMod W ⊥ T := by
  obtain ⟨p, hp, h⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℂ (T.restrict hW)
  refine ⟨p, hp, fun x hx => ?_⟩
  have key : ∀ q : Polynomial ℂ, Polynomial.aeval T q x = (Polynomial.aeval (T.restrict hW) q ⟨x, hx⟩ : W) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q r hq hr => simp only [map_add, LinearMap.add_apply, hq, hr, Submodule.coe_add]
    | monomial n c =>
      simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul,
        Module.End.pow_restrict n hW, LinearMap.restrict_apply]
  rw [key, h]
  rfl

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm in
private theorem bdd_span {K : Type} [Field K] [NumberField K] {n : ℕ} (f : archSmooth K n) (h : IsAutomorphicForm f.1) :
    Bdd (Submodule.span ℂ {f}) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, ?_, ?_, fun z hz => ?_⟩
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact h.isLeftInvariant.smul c
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact h.hasModerateGrowth.smul c
  · obtain ⟨U, -, hU⟩ := exists_openSubgroup_rightInvariant h.isSmooth h.isKFinite
    refine ⟨U.toSubgroup, U.isOpen, fun φ hφ u hu g => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact congrArg (c • ·) (hU g u hu)
  · have hK := h.isKFinite
    unfold IsKFinite at hK
    obtain ⟨V, h1, h2, h3⟩ := exists_types' ((infEmb K n).comp (archCompact K n).subtype) Reduction.maxCompact
      (fun k => k.2) f.1 hK
    refine ⟨V, h1, h2, fun φ hφ g => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    exact V.smul_mem c (h3 g)
  · have hZ : IsZFinite f := h.isZFinite
    unfold IsZFinite at hZ
    refine (exists_monic (uAction z) (Submodule.span ℂ
      ((fun z => uAction z f) '' ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))) (fun ψ hψ => ?_)).mono
      (Submodule.span_mono ?_)
    · induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨y, hy, rfl⟩ := hψ
        exact Submodule.subset_span ⟨z * y, mul_mem hz hy, by simp only [map_mul, Module.End.mul_apply]⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add _ _ _ _ a b => rw [map_add]; exact add_mem a b
      | smul c _ _ a => rw [map_smul]; exact Submodule.smul_mem _ c a
    · rintro _ rfl
      exact ⟨1, one_mem _, by simp only [map_one, Module.End.one_apply]⟩

theorem UpperTheory.V.Cj.S.singleBdd :
    UpperTheory.V.Cj.S.SingleBdd := by
  intro E _ _ _ a φ h
  unfold BddS
  rw [Submodule.map_span, Set.image_singleton]
  exact bdd_span _ ((UpperTheory.V.Cm.isAutForm_iff φ).1 h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SliceBdd
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin

variable {K : Type} [Field K] [NumberField K]

private theorem left_slSp {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n))
    (h : ∀ ψ ∈ S, ∀ g ∈ Γ, ∀ γ m, ψ.1 (g * emb e (AdelicGLn.diagonal K a γ * m)) = ψ.1 (g * emb e m)) :
    ∀ f ∈ slSp e Γ S, IsLeftInvariant f.1 := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ψ, hψ, g, hg, hf⟩ := hf
    intro γ m
    rw [hf, hf, h ψ hψ g hg]
  | zero => exact isLeftInvariant_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

private theorem bdd_slices {r s : ℕ} {S : Submodule ℂ (archSmooth K (r + s))} (hS : Bdd S) (hK : Sat S) :
    Bdd (slSp (e1 r s) (Set.range (emb (e2 r s))) (ctSp r S)) ∧
      Bdd (slSp (e2 r s) (Set.range (emb (e1 r s))) (ctSp r S)) := by
  obtain ⟨ι, _, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  obtain ⟨hN, hG, hL, hK', hM⟩ := UpperTheory.constantTermSpace_automorphic_properties K r s S hS hK
  have hT := UpperTheory.constantTermSpace_types_of_bdd K _ r S hS
  have hA := UpperTheory.algebraic_module_of_vanishing_block K r s _ hN (UpperTheory.constantTermSpace_centre_of_bdd K _ r S hS) ι D
  refine ⟨⟨left_slSp _ _ _ ?_, (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K _ _ _ _ _ hT,
      UpperTheory.siegelLevi_block_aeval_stable K _ _ _ _ _ (Van K r s) ι D ?_ fun τ u => (hA τ u).1⟩,
    ⟨left_slSp _ _ _ ?_, (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K _ _ _ _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K _ _ _ _ _ hT,
      UpperTheory.siegelLevi_block_aeval_stable K _ _ _ _ _ (Van K r s) ι D ?_ fun τ u => (hA τ u).2⟩⟩
  · rintro ψ hψ _ ⟨m₂, rfl⟩ γ m
    rw [← hM ψ hψ γ 1 (emb (e2 r s) m₂ * emb (e1 r s) m), map_mul, ← mul_assoc, ← emb_comm, blk, map_one, mul_one,
      ← (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K _ _ _).2.1, mul_assoc]
  · rintro ψ hψ _ ⟨m₂, rfl⟩ m
    rw [← emb_comm]
    exact hψ m m₂
  · rintro ψ hψ _ ⟨m₁, rfl⟩ γ m
    rw [← hM ψ hψ 1 γ (emb (e1 r s) m₁ * emb (e2 r s) m), map_mul, ← mul_assoc, emb_comm, blk, map_one, one_mul,
      ← (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K _ _ _).2.1, mul_assoc]
  · rintro ψ hψ _ ⟨m₁, rfl⟩ m
    exact hψ m₁ m

private theorem exists_slice {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n)) {ψ : archSmooth K n} (hψ : ψ ∈ S) {g : AdelicGLn.AdelicGL K n} (hg : g ∈ Γ) :
    ∃ f ∈ slSp e Γ S, ∀ m, f.1 m = ψ.1 (g * emb e m) := by
  obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K a n e g
  exact ⟨f ψ, Submodule.subset_span ⟨ψ, hψ, g, hg, hf ψ⟩, hf ψ⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.sliceBdd :
    UpperTheory.V.Cj.S.SingleBdd → UpperTheory.V.Cj.S.SliceBdd := by
  intro hB E _ _ _ r s φ hφ
  obtain ⟨S, hle, hS, hK⟩ := UpperTheory.exists_automorphic_saturation_submodule E (r + s) _ (hB E (r + s) φ hφ)
  have hmem : UpperTheory.V.Cm.smEq E (r + s) φ ∈ S :=
    hle (Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self φ))
  obtain ⟨hs, -⟩ := UpperTheory.constantTerm_archSmooth E (r + s) r (UpperTheory.V.Cm.smEq E (r + s) φ) (UpperTheory.isAutomorphicForm_of_bdd_submodule E _ S hS _ hmem)
  have hψ : (⟨_, hs⟩ : GroundTheory.Automorphic.AutomorphicForm.archSmooth E (r + s)) ∈ UpperTheory.V.Af.Fin.ctSp r S :=
    Submodule.subset_span ⟨_, hmem, rfl⟩
  obtain ⟨h₁, h₂⟩ := bdd_slices hS hK
  refine ⟨Submodule.comap (UpperTheory.V.Cm.smEq E r).toLinearMap _, Submodule.comap (UpperTheory.V.Cm.smEq E s).toLinearMap _,
    h₁.mono (Submodule.map_comap_le _ _), h₂.mono (Submodule.map_comap_le _ _), fun y => ?_, fun x => ?_⟩
  · obtain ⟨f, hf, hf'⟩ := exists_slice (e1 r s) (Set.range (emb (e2 r s))) _ hψ ⟨y, rfl⟩
    refine ⟨(UpperTheory.V.Cm.smEq E r).symm f, by simpa using hf, funext fun x => (hf' x).trans ?_⟩
    rw [← UpperTheory.V.Af.Fin.emb_comm]
    rfl
  · obtain ⟨f, hf, hf'⟩ := exists_slice (e2 r s) (Set.range (emb (e1 r s))) _ hψ ⟨x, rfl⟩
    exact ⟨(UpperTheory.V.Cm.smEq E s).symm f, by simpa using hf, funext fun y => hf' y⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SumInner
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem sum_three {A B C P R : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype P] [Fintype R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq P]
    (f : A → P) (f' : B → P) (f'' : C → P) (h : Function.Bijective (Sum.elim (Sum.elim f f') f''))
    (g : (A → R) → (B → R) → ℂ) :
    ∑ c : P → R, g (c ∘ f) (c ∘ f') = (Fintype.card R : ℂ) ^ Fintype.card C * ∑ c₁, ∑ c₂, g c₁ c₂ := by
  let e : (P → R) ≃ ((A → R) × (B → R)) × (C → R) :=
    ((Equiv.ofBijective _ h).symm.arrowCongr (Equiv.refl R)).trans
      ((Equiv.sumArrowEquivProdArrow _ _ _).trans
        ((Equiv.sumArrowEquivProdArrow _ _ _).prodCongr (Equiv.refl _)))
  have h1 : ∑ c : P → R, g (c ∘ f) (c ∘ f') = ∑ x : ((A → R) × (B → R)) × (C → R), g x.1.1 x.1.2 :=
    Fintype.sum_equiv e _ _ (fun c => rfl)
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  push_cast
  rfl

private def pair3 {r s : ℕ} (S : Finset (Fin (r + s))) (p : sub1 S × ((sub2 S)ᶜ : Finset (Fin s))) : satakePairs S :=
  ⟨(Fin.castAdd s p.1.1, Fin.natAdd r p.2.1), (Finset.mem_filter.1 p.1.2).2, by simpa [sub2] using p.2.2, by
    have := p.1.1.2
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega⟩

private theorem bij3 {r s : ℕ} (S : Finset (Fin (r + s))) :
    Function.Bijective (Sum.elim (Sum.elim (pair1 S) (pair2 S)) (pair3 S)) := by
  constructor
  · rintro ((⟨⟨a, b⟩, h⟩ | ⟨⟨a, b⟩, h⟩) | ⟨⟨a, h⟩, ⟨b, h'⟩⟩) ((⟨⟨c, d⟩, k⟩ | ⟨⟨c, d⟩, k⟩) | ⟨⟨c, k⟩, ⟨d, k'⟩⟩) H <;>
      simp only [Sum.elim_inl, Sum.elim_inr, pair1, pair2, pair3, Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff,
        Fin.val_castAdd, Fin.val_natAdd, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at H ⊢ <;>
      omega
  · rintro ⟨⟨a, b⟩, h1, h2, h3⟩
    induction a using Fin.addCases with
    | left a =>
      induction b using Fin.addCases with
      | left b =>
        exact ⟨.inl (.inl ⟨(a, b), by simpa [sub1] using h1, by simpa [sub1] using h2, h3⟩), rfl⟩
      | right b =>
        exact ⟨.inr (⟨a, by simpa [sub1] using h1⟩, ⟨b, by simpa [sub2] using h2⟩), rfl⟩
    | right a =>
      induction b using Fin.addCases with
      | left b =>
        exfalso
        simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at h3
        omega
      | right b =>
        refine ⟨.inl (.inr ⟨(a, b), by simpa [sub2] using h1, by simpa [sub2] using h2, ?_⟩), rfl⟩
        simp only [Fin.lt_def, Fin.val_natAdd] at h3 ⊢
        omega

theorem UpperTheory.V.Cj.S.sumInner :
    UpperTheory.V.Cj.S.SumInner := by
  intro r s R _ S g
  rw [sum_three (pair1 S) (pair2 S) (pair3 S) (bij3 S) g]
  simp only [Fintype.card_prod, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SuppAdd
section
namespace UpperTheory.V.Cj.S

theorem suppAdd : SuppAdd := by
  intro E _ _ _ r s k l m₁ m₂ B₁ B₂ h₁ h₂
  obtain ⟨ι, _, n, π, μ, hk, hn, hs, hi, hm, hB⟩ := h₁
  obtain ⟨κ, _, n', π', μ', hk', hn', hs', hi', hm', hB'⟩ := h₂
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim n n', fun i => Sum.rec (fun i => π i) (fun i => π' i) i, Sum.elim μ μ',
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_sum]
    exact Nat.add_le_add hk hk'
  · rintro (i | i)
    · exact hn i
    · exact hn' i
  · rw [Fintype.sum_sum_type, ← hs, ← hs']
    rfl
  · rintro (i | i) t
    · exact hi i t
    · exact hi' i t
  · intro t
    rw [Fintype.sum_sum_type]
    show ∑ i, μ i t + ∑ i, μ' i t = m₁ t + m₂ t
    rw [hm t, hm' t]
  · filter_upwards [hB, hB'] with w hw hw'
    obtain ⟨C, hC, hCs⟩ := hw
    obtain ⟨C', hC', hCs'⟩ := hw'
    refine ⟨Sum.elim C C', ?_, ?_⟩
    · rintro (i | i)
      · exact hC i
      · exact hC' i
    · rw [Fintype.sum_sum_type]
      show ∑ i, C i + ∑ i, C' i = B₁ w + B₂ w
      rw [hCs, hCs']

end UpperTheory.V.Cj.S
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SuppTwist
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem sum_map {ι α : Type} [Fintype ι] (f : α → α) (C : ι → Multiset α) :
    ∑ i, (C i).map f = (∑ i, C i).map f := by
  rw [← Multiset.coe_mapAddMonoidHom, map_sum]

private theorem sat_twist {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CG E a) {w : Pl E}
    {B : Multiset ℂˣ} (h : π.HasSat w B) {χ : HChar E} (hχ : χ.UnrAt w) :
    (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

theorem UpperTheory.V.Cj.S.suppTwist :
    UpperTheory.V.Cj.S.SuppTwist := by
  rintro E _ _ _ a k m B ⟨ι, _, n, π, μ, hk, hn, ha, hμ, hm, hB⟩ x ν hν
  refine ⟨ι, inferInstance, n, fun i => (π i).twist ν, fun i t => (μ i t).map (· + (x : ℂ)), hk, hn, ha,
    fun i t => ?_, fun t => ?_, hB.mono ?_⟩
  · have h := (hμ i t).twist ν
    rwa [(InfType.expo_of_infType E ν).2.1 x hν t] at h
  · rw [sum_map, hm]
  · rintro w ⟨C, hC, hs⟩
    exact ⟨fun i => (C i).map (· * ν.val w), fun i => sat_twist _ (hC i) (hν.1 w), by rw [sum_map, hs]⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.TauSat
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem stable_eq {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) (S : Submodule ℂ V)
    (hS : ∀ g, ∀ x ∈ S, ρ g x ∈ S) : S = ⊥ ∨ S = ⊤ := by
  let P : Subrepresentation ρ := ⟨S, fun g x hx => hS g x hx⟩
  exact (hi.eq_bot_or_eq_top P).imp (fun e => congrArg Subrepresentation.toSubmodule e)
    fun e => congrArg Subrepresentation.toSubmodule e

private theorem rank_le_aleph0_of_irred [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    {ρ : Representation ℂ G V} (hs : GlobalTheory.PRep.IsSmooth ρ) (hi : ρ.IsIrreducible) {v : V} (hv : v ≠ 0) :
    Module.rank ℂ V ≤ Cardinal.aleph0 := by
  rw [← rank_top]
  refine GlobalTheory.CompanionTheory.SatAe.rank_le_of_simple (⊤ : Submodule ℂ V) (fun g : G => ρ g)
    ((Submodule.ne_bot_iff _).2 ⟨v, trivial, hv⟩) (fun W _ hW => stable_eq hi W hW) fun x _ => ?_
  exact ⟨_, GlobalTheory.CompanionTheory.SatAe.countable_orbit ρ x (hs x), fun _ _ => trivial, fun g => Submodule.subset_span ⟨g, rfl⟩⟩

end

private theorem biSimple {E : Type} [Field E] [NumberField E] {a : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin a) (Af E)) V} (hi : ρ.IsIrreducible) (w : Pl E) :
    GlobalTheory.CompanionTheory.SatAe.IsBiSimple (locOf ρ w) := by
  intro S h1 h2
  refine stable_eq hi S fun k x hx => ?_
  let g := Matrix.GeneralLinearGroup.map (pLoc E w) k
  have h3 := h2 (ρ (k * (locGL E a w g)⁻¹)) (fun g' => by
    change ρ _ * ρ _ = ρ _ * ρ _
    rw [← map_mul, ← map_mul, LocSph.comm_locGL w _ (by rw [map_mul, map_inv, pLoc_locGL, mul_inv_cancel])])
    _ (h1 g x hx)
  have h4 : ρ (k * (locGL E a w g)⁻¹) (locOf ρ w g x) = ρ k x := by
    change ρ _ (ρ _ x) = ρ k x
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  rwa [h4] at h3

theorem UpperTheory.V.Cj.S.tauSat :
    UpperTheory.V.Cj.S.TauSat := by
  intro E _ _ _ a τ v hv
  haveI := GlobalTheory.CompanionTheory.SatAe.secondCountable_GL (E := E) (a := a)
  rcases τ with @⟨V, _, _, ρ, hs, hi⟩
  change V at v
  have hr := rank_le_aleph0_of_irred hs hi hv
  filter_upwards [LocSph.eventually_mem ((hs v).mem_nhds (by simp))] with w hw
  have hfix : v ∈ fixed (locOf ρ w) (KGL w a) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_
    obtain ⟨g, rfl⟩ := hk
    exact hw g
  have hsl : GlobalTheory.PRep.IsSmooth (locOf ρ w) := fun x => (hs x).preimage (CuspSub.continuous_locGL w)
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_of_scalar (fun h hh => GlobalTheory.CompanionTheory.SatAe.exists_scalar hsl
    (SatCompare.isOpen_isCompact_KGL w a).2 (Final.GLintComm E w a) (Final.HeckeCommGL E w a ℂ) (biSimple hi w) hr h hh)
    ((Submodule.ne_bot_iff _).2 ⟨v, hfix, hv⟩)
  exact ⟨B, hB, hB.2 v hfix hv⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.TypesComm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem UpperTheory.V.Cj.S.exists_interp {Y : Type} (V : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ V] :
    ∃ (n : ℕ) (b : Fin n → V) (c : Fin n → Y →₀ ℂ),
      ∀ f ∈ V, ∀ y, f y = ∑ i, (b i).1 y * (c i).sum fun z t => t * f z := by
  classical
  let ev : Y → (V →ₗ[ℂ] ℂ) := fun y => (LinearMap.proj y).comp V.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_contra h
    apply hz
    ext y
    by_contra hy
    exact h ⟨ev y, ⟨y, rfl⟩, hy⟩
  let b := Module.finBasis ℂ V
  have hc : ∀ i, ∃ c : Y →₀ ℂ, (c.sum fun z t => t • ev z) = b.coord i := fun i =>
    Finsupp.mem_span_range_iff_exists_finsupp.1 (hspan ▸ Submodule.mem_top)
  choose c hc using hc
  refine ⟨_, b, c, fun f hf y => ?_⟩
  have h := congrArg (ev y) (b.sum_repr ⟨f, hf⟩)
  rw [map_sum] at h
  simp only [map_smul] at h
  refine h.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  have h2 : b.repr ⟨f, hf⟩ i = (c i).sum fun z t => t * f z := by
    rw [← b.coord_apply, ← hc i, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply]
    rfl
  rw [h2, smul_eq_mul, mul_comm]
  rfl

theorem UpperTheory.V.Cj.S.typesComm :
    UpperTheory.V.Cj.S.TypesComm := by
  intro E _ _ _ a V hV T hT φ hφ g
  obtain ⟨n, b, c, hc⟩ := UpperTheory.V.Cj.S.exists_interp V
  let R : archCompact E a → Module.End ℂ (Sm E a) := fun k => cptRep E a ((Cm.cptEq E a).symm k)
  have hR : ∀ (k : archCompact E a) (ψ : Sm E a) (x), (R k ψ).1 x = ψ.1 (x * infEmb E a k.1) := by
    intro k ψ x
    obtain ⟨k, rfl⟩ := (Cm.cptEq E a).surjective k
    simp only [R]
    rw [MulEquiv.symm_apply_apply, Cm.infEmb_cptEq]
    rfl
  have hTR : ∀ (k : archCompact E a) (ψ : Sm E a), T (R k ψ) = R k (T ψ) := fun k ψ =>
    LinearMap.congr_fun (hT _).eq ψ
  have hev : ∀ (k : archCompact E a) (ψ : Sm E a) (x),
      (∑ i, (b i).1 k • ∑ z ∈ (c i).support, c i z • R z ψ : Sm E a).1 x =
        ∑ i, (b i).1 k * (c i).sum fun z t => t * ψ.1 (x * infEmb E a z.1) := by
    intro k ψ x
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR, Finsupp.sum]
  have h1 : ∀ k : archCompact E a, R k φ = ∑ i, (b i).1 k • ∑ z ∈ (c i).support, c i z • R z φ := by
    intro k
    refine Subtype.ext (funext fun x => ?_)
    rw [hR, hev]
    exact hc _ (hφ x) k
  have h2 : (fun k : archCompact E a => (T φ).1 (g * infEmb E a k.1)) =
      ∑ i, ((c i).sum fun z t => t * (T φ).1 (g * infEmb E a z.1)) • (b i).1 := by
    funext k
    rw [← hR k, ← hTR, h1 k]
    simp only [map_sum, map_smul, hTR]
    rw [hev]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [h2]
  exact V.sum_mem fun i _ => V.smul_mem _ (b i).2
end

