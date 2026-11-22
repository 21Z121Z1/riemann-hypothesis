import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.Bundle0001

-- bundled from ReciprocityTheory.L2DbarEstimates.MinimalSolutions.HormanderLemma
section
namespace ReciprocityTheory.L2DbarEstimates

open scoped InnerProductSpace

section WeakAdjLemmas

variable {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

theorem weakAdj_zero (ι : E →ₗ[ℂ] H₁) (t : E →ₗ[ℂ] H₂) : WeakAdj ι t 0 0 := by
  intro g
  simp

theorem WeakAdj.add {ι : E →ₗ[ℂ] H₁} {t : E →ₗ[ℂ] H₂} {f f' : H₂} {w w' : H₁}
    (h : WeakAdj ι t f w) (h' : WeakAdj ι t f' w') : WeakAdj ι t (f + f') (w + w') := by
  intro g
  rw [inner_add_right, inner_add_right, h g, h' g]

theorem WeakAdj.smul {ι : E →ₗ[ℂ] H₁} {t : E →ₗ[ℂ] H₂} {f : H₂} {w : H₁}
    (h : WeakAdj ι t f w) (a : ℂ) : WeakAdj ι t (a • f) (a • w) := by
  intro g
  rw [inner_smul_right, inner_smul_right, h g]

theorem WeakAdj.sub {ι : E →ₗ[ℂ] H₁} {t : E →ₗ[ℂ] H₂} {f f' : H₂} {w w' : H₁}
    (h : WeakAdj ι t f w) (h' : WeakAdj ι t f' w') : WeakAdj ι t (f - f') (w - w') := by
  intro g
  rw [inner_sub_right, inner_sub_right, h g, h' g]

def weakAdjGraph (ι : E →ₗ[ℂ] H₁) (t : E →ₗ[ℂ] H₂) : Submodule ℂ (H₂ × H₁) where
  carrier := {p | WeakAdj ι t p.1 p.2}
  add_mem' := fun ha hb => WeakAdj.add ha hb
  zero_mem' := weakAdj_zero ι t
  smul_mem' := fun a _ hp => WeakAdj.smul hp a

end WeakAdjLemmas

theorem split (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] :
    SplitStatement E H₁ H₂ := by
  intro ι t K hK hrange f w hfw
  haveI : CompleteSpace K := hK.completeSpace_coe
  obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := K.exists_add_mem_mem_orthogonal f
  have h2 : WeakAdj ι t f₂ 0 := by
    intro g
    rw [inner_zero_right]
    exact Submodule.inner_right_of_mem_orthogonal (hrange (LinearMap.mem_range_self t g)) hf₂
  refine ⟨f₁, f₂, rfl, hf₁, hf₂, ?_, h2⟩
  have h1 := hfw.sub h2
  simpa using h1

theorem hormanderLemma (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] :
    HormanderLemmaStatement E H₁ H₂ := by
  intro ι t K hK hrange v A hA hv hbound
  let G : Submodule ℂ (H₂ × H₁) := weakAdjGraph ι t ⊓ K.comap (LinearMap.fst ℂ H₂ H₁)
  have hG : ∀ p : G, WeakAdj ι t (p : H₂ × H₁).1 (p : H₂ × H₁).2 ∧ (p : H₂ × H₁).1 ∈ K :=
    fun p => ⟨(Submodule.mem_inf.mp p.2).1, (Submodule.mem_inf.mp p.2).2⟩
  obtain ⟨u, -, hu, huv⟩ := rieszOnRange G H₁ ((LinearMap.snd ℂ H₂ H₁).comp G.subtype)
    ((innerₛₗ ℂ v).comp ((LinearMap.fst ℂ H₂ H₁).comp G.subtype)) A hA (by
      intro p
      obtain ⟨h1, h2⟩ := hG p
      simpa using hbound _ h2 _ h1)
  refine ⟨u, hu, fun f w hfw => ?_⟩
  obtain ⟨f₁, f₂, rfl, hf₁, hf₂, hw1, -⟩ := split E H₁ H₂ ι t K hK hrange f w hfw
  have hmem : ((f₁, w) : H₂ × H₁) ∈ G := Submodule.mem_inf.mpr ⟨hw1, hf₁⟩
  have h3 := huv ⟨(f₁, w), hmem⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearMap.snd_apply, LinearMap.fst_apply] at h3
  rw [inner_add_right, Submodule.inner_right_of_mem_orthogonal hv hf₂, add_zero]
  exact h3

end ReciprocityTheory.L2DbarEstimates
end

-- bundled from ReciprocityTheory.L2DbarEstimates.MinimalSolutions.OntoWithBoundTop
section
namespace ReciprocityTheory.L2DbarEstimates

open scoped InnerProductSpace

theorem ontoWithBound (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] :
    OntoWithBoundStatement E H₁ H₂ := by
  intro G Gs θ Q c hc hadj hbd f hf
  let θ' : (Q × E) →ₗ[ℂ] H₁ := Gs ∘ₗ Q.subtype ∘ₗ LinearMap.fst ℂ Q E + θ ∘ₗ LinearMap.snd ℂ Q E
  let ℓ : (Q × E) →ₗ[ℂ] ℂ := (innerₛₗ ℂ f) ∘ₗ Q.subtype ∘ₗ LinearMap.fst ℂ Q E
  have hθ' : ∀ x : Q × E, θ' x = Gs x.1 + θ x.2 := fun x => rfl
  have hℓ : ∀ x : Q × E, ℓ x = ⟪f, (x.1 : H₂)⟫_ℂ := fun x => rfl
  have hA : 0 ≤ ‖f‖ ^ 2 / c := by positivity
  have hbound : ∀ x : Q × E, ‖ℓ x‖ ^ 2 ≤ ‖f‖ ^ 2 / c * ‖θ' x‖ ^ 2 := by
    intro x
    rw [hℓ, hθ']
    have h1 : ‖⟪f, (x.1 : H₂)⟫_ℂ‖ ≤ ‖f‖ * ‖(x.1 : H₂)‖ := norm_inner_le_norm _ _
    have h2 := hbd x.1 x.1.2 x.2
    have h0 : 0 ≤ ‖⟪f, (x.1 : H₂)⟫_ℂ‖ := norm_nonneg _
    calc ‖⟪f, (x.1 : H₂)⟫_ℂ‖ ^ 2 ≤ (‖f‖ * ‖(x.1 : H₂)‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = ‖f‖ ^ 2 / c * (c * ‖(x.1 : H₂)‖ ^ 2) := by
        rw [mul_pow, div_mul_eq_mul_div, eq_div_iff hc.ne']
        ring
      _ ≤ ‖f‖ ^ 2 / c * ‖Gs x.1 + θ x.2‖ ^ 2 := mul_le_mul_of_nonneg_left h2 hA
  obtain ⟨h, -, hnorm, hinner⟩ := rieszOnRange (Q × E) H₁ θ' ℓ _ hA hbound
  refine ⟨h, ?_, ?_, ?_⟩
  · intro u hu
    have hh : ⟪h, Gs u⟫_ℂ = ⟪f, u⟫_ℂ := by simpa [hθ', hℓ] using hinner (⟨u, hu⟩, 0)
    rw [← hadj u hu h, ← inner_conj_symm, hh, inner_conj_symm]
  · intro e
    simpa [hθ', hℓ] using hinner (0, e)
  · rw [le_div_iff₀ hc] at hnorm
    linarith [hnorm]

end ReciprocityTheory.L2DbarEstimates
end

