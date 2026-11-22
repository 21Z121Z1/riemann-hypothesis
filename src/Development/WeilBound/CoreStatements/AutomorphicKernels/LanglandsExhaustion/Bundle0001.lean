import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.CuspEmbP
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtDefs
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev nxt (Δ : Segment k) : IrrGL k := Δ.first.nu ((Δ.len : ℕ) : ℂ)

variable (k)

def ShlP : Prop :=
  ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (Δ : Fin h → Segment k), (∀ i, IsLSeg (Δ i) (x i).rep) →
    ∀ w : List (IrrGL k), (∀ c ∈ w, c.IsCusp) → Wd (prodIrr x hd) w → InShW (Finset.univ.val.map Δ) w

def DecLP : Prop := ∀ (Γ : Segment k) (σ : IrrGL k), EmbL σ (decW Γ) → IsLSeg Γ σ.rep

end PositivityTheory.Exh

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidDefs
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace PositivityTheory.Exh

section Tensor

variable {G H V V' W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W]

def extL {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'} (f : ρ.IntertwiningMap ρ')
    (σ : Representation ℂ H W) : (extTensor ρ σ).IntertwiningMap (extTensor ρ' σ) where
  toLinearMap := f.toLinearMap.rTensor W
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v w
    simp [f.isIntertwining]

def extR (σ : Representation ℂ H W) {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') : (extTensor σ ρ).IntertwiningMap (extTensor σ ρ') where
  toLinearMap := f.toLinearMap.lTensor W
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v w
    simp [f.isIntertwining]

end Tensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Ind

variable {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def ind₂Map (e : a ⊕ b ≃ n) {ρ : Representation ℂ (GL a k × GL b k) V}
    {ρ' : Representation ℂ (GL a k × GL b k) V'} (f : ρ.IntertwiningMap ρ') :
    (ind₂ e ρ).IntertwiningMap (ind₂ e ρ') :=
  parIndMap (two e) (compMap f _)

end Ind

variable {nA nB m m' N : ℕ} {VA VB V V' : Type} [AddCommGroup VA] [Module ℂ VA] [AddCommGroup VB] [Module ℂ VB]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def T3 (h2 : m + nB = m') (h1 : nA + m' = N) (PA : Representation ℂ (GL (Fin nA) k) VA)
    (PB : Representation ℂ (GL (Fin nB) k) VB) (τ : Representation ℂ (GL (Fin m) k) V) :=
  ind₂ (stdSum h1) (extTensor PA (ind₂ (stdSum h2) (extTensor τ PB)))

def tripleProductMap (h2 : m + nB = m') (h1 : nA + m' = N) (PA : Representation ℂ (GL (Fin nA) k) VA)
    (PB : Representation ℂ (GL (Fin nB) k) VB) {τ : Representation ℂ (GL (Fin m) k) V}
    {τ' : Representation ℂ (GL (Fin m) k) V'} (f : τ.IntertwiningMap τ') :
    (T3 h2 h1 PA PB τ).IntertwiningMap (T3 h2 h1 PA PB τ') :=
  ind₂Map _ (extR PA (ind₂Map _ (extL f PB)))

end PositivityTheory.Exh

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.NotAboveTransGenSelf
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem linkP : LinkP k := by
  intro ρ hρ Δ hl
  obtain ⟨σ, hσ, c, d, c', d', h1, h2, e1, e2⟩ := hl.exists_eq_icc
  have hlen : (Segment.single ρ hρ).len = 1 := rfl
  have hfst : (Segment.single ρ hρ).first = ρ := Segment.first_ofFirst _ _ _ _
  rw [e1, e2, Segment.linked_icc] at hl
  rw [e1] at hlen hfst
  simp only [Segment.icc, Segment.len_ofFirst, Segment.first_ofFirst] at hlen hfst
  have hdc : d = c := by omega
  subst hdc e2 hfst
  simp only [Segment.icc, Segment.len_ofFirst, Segment.first_ofFirst, IrrGL.nu_nu]
  rcases hl with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
  · left
    obtain rfl : c' = d + 1 := by omega
    congr 1
    push_cast
    ring
  · right
    obtain rfl : d = d' + 1 := by omega
    rw [show (((d' - c' + 1).toNat : ℕ) : ℂ) = ((d' - c' + 1 : ℤ) : ℂ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]
    congr 1
    push_cast
    ring

private def Above (a b : IrrGL k) : Prop := 0 < a.1 ∧ ∃ j : ℕ, 0 < j ∧ a = b.nu (j : ℕ)

private theorem eq_zero_of_nu_eq_of_isCusp {ρ : IrrGL k} (hρ : ρ.IsCusp) (n : ℤ) (h : ρ.nu (n : ℂ) = ρ) : n = 0 := by
  have hsub : (Segment.icc ρ hρ n n le_rfl).carrier ⊆ (Segment.icc ρ hρ 0 0 le_rfl).carrier := by
    intro x hx
    rw [Segment.mem_icc] at hx ⊢
    obtain ⟨a, ha1, ha2, rfl⟩ := hx
    obtain rfl : a = n := le_antisymm ha2 ha1
    refine ⟨0, le_rfl, le_rfl, ?_⟩
    rw [h]
    simp [IrrGL.nu_zero]
  have := Segment.icc_subset_icc.mp hsub
  omega

theorem minP : MinP k := by
  classical
  intro l hl hc
  obtain ⟨ρ₀, h₀⟩ := List.exists_mem_of_ne_nil l hl
  set f : ℕ → IrrGL k := fun m => ρ₀.nu (-(m : ℂ)) with hf
  have hinj : Function.Injective f := by
    intro m m' hmm
    have h1 : (f m).nu (m : ℂ) = (f m').nu (m : ℂ) := by rw [hmm]
    simp only [hf, IrrGL.nu_nu, neg_add_cancel, IrrGL.nu_zero] at h1
    have h2 : ρ₀.nu (((m : ℤ) - m' : ℤ) : ℂ) = ρ₀ := by
      conv_rhs => rw [h1]
      congr 1
      push_cast
      ring
    have := eq_zero_of_nu_eq_of_isCusp (hc ρ₀ h₀) _ h2
    omega
  have hfin : {m : ℕ | f m ∈ l}.Finite := by
    refine ((l.toFinset.finite_toSet).preimage hinj.injOn).subset ?_
    intro m hm
    simpa using hm
  have h0 : (0 : ℕ) ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    show f 0 ∈ l
    simpa [hf, IrrGL.nu_zero] using h₀
  set M := hfin.toFinset.max' ⟨0, h0⟩ with hMdef
  have hM : f M ∈ l := by
    have hm := hfin.toFinset.max'_mem ⟨0, h0⟩
    rw [Set.Finite.mem_toFinset] at hm
    exact hm
  refine ⟨f M, hM, fun ρ' hρ' j hj heq => ?_⟩
  have hρ'eq : ρ' = f (M + j) := by
    have h3 : (f M).nu (-(j : ℂ)) = ρ' := by
      rw [heq, IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]
    rw [← h3]
    simp only [hf, IrrGL.nu_nu]
    congr 1
    push_cast
    ring
  have hmem : M + j ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    show f (M + j) ∈ l
    rw [← hρ'eq]
    exact hρ'
  have := hfin.toFinset.le_max' _ hmem
  omega

end PositivityTheory.Exh

end
end

