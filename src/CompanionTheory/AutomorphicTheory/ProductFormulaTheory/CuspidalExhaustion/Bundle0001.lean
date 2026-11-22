import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtDefs
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace CompanionTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev nxt (Δ : Segment k) : IrrGL k := Δ.first.nu ((Δ.len : ℕ) : ℂ)

variable (k)

def ShlP : Prop :=
  ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (Δ : Fin h → Segment k), (∀ i, IsLSeg (Δ i) (x i).rep) →
    ∀ w : List (IrrGL k), (∀ c ∈ w, c.IsCusp) → Wd (prodIrr x hd) w → InShW (Finset.univ.val.map Δ) w

def DecLP : Prop := ∀ (Γ : Segment k) (σ : IrrGL k), EmbL σ (decW Γ) → IsLSeg Γ σ.rep

end CompanionTheory.Exh

end
end

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.MidDefs
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace CompanionTheory.Exh

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

end CompanionTheory.Exh

end
end

-- bundled from CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.NotAboveTransGenSelf
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace CompanionTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem linkP : LinkP k := by
  intro ρ hρ Δ H
  obtain ⟨σ, hσ, c, d, c', d', h, h', e1, rfl⟩ := H.exists_eq_icc
  have hfirst : ρ = σ.nu (c : ℂ) := by
    have := congrArg Segment.first e1
    simpa [Segment.single, Segment.icc] using this
  have hlen : (1 : ℕ) = (d - c + 1).toNat := by
    have := congrArg Segment.len e1
    simpa [Segment.single, Segment.icc] using this
  have hdc : d = c := by omega
  rw [e1, Segment.linked_icc] at H
  have hinj : ∀ a b : ℤ, a = b → σ.nu (a : ℂ) = σ.nu (b : ℂ) := fun a b e => by rw [e]
  have hF : (Segment.icc σ hσ c' d' h').first = σ.nu (c' : ℂ) := rfl
  have hL : (Segment.icc σ hσ c' d' h').len = (d' - c' + 1).toNat := rfl
  rcases H with ⟨h1, h2, -⟩ | ⟨h1, h2, h3⟩
  · left
    rw [hF, hfirst, IrrGL.nu_nu, show (c : ℂ) + 1 = ((c + 1 : ℤ) : ℂ) by push_cast; ring]
    exact hinj _ _ (by omega)
  · right
    have ht : (((d' - c' + 1).toNat : ℕ) : ℂ) = ((d' - c' + 1 : ℤ) : ℂ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [hF, hL, hfirst, IrrGL.nu_nu, ht, show (c' : ℂ) + ((d' - c' + 1 : ℤ) : ℂ) = ((c' + (d' - c' + 1) : ℤ) : ℂ) by push_cast; ring]
    exact hinj _ _ (by omega)

private def Above (a b : IrrGL k) : Prop := 0 < a.1 ∧ ∃ j : ℕ, 0 < j ∧ a = b.nu (j : ℕ)

private theorem above_transGen {a b : IrrGL k} (H : Relation.TransGen Above a b) :
    0 < a.1 ∧ ∃ j : ℕ, 0 < j ∧ a = b.nu (j : ℕ) := by
  induction H with
  | single H => exact H
  | tail _ H ih =>
    obtain ⟨ha, i, hi, e⟩ := ih
    obtain ⟨-, j, hj, e'⟩ := H
    exact ⟨ha, i + j, by omega, by rw [e, e', IrrGL.nu_nu, Nat.cast_add, add_comm]⟩

private theorem not_above_transGen_self (a : IrrGL k) : ¬ Relation.TransGen Above a a := fun H => by
  obtain ⟨ha, j, hj, e⟩ := above_transGen H
  have : a.nu ((0 : ℕ) : ℂ) = a.nu ((j : ℕ) : ℂ) := by simpa using e
  exact hj.ne ((IrrGL.nu_natCast_inj ha).1 this)

theorem minP : MinP k := by
  intro l hl hc
  obtain ⟨l', hl', hp⟩ := exists_list_pairwise_not_rel (not_above_transGen_self (k := k)) (l : Multiset (IrrGL k))
  have hmem : ∀ x, x ∈ l' ↔ x ∈ l := fun x => by
    rw [← Multiset.mem_coe, hl', Multiset.mem_coe]
  cases l' with
  | nil =>
    exfalso
    apply hl
    have := congrArg Multiset.card hl'
    simpa using this.symm
  | cons ρ t =>
    have hρ : ρ ∈ l := (hmem ρ).1 (List.mem_cons_self ..)
    refine ⟨ρ, hρ, fun ρ' hρ' j hj e => ?_⟩
    have hA : Above ρ ρ' := ⟨(hc ρ hρ).1, j, hj, e⟩
    rcases List.mem_cons.1 ((hmem ρ').2 hρ') with h0 | ht
    · exact not_above_transGen_self ρ (.single (h0 ▸ hA))
    · exact (List.pairwise_cons.1 hp).1 ρ' ht hA

end CompanionTheory.Exh

end
end

