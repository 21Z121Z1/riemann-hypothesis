import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
section
noncomputable section

namespace GlobalTheory.Published

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

def DepthZeroJacquetInjective : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ)
    (e : (Σ a, Fin (d a)) ≃ Fin n) (π : Irr k n) (v : π.V),
    v ∈ fixed π.π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))) →
    (Submodule.Quotient.mk v : Jacquet π.π (unipRad k e)) = 0 → v = 0

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
section
noncomputable section

namespace GlobalTheory.Published

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

def MoyPrasadJacquetIso : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ)
    (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsAdmissible π →
    Set.BijOn (fun v : V => (Submodule.Quotient.mk v : Jacquet π (unipRad k e)))
      (fixed π (KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))))
      (fixed (jacU e π) ((KOne k (Fin n) ⊔ (unipRad k e ⊓ KO k (Fin n))).comap (leviEmb k e)))

theorem mapsTo_fixed_jacU {k : Type} [Field k] {n s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (H : Subgroup (GL (Fin n) k)) :
    Set.MapsTo (fun v : V => (Submodule.Quotient.mk v : Jacquet π (unipRad k e)))
      (fixed π H) (fixed (jacU e π) (H.comap (leviEmb k e))) := by
  intro v hv h
  have h1 : π (leviEmb k e h) v = v := by simpa using hv ⟨_, h.2⟩
  have h2 : jacU e π h (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π (leviEmb k e h) v) := rfl
  simp only [h2, h1, MonoidHom.one_apply, Units.val_one, one_smul]

theorem moyPrasadJacquetIso_trivial (k : Type) [Field k] [TopologicalSpace k] {n s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) (H : Subgroup (GL (Fin n) k)) :
    IsAdmissible (Representation.trivial ℂ (GL (Fin n) k) ℂ) ∧
    fixed (Representation.trivial ℂ (GL (Fin n) k) ℂ) H = ⊤ ∧
    Set.BijOn (fun v : ℂ =>
        (Submodule.Quotient.mk v : Jacquet (Representation.trivial ℂ (GL (Fin n) k) ℂ) (unipRad k e)))
      (fixed (Representation.trivial ℂ (GL (Fin n) k) ℂ) H)
      (fixed (jacU e (Representation.trivial ℂ (GL (Fin n) k) ℂ)) (H.comap (leviEmb k e))) := by
  have htop : fixed (Representation.trivial ℂ (GL (Fin n) k) ℂ) H = ⊤ :=
    eq_top_iff.2 fun v _ h => by simp
  have hbot : twKer (Representation.trivial ℂ (GL (Fin n) k) ℂ) (unipRad k e) 1 = ⊥ := by
    refine Submodule.span_eq_bot.2 ?_
    rintro w ⟨u, v, rfl⟩
    simp
  refine ⟨⟨fun v => by simp, fun K _ _ => inferInstance⟩, htop, mapsTo_fixed_jacU e _ H, ?_, ?_⟩
  · intro v _ w _ h
    have := (Submodule.Quotient.eq _).1 h
    rwa [hbot, Submodule.mem_bot, sub_eq_zero] at this
  · intro x _
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨v, by rw [htop]; trivial, rfl⟩

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TotallyDisjointProductIrreducible
section
noncomputable section

namespace GlobalTheory.Published

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

def TotallyDisjointProductIrreducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t s s' : ℕ)
    (π₁ : Irr k r) (π₂ : Irr k t) (d : Fin s → ℕ) (d' : Fin s' → ℕ) (σ : ∀ a, Irr k (d a)) (σ' : ∀ b, Irr k (d' b)),
    IsCuspSupport π₁.π d (fun a => (σ a).π) → IsCuspSupport π₂.π d' (fun b => (σ' b).π) →
    (∀ a b (h : d a = d' b) (j : ℤ), |j| ≤ 1 →
      ¬ Nonempty ((h ▸ σ a : Irr k (d' b)).π.Equiv (twist (σ' b).π (detChar (Fin (d' b)) (absPow k (j : ℂ)))))) →
    (prod₂ π₁.π π₂.π).IsIrreducible

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
section
noncomputable section

namespace GlobalTheory.Published

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

def UnlinkedProductIrreducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t s s' : ℕ)
    (π₁ : Irr k r) (π₂ : Irr k t) (d : Fin s → ℕ) (d' : Fin s' → ℕ) (σ : ∀ a, Irr k (d a)) (σ' : ∀ b, Irr k (d' b)),
    IsCuspSupport π₁.π d (fun a => (σ a).π) → IsCuspSupport π₂.π d' (fun b => (σ' b).π) →
    (∀ a b (h : d a = d' b) (α : ℂˣ),
      ¬ Nonempty ((h ▸ σ a : Irr k (d' b)).π.Equiv (twist (σ' b).π (detChar (Fin (d' b)) (unrChar k α))))) →
    (prod₂ π₁.π π₂.π).IsIrreducible

end GlobalTheory.Published

end
end

