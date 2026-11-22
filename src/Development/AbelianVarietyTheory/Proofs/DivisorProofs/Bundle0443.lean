import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0397
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalNumberZeroOfHorizontal
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ Finset

noncomputable section

namespace GlobalTheory.EZ.HTot

theorem idc_self (n : ℕ) : idc n n = 𝟙 _ := by
  ext j
  simp only [idc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min n (j : ℕ) = (j : ℕ)
  have : (j : ℕ) < n + 1 := j.isLt
  omega

theorem backc_zero : backc 0 0 0 = 𝟙 _ := by
  ext j
  simp only [backc, clampHom, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk]
  change min 0 (0 + (j : ℕ)) = (j : ℕ)
  have : (j : ℕ) < 0 + 1 := j.isLt
  omega

theorem bop_id (a b : ℕ) : bop (𝟙 (SimplexCategory.mk a)) (𝟙 (SimplexCategory.mk b)) = 𝟙 (bo a b) := rfl

theorem idO_self (a b : ℕ) : idO a b a b = 𝟙 (bo a b) := by
  rw [idO, if_pos ⟨rfl, rfl⟩, idc_self, idc_self, bop_id]

theorem idO_ne {a b c d : ℕ} (h : ¬ (a = c ∧ b = d)) : idO a b c d = 0 := by
  rw [idO, if_neg h]

theorem awO_zero : awO 0 0 0 = 𝟙 (bo 0 0) := by
  rw [awO, if_pos rfl, idc_self, backc_zero, bop_id]

theorem sum_idO_comp {T : BOp} (k a b : ℕ) (h : a + b = k) (g : ∀ p q : ℕ, bo p q ⟶ T) :
    ∑ y ∈ antidiagonal k, idO a b y.1 y.2 ≫ g y.1 y.2 = g a b := by
  rw [Finset.sum_eq_single (a, b)]
  · simp [idO_self]
  · rintro ⟨p, q⟩ _ hne
    rw [idO_ne, Limits.zero_comp]
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  · intro hn
    exact absurd (mem_antidiagonal.2 h) hn

theorem sum_comp_idO {S : BOp} (k c d : ℕ) (h : c + d = k) (f : ∀ p q : ℕ, S ⟶ bo p q) :
    ∑ x ∈ antidiagonal k, f x.1 x.2 ≫ idO x.1 x.2 c d = f c d := by
  rw [Finset.sum_eq_single (c, d)]
  · simp [idO_self]
  · rintro ⟨p, q⟩ _ hne
    rw [idO_ne, Limits.comp_zero]
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  · intro hn
    exact absurd (mem_antidiagonal.2 h) hn

theorem dT_comp_dT (a b c d : ℕ) (h : c + d + 2 = a + b) :
    ∑ x ∈ antidiagonal (c + d + 1), dT a b x.1 x.2 ≫ dT x.1 x.2 c d = 0 :=
  GlobalTheory.T.sum_antidiagonal_dT_comp_dT_eq_zero a b c d h

theorem acyclic (a b k : ℕ) (hk : 1 ≤ k) (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b')
    (hz : ∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) :
    ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b',
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d :=
  GlobalTheory.T.bisimplicialOperatorChains_acyclic_positiveDegree a b k hk z hz

theorem exists_fill : ∃ H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b'),
    ∀ a b k (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'), 1 ≤ k →
      (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), H a b k z x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
  have : ∀ a b k (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'), ∃ w : ∀ a' b' : ℕ, bo a b ⟶ bo a' b', 1 ≤ k →
      (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), w x.1 x.2 ≫ dT x.1 x.2 c d = z c d := by
    intro a b k z
    by_cases hk : 1 ≤ k
    · by_cases hz : ∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0
      · obtain ⟨w, hw⟩ := acyclic a b k hk z hz
        exact ⟨w, fun _ _ => hw⟩
      · exact ⟨0, fun _ h => absurd h hz⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose H hH using this
  exact ⟨H, hH⟩

noncomputable def kRec (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b')) (n : ℕ) :
    ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b' :=
  Nat.rec (motive := fun _ => ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b') (fun _ _ _ _ => 0)
    (fun n K a b => H a b (n + 1) (fun a' b' => G a b (n + 1) ≫ awO (n + 1) a' b' - idO a b a' b' -
      ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ K x.1 x.2 a' b')) n

theorem kRec_zero (G : ∀ a b n : ℕ, bo a b ⟶ bo n n)
    (H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b')) (a b a' b' : ℕ) :
    kRec G H 0 a b a' b' = 0 := rfl

end GlobalTheory.EZ.HTot

namespace GlobalTheory.EZ.HTot

theorem kRec_spec (G : ∀ a b n : ℕ, bo a b ⟶ bo n n) (hG0 : G 0 0 0 = 𝟙 (bo 0 0))
    (hGd : ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n)
    (H : ∀ a b k : ℕ, (∀ a' b' : ℕ, bo a b ⟶ bo a' b') → (∀ a' b' : ℕ, bo a b ⟶ bo a' b'))
    (hH : ∀ a b k (z : ∀ a' b' : ℕ, bo a b ⟶ bo a' b'), 1 ≤ k →
      (∀ c d : ℕ, c + d + 1 = k → ∑ x ∈ antidiagonal k, z x.1 x.2 ≫ dT x.1 x.2 c d = 0) →
      ∀ c d : ℕ, c + d = k → ∑ x ∈ antidiagonal (k + 1), H a b k z x.1 x.2 ≫ dT x.1 x.2 c d = z c d) :
    ∀ n a b : ℕ, a + b = n → ∀ a' b' : ℕ, a' + b' = n →
      G a b n ≫ awO n a' b' = idO a b a' b' +
        ∑ x ∈ antidiagonal (n + 1), kRec G H n a b x.1 x.2 ≫ dT x.1 x.2 a' b' +
        ∑ x ∈ antidiagonal (n - 1), dT a b x.1 x.2 ≫ kRec G H (n - 1) x.1 x.2 a' b' := by
  intro n
  induction n with
  | zero =>
    intro a b hab a' b' hab'
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    obtain ⟨rfl, rfl⟩ : a' = 0 ∧ b' = 0 := by omega
    simp [kRec_zero, hG0, awO_zero, idO_self]
  | succ n ih =>
    intro a b hab a' b' hab'
    set E : ∀ a' b' : ℕ, bo a b ⟶ bo a' b' := fun a' b' => G a b (n + 1) ≫ awO (n + 1) a' b' - idO a b a' b' -
      ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 a' b' with hE
    have hcyc : ∀ c d : ℕ, c + d + 1 = n + 1 → ∑ y ∈ antidiagonal (n + 1), E y.1 y.2 ≫ dT y.1 y.2 c d = 0 := by
      intro c d hcd
      have h1 : ∑ y ∈ antidiagonal (n + 1), (G a b (n + 1) ≫ awO (n + 1) y.1 y.2) ≫ dT y.1 y.2 c d =
          ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n ≫ awO n c d := by
        simp only [Category.assoc, ← Preadditive.comp_sum]
        rw [← GlobalTheory.T.dD_comp_awO_eq_sum_awO_comp_dT n c d (by omega), ← Category.assoc, hGd a b n hab, Preadditive.sum_comp]
        simp only [Category.assoc]
      have h2 : ∑ y ∈ antidiagonal (n + 1), idO a b y.1 y.2 ≫ dT y.1 y.2 c d = dT a b c d :=
        sum_idO_comp (n + 1) a b hab (fun p q => dT p q c d)
      have key : ∀ x ∈ antidiagonal n, ∑ y ∈ antidiagonal (n + 1), kRec G H n x.1 x.2 y.1 y.2 ≫ dT y.1 y.2 c d =
          G x.1 x.2 n ≫ awO n c d - idO x.1 x.2 c d -
            ∑ z ∈ antidiagonal (n - 1), dT x.1 x.2 z.1 z.2 ≫ kRec G H (n - 1) z.1 z.2 c d := by
        intro x hx
        rw [ih x.1 x.2 (mem_antidiagonal.1 hx) c d (by omega)]
        abel
      have h4 : ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ idO x.1 x.2 c d = dT a b c d :=
        sum_comp_idO n c d (by omega) (fun p q => dT a b p q)
      have h5 : ∑ x ∈ antidiagonal n, ∑ z ∈ antidiagonal (n - 1),
          dT a b x.1 x.2 ≫ dT x.1 x.2 z.1 z.2 ≫ kRec G H (n - 1) z.1 z.2 c d = 0 := by
        rcases n with _ | m
        · simp [kRec_zero]
        · rw [Nat.add_sub_cancel, Finset.sum_comm]
          refine Finset.sum_eq_zero (fun z hz => ?_)
          have hz' := mem_antidiagonal.1 hz
          simp only [← Category.assoc]
          rw [← Preadditive.sum_comp]
          have h0 := dT_comp_dT a b z.1 z.2 (by omega)
          rw [show z.1 + z.2 + 1 = m + 1 by omega] at h0
          rw [h0, Limits.zero_comp]
      have h3 : ∑ y ∈ antidiagonal (n + 1),
          (∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 y.1 y.2) ≫ dT y.1 y.2 c d =
          ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n ≫ awO n c d - dT a b c d - 0 := by
        have e1 : ∑ y ∈ antidiagonal (n + 1),
            (∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 y.1 y.2) ≫ dT y.1 y.2 c d =
            ∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫
              ∑ y ∈ antidiagonal (n + 1), kRec G H n x.1 x.2 y.1 y.2 ≫ dT y.1 y.2 c d := by
          simp only [Preadditive.sum_comp, Category.assoc, Preadditive.comp_sum]
          exact Finset.sum_comm
        rw [e1, Finset.sum_congr rfl (fun x hx => by rw [key x hx])]
        simp only [Preadditive.comp_sub, Finset.sum_sub_distrib, Preadditive.comp_sum]
        rw [h4, h5]
      calc ∑ y ∈ antidiagonal (n + 1), E y.1 y.2 ≫ dT y.1 y.2 c d
          = ∑ y ∈ antidiagonal (n + 1), (G a b (n + 1) ≫ awO (n + 1) y.1 y.2) ≫ dT y.1 y.2 c d -
            ∑ y ∈ antidiagonal (n + 1), idO a b y.1 y.2 ≫ dT y.1 y.2 c d -
            ∑ y ∈ antidiagonal (n + 1),
              (∑ x ∈ antidiagonal n, dT a b x.1 x.2 ≫ kRec G H n x.1 x.2 y.1 y.2) ≫ dT y.1 y.2 c d := by
            simp only [hE, Preadditive.sub_comp, Finset.sum_sub_distrib]
        _ = 0 := by rw [h1, h2, h3]; abel
    have hk : kRec G H (n + 1) a b = H a b (n + 1) E := rfl
    rw [Nat.add_sub_cancel, hk, hH a b (n + 1) E (by omega) hcyc a' b' hab']
    simp only [hE]
    abel

theorem htot : ∀ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) →
    (∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n) →
    ∃ K : ∀ a b a' b' : ℕ, bo a b ⟶ bo a' b', ∀ a b a' b' : ℕ, a' + b' = a + b →
      G a b (a + b) ≫ awO (a + b) a' b' = idO a b a' b' +
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b + 1), K a b x.1 x.2 ≫ dT x.1 x.2 a' b' +
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (a + b - 1), dT a b x.1 x.2 ≫ K x.1 x.2 a' b' := by
  intro G hG0 hGd
  obtain ⟨H, hH⟩ := exists_fill
  refine ⟨fun a b => kRec G H (a + b) a b, ?_⟩
  intro a b a' b' h
  rw [kRec_spec G hG0 hGd H hH (a + b) a b rfl a' b' h]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  show _ = dT a b x.1 x.2 ≫ kRec G H (x.1 + x.2) x.1 x.2 a' b'
  rw [mem_antidiagonal.1 hx]

end GlobalTheory.EZ.HTot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepBijectionSchwartz
section
open Matrix

namespace GlobalTheory.SchurHeisReindex

variable {k : Type} [Field k] [TopologicalSpace k] {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]

noncomputable def eL (k : Type) [Field k] (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] :
    Matrix (Fin n) (Fin (Fintype.card β)) k ≃ₗ[k] Matrix (Fin n) β k :=
  Matrix.reindexLinearEquiv k k (Equiv.refl (Fin n)) (Fintype.equivFin β).symm

theorem eL_apply (C : Matrix (Fin n) (Fin (Fintype.card β)) k) (i : Fin n) (b : β) :
    eL k n β C i b = C i (Fintype.equivFin β b) := by
  simp [eL, reindexLinearEquiv_apply, reindex_apply, submatrix_apply]

theorem eL_symm_apply (D : Matrix (Fin n) β k) (i : Fin n) (j : Fin (Fintype.card β)) :
    (eL k n β).symm D i j = D i ((Fintype.equivFin β).symm j) := by
  simp [eL, reindexLinearEquiv_symm, reindexLinearEquiv_apply, reindex_apply, submatrix_apply]

theorem continuous_eL : Continuous (eL k n β) := by
  refine continuous_pi fun i => continuous_pi fun b => ?_
  simp only [eL_apply]
  exact (continuous_apply _).comp (continuous_apply i)

theorem continuous_eL_symm : Continuous (eL k n β).symm := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [eL_symm_apply]
  exact (continuous_apply _).comp (continuous_apply i)

noncomputable def eH (k : Type) [Field k] [TopologicalSpace k] (n : ℕ) (β : Type) [Fintype β] [DecidableEq β] :
    Matrix (Fin n) (Fin (Fintype.card β)) k ≃ₜ Matrix (Fin n) β k where
  toEquiv := (eL k n β).toEquiv
  continuous_toFun := continuous_eL
  continuous_invFun := continuous_eL_symm

theorem comp_mem_SB' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : Y ≃ₜ X) {f : X → ℂ}
    (hf : f ∈ GlobalTheory.WeilM.SB X) : (f ∘ e) ∈ GlobalTheory.WeilM.SB Y :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

end GlobalTheory.SchurHeisReindex

open GlobalTheory.SchurHeisReindex in

theorem GlobalTheory.schur_heisenberg_linearModel_fintype : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {β : Type} [Fintype β] [DecidableEq β] {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) β k → ℂ)) (ι₂ : Xt → Matrix (Fin n) β k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) β k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) β k → Xt → Xt) (Mu : (Matrix (Fin n) β k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  intro k _ _ _ _ n β _ _ Xt _ _ V ψ0 hψc hψ1 ι₁ ι₂ hbij hlin Tr Mu hTr hMu
  set e := eL k n β with he
  let ι₁' : Xt →ₗ[ℂ] (Matrix (Fin n) (Fin (Fintype.card β)) k → ℂ) := LinearMap.funLeft ℂ ℂ e ∘ₗ ι₁
  have hι₁' : ∀ x, ι₁' x = ι₁ x ∘ e := fun x => rfl
  let ι₂' : Xt → Matrix (Fin n) (Fin (Fintype.card β)) k → ℂ := fun x => ι₂ x ∘ e
  have hsurj : Function.Surjective e := e.surjective
  have hbij' : Set.BijOn ι₁' (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin (Fintype.card β)) k) : Set _) := by
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun f hf => ?_⟩
    · rw [hι₁']
      exact comp_mem_SB' (eH k n β) (hbij.1 hx)
    · apply hbij.2.1 hx hy
      rw [hι₁', hι₁'] at hxy
      funext Z
      obtain ⟨Y, rfl⟩ := hsurj Z
      exact congrFun hxy Y
    · have hf' : f ∘ (eH k n β).symm ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) β k) := comp_mem_SB' (eH k n β).symm hf
      obtain ⟨x, hx, hxf⟩ := hbij.2.2 hf'
      refine ⟨x, hx, ?_⟩
      rw [hι₁', hxf]
      funext Y
      show f ((eH k n β).symm (e Y)) = f Y
      exact congrArg f ((eL k n β).symm_apply_apply Y)
  have hlin' : ∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂' (c • x + y) = c • ι₂' x + ι₂' y := by
    intro x hx y hy c
    funext Y
    simp [ι₂', hlin x hx y hy c]
  have hadd : ∀ Y C, e (Y + C) = e Y + e C := fun Y C => map_add e Y C
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat V ψ0 hψc hψ1 ι₁' ι₂' hbij' hlin'
    (fun C => Tr (e C)) (fun l => Mu (l ∘ₗ e.symm.toLinearMap))
    (fun C x hx => by
      obtain ⟨h1, h2, h3⟩ := hTr (e C) x hx
      refine ⟨h1, ?_, ?_⟩
      · funext Y; simp [hι₁', h2, hadd]
      · funext Y; simp [ι₂', h3, hadd])
    (fun l x hx => by
      obtain ⟨h1, h2, h3⟩ := hMu (l ∘ₗ e.symm.toLinearMap) x hx
      refine ⟨h1, ?_, ?_⟩
      · funext Y; simp [hι₁', h2]
      · funext Y; simp [ι₂', h3])
  refine ⟨c, fun x hx => ?_⟩
  funext Z
  obtain ⟨Y, rfl⟩ := hsurj Z
  have := congrFun (hc x hx) Y
  simpa [ι₂', hι₁'] using this
end

