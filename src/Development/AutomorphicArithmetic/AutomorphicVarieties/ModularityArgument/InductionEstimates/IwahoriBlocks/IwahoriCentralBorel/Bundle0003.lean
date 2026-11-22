import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensIso
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

section SlopeTestRemainingChoices

variable {P : Type} [Group P] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V]
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]

private theorem tensIso_stable {G : Type} [Group G] (ρ : Representation ℂ G V) (h : ρ.IsIrreducible)
    (N : Submodule ℂ V) (hN : ∀ g, ∀ v ∈ N, ρ g v ∈ N) : N = ⊥ ∨ N = ⊤ := by
  rcases h.eq_bot_or_eq_top (⟨N, fun g v hv => hN g v hv⟩ : Subrepresentation ρ) with h1 | h1
  · left; exact congrArg Subrepresentation.toSubmodule h1
  · right; exact congrArg Subrepresentation.toSubmodule h1

private theorem tensIso_dens {κ : Type} (ρ : Representation ℂ P V) (σ : P → Y →ₗ[ℂ] Y)
    (hρ : ρ.IsIrreducible) (hS : Schur ρ) (b : κ → V →ₗ[ℂ] Y) (hb : LinearIndependent ℂ b)
    (hbe : ∀ j p v, b j (ρ p v) = σ p (b j v)) (s : Finset κ) :
    ∀ v : κ → V, ∑ j ∈ s, b j (v j) = 0 → ∀ j ∈ s, v j = 0 := by
  induction s using Finset.induction_on with
  | empty => intro v _ j hj; simp at hj
  | insert a s ha ih =>
    let N : Submodule ℂ V :=
      { carrier := {u | ∃ v : κ → V, b a u + ∑ j ∈ s, b j (v j) = 0}
        add_mem' := by
          rintro u u' ⟨v, hv⟩ ⟨v', hv'⟩
          refine ⟨v + v', ?_⟩
          simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
          rw [add_add_add_comm, hv, hv', add_zero]
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro c u ⟨v, hv⟩
          refine ⟨c • v, ?_⟩
          simp only [Pi.smul_apply, map_smul]
          rw [← Finset.smul_sum, ← smul_add, hv, smul_zero] }
    have hmove : ∀ (p : P) (u : V) (v : κ → V), b a u + ∑ j ∈ s, b j (v j) = 0 →
        b a (ρ p u) + ∑ j ∈ s, b j (ρ p (v j)) = 0 := by
      intro p u v hv
      simp only [hbe]
      rw [← map_sum, ← map_add, hv, map_zero]
    have huniq : ∀ (u : V) (v v' : κ → V), b a u + ∑ j ∈ s, b j (v j) = 0 →
        b a u + ∑ j ∈ s, b j (v' j) = 0 → ∀ j ∈ s, v j = v' j := by
      intro u v v' h1 h2 j hj
      have := ih (v - v') (by
        simp only [Pi.sub_apply, map_sub, Finset.sum_sub_distrib]
        rw [sub_eq_zero]
        exact add_left_cancel (h1.trans h2.symm)) j hj
      exact sub_eq_zero.mp this
    rcases tensIso_stable ρ hρ N (by
      rintro p u ⟨v, hv⟩
      exact ⟨fun j => ρ p (v j), hmove p u v hv⟩) with hN | hN
    · intro v hv
      rw [Finset.sum_insert ha] at hv
      have h0 : v a = 0 := by
        have : v a ∈ N := ⟨v, hv⟩
        rw [hN] at this
        exact this
      rw [h0, map_zero, zero_add] at hv
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact h0
      · exact ih v hv j hj
    · exfalso
      have hall : ∀ u : V, ∃ v : κ → V, b a u + ∑ j ∈ s, b j (v j) = 0 := by
        intro u
        have : u ∈ N := by rw [hN]; trivial
        exact this
      choose g hg using hall
      have hc : ∀ j : κ, ∃ c : ℂ, j ∈ s → ∀ u, g u j = c • u := by
        intro j
        by_cases hj : j ∈ s
        · let T : V →ₗ[ℂ] V :=
            { toFun := fun u => g u j
              map_add' := fun u u' => huniq (u + u') _ (g u + g u') (hg _) (by
                simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
                rw [add_add_add_comm, hg, hg, add_zero]) j hj
              map_smul' := fun c u => huniq (c • u) _ (c • g u) (hg _) (by
                simp only [Pi.smul_apply, map_smul]
                rw [← Finset.smul_sum, ← smul_add, hg, smul_zero]) j hj }
          obtain ⟨c, hc⟩ := hS T (fun p u =>
            huniq (ρ p u) _ (fun j => ρ p (g u j)) (hg _) (hmove p u _ (hg u)) j hj)
          exact ⟨c, fun _ => hc⟩
        · exact ⟨0, fun h => absurd h hj⟩
      choose c hc using hc
      have hz : ∑ j ∈ insert a s, (Function.update c a 1 j) • b j = 0 := by
        rw [Finset.sum_insert ha]
        ext u
        simp only [Function.update_self, one_smul, LinearMap.add_apply, LinearMap.sum_apply,
          LinearMap.smul_apply, LinearMap.zero_apply]
        refine Eq.trans ?_ (hg u)
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hne : j ≠ a := fun h => ha (h ▸ hj)
        rw [Function.update_of_ne hne, hc j hj, map_smul]
      have := linearIndependent_iff'.mp hb _ _ hz a (Finset.mem_insert_self a s)
      simp at this

private def tensIso_B (ρ : Representation ℂ P V) (y : Representation ℂ (P × Γ) Y) : Submodule ℂ (V →ₗ[ℂ] Y) where
  carrier := {f | ∀ p v, f (ρ p v) = y (p, 1) (f v)}
  add_mem' := by
    intro a b ha hb p v
    simp [ha p v, hb p v]
  zero_mem' := by intro p v; simp
  smul_mem' := by
    intro c a ha p v
    simp [ha p v]

private theorem tensIso_mul (y : Representation ℂ (P × Γ) Y) (a b : P × Γ) (x : Y) :
    y a (y b x) = y (a * b) x := by
  rw [map_mul]; rfl

private def tensIso_m (ρ : Representation ℂ P V) (y : Representation ℂ (P × Γ) Y) :
    Representation ℂ Γ (tensIso_B ρ y) where
  toFun c :=
    { toFun := fun b => ⟨(y (1, c)).comp b.1, fun p v => by
        have hb := b.2 p v
        simp only [LinearMap.comp_apply, hb, tensIso_mul, Prod.mk_mul_mk, one_mul, mul_one]⟩
      map_add' := fun a b => Subtype.ext (by ext v; simp)
      map_smul' := fun t b => Subtype.ext (by ext v; simp) }
  map_one' := by
    ext b v
    have : ((1 : P), (1 : Γ)) = 1 := rfl
    simp [this]
  map_mul' c c' := by
    ext b v
    simp [tensIso_mul]

private theorem tensIso_span (ρ : Representation ℂ P V) (y : Representation ℂ (P × Γ) Y)
    (hy : y.IsIrreducible) (B' : Submodule ℂ (tensIso_B ρ y))
    (hB : ∀ c, ∀ b ∈ B', tensIso_m ρ y c b ∈ B') (hne : B' ≠ ⊥) :
    Submodule.span ℂ {x | ∃ b ∈ B', ∃ v, x = b.1 v} = ⊤ := by
  refine (tensIso_stable y hy _ ?_).resolve_left ?_
  · rintro ⟨p, c⟩ x hx
    have : Submodule.span ℂ {x | ∃ b ∈ B', ∃ v, x = b.1 v} ≤
        (Submodule.span ℂ {x | ∃ b ∈ B', ∃ v, x = b.1 v}).comap (y (p, c)) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, hb, v, rfl⟩
      refine Submodule.subset_span ⟨_, hB c b hb, ρ p v, ?_⟩
      show _ = y (1, c) (b.1 (ρ p v))
      rw [b.2 p v, tensIso_mul]
      simp
    exact this hx
  · intro h
    apply hne
    rw [eq_bot_iff]
    intro b hb
    have : b = 0 := by
      ext v
      have hx : b.1 v ∈ Submodule.span ℂ {x | ∃ b ∈ B', ∃ v, x = b.1 v} :=
        Submodule.subset_span ⟨b, hb, v, rfl⟩
      rw [h] at hx
      exact hx
    exact this

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.tensIso :
    ∀ {P : Type} [Group P] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] {Y : Type} [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ P V) (y : Representation ℂ (P × Γ) Y) (f : V →ₗ[ℂ] Y), ρ.IsIrreducible → Schur ρ →
      y.IsIrreducible → f ≠ 0 → (∀ p v, f (ρ p v) = y (p, 1) (f v)) →
      ∃ (B : Type) (_ : AddCommGroup B) (_ : Module ℂ B) (m : Representation ℂ Γ B) (e : V ⊗[ℂ] B ≃ₗ[ℂ] Y), m.IsIrreducible ∧
        ∀ p c x, e (extTensor ρ m (p, c) x) = y (p, c) (e x) := by
  intro P _ Γ _ V _ _ Y _ _ ρ y f hρ hS hy hf hfe
  let ev : V ⊗[ℂ] tensIso_B ρ y →ₗ[ℂ] Y :=
    TensorProduct.lift ((tensIso_B ρ y).subtype.flip)
  have hev : ∀ v b, ev (v ⊗ₜ b) = b.1 v := fun v b => rfl
  have hf' : (⟨f, hfe⟩ : tensIso_B ρ y) ≠ 0 := fun h => hf (congrArg Subtype.val h)
  have hnt : Nontrivial (tensIso_B ρ y) := nontrivial_of_ne _ _ hf'
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    let β := Module.Basis.ofVectorSpace ℂ (tensIso_B ρ y)
    obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right β x
    have hli : LinearIndependent ℂ (fun j => (β j).1) :=
      β.linearIndependent.map' (tensIso_B ρ y).subtype (Submodule.ker_subtype _)
    have h0 := tensIso_dens ρ (fun p => y (p, 1)) hρ hS _ hli (fun j => (β j).2) c.support c (by
      rw [← hx, Finsupp.sum, map_sum]
      rfl)
    refine Finset.sum_eq_zero fun j hj => ?_
    show c j ⊗ₜ[ℂ] β j = 0
    rw [h0 j hj, TensorProduct.zero_tmul]
  have hsurj : Function.Surjective ev := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← tensIso_span ρ y hy ⊤ (fun _ _ _ => trivial) top_ne_bot,
      Submodule.span_le]
    rintro _ ⟨b, -, v, rfl⟩
    exact ⟨v ⊗ₜ b, rfl⟩
  let e := LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩
  have he : ∀ v b, e (v ⊗ₜ b) = b.1 v := fun v b => rfl
  refine ⟨tensIso_B ρ y, inferInstance, inferInstance, tensIso_m ρ y, e, ?_, ?_⟩
  · have hn : Nontrivial (Subrepresentation (tensIso_m ρ y)) :=
      ⟨⊥, ⊤, fun h => (bot_ne_top : (⊥ : Submodule ℂ (tensIso_B ρ y)) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule h)⟩
    refine ⟨fun Q => ?_⟩
    by_cases hQ : Q.toSubmodule = ⊥
    · left
      exact Subrepresentation.toSubmodule_injective hQ
    · right
      apply Subrepresentation.toSubmodule_injective
      show Q.toSubmodule = ⊤
      rw [eq_top_iff]
      intro b _
      by_contra hb
      obtain ⟨φ, hφ, hφ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hb inferInstance
      have hsp := tensIso_span ρ y hy Q.toSubmodule (fun c b hb => Q.apply_mem_toSubmodule c hb) hQ
      let ψ : Y →ₗ[ℂ] V :=
        (TensorProduct.rid ℂ V).toLinearMap ∘ₗ (LinearMap.lTensor V φ) ∘ₗ e.symm.toLinearMap
      have hψ : ∀ (v : V) (b : tensIso_B ρ y), ψ (b.1 v) = φ b • v := by
        intro v b
        rw [← he]
        simp [ψ]
      have hker : (⊤ : Submodule ℂ Y) ≤ LinearMap.ker ψ := by
        rw [← hsp, Submodule.span_le]
        rintro _ ⟨b', hb', v, rfl⟩
        have : φ b' = 0 := by
          have : φ b' ∈ Q.toSubmodule.map φ := ⟨b', hb', rfl⟩
          rw [hφ'] at this
          exact this
        show ψ _ = 0
        rw [hψ, this, zero_smul]
      apply hf
      ext v
      have h1 : ψ (b.1 v) = 0 := hker trivial
      rw [hψ] at h1
      rw [(smul_eq_zero.mp h1).resolve_left hφ]
      simp
  · intro p c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul v b =>
      have : extTensor ρ (tensIso_m ρ y) (p, c) (v ⊗ₜ b) = ρ p v ⊗ₜ tensIso_m ρ y c b := rfl
      rw [this, he, he]
      show y (1, c) (b.1 (ρ p v)) = _
      rw [b.2 p v, tensIso_mul]
      simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensLaws
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem coef_mem {A B ι : Type} (X : Submodule ℂ (A → ℂ)) (s : Finset ι) (φ : ι → A → ℂ) (ψ : ι → B → ℂ)
    (hψ : LinearIndependent ℂ ψ) (h : ∀ b, (fun a => ∑ i ∈ s, φ i a * ψ i b) ∈ X) : ∀ i ∈ s, φ i ∈ X := by
  intro i hi
  by_contra hn
  obtain ⟨f, hf, hX⟩ := Submodule.exists_le_ker_of_notMem hn
  have h0 : ∑ j ∈ s, f (φ j) • ψ j = 0 := by
    funext b
    have h1 : f (fun a => ∑ i ∈ s, φ i a * ψ i b) = 0 := hX (h b)
    have h2 : (fun a => ∑ i ∈ s, φ i a * ψ i b) = ∑ i ∈ s, ψ i b • φ i := by
      funext a
      simp [Finset.sum_apply, mul_comm]
    rw [h2, map_sum] at h1
    simpa [Finset.sum_apply, mul_comm] using h1
  exact hf (linearIndependent_iff'.1 hψ s _ h0 i hi)

private noncomputable def prodMap {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) :
    X₁ ⊗[ℂ] X₂ →ₗ[ℂ] (A × B → ℂ) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun φ ψ x => φ.1 x.1 * ψ.1 x.2)
    (fun _ _ _ => by funext x; simp [add_mul]) (fun _ _ _ => by funext x; simp [mul_assoc])
    (fun _ _ _ => by funext x; simp [mul_add]) (fun _ _ _ => by funext x; simp [mul_left_comm]))

private theorem prodMap_tmul {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) (φ : X₁) (ψ : X₂) :
    prodMap X₁ X₂ (φ ⊗ₜ ψ) = fun x => φ.1 x.1 * ψ.1 x.2 := by
  simp only [prodMap, TensorProduct.lift.tmul, LinearMap.mk₂_apply]

private theorem prodMap_inj {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) :
    Function.Injective (prodMap X₁ X₂) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  let β := Module.Basis.ofVectorSpace ℂ X₂
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right β t
  have hβ : LinearIndependent ℂ (fun i => (β i).1) :=
    β.linearIndependent.map' X₂.subtype (Submodule.ker_subtype _)
  have hc := coef_mem (⊥ : Submodule ℂ (A → ℂ)) c.support (fun i => (c i).1) (fun i => (β i).1) hβ (by
    intro b
    rw [Submodule.mem_bot]
    funext a
    have := congrFun ht (a, b)
    simpa [Finsupp.sum, map_sum, prodMap_tmul, Finset.sum_apply] using this)
  refine Finset.sum_eq_zero fun i hi => ?_
  have : c i = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 (hc i hi))
  simp [this]

private theorem prodMap_range {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)) :
    LinearMap.range (prodMap X₁ X₂) = tensFn X₁ X₂ := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul φ ψ => exact Submodule.subset_span ⟨φ.1, φ.2, ψ.1, ψ.2, prodMap_tmul X₁ X₂ φ ψ⟩
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, hφ, ψ, hψ, rfl⟩
    exact ⟨⟨φ, hφ⟩ ⊗ₜ ⟨ψ, hψ⟩, prodMap_tmul X₁ X₂ _ _⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.tensLaws :
    ∀ {A B : Type} (X₁ : Submodule ℂ (A → ℂ)) (X₂ : Submodule ℂ (B → ℂ)), (∃ e : X₁ ⊗[ℂ] X₂ ≃ₗ[ℂ] tensFn X₁ X₂, ∀ φ ψ x, (e (φ ⊗ₜ ψ)).1 x = φ.1 x.1 * ψ.1 x.2) ∧
      ∀ (F : A × B → ℂ) (d : ℕ) (φ : Fin d → A → ℂ) (ψ : Fin d → B → ℂ), (∀ x, F x = ∑ i, φ i x.1 * ψ i x.2) →
        (∀ b, (fun a => F (a, b)) ∈ X₁) → (∀ a, (fun b => F (a, b)) ∈ X₂) → F ∈ tensFn X₁ X₂ := by
  intro A B X₁ X₂
  refine ⟨⟨(LinearEquiv.ofInjective _ (prodMap_inj X₁ X₂)).trans (LinearEquiv.ofEq _ _ (prodMap_range X₁ X₂)), ?_⟩, ?_⟩
  · intro φ ψ x
    exact congrFun (prodMap_tmul X₁ X₂ φ ψ) x
  · intro F d φ ψ hF h₁ h₂
    let W : Submodule ℂ (B → ℂ) := X₂ ⊓ Submodule.span ℂ (Set.range ψ)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range ψ)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range ψ)
    haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le inf_le_right
    have hW : ∀ a, (fun b => F (a, b)) ∈ W := by
      intro a
      refine ⟨h₂ a, ?_⟩
      have : (fun b => F (a, b)) = ∑ i, φ i a • ψ i := by
        funext b
        simp [hF, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    let β := Module.finBasis ℂ W
    have hβ : LinearIndependent ℂ (fun i => (β i).1) :=
      β.linearIndependent.map' W.subtype (Submodule.ker_subtype _)
    have hrep : ∀ a b, F (a, b) = ∑ i, β.repr ⟨_, hW a⟩ i * (β i).1 b := by
      intro a b
      have := congrFun (congrArg Subtype.val (β.sum_repr ⟨_, hW a⟩)) b
      rw [Submodule.coe_sum, Finset.sum_apply] at this
      exact this.symm
    have hc := coef_mem X₁ Finset.univ (fun i a => β.repr ⟨_, hW a⟩ i) (fun i => (β i).1) hβ (by
      intro b
      have : (fun a => ∑ i, β.repr ⟨_, hW a⟩ i * (β i).1 b) = fun a => F (a, b) := by
        funext a
        exact (hrep a b).symm
      rw [this]
      exact h₁ b)
    have : F = ∑ i, fun x : A × B => β.repr ⟨_, hW x.1⟩ i * (β i).1 x.2 := by
      funext x
      rw [Finset.sum_apply]
      exact hrep x.1 x.2
    rw [this]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.subset_span ⟨_, hc i (Finset.mem_univ i), _, (β i).2.1, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.TensSimple
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem tens_sep {V B : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup B] [Module ℂ B]
    (z : V ⊗[ℂ] B)
    (h : ∀ φ : Module.Dual ℂ V, TensorProduct.lid ℂ B (LinearMap.rTensor B φ z) = 0) : z = 0 := by
  let b := Module.Basis.ofVectorSpace ℂ V
  let F := TensorProduct.equivFinsuppOfBasisLeft (N := B) b
  have key : ∀ (j : _) (y : V ⊗[ℂ] B),
      F y j = TensorProduct.lid ℂ B (LinearMap.rTensor B (b.coord j) y) := by
    intro j y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w => simp [F, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply F.injective
  rw [map_zero]
  ext j
  rw [key, h]
  simp

private theorem comm_ext {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (X : Representation ℂ G V) (T : Representation ℂ H W)
    (g : H × G) (z : V ⊗[ℂ] W) :
    TensorProduct.comm ℂ V W (extTensor X T (g.2, g.1) z) =
      extTensor T X g (TensorProduct.comm ℂ V W z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v w => simp
  | add x y hx hy => simp only [map_add, hx, hy]

private noncomputable def swapSub {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (X : Representation ℂ G V) (T : Representation ℂ H W)
    (S : Subrepresentation (extTensor X T)) : Subrepresentation (extTensor T X) where
  toSubmodule := S.toSubmodule.map (TensorProduct.comm ℂ V W).toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨extTensor X T (g.2, g.1) z, S.apply_mem_toSubmodule _ hz, comm_ext X T g z⟩

private theorem swapSub_swapSub {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (X : Representation ℂ G V) (T : Representation ℂ H W)
    (S : Subrepresentation (extTensor X T)) : swapSub T X (swapSub X T S) = S := by
  apply Subrepresentation.toSubmodule_injective
  ext z
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hz
    exact ⟨TensorProduct.comm ℂ V W z, ⟨z, hz, rfl⟩, by simp⟩

private noncomputable def swapIso {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (X : Representation ℂ G V) (T : Representation ℂ H W) :
    Subrepresentation (extTensor X T) ≃o Subrepresentation (extTensor T X) where
  toFun := swapSub X T
  invFun := swapSub T X
  left_inv := swapSub_swapSub X T
  right_inv := swapSub_swapSub T X
  map_rel_iff' := by
    intro S S'
    constructor
    · intro h z hz
      obtain ⟨y, hy, e⟩ := h (show TensorProduct.comm ℂ V W z ∈ (swapSub X T S).toSubmodule from
        ⟨z, hz, rfl⟩)
      have e' : y = z := (TensorProduct.comm ℂ V W).injective e
      exact e' ▸ hy
    · rintro h _ ⟨z, hz, rfl⟩
      exact ⟨z, h hz, rfl⟩

private theorem schur_ext {G Γ V B : Type} [Group G] [Group Γ] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup B] [Module ℂ B] [Nontrivial B] (σ : Representation ℂ G V)
    (m : Representation ℂ Γ B) (hσ : Schur σ) (hm : Schur m) : Schur (extTensor σ m) := by
  intro T hT
  obtain ⟨b₀, hb₀⟩ := exists_ne (0 : B)
  obtain ⟨β, hβ⟩ : ∃ β : Module.Dual ℂ B, β b₀ = 1 := by
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ B, φ b₀ ≠ 0 := by
      by_contra! h
      exact hb₀ ((Module.forall_dual_apply_eq_zero_iff ℂ b₀).1 h)
    exact ⟨(φ b₀)⁻¹ • φ, by simp [hφ]⟩
  let L : Module.Dual ℂ V → (V ⊗[ℂ] B →ₗ[ℂ] B) := fun φ =>
    (TensorProduct.lid ℂ B).toLinearMap ∘ₗ LinearMap.rTensor B φ
  let R : V ⊗[ℂ] B →ₗ[ℂ] V := (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V β
  have hLt : ∀ φ x y, L φ (x ⊗ₜ y) = φ x • y := fun φ x y => by simp [L]
  have hRt : ∀ x y, R (x ⊗ₜ y) = β y • x := fun x y => by simp [R]
  have hL : ∀ φ c z, L φ (extTensor σ m (1, c) z) = m c (L φ z) := by
    intro φ c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hLt]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hR : ∀ g z, R (extTensor σ m (g, 1) z) = σ g (R z) := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hRt]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hLR : ∀ (φ : Module.Dual ℂ V) z, φ (R z) = β (L φ z) := by
    intro φ z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hLt, hRt, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  let S : V →ₗ[ℂ] V := R ∘ₗ T ∘ₗ (TensorProduct.mk ℂ V B).flip b₀
  have hS : ∀ v, S v = R (T (v ⊗ₜ b₀)) := fun v => rfl
  have hpure : ∀ v b, T (v ⊗ₜ b) = S v ⊗ₜ b := by
    intro v b
    rw [← sub_eq_zero]
    apply tens_sep
    intro φ
    obtain ⟨c, hc⟩ := hm (L φ ∘ₗ T ∘ₗ TensorProduct.mk ℂ V B v) (by
      intro c y
      have h1 : v ⊗ₜ[ℂ] m c y = extTensor σ m (1, c) (v ⊗ₜ y) := by simp
      simp only [LinearMap.comp_apply, TensorProduct.mk_apply]
      rw [h1, hT, hL])
    have hc' : ∀ y, L φ (T (v ⊗ₜ y)) = c • y := hc
    have hφS : φ (S v) = c := by
      rw [hS, hLR, hc', map_smul, hβ, smul_eq_mul, mul_one]
    change L φ (T (v ⊗ₜ b) - S v ⊗ₜ b) = 0
    rw [map_sub, hc', hLt, hφS, sub_self]
  obtain ⟨c, hc⟩ := hσ S (by
    intro g v
    have h1 : σ g v ⊗ₜ[ℂ] b₀ = extTensor σ m (g, 1) (v ⊗ₜ b₀) := by simp
    rw [hS, h1, hT, hR, ← hS])
  refine ⟨c, fun z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [hpure, hc, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.tensSimple :
    ∀ {G : Type} [Group G] {Γ : Type} [Group Γ] {V : Type} [AddCommGroup V] [Module ℂ V] {B : Type} [AddCommGroup B] [Module ℂ B] (σ : Representation ℂ G V) (m : Representation ℂ Γ B), σ.IsIrreducible → Schur σ → m.IsIrreducible →
      (extTensor σ m).IsIrreducible ∧ (Schur m → Schur (extTensor σ m)) := by
  intro G _ Γ _ V _ _ B _ _ σ m hσ hs hm
  haveI : Nontrivial B := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hm
  have hsc : ∀ A : Module.End ℂ V, (∀ g, A * σ g = σ g * A) → ∃ c : ℂ, A = c • 1 := by
    intro A hA
    obtain ⟨c, hc⟩ := hs A fun g v => congrArg (fun F : Module.End ℂ V => F v) (hA g)
    exact ⟨c, LinearMap.ext fun v => by simpa using hc v⟩
  refine ⟨?_, schur_ext σ m hs⟩
  have h1 : IsSimpleOrder (Subrepresentation (extTensor m σ)) :=
    (GlobalTheory.ExtTensorSub.orderIso m σ hσ hsc).isSimpleOrder_iff.1 hm
  exact (swapIso σ m).isSimpleOrder_iff.2 h1
end

