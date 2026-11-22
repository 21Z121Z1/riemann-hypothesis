import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SubalgebraEqTop
section
noncomputable def UpperTheory.Reformulated.B.Qe26.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.Qe26.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.Qe26.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.Qe26.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.Qe26.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.Qe26.IsIrrSub r ⊤

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe26.tr :
    {k : Type} → [inst : Field k] → {n : ℕ} → GL (Fin n) k → k :=
    fun {k : Type} [Field k] {n : ℕ} (g : GL (Fin n) k) ↦ (↑g : Matrix (Fin n) (Fin n) k).trace

private theorem UpperTheory.Reformulated.B.Qe26.subalgebra_eq_top {k V : Type} [Field k] [IsAlgClosed k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (S : Subalgebra k (Module.End k V))
    (h : ∀ W : Submodule k V, (∀ s ∈ S, ∀ v ∈ W, s v ∈ W) → W = ⊥ ∨ W = ⊤) :
    S = ⊤ := by
  have hsimple : IsSimpleModule S V := by
    rw [isSimpleModule_iff]
    refine ⟨fun p ↦ ?_⟩
    rcases h (p.restrictScalars k) (fun s hs v hv ↦ p.smul_mem ⟨s, hs⟩ hv) with h1 | h1
    · left
      simpa using h1
    · right
      simpa using h1
  have hb := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := V) k
  have hfin : Module.Finite (Module.End S V) V :=
    Module.Finite.of_restrictScalars_finite k _ _
  rw [eq_top_iff]
  intro T _
  let T' : Module.End (Module.End S V) V :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun c v ↦ by
        obtain ⟨a, rfl⟩ := hb.2 c
        simp }
  obtain ⟨s, hs⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := S) (M := V) T'
  have : T = s.1 := by
    ext v
    exact (LinearMap.congr_fun hs v).symm
  rw [this]
  exact s.2

private theorem UpperTheory.Reformulated.B.Qe26.lift_surjective {k : Type} [Field k] [IsAlgClosed k] {H : Type}
    [Group H] {n : ℕ} (R : H →* GL (Fin n) k) (hR : UpperTheory.Reformulated.B.Qe26.IsIrr R) :
    Function.Surjective (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R)) := by
  obtain ⟨h0, -, h1⟩ := hR
  set L := MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) with hL
  have hnt : Nontrivial (Fin n → k) := (Submodule.nontrivial_iff k).1 ⟨⟨_, _, h0⟩⟩
  have htop := UpperTheory.Reformulated.B.Qe26.subalgebra_eq_top
    (((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp L).range) (by
      intro W hW
      refine h1 W le_top (fun g v hv ↦ ?_)
      have := hW _ ⟨MonoidAlgebra.single g 1, rfl⟩ v hv
      simpa [hL] using this)
  intro M
  have hM : Matrix.toLinAlgEquiv' M ∈
      ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp L).range := by
    rw [htop]; trivial
  obtain ⟨x, hx⟩ := hM
  exact ⟨x, (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective hx⟩

theorem UpperTheory.Reformulated.B.Qe26.kerLe :
    ∀ (k : Type) [inst : Field k] [IsAlgClosed k] (H : Type) [inst_2 : Group H] (n : ℕ) (R : H →* GL (Fin n) k),
      UpperTheory.Reformulated.B.Qe26.IsIrr R →
        ∀ (x₀ : GL (Fin n) k) (B : Type) [inst_3 : Ring B] [inst_4 : Algebra k B] [Module.Finite k B] (φ : H →* B)
          (f : B →ₗ[k] k),
          (∀ (h : H), UpperTheory.Reformulated.B.Qe26.tr (x₀ * (R : H → GL (Fin n) k) h) = (f : B → k) ((φ : H → B) h)) →
            n ^ (2 : ℕ) ≤ Module.finrank k ↥(Algebra.adjoin k (Set.range (⇑φ : H → B))) ∧
              ∀ (x : MonoidAlgebra k H),
                ((MonoidAlgebra.lift k B H : (H →* B) → MonoidAlgebra k H →ₐ[k] B) φ : MonoidAlgebra k H → B) x = (0 : B) →
                  ((MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H :
                            (H →* Matrix (Fin n) (Fin n) k) → MonoidAlgebra k H →ₐ[k] Matrix (Fin n) (Fin n) k)
                          ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) :
                        MonoidAlgebra k H → Matrix (Fin n) (Fin n) k)
                      x =
                    (0 : Matrix (Fin n) (Fin n) k) := by
  intro k _ _ H _ n R hR x₀ B _ _ _ φ f hf
  have hsurj := UpperTheory.Reformulated.B.Qe26.lift_surjective R hR
  set L := MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp R) with hL
  set Φ := MonoidAlgebra.lift k B H φ with hΦ
  have htr : ∀ y, ((x₀ : Matrix (Fin n) (Fin n) k) * L y).trace = f (Φ y) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [mul_add, ha, hb]
    | single g c =>
      have := hf g
      simp only [UpperTheory.Reformulated.B.Qe26.tr, Units.val_mul] at this
      simp [hL, hΦ, ← this]
  have hker : ∀ x, Φ x = 0 → L x = 0 := by
    intro x hx
    rw [Matrix.ext_iff_trace_mul_left]
    intro M
    obtain ⟨y, hy⟩ := hsurj ((↑x₀⁻¹ : Matrix (Fin n) (Fin n) k) * M)
    have := htr (y * x)
    rw [map_mul, map_mul, hx, hy, mul_zero, map_zero, ← mul_assoc, Units.mul_inv_cancel_left] at this
    simpa using this
  refine ⟨?_, hker⟩
  have hle : LinearMap.ker Φ.toLinearMap ≤ LinearMap.ker L.toLinearMap := fun x hx ↦ hker x hx
  have hrange : LinearMap.range Φ.toLinearMap ≤
      Subalgebra.toSubmodule (Algebra.adjoin k (Set.range φ)) := by
    rintro _ ⟨y, rfl⟩
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | single g c =>
      have : Φ.toLinearMap (MonoidAlgebra.single g c) = c • φ g := by simp [hΦ]
      rw [this]
      exact Submodule.smul_mem _ _ (Algebra.subset_adjoin ⟨g, rfl⟩)
  let ψ : LinearMap.range Φ.toLinearMap →ₗ[k] Matrix (Fin n) (Fin n) k :=
    ((LinearMap.ker Φ.toLinearMap).liftQ L.toLinearMap hle).comp
      Φ.toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hψ : Function.Surjective ψ := by
    intro M
    obtain ⟨y, rfl⟩ := hsurj M
    exact ⟨Φ.toLinearMap.quotKerEquivRange (Submodule.Quotient.mk y), by simp [ψ]⟩
  calc n ^ 2 = Module.finrank k (Matrix (Fin n) (Fin n) k) := by
        simp [Module.finrank_matrix, sq]
    _ ≤ Module.finrank k (LinearMap.range Φ.toLinearMap) :=
        LinearMap.finrank_le_finrank_of_surjective hψ
    _ ≤ Module.finrank k (Subalgebra.toSubmodule (Algebra.adjoin k (Set.range φ))) :=
        Submodule.finrank_mono hrange
    _ = _ := rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SubgroupFixed
section
noncomputable def UpperTheory.Reformulated.B.SubgroupFixed.HasFixed :
    {Γ V : Type} →
      [inst : Group Γ] → [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ Γ V → Subgroup Γ → Prop :=
    fun {Γ V : Type} [Group Γ] [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ Γ V) (U : Subgroup Γ) ↦
      ∃ (v : V), v ≠ (0 : V) ∧ ∀ u ∈ U, ((ρ : Γ → V →ₗ[ℂ] V) u : V → V) v = v

private lemma UpperTheory.Reformulated.B.SubgroupFixed.core {R M N : Type*} [Ring R] [AddCommGroup M] [_root_.Module R M]
    [AddCommGroup N] [_root_.Module R N] [IsSimpleModule R M]
    (hsup : ∀ S : Submodule R N, (∀ f : M →ₗ[R] N, LinearMap.range f ≤ S) → S = ⊤)
    (W : Submodule R N) (hW : W ≠ ⊥) :
    ∃ g : M →ₗ[R] N, Function.Injective g ∧ LinearMap.range g ≤ W := by
  have hss : IsSemisimpleModule R N := by
    refine isSemisimpleModule_of_isSemisimpleModule_submodule'
      (p := fun f : M →ₗ[R] N => LinearMap.range f) (fun f => IsSemisimpleModule.range f) ?_
    exact hsup _ (fun f => le_iSup (fun f : M →ₗ[R] N => LinearMap.range f) f)
  obtain ⟨C, hC⟩ := exists_isCompl W
  let p : N →ₗ[R] W := W.linearProjOfIsCompl C hC
  have hex : ∃ f : M →ₗ[R] N, p ∘ₗ f ≠ 0 := by
    by_contra hno
    push Not at hno
    have htop : LinearMap.ker p = ⊤ := hsup _ (fun f => by
      rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun (hno f) x)
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have h1 : p w = 0 := by
      have : w ∈ LinearMap.ker p := htop ▸ Submodule.mem_top
      exact this
    have h2 : p w = ⟨w, hw⟩ := Submodule.linearProjOfIsCompl_apply_left hC ⟨w, hw⟩
    have h3 : (⟨w, hw⟩ : W) = 0 := h2.symm.trans h1
    simpa using congrArg Subtype.val h3
  obtain ⟨f, hf⟩ := hex
  have hinj := (LinearMap.injective_or_eq_zero (p ∘ₗ f)).resolve_right hf
  refine ⟨W.subtype ∘ₗ p ∘ₗ f, W.injective_subtype.comp hinj, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (p (f x)).2

theorem UpperTheory.Reformulated.B.SubgroupFixed.sub_fixed :
    ∀ {Γ X V : Type} [inst : Group Γ] [inst_1 : AddCommGroup X] [inst_2 : _root_.Module ℂ X] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (σ : Representation ℂ Γ X),
      σ.IsIrreducible →
        ∀ (τ : Representation ℂ Γ V),
          ⨆ (f :
                { f : X →ₗ[ℂ] V //
                  ∀ (g : Γ) (v : X),
                    (f : X → V) (((σ : Γ → X →ₗ[ℂ] X) g : X → X) v) = ((τ : Γ → V →ₗ[ℂ] V) g : V → V) ((f : X → V) v) }),
                (↑f : X →ₗ[ℂ] V).range =
              ⊤ →
            ∀ (W : Submodule ℂ V),
              (∀ (g : Γ), ∀ v ∈ W, ((τ : Γ → V →ₗ[ℂ] V) g : V → V) v ∈ W) →
                W ≠ ⊥ →
                  ∀ (K : Subgroup Γ),
                    UpperTheory.Reformulated.B.SubgroupFixed.HasFixed σ K → ∃ v ∈ W, v ≠ (0 : V) ∧ ∀ u ∈ K, ((τ : Γ → V →ₗ[ℂ] V) u : V → V) v = v := by
  intro Γ X V _ _ _ _ _ σ hσ τ h W hWinv hW K hK
  obtain ⟨x0, hx0, hfix⟩ := hK
  haveI : IsSimpleModule (MonoidAlgebra ℂ Γ) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  let W' : Submodule (MonoidAlgebra ℂ Γ) τ.asModule :=
    { carrier := {x | τ.asModuleEquiv x ∈ W}
      add_mem' := fun {a b} ha hb => by
        show τ.asModuleEquiv (a + b) ∈ W
        rw [map_add]
        exact W.add_mem ha hb
      zero_mem' := by
        show τ.asModuleEquiv 0 ∈ W
        rw [map_zero]
        exact W.zero_mem
      smul_mem' := fun r x hx => by
        show τ.asModuleEquiv (r • x) ∈ W
        rw [Representation.asModuleEquiv_map_smul]
        exact τ.asAlgebraHom_mem_of_forall_mem W hWinv _ hx r }
  have hW' : W' ≠ ⊥ := by
    intro hbot
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have hmem : τ.asModuleEquiv.symm w ∈ W' := by
      show τ.asModuleEquiv (τ.asModuleEquiv.symm w) ∈ W
      simpa using hw
    rw [hbot, Submodule.mem_bot] at hmem
    simpa using hmem
  have hsup : ∀ S : Submodule (MonoidAlgebra ℂ Γ) τ.asModule,
      (∀ f : σ.asModule →ₗ[MonoidAlgebra ℂ Γ] τ.asModule, LinearMap.range f ≤ S) → S = ⊤ := by
    intro S hS
    let S0 : Submodule ℂ V :=
      (S.restrictScalars ℂ).comap (τ.asModuleEquiv.symm : V →ₗ[ℂ] τ.asModule)
    have hS0 : S0 = ⊤ := by
      rw [eq_top_iff, ← h]
      refine iSup_le fun f => ?_
      rintro _ ⟨x, rfl⟩
      let F : Representation.IntertwiningMap σ τ :=
        f.1.intertwiningMap_of_isIntertwiningMap σ τ f.2
      exact hS (Representation.IntertwiningMap.equivLinearMapAsModule σ τ F)
        ⟨σ.asModuleEquiv.symm x, rfl⟩
    rw [eq_top_iff]
    intro y _
    have hy : τ.asModuleEquiv y ∈ S0 := hS0 ▸ Submodule.mem_top
    simpa [S0] using hy
  obtain ⟨g, hg, hgW⟩ := UpperTheory.Reformulated.B.SubgroupFixed.core hsup W' hW'
  refine ⟨τ.asModuleEquiv (g (σ.asModuleEquiv.symm x0)), hgW ⟨_, rfl⟩, ?_, ?_⟩
  · intro h0
    have h1 : g (σ.asModuleEquiv.symm x0) = 0 := by simpa using h0
    have h2 : σ.asModuleEquiv.symm x0 = 0 := hg (h1.trans (map_zero g).symm)
    exact hx0 (by simpa using h2)
  · intro u hu
    apply τ.asModuleEquiv.symm.injective
    rw [Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply, ← map_smul,
      ← Representation.asModuleEquiv_symm_map_rho, hfix u hu]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumEmbeddingsEqRealAddComplex
section
namespace UpperTheory.Reformulated.B.DYhb7

open NumberField NumberField.InfinitePlace Finset

private lemma algebra_trace_pi_eq_sum_trace {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℝ A]
    [Module.Free ℝ A] [Module.Finite ℝ A] (x : ι → A) :
    Algebra.trace ℝ (ι → A) x = ∑ i, Algebra.trace ℝ A (x i) := by
  classical
  let b := Module.Free.chooseBasis ℝ A
  let B := Pi.basis (fun _ : ι => b)
  rw [Algebra.trace_eq_matrix_trace B]
  simp_rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.diag_apply,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  simp [B, Pi.basis_apply, Pi.basis_repr, Pi.mul_apply]

open scoped Classical in
private lemma fiber_embeddings_eq_pair {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) :
    ({φ | mk φ = w} : Finset (F →+* ℂ)) = {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  conv_lhs => rw [← mk_embedding w, mk_eq_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [← h]; simp [ComplexEmbedding.conjugate])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by rw [h]; simp [ComplexEmbedding.conjugate])

open scoped Classical in
private lemma sum_embeddings_eq_real_add_complex {F : Type} [Field F] [NumberField F] (y : F) :
    ∑ φ : F →+* ℂ, φ y =
      (∑ w : {w : InfinitePlace F // IsReal w}, (embedding_of_isReal w.2 y : ℂ)) +
      ∑ w : {w : InfinitePlace F // IsComplex w}, (((2 * (w.1.embedding y).re : ℝ)) : ℂ) := by
  classical
  rw [← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => mk φ), sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [fiber_embeddings_eq_pair, conjugate_embedding_eq_of_isReal w.2]
    simp
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [fiber_embeddings_eq_pair, Finset.sum_pair]
    · rw [ComplexEmbedding.conjugate_coe_eq]
      push_cast
      rw [Complex.add_conj]
      push_cast
      rfl
    · intro h
      exact (isComplex_iff.mp w.2) (ComplexEmbedding.isReal_iff.mpr h.symm)

end UpperTheory.Reformulated.B.DYhb7

theorem UpperTheory.Reformulated.B.DYhb7.main :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : F),
      (Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace F) : NumberField.mixedEmbedding.mixedSpace F → ℝ)
          ((NumberField.mixedEmbedding F : F → NumberField.mixedEmbedding.mixedSpace F) y) =
        (↑((Algebra.trace ℚ F : F → ℚ) y) : ℝ) := by
  intro F _ _ y
  classical
  apply Complex.ofReal_injective
  have h1 : ((Algebra.trace ℚ F y : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ y := by
    have := _root_.trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun f => f y) _ fun _ => by
      simp [RingHom.equivRatAlgHom_apply]).symm
  rw [Complex.ofReal_ratCast, h1, UpperTheory.Reformulated.B.DYhb7.sum_embeddings_eq_real_add_complex, Algebra.trace_prod_apply,
    UpperTheory.Reformulated.B.DYhb7.algebra_trace_pi_eq_sum_trace, UpperTheory.Reformulated.B.DYhb7.algebra_trace_pi_eq_sum_trace]
  simp [Algebra.trace_complex_apply]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumRMulNe
section
theorem UpperTheory.Reformulated.B.Qn10.sum_r_mul_ne.{u_1} :
    ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A]
    {n : ℕ} (f : MvPolynomial (Fin (n + (1 : ℕ))) A) (v w : Fin (n + (1 : ℕ)) →₀ ℕ),
    (∀ (i : Fin (n + (1 : ℕ))), (v : Fin (n + (1 : ℕ)) → ℕ) i < (2 : ℕ) + f.totalDegree) →
      (∀ (i : Fin (n + (1 : ℕ))), (w : Fin (n + (1 : ℕ)) → ℕ) i < (2 : ℕ) + f.totalDegree) →
        v ≠ w →
          ∑ x : Fin (n + (1 : ℕ)),
              (fun (i : Fin (n + (1 : ℕ))) ↦ ((2 : ℕ) + f.totalDegree) ^ (↑i : ℕ)) x * (v : Fin (n + (1 : ℕ)) → ℕ) x ≠
            ∑ x : Fin (n + (1 : ℕ)),
              (fun (i : Fin (n + (1 : ℕ))) ↦ ((2 : ℕ) + f.totalDegree) ^ (↑i : ℕ)) x * (w : Fin (n + (1 : ℕ)) → ℕ) x := by
  intro A _ _ n f v w hv hw hne h
  apply hne
  have key : finFunctionFinEquiv (fun i => (⟨v i, hv i⟩ : Fin (2 + f.totalDegree))) =
      finFunctionFinEquiv (fun i => (⟨w i, hw i⟩ : Fin (2 + f.totalDegree))) := by
    apply Fin.ext
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    simpa only [mul_comm] using h
  have hfun := finFunctionFinEquiv.injective key
  ext i
  exact congrArg Fin.val (congrFun hfun i)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumRightInverse
section
theorem UpperTheory.Reformulated.B.SumRightInverse.sum_rightInv :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G)
    [μ.IsMulLeftInvariant] (K : Subgroup G),
    IsOpen (↑K : Set G) →
      (μ : Set G → ENNReal) (↑K : Set G) ≠ ⊤ →
        ∀ {S : Set G},
          IsCompact S →
            (∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) →
              ∃ (t : Finset (G ⧸ K)),
                (∀ Q ∈ t, Quotient.out Q ∈ S) ∧
                  ∀ (f : G → ℂ),
                    (∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) →
                      ∫ (g : G) in S, f g ∂μ = ∑ Q ∈ t, f (Quotient.out Q) * (↑(μ.real (↑K : Set G)) : ℂ) := by
  intro G _ _ _ _ _ μ _ K hK hμ S hS hSK
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hfin : ((QuotientGroup.mk : G → G ⧸ K) '' S).Finite :=
    (hS.image QuotientGroup.continuous_mk).finite_of_discrete
  let C : G ⧸ K → Set G := fun Q => (fun g => (Quotient.out Q)⁻¹ * g) ⁻¹' (K : Set G)
  have hC : ∀ Q g, g ∈ C Q ↔ (QuotientGroup.mk g : G ⧸ K) = Q := by
    intro Q g
    have h := QuotientGroup.eq (s := K) (a := Quotient.out Q) (b := g)
    rw [QuotientGroup.out_eq'] at h
    rw [eq_comm, h]
    rfl
  have hout : ∀ Q ∈ hfin.toFinset, Quotient.out Q ∈ S := by
    intro Q hQ
    obtain ⟨s, hs, rfl⟩ := hfin.mem_toFinset.1 hQ
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K s
    rw [hk]
    exact hSK s hs k k.2
  have hmeas : ∀ Q, MeasurableSet (C Q) := fun Q =>
    (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ Q, μ (C Q) = μ K := fun Q => MeasureTheory.measure_preimage_mul μ _ _
  have hU : S = ⋃ Q ∈ hfin.toFinset, C Q := by
    ext g
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hg
      exact ⟨_, hfin.mem_toFinset.2 ⟨g, hg, rfl⟩, (hC _ g).2 rfl⟩
    · rintro ⟨Q, hQ, hg⟩
      have := hSK _ (hout Q hQ) _ hg
      simpa using this
  refine ⟨hfin.toFinset, hout, fun f hf => ?_⟩
  have hconst : ∀ Q ∈ hfin.toFinset, Set.EqOn f (fun _ => f (Quotient.out Q)) (C Q) := by
    intro Q hQ g hg
    have := hf _ (hout Q hQ) _ hg
    simpa using this
  have hsplit : ∫ g in ⋃ Q ∈ hfin.toFinset, C Q, f g ∂μ
      = ∑ Q ∈ hfin.toFinset, ∫ g in C Q, f g ∂μ := by
    refine MeasureTheory.integral_biUnion_finset _ (fun Q _ => hmeas Q) ?_ ?_
    · intro Q _ R _ hQR
      refine Set.disjoint_left.2 fun g h1 h2 => hQR ?_
      rw [← (hC Q g).1 h1, (hC R g).1 h2]
    · intro Q hQ
      refine (MeasureTheory.integrableOn_congr_fun (hconst Q hQ) (hmeas Q)).2 ?_
      exact MeasureTheory.integrableOn_const (by rw [hμC]; exact hμ)
  rw [← hU] at hsplit
  rw [hsplit]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [MeasureTheory.setIntegral_congr_fun (hmeas Q) (hconst Q hQ),
    MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, hμC,
    MeasureTheory.measureReal_def, Complex.real_smul, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummableAbsNormRpowInv
section
open Filter Asymptotics NumberField

private theorem UpperTheory.Reformulated.B.Qp7.partial_sums_isBigO (K : Type*) [Field K] [NumberField K] :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n,
        (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  have hlim := (Ideal.tendsto_norm_le_div_atTop K).comp tendsto_natCast_atTop_atTop
  have hO : (fun n : ℕ ↦ (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (n : ℝ)} : ℝ))
      =O[atTop] fun n : ℕ ↦ (n : ℝ) := by
    refine isBigO_of_div_tendsto_nhds ?_ _ hlim
    filter_upwards [eventually_ne_atTop 0] with n hn h
    exact absurd (Nat.cast_eq_zero.mp h) hn
  simp only [Real.rpow_one]
  refine IsBigO.trans (isBigO_of_le _ fun n ↦ ?_) hO
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc ∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)
      ≤ ∑ k ∈ Finset.Icc 0 n, (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left zero_le_one)
          fun _ _ _ ↦ by positivity
    _ = _ := by
        rw [← Nat.cast_sum, ← Finset.card_preimage_eq_sum_card_image_eq
          (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
        simp [Set.coe_eq_subtype]

private theorem UpperTheory.Reformulated.B.Qp7.summable_count_mul (K : Type*) [Field K] [NumberField K] {σ : ℝ}
    (hσ : 1 < σ) :
    Summable fun n : ℕ ↦
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ σ)⁻¹ := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (s := (σ : ℂ))
    (UpperTheory.Reformulated.B.Qp7.partial_sums_isBigO K) (fun _ ↦ Nat.cast_nonneg _) zero_le_one
    (by simpa using hσ)
  refine h.norm.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn
    simp [Real.zero_rpow (zero_lt_one.trans hσ).ne']
  · simp [div_eq_mul_inv]

theorem UpperTheory.Reformulated.B.Qp7.summable_absNorm_rpow_inv.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] {σ : ℝ},
    (1 : ℝ) < σ →
      Summable fun (I : Ideal (NumberField.RingOfIntegers K)) ↦
        ((↑((Ideal.absNorm : Ideal (NumberField.RingOfIntegers K) → ℕ) I) : ℝ) ^ σ)⁻¹ := by
  intro K _ _ σ hσ
  have hfin : ∀ n : ℕ, Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    fun n ↦ (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ Ideal.absNorm I)).summable_iff,
    summable_sigma_of_nonneg (fun _ ↦ by simp only [Function.comp_apply]; positivity)]
  refine ⟨fun n ↦ Summable.of_finite, ?_⟩
  refine (UpperTheory.Reformulated.B.Qp7.summable_count_mul K hσ).congr fun n ↦ ?_
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((Ideal.absNorm I.1 : ℝ) ^ σ)⁻¹ = ((n : ℝ) ^ σ)⁻¹ := fun I ↦ by rw [I.2]
  simp only [Function.comp_apply, Equiv.sigmaFiberEquiv_apply, this, tsum_const, nsmul_eq_mul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TensorSubRight
section
theorem UpperTheory.Reformulated.B.Qn17.tensor_sub_right.{u} :
    ∀ {R : Type} [inst : CommRing R] (M N : Type u) [inst_1 : AddCommMonoid M]
    [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M] [inst_4 : _root_.Module R N] [Subsingleton N],
    Subsingleton (TensorProduct R M N) := by
  intro R _ M N _ _ _ _ _
  have h : ∀ x : TensorProduct R M N, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => (h x).trans (h y).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TripleNe
section
theorem UpperTheory.Reformulated.B.Qk1.triple_ne :
    ∀ {R ι : Type} [inst : CommRing R] [inst_1 : Fintype ι]
    {A Y B : Matrix ι ι R} {a b : ι},
    (A * Y * B) a b ≠ (0 : R) → ∃ (c : ι) (d : ι), A a c ≠ (0 : R) ∧ Y c d ≠ (0 : R) ∧ B d b ≠ (0 : R) := by
  intro R ι _ _ A Y B a b h
  rw [Matrix.mul_apply] at h
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 := left_ne_zero_of_mul hd
  rw [Matrix.mul_apply] at h1
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  exact ⟨c, d, left_ne_zero_of_mul hc, right_ne_zero_of_mul hc, right_ne_zero_of_mul hd⟩
end

