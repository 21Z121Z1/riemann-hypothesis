import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.RbarProd
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem rbar_J {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (Jmat K n * Xᵀ * Jmat K n) i j = X j.rev i.rev := by
  have h : ∀ x : Fin n, j = x.rev ↔ x = j.rev := fun x => by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [Matrix.mul_apply, Jmat, h]

private theorem rbar_w {n : ℕ} (i : Fin n) : w n i.rev = - w n i := by
  have hi := i.2
  unfold w
  rw [Fin.val_rev]
  split_ifs with h <;> omega

private theorem rbar_prod {K : Type} [CommRing K] {n : ℕ} (L : List (Fin n → K)) :
    (L.map fun d => Matrix.diagonal d).prod = Matrix.diagonal L.prod := by
  induction L with
  | nil => simp [← Matrix.diagonal_one]
  | cons a L ih => rw [List.map_cons, List.prod_cons, ih, Matrix.diagonal_mul_diagonal, List.prod_cons]; rfl

private theorem rbar_ord {H K : Type} [CommRing K] {n : ℕ} (ψ : Fin n → H → K) (g : Fin n → H) :
    ordProd (fun s => Matrix.diagonal fun j => ψ j s) ψ g = 0 := by
  unfold ordProd
  have e : (List.ofFn fun i => (Matrix.diagonal fun j => ψ j (g i)) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) K)) =
      (List.ofFn fun i => fun j => ψ j (g i) - ψ i (g i)).map fun d => Matrix.diagonal d := by
    rw [List.map_ofFn]
    congr 1
    funext i
    ext a b
    by_cases h : a = b <;> simp [h, Matrix.one_apply]
  rw [e, rbar_prod, List.prod_ofFn, ← Matrix.diagonal_zero]
  congr 1
  funext j
  rw [Finset.prod_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)

theorem UpperTheory.V.Fr.rbar :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → ∃ ρ : NRep F n k, ρ.IsBar (RingHom.id k) ∧ ρ.IsDiag := by
  intro l _ k _ _ F C₀ n _
  have hs : ∀ g : F.G0, F.Ψ (F.star g) = (F.Ψ g)⁻¹ := fun g => by
    have : ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm]
  refine ⟨{ r := { toFun := fun g => Matrix.diagonal fun i => ((F.Ψ g ^ w n i : kˣ) : k)
                   map_one' := by simp
                   map_mul' := fun g h => by simp [Matrix.diagonal_mul_diagonal, mul_zpow] }
            ψ := fun v i => (zpowGroupHom (w n i)).comp (F.Ψ.comp (F.loc v))
            pol := fun g => ?_
            diag := fun i j h => ?_
            ord := fun v g => ?_ }, ⟨fun g i => ?_, fun v i g => rfl⟩, fun g i j h => ?_⟩
  · ext i j
    rw [rbar_J]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, hs]
    by_cases h : i = j
    · subst h
      simp [rbar_w]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne]
      exact fun e => h (Fin.rev_injective e).symm
  · simp [Matrix.diagonal_apply_ne _ h]
  · exact rbar_ord (fun i s => ((F.Ψ (F.loc v s) ^ w n i : kˣ) : k)) g
  · simp
  · exact Matrix.diagonal_apply_ne _ h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ResiduallyDiagonalRepresentation
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.residually_diagonal_representation :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] (f : k →+* Q) (ρ : NRep F n Q), (ρ.map (residue Q)).IsBar ((residue Q).comp f) → ρ.triM = ⊥ → (∀ v g, (ρ.r (F.loc0 v g)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (ρ.ψ v i g : Q))) → (∀ (g : F.G0) (i : Fin n), ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k)) → ρ.IsBar f := by
  intro l _ k _ F n Q _ _ _ f ρ hbar htri hchar hdiag
  refine ⟨hdiag, fun v i g => ?_⟩
  have hz : ∀ (s : F.G0) (a b : Fin n), a < b → ρ.r s a b = 0 := fun s a b hab => by
    have : ρ.r s a b ∈ ρ.triM := Ideal.subset_span ⟨s, a, b, hab, rfl⟩
    rw [htri] at this
    exact (Submodule.mem_bot Q).1 this
  have hT : (ρ.r (F.loc0 v g))ᵀ.BlockTriangular id := fun a b hab => hz _ b a hab
  have h1 := Matrix.charpoly_of_upperTriangular _ hT
  rw [Matrix.charpoly_transpose, hchar] at h1
  have h2 := congrArg (Polynomial.eval (ρ.ψ v i g : Q)) h1
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)] at h2
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 h2.symm
  rw [sub_eq_zero, Matrix.transpose_apply, hdiag] at hj
  have h3 := hbar.2 v i g
  rw [NRep.map_ψ, hj] at h3
  have h4 := ((residue Q).comp f).injective h3
  rw [hj, h4]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap
section
noncomputable section

namespace UpperTheory.V.Fr.Frame

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (M : Type) [AddCommGroup M] [Module k M]

def strY : Submodule k (F.G0 → M) where
  carrier := {y | IsLocallyConstant y ∧ (∀ g h : F.G0, y (g * h) = (F.Ψ h : k) • y g + y h) ∧
    y F.g0 = y (F.star F.g0) ∧
    (∀ v, ∃ α : M, ∀ s, y (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) • α) ∧
    ∀ v, ∃ β : M, ∀ s, y (F.star (F.loc0 v s)) = (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • β}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩
    refine ⟨a1.add b1, fun g h => ?_, by simp [a3, b3], fun v => ?_, fun v => ?_⟩
    · simp only [Pi.add_apply, a2, b2, smul_add]; abel
    · obtain ⟨α, h⟩ := a4 v
      obtain ⟨α', h'⟩ := b4 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
    · obtain ⟨α, h⟩ := a5 v
      obtain ⟨α', h'⟩ := b5 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, rfl, fun _ => ⟨0, by simp⟩, fun _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4, a5⟩
    refine ⟨a1.comp (c • ·), fun g h => ?_, by simp [a3], fun v => ?_, fun v => ?_⟩
    · simp only [Pi.smul_apply, a2, smul_add, smul_comm c]
    · obtain ⟨α, h⟩ := a4 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩
    · obtain ⟨α, h⟩ := a5 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩

def strS : Submodule k (F.G0 → M) where
  carrier := {a | IsLocallyConstant a ∧
    (∀ g h : F.G0, a (g * h) = (F.Ψ h : k) • a g + (((F.Ψ g)⁻¹ : kˣ) : k) • a h) ∧ (∀ g, a (F.star g) = a g) ∧
    ∀ v, ∃ γ : M, ∀ s, a (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • γ}
  add_mem' := by
    rintro x y ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨a1.add b1, fun g h => ?_, fun g => by simp [a3, b3], fun v => ?_⟩
    · simp only [Pi.add_apply, a2, b2, smul_add]; abel
    · obtain ⟨α, h⟩ := a4 v
      obtain ⟨α', h'⟩ := b4 v
      exact ⟨α + α', fun s => by rw [Pi.add_apply, h, h', smul_add]⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, by simp, fun _ => rfl, fun _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c x ⟨a1, a2, a3, a4⟩
    refine ⟨a1.comp (c • ·), fun g h => ?_, fun g => by simp [a3], fun v => ?_⟩
    · simp only [Pi.smul_apply, a2, smul_add, smul_comm c]
    · obtain ⟨α, h⟩ := a4 v
      exact ⟨c • α, fun s => by rw [Pi.smul_apply, h, smul_comm]⟩

variable {F M} {M' : Type} [AddCommGroup M'] [Module k M']

theorem strY_map (f : M →ₗ[k] M') {y : F.G0 → M} (hy : y ∈ F.strY M) : (fun g => f (y g)) ∈ F.strY M' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy
  refine ⟨h1.comp f, fun g h => ?_, congrArg f h3, fun v => ?_, fun v => ?_⟩
  · simp only [h2, map_add, map_smul]
  · obtain ⟨α, hα⟩ := h4 v
    exact ⟨f α, fun s => by simp only [hα, map_smul]⟩
  · obtain ⟨β, hβ⟩ := h5 v
    exact ⟨f β, fun s => by simp only [hβ, map_smul]⟩

theorem strS_map (f : M →ₗ[k] M') {a : F.G0 → M} (ha : a ∈ F.strS M) : (fun g => f (a g)) ∈ F.strS M' := by
  obtain ⟨h1, h2, h3, h4⟩ := ha
  refine ⟨h1.comp f, fun g h => ?_, fun g => congrArg f (h3 g), fun v => ?_⟩
  · simp only [h2, map_add, map_smul]
  · obtain ⟨γ, hγ⟩ := h4 v
    exact ⟨f γ, fun s => by simp only [hγ, map_smul]⟩

end UpperTheory.V.Fr.Frame
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TensorProjMemOfMemBaseChange
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {k K : Type} [Field k] [Field K] [Algebra k K]

private theorem rank_eq_of_scalar_extension_data {H H' : Type} [AddCommGroup H] [Module k H] [AddCommGroup H'] [Module K H']
    (ι : H →+ H') (hι : ∀ (a : k) h, ι (a • h) = algebraMap k K a • ι h)
    (π : (K →ₗ[k] k) → H' →+ H) (hπ : ∀ l c h, π l (c • ι h) = l c • h)
    (hs : Submodule.span K (Set.range ι) = ⊤) : Module.rank K H' = Module.rank k H := by
  classical
  let e := Module.Free.chooseBasis k H
  have hli : LinearIndependent K (fun j => ι (e j)) := by
    rw [linearIndependent_iff']
    intro s c hc j hj
    rw [← Module.forall_dual_apply_eq_zero_iff k]
    intro l
    have h1 := congrArg (π l) hc
    rw [map_sum, map_zero] at h1
    simp only [hπ] at h1
    exact linearIndependent_iff'.1 e.linearIndependent s (fun j => l (c j)) h1 j hj
  have hsp : ⊤ ≤ Submodule.span K (Set.range fun j => ι (e j)) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨h, rfl⟩
    have hh : h ∈ Submodule.span k (Set.range e) := by rw [e.span_eq]; trivial
    induction hh using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.subset_span ⟨j, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [hι]; exact Submodule.smul_mem _ _ hx
  rw [← (Module.Basis.mk hli hsp).mk_eq_rank'', ← e.mk_eq_rank'']

variable {W : Type} [AddCommGroup W] [Module k W]

private noncomputable def n4p (l : K →ₗ[k] k) : K ⊗[k] W →ₗ[k] W :=
  (TensorProduct.lid k W).toLinearMap ∘ₗ l.rTensor W

@[simp] private theorem tensor_proj_tmul (l : K →ₗ[k] k) (c : K) (x : W) : n4p l (c ⊗ₜ[k] x) = l c • x := by
  simp [n4p]

private theorem tensor_proj_smul_one_tmul (l : K →ₗ[k] k) (c : K) (x : W) : n4p l (c • ((1 : K) ⊗ₜ[k] x)) = l c • x := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, tensor_proj_tmul]

private theorem tensor_proj_baseChange_map (l : K →ₗ[k] k) (f : W →ₗ[k] W) (x : K ⊗[k] W) :
    n4p l (f.baseChange K x) = f (n4p l x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => simp
  | add x y hx hy => simp [hx, hy]

private theorem tensor_proj_mem_of_mem_baseChange (l : K →ₗ[k] k) (b : Submodule k W) (x : K ⊗[k] W) (hx : x ∈ b.baseChange K) :
    n4p l x ∈ b := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c x => simpa using b.smul_mem _ x.2
  | add x y hx hy => simpa using add_mem hx hy

private theorem baseChange_eq_sum_coord_basis {I : Type} (e : Module.Basis I k K) (x : K ⊗[k] W) :
    ∃ s : Finset I, ∀ t : Finset I, s ⊆ t → x = ∑ i ∈ t, e i • ((1 : K) ⊗ₜ[k] n4p (e.coord i) x) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun t _ => by simp⟩
  | tmul c x =>
    refine ⟨(e.repr c).support, fun t ht => ?_⟩
    have h1 : c = ∑ i ∈ t, e.repr c i • e i := by
      conv_lhs => rw [← e.linearCombination_repr c, Finsupp.linearCombination_apply]
      exact Finsupp.sum_of_support_subset _ ht _ (fun _ _ => by simp)
    conv_lhs => rw [h1]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tensor_proj_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    refine ⟨s ∪ s', fun t ht => ?_⟩
    conv_lhs => rw [hs t (Finset.subset_union_left.trans ht), hs' t (Finset.subset_union_right.trans ht)]
    simp [← Finset.sum_add_distrib, TensorProduct.tmul_add]

variable {G V : Type}

variable (K) in
private noncomputable def n4i : ((G → W) × (V → W)) →+ ((G → K ⊗[k] W) × (V → K ⊗[k] W)) where
  toFun y := (fun g => (1 : K) ⊗ₜ y.1 g, fun v => (1 : K) ⊗ₜ y.2 v)
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [TensorProduct.tmul_add]

private noncomputable def n4q (l : K →ₗ[k] k) : ((G → K ⊗[k] W) × (V → K ⊗[k] W)) →+ ((G → W) × (V → W)) where
  toFun y := (fun g => n4p l (y.1 g), fun v => n4p l (y.2 v))
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

private theorem inclusion_smul_algebraMap (a : k) (y : (G → W) × (V → W)) :
    n4i (k := k) K (a • y) = algebraMap k K a • n4i (k := k) K y := by
  ext <;> simp [n4i]

private theorem descend_smul_inclusion (l : K →ₗ[k] k) (c : K) (y : (G → W) × (V → W)) :
    n4q l (c • n4i (k := k) K y) = l c • y := by
  ext <;> simp [n4i, n4q, tensor_proj_smul_one_tmul]

variable [Group G] [TopologicalSpace G] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G)
  (ρ : Representation k G W) (b : V → Submodule k W) (ρ' : Representation K G (K ⊗[k] W))
  (hρ : ∀ g, ρ' g = (ρ g).baseChange K)

include hρ

private theorem inclusion_cocycle_mem_Z1 (y) (hy : y ∈ Z1C loc ρ b) :
    n4i (k := k) K y ∈ Z1C loc ρ' (fun v => (b v).baseChange K) := by
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨h1.comp (fun x => (1 : K) ⊗ₜ[k] x), fun s t => ?_, fun v s => ?_⟩
  · simp [n4i, hρ, h2, TensorProduct.tmul_add]
  · have := Submodule.tmul_mem_baseChange_of_mem (1 : K) (h3 v s)
    simpa [n4i, hρ, TensorProduct.tmul_sub] using this

private theorem descend_cocycle_mem_Z1 (l : K →ₗ[k] k) (y) (hy : y ∈ Z1C loc ρ' (fun v => (b v).baseChange K)) :
    n4q l y ∈ Z1C loc ρ b := by
  obtain ⟨h1, h2, h3⟩ := hy
  refine ⟨h1.comp (n4p l), fun s t => ?_, fun v s => ?_⟩
  · simp [n4q, hρ, h2, tensor_proj_baseChange_map]
  · have := tensor_proj_mem_of_mem_baseChange l _ _ (h3 v s)
    simpa [n4q, hρ, tensor_proj_baseChange_map] using this

omit [TopologicalSpace G] in
private theorem inclusion_coboundary_mem_B1 (y) (hy : y ∈ continuousCoboundaries1 ρ b) :
    n4i (k := k) K y ∈ continuousCoboundaries1 ρ' (fun v => (b v).baseChange K) := by
  obtain ⟨X, h2, h3⟩ := hy
  refine ⟨1 ⊗ₜ X, fun s => ?_, fun v => ?_⟩
  · simp [n4i, hρ, h2, TensorProduct.tmul_sub]
  · have := Submodule.tmul_mem_baseChange_of_mem (1 : K) (h3 v)
    simpa [n4i, TensorProduct.tmul_sub] using this

omit [TopologicalSpace G] in
private theorem descend_coboundary_mem_B1 (l : K →ₗ[k] k) (y) (hy : y ∈ continuousCoboundaries1 ρ' (fun v => (b v).baseChange K)) :
    n4q l y ∈ continuousCoboundaries1 ρ b := by
  obtain ⟨X, h2, h3⟩ := hy
  refine ⟨n4p l X, fun s => ?_, fun v => ?_⟩
  · simp [n4q, hρ, h2, tensor_proj_baseChange_map]
  · have := tensor_proj_mem_of_mem_baseChange l _ _ (h3 v)
    simpa [n4q] using this

private theorem cocycles_baseChange_eq_span [CompactSpace G] [Finite V] :
    Z1C loc ρ' (fun v => (b v).baseChange K) =
      Submodule.span K (n4i (k := k) K '' (Z1C loc ρ b : Set ((G → W) × (V → W)))) := by
  classical
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
  · let e := Module.Free.chooseBasis k K
    choose s hs using fun x : K ⊗[k] W => baseChange_eq_sum_coord_basis e x
    have hf : (Set.range y.1 ∪ Set.range y.2).Finite := hy.1.range_finite.union (Set.finite_range _)
    have hy' : y = ∑ i ∈ hf.toFinset.biUnion s, e i • n4i (k := k) K (n4q (e.coord i) y) := by
      ext g
      · rw [Prod.fst_sum, Finset.sum_apply]
        exact hs _ _ (Finset.subset_biUnion_of_mem s (by simp))
      · rw [Prod.snd_sum, Finset.sum_apply]
        exact hs _ _ (Finset.subset_biUnion_of_mem s (by simp))
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, descend_cocycle_mem_Z1 loc ρ b ρ' hρ _ y hy, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    exact inclusion_cocycle_mem_Z1 loc ρ b ρ' hρ y hy

private theorem rank_H1_baseChange_eq [CompactSpace G] [Finite V] :
    Module.rank K (H1C loc ρ' fun v => (b v).baseChange K) = Module.rank k (H1C loc ρ b) := by
  let i0 : Z1C loc ρ b →+ Z1C loc ρ' (fun v => (b v).baseChange K) :=
    { toFun := fun y => ⟨n4i (k := k) K y.1, inclusion_cocycle_mem_Z1 loc ρ b ρ' hρ _ y.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  let q0 (l : K →ₗ[k] k) : Z1C loc ρ' (fun v => (b v).baseChange K) →+ Z1C loc ρ b :=
    { toFun := fun y => ⟨n4q l y.1, descend_cocycle_mem_Z1 loc ρ b ρ' hρ l _ y.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _) }
  let i1 : H1C loc ρ b →+ H1C loc ρ' (fun v => (b v).baseChange K) :=
    QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) i0
      (fun y hy => inclusion_coboundary_mem_B1 ρ b ρ' hρ _ hy)
  let q1 (l : K →ₗ[k] k) : H1C loc ρ' (fun v => (b v).baseChange K) →+ H1C loc ρ b :=
    QuotientAddGroup.map (Submodule.toAddSubgroup _) (Submodule.toAddSubgroup _) (q0 l)
      (fun y hy => descend_coboundary_mem_B1 ρ b ρ' hρ l _ hy)
  have hi : ∀ y, i1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (i0 y) := fun _ => rfl
  have hq : ∀ l y, q1 l (Submodule.Quotient.mk y) = Submodule.Quotient.mk (q0 l y) := fun _ _ => rfl
  refine rank_eq_of_scalar_extension_data i1 (fun a h => ?_) q1 (fun l c h => ?_) ?_
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [← Submodule.Quotient.mk_smul, hi, hi, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (inclusion_smul_algebraMap a y.1)
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    rw [hi, ← Submodule.Quotient.mk_smul, hq, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (descend_smul_inclusion l c y.1)
  · rw [eq_top_iff]
    intro h hT
    clear hT
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    have hy' := hy
    rw [cocycles_baseChange_eq_span loc ρ b ρ' hρ] at hy'
    revert hy
    induction hy' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      intro hy
      exact Submodule.subset_span ⟨Submodule.Quotient.mk ⟨z, hz⟩, rfl⟩
    | zero => intro hy; exact zero_mem _
    | add x y hx' hy' hx hy =>
      intro _
      rw [← cocycles_baseChange_eq_span loc ρ b ρ' hρ] at hx' hy'
      exact add_mem (hx hx') (hy hy')
    | smul a x hx' hx =>
      intro _
      rw [← cocycles_baseChange_eq_span loc ρ b ρ' hρ] at hx'
      exact Submodule.smul_mem _ a (hx hx')

end SlopeTestRemainingChoices

theorem UpperTheory.V.Fr.n4 :
    ∀ {k K G W V : Type} [Field k] [Field K] [Algebra k K] [Group G] [TopologicalSpace G] [CompactSpace G] [AddCommGroup W] [Module k W] [Module.Finite k W] {Gv : V → Type} [∀ v, Group (Gv v)] [Finite V] (loc : ∀ v, Gv v →* G) (ρ : Representation k G W) (b : V → Submodule k W) (ρ' : Representation K G (TensorProduct k K W)), (∀ g, ρ' g = (ρ g).baseChange K) → Z1C loc ρ' (fun v => (b v).baseChange K) = Submodule.span K ((fun y : (G → W) × (V → W) => (fun g => (1 : K) ⊗ₜ y.1 g, fun v => (1 : K) ⊗ₜ y.2 v)) '' (Z1C loc ρ b : Set ((G → W) × (V → W)))) ∧ Module.rank K (H1C loc ρ' fun v => (b v).baseChange K) = Module.rank k (H1C loc ρ b) := by
  intro k K G W V _ _ _ _ _ _ _ _ _ Gv _ _ loc ρ b ρ' hρ
  exact ⟨cocycles_baseChange_eq_span loc ρ b ρ' hρ, rank_H1_baseChange_eq loc ρ b ρ' hρ⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TrdegQuotLeOne
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem alg_of_rel {R D : Type} [CommRing R] [CommRing D] [IsDomain D] [Algebra R D]
    (T : Subalgebra R D) {x c d : D} {p : ℕ} (hp : 0 < p) (hc : c ∈ T) (hd : d ∈ T) (h0 : c ≠ 0)
    (h : x ^ p * c = d) : IsAlgebraic T x := by
  refine IsAlgebraic.of_pow hp ?_
  have hc' : (⟨c, hc⟩ : T) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  refine IsAlgebraic.of_smul (y := (⟨c, hc⟩ : T)) (mem_nonZeroDivisors_of_ne_zero hc') ?_
  have : (⟨c, hc⟩ : T) • x ^ p = algebraMap T D ⟨d, hd⟩ := by
    rw [Algebra.smul_def, mul_comm]; exact h
  rw [this]
  exact isAlgebraic_algebraMap _

private theorem trdeg_le_one {R D ι : Type} [CommRing R] [CommRing D] [IsDomain D] [Algebra R D]
    [FaithfulSMul R D] (x : ι → D) (wt : ι → ℤ) (hgen : Algebra.adjoin R (Set.range x) = ⊤)
    (h0 : ∀ (i j : ι) (p q : ℕ), p * wt i + q * wt j = 0 → x i ^ p * x j ^ q ∈ Set.range (algebraMap R D))
    {a b : ι} (ha : 0 < wt a) (hb : wt b < 0) (ha0 : x a ≠ 0) (hb0 : x b ≠ 0) : Algebra.trdeg R D ≤ 1 := by
  set T : Subalgebra R D := Algebra.adjoin R {x a} with hT
  have haT : x a ∈ T := Algebra.subset_adjoin rfl
  have hR : ∀ {y}, y ∈ Set.range (algebraMap R D) → y ∈ T := by
    rintro _ ⟨r, rfl⟩; exact T.algebraMap_mem r
  obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le ha.le
  obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hb.le)
  have hp0 : 0 < p := by omega
  have hq0 : 0 < q := by omega
  have hq' : wt b = -q := by omega
  have key : ∀ i, IsAlgebraic T (x i) := by
    intro i
    rcases le_total (wt i) 0 with h | h
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 h)
      have hm' : wt i = -m := by omega
      exact alg_of_rel T hp0 (pow_mem haT m) (hR (h0 i a p m (by rw [hm', hp]; ring))) (pow_ne_zero _ ha0) rfl
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h
      have h1 := hR (h0 i b q m (by rw [hm, hq']; ring))
      have h2 := hR (h0 b a p q (by rw [hp, hq']; ring))
      refine alg_of_rel T (mul_pos hq0 hp0) (pow_mem h2 m) (mul_mem (pow_mem h1 p) (pow_mem haT (q * m)))
        (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hb0) (pow_ne_zero _ ha0))) (by ring)
  have hall : Algebra.IsAlgebraic T D := ⟨fun y => by
    have hy : y ∈ Algebra.adjoin R (Set.range x) := hgen ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact key i
    | algebraMap r => exact isAlgebraic_algebraMap (⟨_, T.algebraMap_mem r⟩ : T)
    | add y z _ _ h1 h2 => exact h1.add h2
    | mul y z _ _ h1 h2 => exact h1.mul h2⟩
  simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk R ({x a} : Set D)

private theorem trdeg_quot_le_one {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    (η : Ideal A) (hη : η.IsPrime) (x : ι → A) (wt : ι → ℤ) (hgen : Algebra.adjoin R (Set.range x) = ⊤)
    (h0 : ∀ (i j : ι) (p q : ℕ), p * wt i + q * wt j = 0 → x i ^ p * x j ^ q ∈ Set.range (algebraMap R A))
    {a b : ι} (ha : 0 < wt a) (hb : wt b < 0) (ha0 : x a ∉ η) (hb0 : x b ∉ η) :
    Algebra.trdeg (R ⧸ η.comap (algebraMap R A)) (A ⧸ η) ≤ 1 := by
  refine trdeg_le_one (fun s => Ideal.Quotient.mk η (x s)) wt ?_ ?_ ha hb
    (fun e => ha0 (Ideal.Quotient.eq_zero_iff_mem.1 e)) (fun e => hb0 (Ideal.Quotient.eq_zero_iff_mem.1 e))
  · rw [eq_top_iff]
    intro y hy
    clear hy
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hy : y ∈ Algebra.adjoin R (Set.range x) := hgen ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (Ideal.Quotient.mk (η.comap (algebraMap R A)) r)
    | add y z _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
    | mul y z _ _ h1 h2 => rw [map_mul]; exact mul_mem h1 h2
  · intro i j p q h
    obtain ⟨r, hr⟩ := h0 i j p q h
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [← map_pow, ← map_pow, ← map_mul, ← hr]
    rfl

private theorem w_lt {n : ℕ} {i j : Fin n} (h : i < j) : w n j < w n i := by
  have : (i : ℕ) < j := h
  unfold w
  split_ifs <;> omega

theorem UpperTheory.V.Fr.fibre :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ η : Ideal S.A, η.IsPrime → S.u.OffTri η → S.td η ≤ 1 := by
  intro l _ O _ _ _ _ F C₀ n _ _ S η hη hoff
  obtain ⟨h1, h2⟩ := hoff
  have hb : ∃ g i j, j < i ∧ S.u.r g i j ∉ η := by
    by_contra h
    push Not at h
    exact h1 (Ideal.span_le.2 (by rintro _ ⟨g, i, j, hij, rfl⟩; exact h g i j hij))
  have ha : ∃ g i j, i < j ∧ S.u.r g i j ∉ η := by
    by_contra h
    push Not at h
    exact h2 (Ideal.span_le.2 (by rintro _ ⟨g, i, j, hij, rfl⟩; exact h g i j hij))
  obtain ⟨g, i, j, hij, hg⟩ := ha
  obtain ⟨g', i', j', hij', hg'⟩ := hb
  refine trdeg_quot_le_one (ι := F.G0 × Fin n × Fin n) η hη (fun s => S.u.r s.1 s.2.1 s.2.2)
    (fun s => w n s.2.1 - w n s.2.2) ?_ ?_ (a := (g, i, j)) (b := (g', i', j'))
    (sub_pos.2 (w_lt hij)) (sub_neg.2 (w_lt hij')) hg hg'
  · rw [eq_top_iff]
    rintro ⟨y, hy⟩ hy'
    clear hy'
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with hy | ⟨g, i, j, rfl⟩
      · exact Subalgebra.algebraMap_mem _ (⟨y, hy⟩ : S.B)
      · exact Algebra.subset_adjoin ⟨(g, i, j), rfl⟩
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (algebraMap O S.B r)
    | add y z hy hz h1 h2 => exact add_mem h1 h2
    | mul y z hy hz h1 h2 => exact mul_mem h1 h2
  · intro s t p q h
    have hm : S.ρ.r s.1 s.2.1 s.2.2 ^ p * S.ρ.r t.1 t.2.1 t.2.2 ^ q ∈ S.ρ.mon 0 :=
      ⟨List.replicate p s ++ List.replicate q t, by simpa using h, by simp⟩
    exact ⟨⟨_, S.mon_mem hm⟩, rfl⟩
end

