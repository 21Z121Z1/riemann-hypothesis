import Mathlib

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HasProdFiniteSupport
section
noncomputable section

namespace Formalism.L2.SG.Pf.HasProdFiniteSupport

open Filter Topology

variable {ι : Type*}

theorem hasProd_inv₀' {f : ι → ℝ} {a : ℝ} (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  unfold HasProd at h ⊢
  refine (h.inv₀ ha).congr (fun s => ?_)
  exact (Finset.prod_inv_distrib f).symm

theorem hasProd_rpow' {f : ι → ℝ} {a : ℝ} (p : ℝ) (hf : ∀ i, 0 ≤ f i) (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => f i ^ p) (a ^ p) := by
  unfold HasProd at h ⊢
  refine (h.rpow_const (Or.inl ha)).congr (fun s => ?_)
  exact (Real.finsetProd_rpow s f (fun i _ => hf i) p).symm

theorem hasProd_of_compl (P : ι → Prop) [DecidablePred P] [Fintype {i // P i}] {f : ι → ℝ} {a : ℝ}
    (h : HasProd (fun i : {i // ¬ P i} => f i) a) : HasProd f (a * ∏ i : {i // P i}, f i) := by
  have h1 : HasProd ({i | ¬ P i}.mulIndicator f) a :=
    (hasProd_subtype_iff_mulIndicator (s := {i | ¬ P i})).mp h
  have h2 : HasProd ({i | P i}.mulIndicator f) (∏ i : {i // P i}, f i) :=
    letI : Fintype ({i | P i} : Set ι) := inferInstanceAs (Fintype {i // P i})
    (hasProd_subtype_iff_mulIndicator (s := {i | P i})).mp (hasProd_fintype _)
  have h3 := h1.mul h2
  convert h3 using 1
  funext i
  by_cases hp : P i <;> simp [Set.mulIndicator, hp]

theorem hasProd_compl_of (P : ι → Prop) [DecidablePred P] [Fintype {i // P i}] {f : ι → ℝ} {a : ℝ}
    (h : HasProd f a) (hf : ∀ i, P i → f i ≠ 0) :
    HasProd (fun i : {i // ¬ P i} => f i) (a * (∏ i : {i // P i}, f i)⁻¹) := by
  have h2 : HasProd (fun i => ({i | P i}.mulIndicator f i)⁻¹) (∏ i : {i // P i}, f i)⁻¹ := by
    have h0 : HasProd ({i | P i}.mulIndicator f) (∏ i : {i // P i}, f i) :=
      letI : Fintype ({i | P i} : Set ι) := inferInstanceAs (Fintype {i // P i})
    (hasProd_subtype_iff_mulIndicator (s := {i | P i})).mp (hasProd_fintype _)
    exact hasProd_inv₀' h0 (Finset.prod_ne_zero_iff.mpr fun i _ => hf i i.2)
  have h3 := h.mul h2
  have h4 : HasProd ({i | ¬ P i}.mulIndicator f) (a * (∏ i : {i // P i}, f i)⁻¹) := by
    convert h3 using 1
    funext i
    by_cases hp : P i
    · simp [Set.mulIndicator, hp, hf i hp]
    · simp [Set.mulIndicator, hp]
  exact (hasProd_subtype_iff_mulIndicator (s := {i | ¬ P i})).mpr h4

theorem hasProd_of_finite_support {f : ι → ℝ} (s : Set ι) (hs : s.Finite) (h1 : ∀ i ∉ s, f i = 1) :
    HasProd f (∏ i ∈ hs.toFinset, f i) :=
  hasProd_prod_of_ne_finset_one (fun i hi => h1 i (by simpa using hi))

theorem hasProd_of_compl' (s : Finset ι) {f : ι → ℝ} {a : ℝ}
    (h : HasProd (fun i : {i // i ∉ s} => f i) a) : HasProd f (a * ∏ i : s, f i) := by
  classical
  have h1 : HasProd ((↑s : Set ι)ᶜ.mulIndicator f) a :=
    (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι)ᶜ)).mp h
  have h2 : HasProd ((↑s : Set ι).mulIndicator f) (∏ i : s, f i) :=
    (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι))).mp (hasProd_fintype _)
  have h3 := h1.mul h2
  convert h3 using 1
  · funext i
    by_cases hp : i ∈ s <;> simp [Set.mulIndicator, hp]

theorem hasProd_compl_of' (s : Finset ι) {f : ι → ℝ} {a : ℝ} (h : HasProd f a) (hf : ∀ i ∈ s, f i ≠ 0) :
    HasProd (fun i : {i // i ∉ s} => f i) (a * (∏ i : s, f i)⁻¹) := by
  classical
  have h2 : HasProd (fun i => ((↑s : Set ι).mulIndicator f i)⁻¹) (∏ i : s, f i)⁻¹ := by
    have h0 : HasProd ((↑s : Set ι).mulIndicator f) (∏ i : s, f i) :=
      (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι))).mp (hasProd_fintype _)
    exact hasProd_inv₀' h0 (Finset.prod_ne_zero_iff.mpr fun i _ => hf i i.2)
  have h3 := h.mul h2
  have h4 : HasProd ((↑s : Set ι)ᶜ.mulIndicator f) (a * (∏ i : s, f i)⁻¹) := by
    convert h3 using 1
    funext i
    by_cases hp : i ∈ s
    · simp [Set.mulIndicator, hp, hf i hp]
    · simp [Set.mulIndicator, hp]
  exact (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι)ᶜ)).mpr h4

end Formalism.L2.SG.Pf.HasProdFiniteSupport
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXGLP
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.LT.GLP

variable {K : Type*} [Field K]

theorem surj_equiv {C W : Type*} [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup W] [Module K W] (L1 L2 : C →ₗ[K] W) (h1 : Function.Surjective L1)
    (h2 : Function.Surjective L2) : ∃ δ : C ≃ₗ[K] C, ∀ c, L1 (δ c) = L2 c := by
  obtain ⟨D1, hD1⟩ := Submodule.exists_isCompl (LinearMap.ker L1)
  obtain ⟨D2, hD2⟩ := Submodule.exists_isCompl (LinearMap.ker L2)
  let e1 : D1 ≃ₗ[K] W := (Submodule.quotientEquivOfIsCompl _ _ hD1).symm.trans (L1.quotKerEquivOfSurjective h1)
  let e2 : D2 ≃ₗ[K] W := (Submodule.quotientEquivOfIsCompl _ _ hD2).symm.trans (L2.quotKerEquivOfSurjective h2)
  have he1 : ∀ d : D1, e1 d = L1 d := fun d => by
    simp [e1, Submodule.quotientEquivOfIsCompl_symm_apply]
  have he2 : ∀ d : D2, e2 d = L2 d := fun d => by
    simp [e2, Submodule.quotientEquivOfIsCompl_symm_apply]
  have : FiniteDimensional K W := Module.Finite.of_surjective L1 h1
  have hk : Module.finrank K (LinearMap.ker L2) = Module.finrank K (LinearMap.ker L1) := by
    have a1 := LinearMap.finrank_range_add_finrank_ker L1
    have a2 := LinearMap.finrank_range_add_finrank_ker L2
    rw [LinearMap.range_eq_top.2 h1, finrank_top] at a1
    rw [LinearMap.range_eq_top.2 h2, finrank_top] at a2
    omega
  let k : LinearMap.ker L2 ≃ₗ[K] LinearMap.ker L1 := LinearEquiv.ofFinrankEq _ _ hk
  let δ : C ≃ₗ[K] C := (Submodule.prodEquivOfIsCompl _ _ hD2).symm.trans
    ((k.prodCongr (e2.trans e1.symm)).trans (Submodule.prodEquivOfIsCompl _ _ hD1))
  refine ⟨δ, fun c => ?_⟩
  set p := (Submodule.prodEquivOfIsCompl _ _ hD2).symm c with hp
  have hc : c = (p.1 : C) + (p.2 : C) := by
    rw [← Submodule.coe_prodEquivOfIsCompl' _ _ hD2, hp, LinearEquiv.apply_symm_apply]
  have hδ : δ c = ((k p.1 : LinearMap.ker L1) : C) + ((e1.symm (e2 p.2) : D1) : C) := by
    simp only [δ, LinearEquiv.trans_apply, ← hp]
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  rw [hδ, map_add, LinearMap.mem_ker.1 (k p.1).2, zero_add, ← he1, LinearEquiv.apply_symm_apply, he2]
  conv_rhs => rw [hc]
  rw [map_add, LinearMap.mem_ker.1 p.1.2, zero_add]

theorem pi_surj {V : Type*} [AddCommGroup V] [Module K V] {a : ℕ} (ψ : Fin a → Module.Dual K V)
    (hψ : LinearIndependent K ψ) : Function.Surjective (LinearMap.pi ψ) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  have hsum : ∑ i, f (Pi.single i 1) • ψ i = 0 := by
    ext v
    have hv : f (LinearMap.pi ψ v) = 0 := hfk ⟨v, rfl⟩
    have hdec : LinearMap.pi ψ v = ∑ i, ψ i v • (Pi.single i 1 : Fin a → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hdec, map_sum] at hv
    simpa [smul_eq_mul, mul_comm] using hv
  have hc := Fintype.linearIndependent_iff.1 hψ _ hsum
  apply LinearMap.pi_ext'
  intro i
  ext
  simp [hc i]

theorem trans_tuple {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (hx : LinearIndependent K x) (hy : LinearIndependent K y) :
    ∃ A : V ≃ₗ[K] V, ∀ j, A (x j) = y j := by
  set U := Submodule.span K (Set.range x)
  set U' := Submodule.span K (Set.range y)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl U'
  let bx := Module.Basis.span hx
  let by' := Module.Basis.span hy
  have hU : Module.finrank K U = a := by rw [Module.finrank_eq_card_basis bx, Fintype.card_fin]
  have hU' : Module.finrank K U' = a := by rw [Module.finrank_eq_card_basis by', Fintype.card_fin]
  have h1 := Submodule.finrank_add_eq_of_isCompl hC
  have h2 := Submodule.finrank_add_eq_of_isCompl hC'
  let eC : C ≃ₗ[K] C' := LinearEquiv.ofFinrankEq _ _ (by omega)
  let eU : U ≃ₗ[K] U' := bx.equiv by' (Equiv.refl _)
  refine ⟨(Submodule.prodEquivOfIsCompl _ _ hC).symm.trans
    ((eU.prodCongr eC).trans (Submodule.prodEquivOfIsCompl _ _ hC')), fun j => ?_⟩
  have hxj : x j ∈ U := Submodule.subset_span ⟨j, rfl⟩
  simp only [LinearEquiv.trans_apply]
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hC ⟨x j, hxj⟩]
  rw [Submodule.coe_prodEquivOfIsCompl']
  have : eU ⟨x j, hxj⟩ = ⟨y j, Submodule.subset_span ⟨j, rfl⟩⟩ := by
    have hb : (⟨x j, hxj⟩ : U) = bx j := by ext; simp [bx, Module.Basis.span_apply]
    rw [hb]
    simp only [eU, Module.Basis.equiv_apply, Equiv.refl_apply]
    exact Module.Basis.span_apply hy j
  simp [LinearEquiv.prodCongr_apply, this]

theorem fix_tuple {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x : Fin a → V) (hx : LinearIndependent K x) (φ ψ : Fin a → Module.Dual K V)
    (hφ : LinearIndependent K φ) (hψ : LinearIndependent K ψ) (h : ∀ i j, φ i (x j) = ψ i (x j)) :
    ∃ B : V ≃ₗ[K] V, (∀ j, B (x j) = x j) ∧ ∀ i v, ψ i (B v) = φ i v := by
  set U := Submodule.span K (Set.range x)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  set Φ := LinearMap.pi φ
  set Ψ := LinearMap.pi ψ
  have hUeq : Φ ∘ₗ U.subtype = Ψ ∘ₗ U.subtype := by
    apply (Module.Basis.span hx).ext
    intro j
    ext i
    simp [Φ, Ψ, Module.Basis.span_apply, h i j]
  have hUv : ∀ u : U, Φ u = Ψ u := fun u => LinearMap.congr_fun hUeq u
  have hsplit : ∀ v : V, ∃ u ∈ U, ∃ c ∈ C, u + c = v := fun v =>
    Submodule.mem_sup.1 (by rw [hC.sup_eq_top]; exact Submodule.mem_top)
  set R := LinearMap.range (Ψ ∘ₗ U.subtype)
  have hsurj : ∀ Θ : V →ₗ[K] (Fin a → K), Function.Surjective Θ → (∀ u : U, Θ u = Ψ u) →
      Function.Surjective (R.mkQ ∘ₗ Θ ∘ₗ C.subtype) := by
    intro Θ hΘ hΘU w
    obtain ⟨w', rfl⟩ := R.mkQ_surjective w
    obtain ⟨v, rfl⟩ := hΘ w'
    obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    refine ⟨⟨c, hc⟩, ?_⟩
    have h0 : R.mkQ (Θ u) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨⟨u, hu⟩, (hΘU ⟨u, hu⟩).symm⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_add, h0, zero_add]
  obtain ⟨δ, hδ⟩ := surj_equiv (R.mkQ ∘ₗ Ψ ∘ₗ C.subtype) (R.mkQ ∘ₗ Φ ∘ₗ C.subtype)
    (hsurj Ψ (pi_surj ψ hψ) fun _ => rfl) (hsurj Φ (pi_surj φ hφ) hUv)
  set D : C →ₗ[K] (Fin a → K) := Φ ∘ₗ C.subtype - Ψ ∘ₗ C.subtype ∘ₗ δ.toLinearMap
  have hD : ∀ c, D c ∈ R := by
    intro c
    have e := hδ c
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at e
    exact (Submodule.Quotient.eq R).1 e.symm
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (Ψ ∘ₗ U.subtype).rangeRestrict
    (LinearMap.range_rangeRestrict _)
  set β : C →ₗ[K] U := s ∘ₗ D.codRestrict R hD
  have hβ : ∀ c, Ψ (β c : V) = D c := by
    intro c
    have e := congrArg Subtype.val (LinearMap.congr_fun hs (D.codRestrict R hD c))
    simpa [β] using e
  set P := (Submodule.prodEquivOfIsCompl _ _ hC).symm
  have hP : ∀ (u : U) (c : C), P ((u : V) + c) = (u, c) := by
    intro u c
    have e : (u : V) + c = Submodule.prodEquivOfIsCompl _ _ hC (u, c) :=
      (Submodule.coe_prodEquivOfIsCompl' _ _ hC (u, c)).symm
    rw [e]
    exact LinearEquiv.symm_apply_apply _ _
  set B0 : V →ₗ[K] V := (U.subtype ∘ₗ LinearMap.fst K U C + U.subtype ∘ₗ β ∘ₗ LinearMap.snd K U C +
    C.subtype ∘ₗ δ.toLinearMap ∘ₗ LinearMap.snd K U C) ∘ₗ P.toLinearMap
  have hB0 : ∀ (u : U) (c : C), B0 ((u : V) + c) = (u : V) + (β c : V) + (δ c : V) := by
    intro u c
    simp [B0, hP u c]
  have hinj : Function.Injective B0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    have e := hB0 ⟨u, hu⟩ ⟨c, hc⟩
    rw [hv] at e
    have hδU : (δ ⟨c, hc⟩ : V) ∈ U := by
      have : (δ ⟨c, hc⟩ : V) = -(u + (β ⟨c, hc⟩ : V)) := eq_neg_of_add_eq_zero_right e.symm
      rw [this]
      exact U.neg_mem (U.add_mem hu (β _).2)
    have h1 : (δ ⟨c, hc⟩ : V) = 0 := Submodule.disjoint_def.1 hC.disjoint _ hδU (δ _).2
    have h2 : (⟨c, hc⟩ : C) = 0 := δ.injective (by rw [map_zero]; exact Subtype.ext h1)
    have hc0 : c = 0 := congrArg Subtype.val h2
    subst hc0
    have hβ0 : (β ⟨0, hc⟩ : V) = 0 := by
      rw [show (⟨0, hc⟩ : C) = 0 from rfl, map_zero]; rfl
    rw [h1, hβ0, add_zero, add_zero] at e
    rw [add_zero]
    exact e.symm
  refine ⟨LinearEquiv.ofInjectiveEndo B0 hinj, fun j => ?_, fun i v => ?_⟩
  · have hxj : x j ∈ U := Submodule.subset_span ⟨j, rfl⟩
    have e := hB0 ⟨x j, hxj⟩ 0
    simp only [map_zero, Submodule.coe_zero, add_zero] at e
    exact e
  · obtain ⟨u, hu, c, hc, rfl⟩ := hsplit v
    have hv : Ψ (B0 (u + c)) = Φ (u + c) := by
      rw [show u + c = ((⟨u, hu⟩ : U) : V) + ((⟨c, hc⟩ : C) : V) from rfl, hB0]
      simp only [map_add, hβ, hUv ⟨u, hu⟩, D, LinearMap.sub_apply, LinearMap.comp_apply,
        Submodule.subtype_apply, LinearEquiv.coe_coe]
      abel
    exact congrFun hv i

theorem glPair {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {a : ℕ}
    (x y : Fin a → V) (ξ η : Fin a → Module.Dual K V) (hx : LinearIndependent K x)
    (hy : LinearIndependent K y) (hξ : LinearIndependent K ξ) (hη : LinearIndependent K η)
    (h : ∀ i j, ξ i (x j) = η i (y j)) :
    ∃ A : V ≃ₗ[K] V, (∀ j, A (x j) = y j) ∧ ∀ i v, η i (A v) = ξ i v := by
  obtain ⟨A0, hA0⟩ := trans_tuple x y hx hy
  set η' : Fin a → Module.Dual K V := fun i => η i ∘ₗ A0.toLinearMap
  have hη' : LinearIndependent K η' := by
    rw [Fintype.linearIndependent_iff] at hη ⊢
    intro c hc i
    apply hη c _ i
    ext v
    have e := LinearMap.congr_fun hc (A0.symm v)
    simpa [η'] using e
  obtain ⟨B, hBx, hB⟩ := fix_tuple x hx ξ η' hξ hη' (fun i j => by simp [η', hA0, h])
  refine ⟨B.trans A0, fun j => by simp [hBx, hA0], fun i v => ?_⟩
  simpa [η'] using hB i v

end Formalism.L2.SG.Pf.NcX.LT.GLP
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RealCovolume
section
noncomputable section

open MeasureTheory
open scoped Matrix

namespace Formalism.L2.SG.Pf.RealCovolume

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def reCo : (ι → κ → ℂ) ≃ₗ[ℝ] (ι × κ × Fin 2 → ℝ) where
  toFun a p := if p.2.2 = 0 then (a p.1 p.2.1).re else (a p.1 p.2.1).im
  invFun x i c := ⟨x (i, c, 0), x (i, c, 1)⟩
  map_add' a b := by funext p; by_cases h : p.2.2 = 0 <;> simp [h]
  map_smul' r a := by funext p; by_cases h : p.2.2 = 0 <;> simp [h]
  left_inv a := by funext i c; apply Complex.ext <;> simp
  right_inv x := by
    funext p
    obtain ⟨i, c, t⟩ := p
    fin_cases t <;> simp

theorem reCo_apply (a : ι → κ → ℂ) (p : ι × κ × Fin 2) :
    reCo a p = if p.2.2 = 0 then (a p.1 p.2.1).re else (a p.1 p.2.1).im := rfl

def bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ) := (Pi.basisFun ℝ (ι × κ × Fin 2)).map reCo.symm

theorem bstd_repr (a : ι → κ → ℂ) (p : ι × κ × Fin 2) : (bstd : Module.Basis _ ℝ (ι → κ → ℂ)).repr a p = reCo a p := by
  first
  | rfl
  | simp [bstd]

def Qf (g : κ → ℝ) (a b : ι → κ → ℂ) : ℝ := ∑ i, ∑ c, (a i c * star (b i c)).re * g c

theorem Qf_eq (g : κ → ℝ) (a b : ι → κ → ℂ) :
    Qf g a b = ∑ p : ι × κ × Fin 2, reCo a p * reCo b p * g p.2.1 := by
  simp only [Qf, Fintype.sum_prod_type, Fin.sum_univ_two, reCo_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
  simp [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] <;> ring

def boxC : Set ℂ := {z | z.re ∈ Set.Ico (0 : ℝ) 1 ∧ z.im ∈ Set.Ico (0 : ℝ) 1}

theorem volume_boxC : volume boxC = 1 := by
  have h : boxC = Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    first
    | exact Iff.rfl
    | simp [boxC, Complex.measurableEquivRealProd, Complex.equivRealProdCLM]
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ico]
  simp

omit [DecidableEq ι] [DecidableEq κ] in
theorem volume_box : volume (Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : κ => boxC) = 1 := by
  simp [volume_pi_pi, volume_boxC]

omit [DecidableEq ι] [DecidableEq κ] in
theorem isAddHaar_vol : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := by
  first
  | infer_instance
  | exact Measure.pi.isAddHaarMeasure _

private theorem mem_fundamentalDomain_reindex_bstd_iff {N : ℕ} (e : Fin N ≃ ι × κ × Fin 2) (m : ι → κ → ℂ) :
    m ∈ ZSpan.fundamentalDomain ((bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ)).reindex e.symm) ↔
      ∀ p, reCo m p ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ZSpan.mem_fundamentalDomain]
  first
  | simp only [Module.Basis.repr_reindex_apply, Equiv.symm_symm, bstd_repr]
  | simp only [Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, bstd_repr]
  constructor
  · intro h p
    have := h (e.symm p)
    rwa [Equiv.apply_symm_apply] at this
  · intro h j
    exact h (e j)

theorem volume_fd_std {N : ℕ} (e : Fin N ≃ ι × κ × Fin 2) :
    volume (ZSpan.fundamentalDomain ((bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ)).reindex e.symm)) = 1 := by
  have hset : ZSpan.fundamentalDomain ((bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ)).reindex e.symm) =
      Set.pi Set.univ fun _ : ι => Set.pi Set.univ fun _ : κ => boxC := by
    ext m
    rw [mem_fundamentalDomain_reindex_bstd_iff]
    constructor
    · intro h
      rw [Set.mem_pi]
      intro i _
      rw [Set.mem_pi]
      intro c _
      show (m i c).re ∈ Set.Ico (0 : ℝ) 1 ∧ (m i c).im ∈ Set.Ico (0 : ℝ) 1
      exact ⟨by simpa [reCo_apply] using h (i, c, 0), by simpa [reCo_apply] using h (i, c, 1)⟩
    · intro h p
      obtain ⟨i, c, t⟩ := p
      have hi := Set.mem_pi.1 h i (Set.mem_univ _)
      have hic' := Set.mem_pi.1 hi c (Set.mem_univ _)
      have hic : (m i c).re ∈ Set.Ico (0 : ℝ) 1 ∧ (m i c).im ∈ Set.Ico (0 : ℝ) 1 := hic'
      rw [reCo_apply]
      fin_cases t
      · simpa using hic.1
      · simpa using hic.2
  rw [hset, volume_box]

theorem covol_of_gram {N : ℕ} (w : Fin N → (ι → κ → ℂ)) (g : κ → ℝ) (hg : ∀ c, g c ≠ 0)
    (hN : Fintype.card (ι × κ × Fin 2) = N)
    (hdet : (Matrix.of fun i j => Qf g (w i) (w j)).det ≠ 0) :
    Countable (AddSubgroup.closure (Set.range w)) ∧
    (∃ F : Set (ι → κ → ℂ), MeasurableSet F ∧
      ∀ v, ∃! a : AddSubgroup.closure (Set.range w), (a : ι → κ → ℂ) + v ∈ F) ∧
    ∀ F : Set (ι → κ → ℂ), MeasurableSet F →
      (∀ v, ∃! a : AddSubgroup.closure (Set.range w), (a : ι → κ → ℂ) + v ∈ F) →
        volume F = ENNReal.ofReal (√|(Matrix.of fun i j => Qf g (w i) (w j)).det| / ∏ i : ι, ∏ c : κ, |g c|) := by
  have hEqW : (Submodule.span ℤ (Set.range w)).toAddSubgroup = AddSubgroup.closure (Set.range w) := by
    refine le_antisymm ?_ ((AddSubgroup.closure_le _).2 Submodule.subset_span)
    intro x hx
    exact Submodule.span_induction (p := fun x _ => x ∈ AddSubgroup.closure (Set.range w))
      (fun y hy => AddSubgroup.subset_closure hy) (AddSubgroup.zero_mem _)
      (fun _ _ _ _ hx hy => AddSubgroup.add_mem _ hx hy) (fun a _ _ hx => AddSubgroup.zsmul_mem _ hx a) hx
  have hL : ∀ x : ι → κ → ℂ, x ∈ AddSubgroup.closure (Set.range w) ↔ ∃ c : Fin N → ℤ, ∑ i, c i • w i = x := by
    intro x
    rw [← hEqW, Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun]
  have hcount : Countable (AddSubgroup.closure (Set.range w)) := by
    refine Function.Surjective.countable
      (f := fun c : Fin N → ℤ => (⟨∑ i, c i • w i, (hL _).2 ⟨c, rfl⟩⟩ : AddSubgroup.closure (Set.range w))) ?_
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hL x).1 hx
    exact ⟨c, rfl⟩
  obtain ⟨e⟩ : Nonempty (Fin N ≃ ι × κ × Fin 2) := ⟨(Fintype.equivFinOfCardEq hN).symm⟩
  obtain ⟨b0, hb0def⟩ : ∃ b0 : Module.Basis (Fin N) ℝ (ι → κ → ℂ),
      b0 = (bstd : Module.Basis (ι × κ × Fin 2) ℝ (ι → κ → ℂ)).reindex e.symm := ⟨_, rfl⟩
  have hb0 : ∀ v k, b0.repr v k = reCo v (e k) := by
    intro v k
    rw [hb0def]
    first
    | rw [Module.Basis.repr_reindex_apply, Equiv.symm_symm, bstd_repr]
    | simp [bstd_repr]
  have hvol0 : volume (ZSpan.fundamentalDomain b0) = 1 := by
    rw [hb0def]
    exact volume_fd_std e
  have hGram : (Matrix.of fun i j => Qf g (w i) (w j)) =
      (b0.toMatrix w)ᵀ * Matrix.diagonal (fun k => g (e k).2.1) * b0.toMatrix w := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply,
      Module.Basis.toMatrix_apply, hb0, Qf_eq]
    rw [← e.sum_comp]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdetG : (Matrix.of fun i j => Qf g (w i) (w j)).det =
      (b0.toMatrix w).det * (b0.toMatrix w).det * ∏ k, g (e k).2.1 := by
    rw [hGram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    ring
  have hprod : ∏ k, g (e k).2.1 = ∏ i : ι, ∏ c : κ, (g c * g c) :=
    (e.prod_comp (fun p => g p.2.1)).trans (by simp only [Fintype.prod_prod_type, Fin.prod_univ_two])
  set P : ℝ := ∏ i : ι, ∏ c : κ, |g c| with hPdef
  have hP : 0 < P := Finset.prod_pos fun i _ => Finset.prod_pos fun c _ => abs_pos.mpr (hg c)
  have habs : |∏ k, g (e k).2.1| = P * P := by
    rw [hprod, hPdef]
    simp only [Finset.abs_prod, abs_mul, Finset.prod_mul_distrib]
  have hval : √|(Matrix.of fun i j => Qf g (w i) (w j)).det| / P = |(b0.toMatrix w).det| := by
    rw [hdetG, abs_mul, abs_mul, habs,
      show |(b0.toMatrix w).det| * |(b0.toMatrix w).det| * (P * P) = (|(b0.toMatrix w).det| * P) ^ 2 by ring,
      Real.sqrt_sq (mul_nonneg (abs_nonneg _) hP.le)]
    exact mul_div_cancel_right₀ _ hP.ne'
  have hdetM : (b0.toMatrix w).det ≠ 0 := by
    intro h
    apply hdet
    rw [hdetG, h]
    ring
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hMc : (b0.toMatrix w) *ᵥ c = 0 := by
      ext k
      have h1 := congrArg (fun v => b0.repr v k) hc
      simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
        smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
      simp only [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Pi.zero_apply]
      rw [← h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdetM hMc) i
  have hcard : Fintype.card (Fin N) = Module.finrank ℝ (ι → κ → ℂ) := by
    first
    | exact (Module.finrank_eq_card_basis b0).symm
    | exact (FiniteDimensional.finrank_eq_card_basis b0).symm
  have hsp : Submodule.span ℝ (Set.range w) = ⊤ := by
    first
    | exact Submodule.eq_top_of_finrank_eq ((finrank_span_eq_card hli).trans hcard)
    | exact Submodule.eq_top_of_finrank_eq ((finrank_span_eq_card hli).trans (by simpa using hcard))
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin N) ℝ (ι → κ → ℂ), ⇑b = w :=
    ⟨Module.Basis.mk hli hsp.ge, by simp⟩
  have hEq : (Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup = AddSubgroup.closure (Set.range w) := by
    rw [hb]
    exact hEqW
  refine ⟨hcount, ⟨ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, fun v => ?_⟩,
    fun F hFm hF => ?_⟩
  · rw [← hEq]
    obtain ⟨a, ha, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b v
    refine ⟨⟨a.1, a.2⟩, ha, fun a' ha' => ?_⟩
    exact Subtype.ext (congrArg Subtype.val (huniq ⟨a'.1, a'.2⟩ ha'))
  · haveI := hcount
    haveI : (volume : Measure (ι → κ → ℂ)).IsAddHaarMeasure := isAddHaar_vol
    have h1 : IsAddFundamentalDomain (AddSubgroup.closure (Set.range w)) F volume := by
      first
      | exact IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hF
      | exact IsAddFundamentalDomain.mk' hFm.nullMeasurableSet (by simpa only [AddSubgroup.vadd_def, vadd_eq_add] using hF)
    have h2 : IsAddFundamentalDomain (AddSubgroup.closure (Set.range w)) (ZSpan.fundamentalDomain b) volume := by
      rw [← hEq]
      exact ZSpan.isAddFundamentalDomain b volume
    rw [h1.measure_eq h2, ZSpan.measure_fundamentalDomain b volume b0, hvol0, mul_one, hval,
      Module.Basis.det_apply, hb]

end Formalism.L2.SG.Pf.RealCovolume
end
end

