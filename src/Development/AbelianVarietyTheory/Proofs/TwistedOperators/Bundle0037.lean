import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import GroundTheory.GlobalFields.TateThesis.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelCasselmanHolds
section
namespace GlobalTheory.Published

theorem BorelCasselman_holds : GlobalTheory.Published.BorelCasselman :=
  fun k _ _ _ _ n _ _ _ V _ _ π hπ =>
    ⟨GlobalTheory.IwahoriInj.iwahoriProj_injective k n V π hπ.1,
      GlobalTheory.SmGL.IwahoriOnto.iwahoriProj_surjective k n V π hπ⟩

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.StepData ValuativeRel Matrix Topology Filter
open scoped TensorProduct

namespace GlobalTheory.CentralExponent

section Abstract

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem exists_bound {π : Representation ℂ G V} (hπ : IsAdmissible π) (hU : IsUnitarisable π)
    {K N : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (a : G) (C : Set G)
    (hCK : ∀ c ∈ C, c ∈ K) (hfac : ∀ g ∈ K, ∃ x ∈ N, ∃ c ∈ C, g = x * c)
    (hcon : ∀ c ∈ C, a⁻¹ * c * a ∈ C) {u : V} (hu : ∀ g ∈ K, π g u = u) (l : V →ₗ[ℂ] ℂ)
    (hl : ∀ x ∈ N, ∀ v, l (π x v) = l v) : ∃ M : ℝ, ∀ r : ℕ, ‖l (π (a ^ r) u)‖ ≤ M := by
  obtain ⟨B, hB, hp, hi⟩ := hU
  let core : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => B y x
      conj_inner_symm := fun x y => (hB x y).symm
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · exact (hp x h).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        have := hp x h
        have hx' : B x x = 0 := hx
        simp [hx'] at this }
  letI : NormedAddCommGroup V := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore _
  have hin : ∀ x y : V, inner ℂ x y = B y x := fun _ _ => rfl
  have hn : ∀ g v, ‖π g v‖ = ‖v‖ := fun g v => by
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hin, hin, hi]
  haveI := hπ.2 K ho hc
  let L : fixed π K →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (l ∘ₗ (fixed π K).subtype)
  refine ⟨‖L‖ * ‖u‖, fun r => ?_⟩
  have hpow : ∀ c ∈ C, (a ^ r)⁻¹ * c * a ^ r ∈ C := by
    induction r with
    | zero => simp
    | succ r ih =>
      intro c hcC
      have := hcon _ (ih c hcC)
      convert this using 1
      rw [pow_succ]; group
  let f : V →ₗ[ℂ] ℂ × (fixed π K → ℂ) := l.prod (LinearMap.pi fun z => B.flip z.1)
  obtain ⟨v, hv, e⟩ := IwahoriOnto.exists_fixed_map_eq hπ.1 hc f (π (a ^ r) u) fun g hg => by
    refine Prod.ext ?_ (funext fun z => ?_)
    · obtain ⟨x, hx, c, hcC, rfl⟩ := hfac g hg
      show l _ = l _
      rw [map_mul, Module.End.mul_apply, hl x hx]
      conv_rhs => rw [← hu _ (hCK _ (hpow c hcC))]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 3
      group
    · show B _ z.1 = B _ z.1
      have hz : π g z.1 = z.1 := by simpa using z.2 ⟨g, hg⟩
      conv_lhs => rw [← hz, hi]
  have e1 : l v = l (π (a ^ r) u) := congrArg Prod.fst e
  have e2 : B v v = B (π (a ^ r) u) v := congrFun (congrArg Prod.snd e) ⟨v, hv⟩
  have hv' : ‖v‖ ≤ ‖u‖ := by
    have h1 : ‖v‖ * ‖v‖ ≤ ‖v‖ * ‖u‖ := by
      rw [← inner_self_eq_norm_mul_norm (𝕜 := ℂ), hin, e2, ← hin, ← hn (a ^ r) u]
      exact re_inner_le_norm _ _
    by_cases h : v = 0
    · simp [h]
    · exact le_of_mul_le_mul_left h1 (norm_pos_iff.2 h)
  rw [← e1]
  exact (L.le_opNorm ⟨v, hv⟩).trans (mul_le_mul_of_nonneg_left hv' (norm_nonneg _))

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mul_small {γ : (ValueGroupWithZero k)ˣ} {A B : Matrix n n k} (hA : IntM A)
    (hB : ∀ i j, valuation k (B i j) < γ) (i j : n) : valuation k ((A * B) i j) < γ := by
  refine Valuation.map_sum_lt _ γ.ne_zero fun s _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_left' (hA i s)).trans_lt (hB s j)

variable (n) in

def cong (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) : Subgroup (GL n k) where
  carrier := {g | ∀ i j, valuation k ((g.val - 1) i j) < γ}
  one_mem' := fun i j => by simp
  mul_mem' := by
    intro g h hg hh i j
    have h1 : g ∈ KOne k n := mem_KOne.2 fun i j => (hg i j).trans_le hγ
    have : (g * h).val - 1 = g.val * (h.val - 1) + (g.val - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [this]
    exact Valuation.map_add_lt _ (mul_small (intM_of_mem_KO (KOne_le_KO h1)) hh i j) (hg i j)
  inv_mem' := by
    intro g hg i j
    have h1 : g ∈ KOne k n := mem_KOne.2 fun i j => (hg i j).trans_le hγ
    have : (g⁻¹).val - 1 = (-(g⁻¹).val) * (g.val - 1) := by
      rw [neg_mul, mul_sub, Units.inv_mul]; simp
    rw [this]
    exact mul_small (intM_of_mem_KO (KOne_le_KO (inv_mem h1))).neg hg i j

theorem isOpen_cong (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) :
    IsOpen (cong n γ hγ : Set (GL n k)) := by
  have e : (cong n γ hγ : Set (GL n k)) = ⋂ i, ⋂ j,
      (fun g : GL n k => (g.val - 1) i j) ⁻¹' {x | valuation k x < γ} := by
    ext g; simp only [SetLike.mem_coe, Set.mem_iInter]; rfl
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.preimage ?_ ?_
  · exact (Units.continuous_val.sub continuous_const).matrix_elem i j
  · refine isOpen_iff_mem_nhds.2 fun x hx => (IsValuativeTopology.mem_nhds_iff).2 ⟨γ, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact Valuation.map_add_lt (valuation k) (g := γ) hx hy

theorem isCompact_cong (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) :
    IsCompact (cong n γ hγ : Set (GL n k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (isOpen_cong γ hγ))
    fun _ hg => KOne_le_KO (mem_KOne.2 fun i j => (hg i j).trans_le hγ)

theorem exists_cong_subset {U : Set (GL n k)} (hU : U ∈ 𝓝 (1 : GL n k)) :
    ∃ (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1), ∀ g ∈ cong n γ hγ, g ∈ U := by
  rw [SplitFlip.isEmbedding_val_GL.nhds_eq_comap] at hU
  obtain ⟨T, hT, hTU⟩ := hU
  have h1 : (fun A : Matrix n n k => A + 1) ⁻¹' T ∈ 𝓝 (0 : Matrix n n k) :=
    (continuous_add_right _).continuousAt.preimage_mem_nhds (by simpa using hT)
  have h2 : Tendsto (fun p : (ValueGroupWithZero k)ˣ × Matrix n n k =>
      if ∀ i j, valuation k (p.2 i j) < p.1 then p.2 else 0) (atBot ×ˢ ⊤) (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    rw [Matrix.zero_apply, (IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
    intro γ _
    filter_upwards [prod_mem_prod (mem_atBot γ) univ_mem] with p hp
    split_ifs with h
    · exact (h i j).trans_le hp.1
    · simp
  obtain ⟨γ, hγ1, hγ⟩ := ((eventually_le_atBot 1).and (mem_prod_top.1 (h2 h1))).exists
  refine ⟨γ, hγ1, fun g hg => hTU ?_⟩
  have := hγ (g.val - 1)
  have hg' : ∀ i j, valuation k ((g.val - 1) i j) < γ := hg
  rw [Set.mem_preimage, Set.mem_preimage, if_pos hg', sub_add_cancel] at this
  exact this

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

theorem cong_factor (e : a ⊕ b ≃ n) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) :
    ∀ g ∈ cong n γ hγ, ∃ x ∈ unipRad k (two e), ∃ c ∈ cong n γ hγ ⊓ parabLower k (two e), g = x * c := by
  intro g hg
  let M : Matrix n n k := Matrix.of fun i j => if (e.symm j).isLeft then (1 : Matrix n n k) i j else g.val i j
  have hM : ∀ i j, valuation k ((M - 1) i j) < γ := fun i j => by
    by_cases h : (e.symm j).isLeft
    · simp [M, h]
    · simpa [M, h] using hg i j
  obtain ⟨p, -, hp⟩ := exists_mem_KOne (M := M) fun i j => (hM i j).trans_le hγ
  have hpK : p ∈ cong n γ hγ := fun i j => hp ▸ hM i j
  have hpP : p ∈ parab k (two e) := (mem_parab_two k).2 fun j i => by simp [hp, M, one_apply]
  let q : parab k (two e) := ⟨_, leviEmb_mem_parab k (two e) (leviProj k (two e) ⟨p, hpP⟩)⟩
  have hqK : q.1 ∈ cong n γ hγ := by
    intro i j
    obtain ⟨⟨s, i⟩, rfl⟩ := (two e).surjective i
    obtain ⟨⟨t, j⟩, rfl⟩ := (two e).surjective j
    by_cases h : s = t
    · subst h
      have := hpK (two e ⟨s, i⟩) (two e ⟨s, j⟩)
      simpa [q] using this
    · rw [Matrix.sub_apply, leviEmb_apply_ne k (two e) _ h, one_apply_ne (by simp [h])]
      simp
  refine ⟨((⟨p, hpP⟩ * q⁻¹ : parab k (two e)) : GL n k), (coe_mem_unipRad k _).2 ?_, q * (p⁻¹ * g),
    Subgroup.mem_inf.2 ⟨mul_mem hqK (mul_mem (inv_mem hpK) hg), mul_mem (leviEmb_mem_parabLower k _ _)
      ((mem_parabLower_two k).2 fun i j => ?_)⟩, by simp [mul_assoc]⟩
  · rw [map_mul, map_inv, leviProj_leviEmb, mul_inv_cancel]
  · have : (p⁻¹ * g).val (e (.inl i)) (e (.inr j)) = (p⁻¹ * p).val (e (.inl i)) (e (.inr j)) := by
      simp only [Units.val_mul, mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      simp [hp, M]
    rw [this, inv_mul_cancel, Units.val_one, one_apply_ne (by simp)]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem val_emb₂_scalar (e : a ⊕ b ≃ n) (z : kˣ) :
    (emb₂ k e (GeneralLinearGroup.scalar a z, 1)).val =
      diagonal fun i => if (e.symm i).isLeft then (z : k) else 1 := by
  rw [val_emb₂]
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [GeneralLinearGroup.scalar, diagonal_apply, one_apply]

theorem cong_contract (e : a ⊕ b ≃ n) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1) {z : kˣ}
    (hz : valuation k (z : k) ≤ 1) : ∀ c ∈ cong n γ hγ ⊓ parabLower k (two e),
      (emb₂ k e (GeneralLinearGroup.scalar a z, 1))⁻¹ * c * emb₂ k e (GeneralLinearGroup.scalar a z, 1) ∈
        cong n γ hγ ⊓ parabLower k (two e) := by
  intro c hcc
  obtain ⟨hc, hc'⟩ := Subgroup.mem_inf.1 hcc
  have hm : emb₂ k e (GeneralLinearGroup.scalar a z, 1) ∈ parabLower k (two e) :=
    leviEmb_mem_parabLower k _ _
  refine Subgroup.mem_inf.2 ⟨fun i j => ?_, mul_mem (mul_mem (inv_mem hm) hc') hm⟩
  have h1 := hc i j
  rw [← map_inv, Prod.inv_mk, ← map_inv, inv_one, Units.val_mul, Units.val_mul, val_emb₂_scalar,
    val_emb₂_scalar, Matrix.sub_apply, mul_diagonal, diagonal_mul]
  rw [Matrix.sub_apply] at h1
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j
  · simpa [mul_comm, mul_left_comm] using h1
  · simp [(mem_parabLower_two k).1 hc' i j, one_apply]
  · simp only [one_apply, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, if_false, sub_zero] at h1 ⊢
    simpa using (mul_le_of_le_one_right' hz).trans_lt h1
  · simpa using h1

end Local

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n a b : Type} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  {V X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

variable (k) in
theorem exists_nabs_lt_one : ∃ z : kˣ, valuation k (z : k) ≤ 1 ∧ nabs k z < 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by simpa using hϖ.ne_zero
  refine ⟨Units.mk0 _ h0, ϖ.2, ?_⟩
  rw [nabs_uniformiser hϖ (x := Units.mk0 _ h0) rfl]
  refine inv_lt_one_of_one_lt₀ ?_
  rw [resCard]
  exact_mod_cast Finite.one_lt_card

end Main

end GlobalTheory.CentralExponent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminedOnOpenStratum
section
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.OpenStratumMaps

section General

variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]

theorem exists_factor {ρ : Representation F G V} {σ : Representation F G W} {τ : Representation F G U}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (q : ρ.IntertwiningMap τ)
    (hq : ∀ v, f v = 0 → q v = 0) : ∃ q' : σ.IntertwiningMap τ, ∀ v, q' (f v) = q v := by
  obtain ⟨s, hs⟩ := f.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ w, f (s w) = w := fun w => congr($hs w)
  have key : ∀ v, q (s (f v)) = q v := fun v => by
    rw [← sub_eq_zero, ← map_sub]
    apply hq
    rw [map_sub, hs', sub_self]
  refine ⟨⟨q.toLinearMap ∘ₗ s, fun g => ?_⟩, key⟩
  ext w
  obtain ⟨v, rfl⟩ := hf w
  show q (s (σ g (f v))) = τ g (q (s (f v)))
  rw [← f.isIntertwining, key, key, q.isIntertwining]

def contraction (ρ : Representation F G V) (σ : Representation F H W) (l : W →ₗ[F] F) :
    Representation.IntertwiningMap ((extTensor ρ σ).comp (MonoidHom.inl G H)) ρ where
  toLinearMap := (TensorProduct.rid F V).toLinearMap ∘ₗ l.lTensor V
  isIntertwining' g := by
    refine TensorProduct.ext' fun v w => ?_
    show TensorProduct.rid F V (l.lTensor V (extTensor ρ σ (g, 1) (v ⊗ₜ w))) =
      ρ g (TensorProduct.rid F V (l.lTensor V (v ⊗ₜ w)))
    rw [extTensor_tmul]
    simp

theorem step {ρ : Representation F G V} {σ : Representation F G W} {τ : Representation F G U}
    (S T : Subrepresentation ρ) (e : (subQuot S T).Equiv σ)
    (h : ∀ f : σ.IntertwiningMap τ, ∀ w, f w = 0) (q : ρ.IntertwiningMap τ)
    (hq : ∀ v ∈ T.toSubmodule, q v = 0) : ∀ v ∈ S.toSubmodule, q v = 0 := by
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) :=
    ⟨Submodule.mkQ _, fun g => LinearMap.ext fun v => rfl⟩
  let qS : S.toRepresentation.IntertwiningMap τ :=
    ⟨q.toLinearMap ∘ₗ S.toSubmodule.subtype, fun g => LinearMap.ext fun v => q.isIntertwining _ _ g v⟩
  obtain ⟨q', hq'⟩ := exists_factor (e.toIntertwiningMap.comp p)
    (e.toLinearEquiv.surjective.comp (Submodule.mkQ_surjective _)) qS (fun v hv => by
      have h1 : e.toLinearEquiv (Submodule.Quotient.mk v) = 0 := hv
      rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h1
      exact hq _ h1)
  intro v hv
  exact (hq' ⟨v, hv⟩).symm.trans (h q' _)

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.OpenStratumMaps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfOrthogonalSchrodingerGaussian
section
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap

open scoped FourierTransform RealInnerProductSpace Real

namespace GlobalTheory.RealWeil

theorem eq_zero_of_inner_rhoSch_gaussian : ∀ (l : Type) [Fintype l] (k : Sch l),
    (∀ w : l ⊕ l → ℝ, inner ℂ ((rhoSch w (GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l))).toLp 2 volume)
      (k.toLp 2 volume) = 0) → k = 0 := by
  intro l _ k h
  set G := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hG
  let m : EuclideanSpace ℝ l → ℂ := fun x => G x * k x
  have hGn : ∀ x, ‖G x‖ ≤ 1 := fun x => by
    rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := Real.pi_pos
    nlinarith [sq_nonneg ‖x‖]
  have hm_cont : Continuous m := G.continuous.mul k.continuous
  have hm_int : Integrable m := k.integrable.norm.mono' hm_cont.aestronglyMeasurable
    (ae_of_all _ fun x => by
      simp only [m, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hGn x))
  have hF : 𝓕 m = 0 := by
    funext q
    have hq := h (Sum.elim 0 (fun i => q i))
    have hp : pPart (Sum.elim 0 (fun i => q i) : l ⊕ l → ℝ) = 0 := by
      ext i; simp [pPart]
    have hqq : qPart (Sum.elim 0 (fun i => q i) : l ⊕ l → ℝ) = q := by
      ext i; simp [qPart]
    rw [SchwartzMap.inner_toL2_toL2_eq _ _ volume] at hq
    rw [Real.fourier_eq', Pi.zero_apply, ← hq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [m, coe_rhoSch, rhoFun, phase, hp, hqq, add_zero, inner_zero_left, mul_zero, RCLike.inner_apply,
      map_mul, smul_eq_mul]
    rw [← Complex.exp_conj]
    have hGc : (starRingEnd ℂ) (G x) = G x := by
      rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.conj_ofReal]
    rw [hGc]
    have : (starRingEnd ℂ) (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * Complex.I) =
        ((-2 * π * ⟪x, q⟫ : ℝ) : ℂ) * Complex.I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I, real_inner_comm]
      push_cast
      ring
    rw [this]
    ring
  have hm0 : m = 0 := by
    have hi : Integrable (𝓕 m) := by rw [hF]; exact integrable_zero _ _ _
    rw [← hm_cont.fourierInv_fourier_eq hm_int hi, hF]
    funext v
    simp [Real.fourierInv_eq]
  ext x
  have hx := congrFun hm0 x
  simp only [m, Pi.zero_apply, mul_eq_zero] at hx
  rcases hx with hx | hx
  · exfalso
    rw [hG, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_eq_zero] at hx
    exact (Real.exp_pos _).ne' hx
  · simpa using hx

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
section
namespace GlobalTheory.LocAsm

def exOne {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) : ∀ b, X b → ℂ := fun b x =>
  match b, x with
  | .ex _ _, _ => 1
  | .theta i j, x => φ (.theta i j) x

@[simp] theorem exOne_ex {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) (i j : ℕ) (x : X (.ex i j)) :
    exOne φ (.ex i j) x = 1 := rfl

@[simp] theorem exOne_theta {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) (i j : ℕ) (x : X (.theta i j)) :
    exOne φ (.theta i j) x = φ (.theta i j) x := rfl

end GlobalTheory.LocAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqActStdLat
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem exists_eq_act_stdLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι]
    (L : Submodule 𝒪[k] (ι → k)) (hL : Submodule.IsLattice k L) :
    ∃ g : GL ι k, L = act g (stdLat k ι) := by
  haveI := hL
  haveI : Module.Free 𝒪[k] L := Submodule.IsLattice.free k L
  haveI : Module.Finite 𝒪[k] L := Module.Finite.iff_fg.mpr hL.fg
  have hr : Module.finrank 𝒪[k] L = Fintype.card ι := Submodule.IsLattice.finrank_of_pi k L
  let b : Module.Basis ι 𝒪[k] L :=
    (Module.finBasisOfFinrankEq 𝒪[k] L hr).reindex (Fintype.equivFin ι).symm
  let c : Module.Basis ι k (ι → k) := b.extendOfIsLattice k
  have hc : ∀ i, c i = (b i : ι → k) := fun i => Module.Basis.extendOfIsLattice_apply k b i
  let A : Matrix ι ι k := Matrix.of fun i j => (b j : ι → k) i
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have : A.col = c := by
      funext j i
      rw [hc]; rfl
    rw [this]; exact c.linearIndependent
  obtain ⟨g, hg⟩ := hA
  have key : ∀ a : ι → 𝒪[k], (g : Matrix ι ι k) *ᵥ (fun i => (a i : k))
      = ((∑ j, a j • b j : L) : ι → k) := by
    intro a
    funext i
    rw [hg, Submodule.coe_sum, Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply, Submodule.coe_smul, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]; rfl
  refine ⟨g, ?_⟩
  ext v
  rw [mem_act]
  constructor
  · intro hv
    refine ⟨fun i => (b.repr ⟨v, hv⟩ i : k), mem_stdLat.2 fun i => (b.repr ⟨v, hv⟩ i).2, ?_⟩
    rw [key, b.sum_repr]
  · rintro ⟨w, hw, rfl⟩
    rw [mem_stdLat] at hw
    have := key fun i => ⟨w i, hw i⟩
    change (g : Matrix ι ι k) *ᵥ w = _ at this
    rw [this]
    exact Subtype.property _

end GlobalTheory.RootEx.UnfoldShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLMulRightColumnsEqZeroOfRank
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

theorem exists_gl_mul_cols_eq_zero_of_rank (k m a b n : Type) [Field k] [Fintype m] [Fintype a]
    [Fintype b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (x : Matrix m n k)
    (hx : x.rank = Fintype.card a) :
    ∃ g : GL n k, ∀ i j, (x * g.val) i (e (Sum.inr j)) = 0 := by
  classical

  let f := x.mulVecLin
  obtain ⟨C, hKC⟩ := Submodule.exists_isCompl (LinearMap.ker f)
  have hcard : Fintype.card n = Fintype.card a + Fintype.card b := by
    rw [← Fintype.card_congr e, Fintype.card_sum]
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hrank : Module.finrank k (LinearMap.range f) = Fintype.card a := hx
  rw [hrank, Module.finrank_fintype_fun_eq_card, hcard] at hrn
  have hK : Module.finrank k (LinearMap.ker f) = Fintype.card b := by omega
  have hsum := Submodule.finrank_add_eq_of_isCompl hKC
  rw [hK, Module.finrank_fintype_fun_eq_card, hcard] at hsum
  have hC : Module.finrank k C = Fintype.card a := by omega
  let bK : Module.Basis b k (LinearMap.ker f) :=
    (Module.finBasisOfFinrankEq k (LinearMap.ker f) hK).reindex (Fintype.equivFin b).symm
  let bC : Module.Basis a k C := (Module.finBasisOfFinrankEq k C hC).reindex (Fintype.equivFin a).symm
  let B : Module.Basis n k (n → k) :=
    ((bC.prod bK).map (Submodule.prodEquivOfIsCompl C (LinearMap.ker f) hKC.symm)).reindex e
  have hB : ∀ j, f (B (e (Sum.inr j))) = 0 := by
    intro j
    simp [B, Module.Basis.reindex_apply, Module.Basis.map_apply, Module.Basis.prod_apply]
  let P := (Pi.basisFun k n).toMatrix B
  have : Invertible P := (Pi.basisFun k n).invertibleToMatrix B
  refine ⟨unitOfInvertible P, fun i j => ?_⟩
  show (x * P) i (e (Sum.inr j)) = 0
  have hcol : (x * P) i (e (Sum.inr j)) = f (B (e (Sum.inr j))) i := by
    simp [P, f, Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply]
  rw [hcol, hB j]
  rfl

end GlobalTheory
end

