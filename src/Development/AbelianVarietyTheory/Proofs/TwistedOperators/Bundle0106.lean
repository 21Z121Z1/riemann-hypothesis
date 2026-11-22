import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0092
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0229
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0203

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqOfIrreducible
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.InvFormUnique

theorem inner_eq_of_common_kernel_line {V H₁ H₂ ι : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (j₁ : V →ₗ[ℂ] H₁) (j₂ : V →ₗ[ℂ] H₂) (A A' : ι → Module.End ℂ V) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] (hA : ∀ i, ∀ w ∈ W, A i w ∈ W) (hA' : ∀ i, ∀ w ∈ W, A' i w ∈ W)
    (h₁ : ∀ i x y, inner ℂ (j₁ (A i x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (A' i y)))
    (h₂ : ∀ i x y, inner ℂ (j₂ (A i x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (A' i y)))
    (hinj : Function.Injective j₂) (v : V) (hv : ∀ i, A i v = 0)
    (hline : ∀ h, (∀ i, A i h = 0) → ∃ c : ℂ, c • v = h)
    (hn : inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v)) (y : V) (hy : y ∈ W) :
    inner ℂ (j₁ v) (j₁ y) = inner ℂ (j₂ v) (j₂ y) := by
  classical

  let f : W →ₗ[ℂ] H₂ := j₂ ∘ₗ W.subtype
  have hfi : Function.Injective f := hinj.comp Subtype.val_injective
  let e : W ≃ₗ[ℂ] LinearMap.range f := LinearEquiv.ofInjective f hfi
  let ψ : V →ₗ[ℂ] ℂ := (innerₛₗ ℂ (j₁ v)) ∘ₗ j₁ - (innerₛₗ ℂ (j₂ v)) ∘ₗ j₂
  have hψ : ∀ x, ψ x = inner ℂ (j₁ v) (j₁ x) - inner ℂ (j₂ v) (j₂ x) := fun x => by
    simp [ψ]
  let g : LinearMap.range f →ₗ[ℂ] ℂ := ψ ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap

  obtain ⟨u, huW, hrep⟩ : ∃ u ∈ W, ∀ z ∈ W, inner ℂ (j₂ u) (j₂ z) = ψ z := by
    let u' := (InnerProductSpace.toDual ℂ (LinearMap.range f)).symm (LinearMap.toContinuousLinearMap g)
    have key : ∀ s : LinearMap.range f, inner ℂ (u' : H₂) (s : H₂) = g s := by
      intro s
      rw [← Submodule.coe_inner]
      exact InnerProductSpace.toDual_symm_apply
    refine ⟨(e.symm u' : V), (e.symm u').2, fun z hz => ?_⟩
    have h1 := key (e ⟨z, hz⟩)
    have h2 : ((e ⟨z, hz⟩ : LinearMap.range f) : H₂) = j₂ z := LinearEquiv.ofInjective_apply _ _
    have h3 : ((u' : LinearMap.range f) : H₂) = j₂ (e.symm u' : V) := by
      conv_lhs => rw [← e.apply_symm_apply u']
      exact LinearEquiv.ofInjective_apply _ _
    rw [h2, h3] at h1
    rw [h1]
    simp [g]

  have hker : ∀ i, A i u = 0 := by
    intro i
    have horth : ∀ z ∈ W, inner ℂ (j₂ (A i u)) (j₂ z) = 0 := by
      intro z hz
      rw [h₂, hrep _ (hA' i z hz), hψ, ← h₁, ← h₂, hv]
      simp
    have h0 := horth _ (hA i u huW)
    rw [inner_self_eq_zero] at h0
    exact hinj (by rw [h0, map_zero])

  obtain ⟨c, hc⟩ := hline u hker
  have hψv : ψ v = 0 := by rw [hψ, hn, sub_self]
  have hψu : ψ u = 0 := by rw [← hc, map_smul, hψv, smul_zero]
  have hj : j₂ u = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), hrep u huW, hψu]
  have hy' := hrep y hy
  rw [hj, inner_zero_left, hψ] at hy'
  exact sub_eq_zero.mp hy'.symm

theorem adjZ_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : adjZ (Eab a b) = Eab b a := by
  unfold adjZ Eab Jm Formalism.UG.Jpq

  have hJ : (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1) : Mat p q) =
      Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, apply_ite]
  rw [hJ]
  rcases a with a | a <;> rcases b with b | b
  all_goals try exact (h : False).elim
  all_goals
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.single_apply]
    split_ifs with h1 h2 <;> (try obtain ⟨rfl, rfl⟩ := h1) <;> simp_all

theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  unfold IsKC Eab
  intro c d hcd
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd h

theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b ∧ sameBlock b a := by
  rcases a with i | i <;> rcases b with j | j
  all_goals first
    | exact ⟨True.intro, True.intro⟩
    | exact (h : False).elim

theorem sameBlock_refl {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> exact True.intro

private theorem mem_hwSub_iff' {p q : ℕ} {V0 : Type} [AddCommGroup V0] [Module ℂ V0]
    (f : Mat p q →ₗ[ℂ] Module.End ℂ V0) (μ : Ix p q → ℚ) (z : V0) :
    z ∈ hwSub f μ ↔ (∀ a, f (Eab a a) z = (μ a : ℂ) • z) ∧ ∀ a b, posC a b → f (Eab a b) z = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem inner_eq_of_irreducible (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁]
    [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (j₁ : M.V →ₗ[ℂ] H₁) (j₂ : M.V →ₗ[ℂ] H₂)
    (h₁ : ∀ Z x y, inner ℂ (j₁ (M.act Z x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (M.act (adjZ Z) y)))
    (h₂ : ∀ Z x y, inner ℂ (j₂ (M.act Z x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (M.act (adjZ Z) y)))
    (hinj : Function.Injective j₂) (hirr : IrrGK M) (μ : Ix p q → ℚ) (v : M.V) (hv : IsHW M.act μ v)
    (hdim : Module.finrank ℂ ↥(hwSub M.act μ) = 1)
    (hn : inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v)) (x y : M.V) :
    inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y) := by
  classical

  let N : Submodule ℂ M.V :=
    { carrier := {z | ∀ w, inner ℂ (j₁ z) (j₁ w) = inner ℂ (j₂ z) (j₂ w)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        intro w
        rw [map_add, map_add, inner_add_left, inner_add_left, ha, hb]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero, inner_zero_left, implies_true]
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        intro w
        rw [map_smul, map_smul, inner_smul_left, inner_smul_left, ha] }
  have hmemN : ∀ z, z ∈ N ↔ ∀ w, inner ℂ (j₁ z) (j₁ w) = inner ℂ (j₂ z) (j₂ w) := fun z => Iff.rfl

  have hNinv : ∀ Z, ∀ z ∈ N, M.act Z z ∈ N := by
    intro Z z hz
    rw [hmemN] at hz ⊢
    intro w
    rw [h₁, h₂, hz]
  obtain ⟨hv0, hvmem⟩ : v ≠ 0 ∧ v ∈ hwSub M.act μ := hv
  have hmem := (mem_hwSub_iff' M.act μ v).mp hvmem

  let A : ({ab : Ix p q × Ix p q // posC ab.1 ab.2} ⊕ Ix p q) → Module.End ℂ M.V :=
    Sum.elim (fun ab => M.act (Eab ab.1.1 ab.1.2)) (fun c => M.act (Eab c c) - (μ c : ℂ) • LinearMap.id)
  let A' : ({ab : Ix p q × Ix p q // posC ab.1 ab.2} ⊕ Ix p q) → Module.End ℂ M.V :=
    Sum.elim (fun ab => M.act (Eab ab.1.2 ab.1.1)) (fun c => M.act (Eab c c) - (μ c : ℂ) • LinearMap.id)
  have hh : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M.V →ₗ[ℂ] H),
      (∀ Z z w, inner ℂ (j (M.act Z z)) (j w) = inner ℂ (j z) (j (M.act (adjZ Z) w))) →
      ∀ i z w, inner ℂ (j (A i z)) (j w) = inner ℂ (j z) (j (A' i w)) := by
    intro H _ _ j hj
    rintro (⟨⟨a, b⟩, hab⟩ | c) z w
    · simp only [A, A', Sum.elim_inl]
      rw [hj, adjZ_Eab (sameBlock_of_posC hab).1]
    · simp only [A, A', Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
      rw [hj, adjZ_Eab (sameBlock_refl c)]
      all_goals simp
  have hAv : ∀ i, A i v = 0 := by
    rintro (⟨⟨a, b⟩, hab⟩ | c)
    · exact hmem.2 a b hab
    · simp only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hmem.1 c, sub_self]
  have hline : ∀ z, (∀ i, A i z = 0) → ∃ c : ℂ, c • v = z := by
    intro z hz0
    have hzmem : z ∈ hwSub M.act μ := by
      rw [mem_hwSub_iff']
      refine ⟨fun c => ?_, fun a b hab => hz0 (Sum.inl ⟨(a, b), hab⟩)⟩
      have hc0 := hz0 (Sum.inr c)
      simp only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hc0
      exact hc0
    have hne : (⟨v, hvmem⟩ : hwSub M.act μ) ≠ 0 := by
      rwa [Ne, Submodule.mk_eq_zero]
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hdim ⟨z, hzmem⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩

  have hvN : v ∈ N := by
    rw [hmemN]
    intro w
    obtain ⟨W, hWfin, hwW, hWst⟩ := M.kfin w
    have := hWfin
    have hWst' : ∀ Z, IsKC Z → ∀ u ∈ W, M.act Z u ∈ W := hWst
    have hAW : ∀ i, ∀ u ∈ W, A i u ∈ W := by
      rintro (⟨⟨a, b⟩, hab⟩ | c) u hu
      · exact hWst' _ (isKC_Eab (sameBlock_of_posC hab).1) u hu
      · simp only [A, Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
        exact W.sub_mem (hWst' _ (isKC_Eab (sameBlock_refl c)) u hu) (W.smul_mem _ hu)
    have hA'W : ∀ i, ∀ u ∈ W, A' i u ∈ W := by
      rintro (⟨⟨a, b⟩, hab⟩ | c) u hu
      · exact hWst' _ (isKC_Eab (sameBlock_of_posC hab).2) u hu
      · simp only [A', Sum.elim_inr, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
        exact W.sub_mem (hWst' _ (isKC_Eab (sameBlock_refl c)) u hu) (W.smul_mem _ hu)
    exact inner_eq_of_common_kernel_line j₁ j₂ A A' W hAW hA'W (hh H₁ j₁ h₁) (hh H₂ j₂ h₂) hinj v hAv
      hline hn w hwW

  obtain ⟨-, hirr2⟩ := hirr
  rcases hirr2 N hNinv with hN | hN
  · exact absurd ((Submodule.mem_bot ℂ).mp (hN ▸ hvN)) hv0
  · have hx : x ∈ N := by rw [hN]; exact Submodule.mem_top
    exact (hmemN x).mp hx y

end GlobalTheory.InvFormUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFunctionEquivalence
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.PsEquivar

open GlobalTheory.Dec.Local

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

theorem eventually_fderiv_ps (hl : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y * Jm ε = Jm ε * Y) :
    ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
      fderiv ℂ (ps ε lam τ w) z (z * Y) = ps ε lam τ w z * fderiv ℂ (fun y => τ (prJ ε y)) 1 Y ∧
      fderiv ℂ (ps ε lam τ w) z (Y * z) = fderiv ℂ (fun y => τ (prJ ε y)) 1 Y * ps ε lam τ w z := by
  have hf1 : HasFDerivAt (fun y => τ (prJ ε y)) (fderiv ℂ (fun y => τ (prJ ε y)) 1) 1 :=
    (eventually_differentiableAt_tau hτ).self_of_nhds.hasFDerivAt
  have hτ1 : τ 1 = 1 := hτ.2.1.1
  have hc : HasDerivAt (fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • Y) Y 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const Y).const_add (1 : Matrix (Fin n) (Fin n) ℂ)
  have hcJ : ∀ t : ℂ, prJ ε (1 + t • Y) = 1 + t • Y := fun t =>
    prJ_of_comm (by rw [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hY])
  have hτc : HasDerivAt (fun t : ℂ => τ (prJ ε (1 + t • Y))) (fderiv ℂ (fun y => τ (prJ ε y)) 1 Y) 0 :=
    hf1.comp_hasDerivAt_of_eq 0 hc (by simp)
  obtain ⟨hUo, hU1, hUd, -⟩ := psBasic n ε lam W τ w hl hτ
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℂ).symm.toLinearMap
  have hdiff : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), DifferentiableAt ℂ (ps ε lam τ w) z := by
    have hm : L 1 ∈ {z : Fin n → Fin n → ℂ | Matrix.of z ∈ U1 ε} := hU1 1 Matrix.PosDef.one
    filter_upwards [L.continuous.continuousAt.preimage_mem_nhds (hUo.mem_nhds hm)] with z hz
    exact ((hUd (L z) hz).differentiableAt (hUo.mem_nhds hz)).comp z L.differentiableAt
  have hmul := eventually_ps_mul psBasic GlobalTheory.Dec.Equivar.psEquiv hl hτ
  have hR : ∀ᶠ p : Matrix (Fin n) (Fin n) ℂ × ℂ in 𝓝 ((1 : Matrix (Fin n) (Fin n) ℂ), (0 : ℂ)),
      ps ε lam τ w (p.1 * (1 + p.2 • Y)) = ps ε lam τ w p.1 * τ (prJ ε (1 + p.2 • Y)) := by
    have hcont : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × ℂ =>
        (((1 : Matrix (Fin n) (Fin n) ℂ), p.1), ((1 : Matrix (Fin n) (Fin n) ℂ) + p.2 • Y,
          (1 : Matrix (Fin n) (Fin n) ℂ)))) := by fun_prop
    have ht := hcont.tendsto ((1 : Matrix (Fin n) (Fin n) ℂ), (0 : ℂ))
    simp only [zero_smul, add_zero] at ht
    filter_upwards [ht.eventually hmul] with p hp
    have key := sub_eq_zero.mp hp
    simp only [prJ_one, hτ1, one_mul, mul_one] at key
    calc ps ε lam τ w (p.1 * (1 + p.2 • Y)) = ps ε lam τ w (p.1 * prJ ε (1 + p.2 • Y)) := by rw [hcJ]
      _ = _ := key
  have hL : ∀ᶠ p : Matrix (Fin n) (Fin n) ℂ × ℂ in 𝓝 ((1 : Matrix (Fin n) (Fin n) ℂ), (0 : ℂ)),
      ps ε lam τ w ((1 + p.2 • Y) * p.1) = τ (prJ ε (1 + p.2 • Y)) * ps ε lam τ w p.1 := by
    have hcont : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × ℂ =>
        (((1 : Matrix (Fin n) (Fin n) ℂ) + p.2 • Y, (1 : Matrix (Fin n) (Fin n) ℂ)),
          ((1 : Matrix (Fin n) (Fin n) ℂ), p.1))) := by fun_prop
    have ht := hcont.tendsto ((1 : Matrix (Fin n) (Fin n) ℂ), (0 : ℂ))
    simp only [zero_smul, add_zero] at ht
    filter_upwards [ht.eventually hmul] with p hp
    have key := sub_eq_zero.mp hp
    simp only [prJ_one, hτ1, one_mul, mul_one] at key
    calc ps ε lam τ w ((1 + p.2 • Y) * p.1) = ps ε lam τ w (prJ ε (1 + p.2 • Y) * p.1) := by rw [hcJ]
      _ = _ := key
  rw [nhds_prod_eq] at hR hL
  filter_upwards [hdiff, hR.curry, hL.curry] with z hz hRz hLz
  have hps := hz.hasFDerivAt
  constructor
  · have h1 : HasDerivAt (fun t : ℂ => ps ε lam τ w (z * (1 + t • Y)))
        (fderiv ℂ (ps ε lam τ w) z (z * Y)) 0 :=
      hps.comp_hasDerivAt_of_eq 0 (hc.const_mul z) (by simp)
    have h2 : HasDerivAt (fun t : ℂ => ps ε lam τ w z * τ (prJ ε (1 + t • Y)))
        (ps ε lam τ w z * fderiv ℂ (fun y => τ (prJ ε y)) 1 Y) 0 := hτc.const_mul _
    exact h1.unique (h2.congr_of_eventuallyEq hRz)
  · have h1 : HasDerivAt (fun t : ℂ => ps ε lam τ w ((1 + t • Y) * z))
        (fderiv ℂ (ps ε lam τ w) z (Y * z)) 0 :=
      hps.comp_hasDerivAt_of_eq 0 (hc.mul_const z) (by simp)
    have h2 : HasDerivAt (fun t : ℂ => τ (prJ ε (1 + t • Y)) * ps ε lam τ w z)
        (fderiv ℂ (fun y => τ (prJ ε y)) 1 Y * ps ε lam τ w z) 0 := hτc.mul_const _
    exact h1.unique (h2.congr_of_eventuallyEq hLz)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
  {j : W →ₗᵢ[ℂ] V}

theorem fderiv_tau_of_inK {abelian₂ : Fin n → ℝ} (hτ : IsTau ε abelian₂ τ w) (hT : TauTie ε E j τ)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) {v v' : W} (hv : j v' = actM E (Y.map star) (j v)) :
    fderiv ℂ (fun y => τ (prJ ε y)) 1 Y v = v' := by
  have hf1 : HasFDerivAt (fun y => τ (prJ ε y)) (fderiv ℂ (fun y => τ (prJ ε y)) 1) 1 :=
    (eventually_differentiableAt_tau hτ).self_of_nhds.hasFDerivAt
  have hγ : HasDerivAt (fun u : ℂ => NormedSpace.exp (u • Y)) Y 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℂ) Y (0 : ℂ)
  have hcommc : ∀ u : ℂ, prJ ε (NormedSpace.exp (u • Y)) = NormedSpace.exp (u • Y) := fun u =>
    prJ_of_comm ((Commute.smul_left (show Commute Y (Jm ε) from hY.2) u).exp_left).eq
  have hg : HasDerivAt (fun u : ℂ => τ (NormedSpace.exp (u • Y)) v)
      (fderiv ℂ (fun y => τ (prJ ε y)) 1 Y v) ((0 : ℝ) : ℂ) := by
    have h1 := hf1.comp_hasDerivAt_of_eq 0 hγ (by simp)
    have h2 := (ContinuousLinearMap.apply ℂ W v).hasFDerivAt.comp_hasDerivAt 0 h1
    rw [Complex.ofReal_zero]
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp [hcommc u]
  have hh : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h4 : HasDerivAt (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y)) v)
      (fderiv ℂ (fun y => τ (prJ ε y)) 1 Y v) 0 := by
    have h3 := HasDerivAt.scomp (x := (0 : ℝ)) hg hh
    rw [one_smul] at h3
    exact h3
  exact ((hT Y hY v v' hv).unique h4).symm

theorem actM_single (a b : Fin n) : actM E (Matrix.single a b (1 : ℂ)) = E a b := by
  simp [actM, Matrix.single_apply, ite_and]

theorem actM_add (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by
  simp [actM, add_smul, Finset.sum_add_distrib]

theorem actM_smul (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : actM E (c • X) = c • actM E X := by
  simp [actM, Finset.smul_sum, mul_smul]

theorem single_comm_Jm {a b : Fin n} (h : ε a = ε b) :
    Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b (1 : ℂ) := by
  ext i k
  rw [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  by_cases h1 : a = i ∧ b = k
  · rcases h1 with ⟨rfl, rfl⟩
    rw [if_pos ⟨rfl, rfl⟩, h, one_mul, mul_one]
  · rw [if_neg h1, zero_mul, mul_zero]

theorem inK_of_skew {Y : Matrix (Fin n) (Fin n) ℂ} (h : Yᴴ = -Y) (h' : Y * Jm ε = Jm ε * Y) : inK ε Y := by
  refine ⟨?_, h'⟩
  show Yᴴ * Jm ε + Jm ε * Y = 0
  rw [h, neg_mul, h', neg_add_cancel]

private lemma actM_mem_kSpan_of_block_diagonal {u : V} (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : ∀ c d, ε c ≠ ε d → Z c d = 0)
    {x : V} (hx : x ∈ kSpan ε E u) : actM E Z x ∈ kSpan ε E u := by
  unfold actM
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun d _ => ?_
  by_cases hcd : ε c = ε d
  · rw [LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    simp only [kSpan, Submodule.mem_sInf] at hx ⊢
    exact fun S hS => hS.2 c d hcd x (hx S hS)
  · rw [hZ c d hcd, zero_smul, LinearMap.zero_apply]
    exact Submodule.zero_mem _

theorem fderiv_tau_thE {abelian₂ Λ : Fin n → ℝ} {u : V} (hτ : IsTau ε abelian₂ τ w) (hL : LowData ε E Λ u j)
    (hT : TauTie ε E j τ) {a b : Fin n} (hab : ε a = ε b) (v : W) :
    j (fderiv ℂ (fun y => τ (prJ ε y)) 1 (thE ε (a, b)) v) = E a b (j v) := by
  set D := fderiv ℂ (fun y => τ (prJ ε y)) 1 with hD
  set S : Matrix (Fin n) (Fin n) ℂ := Matrix.single b a 1 with hS
  set T : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 with hT'
  have hSh : Sᴴ = T := by simp [S, T]
  have hTh : Tᴴ = S := by simp [S, T]
  have hSJ : S * Jm ε = Jm ε * S := single_comm_Jm hab.symm
  have hTJ : T * Jm ε = Jm ε * T := single_comm_Jm hab
  have hA : inK ε (S - T) := inK_of_skew (by rw [Matrix.conjTranspose_sub, hSh, hTh, neg_sub])
    (by rw [sub_mul, mul_sub, hSJ, hTJ])
  have hB : inK ε (Complex.I • (S + T)) := inK_of_skew
    (by simp [Matrix.conjTranspose_smul, hSh, hTh, add_comm])
    (by rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, hSJ, hTJ])
  have hS0 : ∀ c d, ε c ≠ ε d → S c d = 0 := by
    intro c d hcd
    simp only [S, Matrix.single_apply]
    split_ifs with h1
    · rcases h1 with ⟨rfl, rfl⟩
      exact absurd hab.symm hcd
    · rfl
  have hT0 : ∀ c d, ε c ≠ ε d → T c d = 0 := by
    intro c d hcd
    simp only [T, Matrix.single_apply]
    split_ifs with h1
    · rcases h1 with ⟨rfl, rfl⟩
      exact absurd hab hcd
    · rfl
  have hjv : j v ∈ kSpan ε E u := by
    rw [← hL.2.2.2.2]
    exact LinearMap.mem_range_self _ v
  have hmA : actM E ((S - T).map star) (j v) ∈ LinearMap.range j.toLinearMap := by
    rw [hL.2.2.2.2]
    exact actM_mem_kSpan_of_block_diagonal _ (fun c d hcd => by simp [hS0 c d hcd, hT0 c d hcd]) hjv
  have hmB : actM E ((Complex.I • (S + T)).map star) (j v) ∈ LinearMap.range j.toLinearMap := by
    rw [hL.2.2.2.2]
    exact actM_mem_kSpan_of_block_diagonal _ (fun c d hcd => by simp [hS0 c d hcd, hT0 c d hcd]) hjv
  obtain ⟨xA, hxA⟩ := LinearMap.mem_range.mp hmA
  obtain ⟨xB, hxB⟩ := LinearMap.mem_range.mp hmB
  have hDA : D (S - T) v = xA := fderiv_tau_of_inK hτ hT hA hxA
  have hDB : D (Complex.I • (S + T)) v = xB := fderiv_tau_of_inK hτ hT hB hxB
  have hAm : (S - T).map star = S + (-1 : ℂ) • T := by
    ext c d
    simp only [S, T, Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.single_apply]
    split_ifs <;> simp <;> ring
  have hBm : (Complex.I • (S + T)).map star = (-Complex.I) • S + (-Complex.I) • T := by
    ext c d
    simp only [S, T, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply]
    split_ifs <;> simp <;> ring
  have hthE : thE ε (a, b) = -((1 / 2 : ℂ) • ((S - T) - Complex.I • (Complex.I • (S + T)))) := by
    rw [smul_smul, Complex.I_mul_I]
    simp only [thE, Formalism.REAL.sgn, hab, if_true, Complex.ofReal_one]
    module
  rw [hthE, map_neg, map_smul, map_sub, map_smul]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply]
  rw [hDA, hDB]
  simp only [map_neg, map_smul, map_sub]
  have hxA' : j xA = actM E ((S - T).map star) (j v) := hxA
  have hxB' : j xB = actM E ((Complex.I • (S + T)).map star) (j v) := hxB
  rw [hxA', hxB', hAm, hBm, actM_add, actM_add, actM_smul, actM_smul, actM_smul, actM_single,
    actM_single]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_smul, mul_neg,
    Complex.I_mul_I]
  module

theorem psFunEquiv : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam →
    IsTau ε (lowK ε lam) τ w → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (u : V) (j : W →ₗᵢ[ℂ] V), LowData ε E (lowK ε lam) u j →
    TauTie ε E j τ → FunEquiv ε E j (ps ε lam τ w) := by
  intro n ε lam W _ _ τ w hl hτ V _ _ E u j hL hT a b hab
  have hY : thE ε (a, b) * Jm ε = Jm ε * thE ε (a, b) := by
    simp only [thE, smul_mul_assoc, mul_smul_comm, single_comm_Jm hab.symm]
  filter_upwards [eventually_fderiv_ps hl hτ hY] with z hz
  refine ⟨fun x x' hx => ?_, fun y y' x hy => ?_⟩
  · rw [hz.1, ContinuousLinearMap.mul_apply]
    congr 1
    apply j.injective
    rw [fderiv_tau_thE hτ hL hT hab x, hx]
  · rw [hz.2, ContinuousLinearMap.mul_apply, ← j.inner_map_map y, fderiv_tau_thE hτ hL hT hab,
      ← j.inner_map_map y', hy, hL.2.1 b a]
    simp [Formalism.REAL.sgn, hab]

end GlobalTheory.SphJet.PsEquivar
end
end

