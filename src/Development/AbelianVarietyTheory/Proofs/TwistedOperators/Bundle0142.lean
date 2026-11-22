import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorDoublyIndexedSwapBlocksEquiv
section
open scoped TensorProduct

noncomputable section

open PiTensorProduct GlobalTheory.PRep GlobalTheory.JacStages

namespace GlobalTheory.SmGL

section SwapTensor

def sigmaPairSwap (α β : Type) : (Σ _ : α, β) ≃ (Σ _ : β, α) where
  toFun p := ⟨p.2, p.1⟩
  invFun q := ⟨q.2, q.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {α β : Type} [Finite α] [Finite β]
  (Y : α → β → Type) [∀ i j, AddCommGroup (Y i j)] [∀ i j, Module ℂ (Y i j)]

theorem exists_pairCurry : ∃ e : (⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2) ≃ₗ[ℂ] ⨂[ℂ] i, ⨂[ℂ] j, Y i j,
    ∀ x : ∀ p : (Σ _ : α, β), Y p.1 p.2, e (tprod ℂ x) = tprod ℂ fun i => tprod ℂ fun j => x ⟨i, j⟩ := by
  classical
  exact ⟨sigmaCurry (fun p : (Σ _ : α, β) => Y p.1 p.2),
    sigmaCurry_tprod (fun p : (Σ _ : α, β) => Y p.1 p.2)⟩

omit [Finite α] [Finite β] in

theorem exists_pairSwap :
    ∃ e : (⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2) ≃ₗ[ℂ] ⨂[ℂ] q : (Σ _ : β, α), Y q.2 q.1,
    ∀ x : ∀ p : (Σ _ : α, β), Y p.1 p.2,
      e (tprod ℂ x) = tprod ℂ fun q : (Σ _ : β, α) => x ⟨q.2, q.1⟩ :=
  ⟨reindex ℂ (fun p : (Σ _ : α, β) => Y p.1 p.2) (sigmaPairSwap α β),
    fun x => reindex_tprod (sigmaPairSwap α β) x⟩

theorem exists_pairCurrySwap : ∃ e : (⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2) ≃ₗ[ℂ] ⨂[ℂ] j, ⨂[ℂ] i, Y i j,
    ∀ x : ∀ p : (Σ _ : α, β), Y p.1 p.2, e (tprod ℂ x) = tprod ℂ fun j => tprod ℂ fun i => x ⟨i, j⟩ := by
  obtain ⟨e₁, h₁⟩ := exists_pairSwap Y
  obtain ⟨e₂, h₂⟩ := exists_pairCurry (fun j i => Y i j)
  refine ⟨e₁.trans e₂, fun x => ?_⟩
  rw [LinearEquiv.trans_apply, h₁]
  exact h₂ _

end SwapTensor

theorem piTensor_swapBlocks_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α β : Type) [Fintype α] [Fintype β] (c : α → β → Type)
    [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (Y : α → β → Type) [∀ i j, AddCommGroup (Y i j)]
    [∀ i j, Module ℂ (Y i j)] (σ : ∀ i j, Representation ℂ (GL (c i j) k) (Y i j)),
    Nonempty (Representation.Equiv
      ((GlobalTheory.SmGL.piTensor fun i => GlobalTheory.SmGL.piTensor fun j => σ i j).comp (GlobalTheory.SmGL.swapBlocks k c))
      (GlobalTheory.SmGL.piTensor fun j => GlobalTheory.SmGL.piTensor fun i => σ i j)) := by
  intro k _ _ _ _ α β _ _ c _ _ Y _ _ σ
  obtain ⟨e₁, h₁⟩ := exists_pairCurry Y
  obtain ⟨e₂, h₂⟩ := exists_pairCurrySwap Y
  refine ⟨Representation.Equiv.mk (e₁.symm.trans e₂) fun g => ?_⟩
  have key : ∀ w : ⨂[ℂ] p : (Σ _ : α, β), Y p.1 p.2,
      e₂ (e₁.symm ((piTensor fun i => piTensor fun j => σ i j) (swapBlocks k c g) (e₁ w))) =
        (piTensor fun j => piTensor fun i => σ i j) g (e₂ w) := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      have h : (piTensor fun i => piTensor fun j => σ i j) (swapBlocks k c g) (e₁ (tprod ℂ x)) =
          e₁ (tprod ℂ fun p : (Σ _ : α, β) => σ p.1 p.2 (g p.2 p.1) (x p)) := by
        rw [h₁, h₁, piTensor_tprod]
        congr 1
        funext i
        exact piTensor_tprod (fun j => σ i j) _ _
      have h' : (piTensor fun j => piTensor fun i => σ i j) g (e₂ (tprod ℂ x)) =
          e₂ (tprod ℂ fun p : (Σ _ : α, β) => σ p.1 p.2 (g p.2 p.1) (x p)) := by
        rw [h₂, h₂, piTensor_tprod]
        congr 1
        funext j
        exact piTensor_tprod (fun i => σ i j) _ _
      rw [map_smul, map_smul, map_smul, map_smul, map_smul, map_smul, h, h', LinearEquiv.symm_apply_apply]
    | add w w' hw hw' =>
      rw [map_add, map_add, map_add, map_add, map_add, map_add, hw, hw']
  refine LinearMap.ext fun v => ?_
  obtain ⟨w, rfl⟩ := e₁.surjective v
  have h := key w
  rw [← e₁.symm_apply_apply w, e₁.apply_symm_apply] at h
  exact h

end GlobalTheory.SmGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiTensorSmoothRepsExactEachFactor
section
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL

def piTensorHom {α : Type} {Γ : α → Type} [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)]
    {X Y : ∀ i, SmRep (Γ i)} (f : ∀ a, (X a).ρ.IntertwiningMap (Y a).ρ) :
    (piTensor fun a => (X a).ρ).IntertwiningMap (piTensor fun a => (Y a).ρ) where
  toLinearMap := PiTensorProduct.map fun a => (f a).toLinearMap
  isIntertwining' g := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, piTensor_tprod,
      PiTensorProduct.map_tprod]
    congr 1
    funext a
    exact LinearMap.congr_fun ((f a).isIntertwining' (g a)) (x a)

theorem piTensorMap_add_eq_id {α : Type} [DecidableEq α] {Y : α → Type} [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℂ (Y a)] (i : α) (u v : ∀ a, Y a →ₗ[ℂ] Y a) (hu : ∀ a, a ≠ i → u a = LinearMap.id)
    (hv : ∀ a, a ≠ i → v a = LinearMap.id) (h : u i + v i = LinearMap.id) :
    PiTensorProduct.map u + PiTensorProduct.map v = LinearMap.id := by
  ext x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, PiTensorProduct.map_tprod,
    LinearMap.id_apply]

  have hx : ∀ w : ∀ a, Y a →ₗ[ℂ] Y a, (∀ a, a ≠ i → w a = LinearMap.id) →
      (fun a => w a (x a)) = Function.update x i (w i (x i)) := by
    intro w hw
    funext a
    by_cases ha : a = i
    · subst ha
      simp
    · rw [Function.update_of_ne ha, hw a ha, LinearMap.id_apply]
  rw [hx u hu, hx v hv, ← MultilinearMap.map_update_add, ← LinearMap.add_apply, h,
    LinearMap.id_apply, Function.update_eq_self]

theorem piTensor_exact_position : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)] (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α) (B B₁ B₂ : GlobalTheory.SmGL.SmRep (Γ i)) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → ∃ (ι' : (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B₁ a).ρ).IntertwiningMap (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B a).ρ)) (p' : (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B a).ρ).IntertwiningMap (GlobalTheory.SmGL.piTensor fun a => (Function.update A i B₂ a).ρ)), Function.Injective ι' ∧ Function.Surjective p' ∧ (∀ u, p' (ι' u) = 0) ∧ (∀ v, p' v = 0 → ∃ u, ι' u = v) := by
  intro α _ _ Γ _ _ A i B B₁ B₂ ι p hι hp hpι hker

  have key : ∀ a, ∃ (f : (Function.update A i B₁ a).ρ.IntertwiningMap (Function.update A i B a).ρ)
      (g : (Function.update A i B a).ρ.IntertwiningMap (Function.update A i B₂ a).ρ)
      (s : (Function.update A i B a).V →ₗ[ℂ] (Function.update A i B₁ a).V)
      (t : (Function.update A i B₂ a).V →ₗ[ℂ] (Function.update A i B a).V),
      s ∘ₗ f.toLinearMap = LinearMap.id ∧ g.toLinearMap ∘ₗ t = LinearMap.id ∧
      (a ≠ i → f.toLinearMap ∘ₗ s = LinearMap.id ∧ t ∘ₗ g.toLinearMap = LinearMap.id) ∧
      (a = i → f.toLinearMap ∘ₗ s + t ∘ₗ g.toLinearMap = LinearMap.id ∧
        g.toLinearMap ∘ₗ f.toLinearMap = 0) := by
    intro a
    by_cases ha : a = i
    · subst ha
      rw [Function.update_self, Function.update_self, Function.update_self]
      obtain ⟨t, ht⟩ := p.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
      obtain ⟨s₀, hs₀⟩ := ι.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hι)
      have hs₀' : ∀ u, s₀ (ι u) = u := fun u => LinearMap.congr_fun hs₀ u
      have ht' : ∀ z, p (t z) = z := fun z => LinearMap.congr_fun ht z
      refine ⟨ι, p, s₀ ∘ₗ (LinearMap.id - t ∘ₗ p.toLinearMap), t, ?_, ht, fun h => absurd rfl h,
        fun _ => ⟨?_, ?_⟩⟩
      · ext u
        simp [hpι, hs₀']
      · ext y

        obtain ⟨u, hu⟩ := hker (y - t (p y)) (by simp [ht'])
        simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
          Representation.IntertwiningMap.coe_toLinearMap]
        rw [← hu, hs₀', hu, sub_add_cancel]
      · ext u
        simp [hpι]
    · rw [Function.update_of_ne ha, Function.update_of_ne ha, Function.update_of_ne ha]
      exact ⟨Representation.IntertwiningMap.id _, Representation.IntertwiningMap.id _, LinearMap.id, LinearMap.id, by ext; rfl,
        by ext; rfl, fun _ => ⟨by ext; rfl, by ext; rfl⟩, fun h => absurd h ha⟩
  choose f g s t hsf hgt hne heq using key
  have hF : ∀ x, piTensorHom f x = PiTensorProduct.map (fun a => (f a).toLinearMap) x := fun _ => rfl
  have hG : ∀ x, piTensorHom g x = PiTensorProduct.map (fun a => (g a).toLinearMap) x := fun _ => rfl
  have hSF : PiTensorProduct.map s ∘ₗ PiTensorProduct.map (fun a => (f a).toLinearMap) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, funext hsf, PiTensorProduct.map_id]
  have hGT : PiTensorProduct.map (fun a => (g a).toLinearMap) ∘ₗ PiTensorProduct.map t = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, funext hgt, PiTensorProduct.map_id]
  have hsum : PiTensorProduct.map (fun a => (f a).toLinearMap) ∘ₗ PiTensorProduct.map s +
      PiTensorProduct.map t ∘ₗ PiTensorProduct.map (fun a => (g a).toLinearMap) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
    exact piTensorMap_add_eq_id i _ _ (fun a ha => (hne a ha).1) (fun a ha => (hne a ha).2)
      (heq i rfl).1
  have hGF : PiTensorProduct.map (fun a => (g a).toLinearMap) ∘ₗ
      PiTensorProduct.map (fun a => (f a).toLinearMap) = 0 := by
    rw [← PiTensorProduct.map_comp]
    ext x
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]

    exact MultilinearMap.map_coord_zero _ i (by rw [(heq i rfl).2, LinearMap.zero_apply])
  refine ⟨piTensorHom f, piTensorHom g, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have := congrArg (PiTensorProduct.map s) hxy
    rw [hF, hF] at this
    simpa using (LinearMap.congr_fun hSF x).symm.trans (this.trans (LinearMap.congr_fun hSF y))
  · intro z
    exact ⟨PiTensorProduct.map t z, by rw [hG]; exact LinearMap.congr_fun hGT z⟩
  · intro u
    rw [hG, hF]
    exact LinearMap.congr_fun hGF u
  · intro v hv
    refine ⟨PiTensorProduct.map s v, ?_⟩
    rw [hG] at hv
    have := LinearMap.congr_fun hsum v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hv, map_zero, add_zero,
      LinearMap.id_apply] at this
    rw [hF]
    exact this

end GlobalTheory.SmGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConstRatio

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

section Rat

variable {T L : Type} [Field L] (σ : L →+* ℂ) (t₀ : T)

def RatIn (f : T → ℂ) : Prop := ∀ t, f t ≠ 0 ∧ ∃ y : Lˣ, σ y = f t / f t₀

variable {σ t₀}

theorem RatIn.mul {f g : T → ℂ} (hf : RatIn σ t₀ f) (hg : RatIn σ t₀ g) : RatIn σ t₀ fun t => f t * g t := by
  intro t
  obtain ⟨hf0, y, hy⟩ := hf t
  obtain ⟨hg0, z, hz⟩ := hg t
  refine ⟨mul_ne_zero hf0 hg0, y * z, ?_⟩
  rw [Units.val_mul, map_mul, hy, hz, mul_div_mul_comm]

theorem RatIn.inv {f : T → ℂ} (hf : RatIn σ t₀ f) : RatIn σ t₀ fun t => (f t)⁻¹ := by
  intro t
  obtain ⟨hf0, y, hy⟩ := hf t
  refine ⟨inv_ne_zero hf0, y⁻¹, ?_⟩
  rw [map_units_inv, hy, inv_div, inv_div_inv]

theorem ratIn_const {κ : ℂ} (h : κ ≠ 0) : RatIn σ t₀ fun _ => κ := by
  intro _
  exact ⟨h, 1, by rw [Units.val_one, map_one, div_self h]⟩

theorem ratIn_of_unit {f : T → ℂ} (h : ∀ t, ∃ y : Lˣ, σ y = f t) : RatIn σ t₀ f := by
  intro t
  obtain ⟨y, hy⟩ := h t
  obtain ⟨y₀, hy₀⟩ := h t₀
  refine ⟨hy ▸ (map_ne_zero σ).2 y.ne_zero, y * y₀⁻¹, ?_⟩
  rw [Units.val_mul, map_mul, map_units_inv, hy, hy₀, div_eq_mul_inv]

theorem RatIn.of_mul {f g u : T → ℂ} (hg : RatIn σ t₀ g) (hu : RatIn σ t₀ u) (h : ∀ t, f t * u t = g t) : RatIn σ t₀ f := by

  have e : f = fun t => g t * (u t)⁻¹ := funext fun t => by rw [← h t, mul_inv_cancel_right₀ (hu t).1]
  rw [e]
  exact hg.mul hu.inv

theorem ratIn_prod {ι : Type} (s : Finset ι) {f : ι → T → ℂ} (h : ∀ i ∈ s, RatIn σ t₀ (f i)) :
    RatIn σ t₀ fun t => ∏ i ∈ s, f i t := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    exact ratIn_const one_ne_zero
  · intro a s ha ih h
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Rat

variable {D : D7}

section Factor

variable {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)

def Factor (lam : T → ℂ) : Prop :=
  (∀ t, lam t ≠ 0) ∧
    ∃ (Pi : ModuleCat.{0} ℂ) (p : PolF D WW.rank A.rank →ₗ[ℂ] Pi) (p' : PolF D WW.rank A'.rank →ₗ[ℂ] Pi)
      (J : T → (Pi →ₗ[ℂ] (GA D WW → ℂ))),
      Function.Surjective p ∧ (∀ t, Function.Injective (J t)) ∧
      (∀ t P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) ∧
      (∀ t P, X.I ψ θ t P = lam t • J t (p P)) ∧
      (∀ t P', (∀ h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') → X.I' ψ θ t P' = J t (p' P')) ∧
      ∃ P', p' P' ≠ 0 ∧ ∀ t h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m'

variable {X ψ θ}

theorem Factor.isConst [Nonempty T] {lam : T → ℂ} (h : Factor X ψ θ lam) : X.IsConst ψ θ lam := by
  unfold Factor at h
  obtain ⟨hlam, Pi, p, p', J, hp, hJ, hint, hI, hI', P', hP', hint'⟩ := h

  obtain ⟨P, hPP⟩ := hp (p' P')
  unfold Tri.IsConst
  refine ⟨⟨Classical.arbitrary T, hlam _⟩, P, P', fun t => ⟨fun h => ⟨hint t P h, hint' t h⟩, ?_, fun h => ?_⟩⟩
  · by_contra hcon
    push_neg at hcon
    apply hP'
    apply hJ t
    rw [map_zero, ← hI' t P' (hint' t)]
    funext h
    exact hcon h
  · rw [hI t P, hI' t P' (hint' t), hPP]
    rfl

theorem Factor.eq_mul {lam c : T → ℂ} (h : Factor X ψ θ lam) (hc : X.IsConst ψ θ c) : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ t, c t = κ * lam t := by
  unfold Factor at h
  unfold Tri.IsConst at hc
  obtain ⟨hlam, Pi, p, p', J, -, hJ, -, hI, hI', -⟩ := h
  obtain ⟨⟨t₁, ht₁⟩, P, P', hc⟩ := hc

  have key : ∀ t, lam t • p P = c t • p' P' := by
    intro t
    obtain ⟨hi, -, heq⟩ := hc t
    apply hJ t
    rw [map_smul, map_smul, ← hI t P, ← hI' t P' (fun h => (hi h).2)]
    funext h
    exact heq h
  have hne : p' P' ≠ 0 := by
    intro h0
    obtain ⟨hi, ⟨h₁, hh₁⟩, -⟩ := hc t₁
    apply hh₁
    rw [hI' t₁ P' (fun h => (hi h).2), h0, map_zero]
    rfl
  have hq : ∀ t, p P = ((lam t)⁻¹ * c t) • p' P' := by
    intro t
    rw [← smul_smul, ← key t, inv_smul_smul₀ (hlam t)]
  refine ⟨(lam t₁)⁻¹ * c t₁, mul_ne_zero (inv_ne_zero (hlam t₁)) ht₁, fun t => ?_⟩
  have e := smul_left_injective ℂ hne ((hq t).symm.trans (hq t₁))
  rw [← e]
  field_simp [hlam t]

end Factor

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {Fam : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D Fam Ks}

def Standing (F : Face D Fam) (G : GridPre R) : Prop :=
  R.Char F ∧ G.Is ∧ PrimeToPolarisation G ∧ Formalism.L2.Host.ValLL D R.C ∧ G.ValuesInField ∧
    ∀ t, (R.xiH t).ValuesIn 0 D.what₂.embLL

def NegIdx (V : HSp D) (q : ℕ) : Prop := ∀ τ, Formalism.UG.HasSignature (gramAt D V τ) (V.rank - q) q

def IsStage (G : GridPre R) (i j : Fin D.R.m) (p q : ℕ) {A A' WW : HSp D} (X : Tri T A A' WW) : Prop :=
  p ≤ (D.R.m - (j + 1)) / 2 ∧ q ≤ (D.R.m - j) / 2 ∧
    A.rank + 2 * ((D.R.m - (j + 1)) / 2) = rkV D (i + 1) (j + 1) + 2 * p ∧
    A'.rank + 2 * ((D.R.m - j) / 2) = rkV D i j + 2 * q ∧
    NegIdx A p ∧ NegIdx A' q ∧ NegIdx WW (p + q) ∧
    X.Is R.ψ R.θ (alpha R i j) (beta G i j) (nuH G i j) (places G)

theorem IsStage.exists_half {G : GridPre R} {i j : Fin D.R.m} {p q : ℕ} {A A' WW : HSp D} {X : Tri T A A' WW}
    (h : IsStage G i j p q X) : ∃ e : ℕ, A.rank = A'.rank + 2 * e ∧ 2 ≤ e ∧ e ≤ bigN D := by
  obtain ⟨hp, hq, hA, hA', -⟩ := h
  have hs : sLen D = D.R.r + 6 := rfl
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hN : bigN D = D.R.k + D.R.m * (D.R.t + sLen D + 1) := rfl
  have hm := Nat.mul_le_mul_right (D.R.t + sLen D + 1) D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  obtain ⟨c, hc⟩ := D.R.t_odd
  have h5 := D.R.rank_add_five_le
  simp only [rkV, add_mul, one_mul] at hA hA'

  refine ⟨(D.R.t + sLen D) / 2 + p + (D.R.m - j) / 2 - q - (D.R.m - (j + 1)) / 2, ?_, ?_, ?_⟩ <;> omega

end GlobalTheory.ConstRatio

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PlaceTensor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def VacAt (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) :
    Place D → (WO S T → ℂ) → Prop
  | .inl v => fun f => IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f
  | .inr τ => fun f => IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f

def IsLocOp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f₀ : WO S T → ℂ)
    (p : Place D) (x : WO S T → ℂ) : Prop :=
  ∃ L : (WO S T → ℂ) → ℂ, (∀ (c : ℂ) (φ : WO S T → ℂ), L (fun w => c * φ w) = c * L φ) ∧
    (∀ f, IsThetaFunO ψ S T f → ∃ f', IsThetaFunO ψ S T f' ∧ ∀ g, IsThetaFunO ψ S T g →
      ipO μ 𝓕 f' g = L fun w => ipO μ 𝓕 (heisO ψ S T (wAt p w) f) g) ∧
    ∀ g, IsThetaFunO ψ S T g → ipO μ 𝓕 x g = L fun w => ipO μ 𝓕 (heisO ψ S T (wAt p w) f₀) g

open Classical in

def pull {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v))
    (Φ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → ℂ) : WO S T → ℂ :=
  fun t => if IsHalf a t then Φ (κ t) else 0

def IsCoord {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D) (Λ : AddSubgroup (WO S T))
    (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)) : Prop :=
  (∀ x y, κ (x + y) = κ x + κ y) ∧ Set.BijOn κ {t | IsHalf a t} Set.univ ∧
    IsOpen (κ '' {t | t ∈ Λ ∧ IsHalf a t}) ∧ IsCompact (κ '' {t | t ∈ Λ ∧ IsHalf a t})

theorem wAt_eq_smul {m n : ℕ} (p : Place D) (w : Mx D m n) : wAt p w = idem D p • w := rfl

theorem onHalf_eq_pull {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) : onHalf φ S T BS BT e = pull e (mapCo φ S T BS BT) := rfl

theorem onHalfAdj_eq_pull {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) :
    onHalfAdj φ S T BS BT e = pull (cA D e) (adjCo φ S T BS BT) := rfl

theorem gAt_one (V : HSp D) (p : Place D) : gAt V p 1 = 1 := by
  cases p <;> simp [gAt]

theorem gAt_mul (V : HSp D) (p : Place D) (g g' : GA D V) : gAt V p (g * g') = gAt V p g * gAt V p g' := by
  cases p <;> simp [gAt]

theorem gAt_inv (V : HSp D) (p : Place D) (g : GA D V) : gAt V p g⁻¹ = (gAt V p g)⁻¹ := by
  cases p <;> simp [gAt]

theorem latO_mono {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P Q : FinPl D → Prop} (h : ∀ v, P v → Q v) : latO S T LS LT P ≤ latO S T LS LT Q := by
  unfold latO
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun v hQ => hv v fun hP => hQ (h v hP), rest⟩

theorem isLatVac_mono {m n : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ Λ' : AddSubgroup (Mx D m n)}
    (h : Λ ≤ Λ') {f : Mx D m n → ℂ} (hf : IsLatVac hs Λ' f) : IsLatVac hs Λ f := by
  unfold IsLatVac at hf ⊢
  exact ⟨fun u hu => hf.1 u (h hu), fun e he u hu hh => hf.2 e he u (h hu) hh⟩

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f f₀ : WO S T → ℂ}

theorem vacAt_of_isLocal {p q : Place D} (h : IsLocal ψ θ S T sS sT ΛS ΛT p f) (hq : q ≠ p) :
    VacAt ψ θ S T sS sT ΛS ΛT q f := by
  rcases q with v | τ
  · exact isLatVac_mono (latO_mono fun u hu => hu ▸ hq) h.2.1
  · exact h.2.2 τ hq

theorem base_std (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsStdChar D ψ (-1) := by
  exact h.2.2.2.2.1

theorem base_inf (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsInfFam θ :=
  h.2.2.2.2.2.inf

theorem base_theta (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsThetaFunO ψ S T f₀ :=
  h.2.2.2.2.2.theta

theorem restrictedTensorBasePoint_norm_sq (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) : nrm2 μ 𝓕 f₀ = 1 := by
  exact h.2.2.2.2.2.norm.2 (μ, 𝓕) hμ

theorem base_ne_zero (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : f₀ ≠ 0 := by
  rintro rfl
  obtain ⟨⟨μ, 𝓕⟩, hq⟩ := h.2.2.2.2.2.norm.1
  have h1 := restrictedTensorBasePoint_norm_sq h hq
  simp [nrm2] at h1

theorem base_isLocal (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (p : Place D) : IsLocal ψ θ S T sS sT ΛS ΛT p f₀ :=
  ⟨h.2.2.2.2.2.theta, isLatVac_mono (latO_mono fun _ _ => trivial) h.2.2.2.2.2.lat,
    fun τ _ => h.2.2.2.2.2.fock τ⟩

theorem base_vacAt (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (p : Place D) : VacAt ψ θ S T sS sT ΛS ΛT p f₀ := by
  rcases p with v | τ
  · exact isLatVac_mono (latO_mono fun _ _ => trivial) h.2.2.2.2.2.lat
  · exact h.2.2.2.2.2.fock τ

end

end GlobalTheory.PlaceTensor

end
end

