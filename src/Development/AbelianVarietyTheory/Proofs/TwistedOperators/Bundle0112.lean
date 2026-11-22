import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0223
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0047

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
section
noncomputable section

open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct

namespace GlobalTheory.OneFunctional

section General

variable {G H K V W X : Type} [Monoid G] [Monoid H] [Monoid K] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

def Iso (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Prop :=
  ∃ e : V ≃ₗ[ℂ] W, ∀ g x, e (ρ g x) = σ g (e x)

theorem Iso.refl (ρ : Representation ℂ G V) : Iso ρ ρ := ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem Iso.symm {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) : Iso σ ρ := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, fun g x => e.injective (by rw [he]; simp)⟩

theorem Iso.trans {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X} (h : Iso ρ σ)
    (h' : Iso σ τ) : Iso ρ τ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun g x => by simp [he, he']⟩

theorem Iso.comp {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (f : H →* G) :
    Iso (ρ.comp f : Representation ℂ H V) (σ.comp f) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, fun g x => he (f g) x⟩

theorem Iso.twist {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (χ : G →* ℂˣ) :
    Iso (twist χ ρ) (twist χ σ) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun g x => ?_⟩
  change e ((χ g : ℂ) • ρ g x) = (χ g : ℂ) • σ g (e x)
  rw [map_smul, he]

theorem Iso.tprod {V' W' : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'}
    (h : Iso ρ σ) (h' : Iso ρ' σ') : Iso (ρ.tprod ρ') (σ.tprod σ') := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨TensorProduct.congr e e', fun g x => ?_⟩
  induction x with
  | zero => simp
  | tmul a b => simp [he, he']
  | add a b ha hb => simp only [map_add, ha, hb]

theorem Iso.tprod_comm (ρ : Representation ℂ G V) (σ : Representation ℂ G W) : Iso (ρ.tprod σ) (σ.tprod ρ) := by
  refine ⟨TensorProduct.comm ℂ V W, fun g x => ?_⟩
  induction x with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, ha, hb]

theorem Iso.dual {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Iso ρ.dual σ.dual := by
  obtain ⟨e, he⟩ := h.symm
  refine ⟨e.dualMap, fun g x => ?_⟩
  ext w
  simp [Module.Dual.transpose_apply, he]

theorem Iso.of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) : Iso ρ σ :=
  ⟨e.toLinearEquiv, fun g x => e.toIntertwiningMap.isIntertwining _ _ g x⟩

theorem mem_invFun {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} : l ∈ invFun ρ ↔ ∀ g x, l (ρ g x) = l x := Iff.rfl

theorem Iso.nonempty_invFun_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Nonempty (invFun ρ ≃ₗ[ℂ] invFun σ) := by
  obtain ⟨e, he⟩ := h.symm
  refine ⟨e.dualMap.ofSubmodules _ _ (le_antisymm ?_ fun l hl => ⟨e.symm.dualMap l, fun g x => ?_, ?_⟩)⟩
  · rintro _ ⟨l, hl, rfl⟩ g x
    change l (e (σ g x)) = l (e x)
    rw [he, hl]
  · obtain ⟨x, rfl⟩ := e.surjective x
    change l (e.symm _) = l (e.symm _)
    rw [← he, e.symm_apply_apply, e.symm_apply_apply, hl]
  · ext x
    simp

theorem Iso.finrank_invFun {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) :
    Module.finrank ℂ (invFun ρ) = Module.finrank ℂ (invFun σ) := by
  obtain ⟨e⟩ := h.nonempty_invFun_equiv
  exact e.finrank_eq

theorem Iso.invFun_eq_bot {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (h : Iso ρ σ) (h0 : invFun σ = ⊥) :
    invFun ρ = ⊥ := by
  obtain ⟨e⟩ := h.nonempty_invFun_equiv
  rw [← Submodule.subsingleton_iff_eq_bot] at h0 ⊢
  exact e.toEquiv.subsingleton

def Contracts {F : Type} [AddCommGroup F] [Module ℂ F] (φ : Representation ℂ (H × G) F) (σ : Representation ℂ H V)
    (σ' : Representation ℂ G W) : Prop :=
  ∃ π : F ⊗[ℂ] V →ₗ[ℂ] W, Function.Surjective π ∧
    (∀ h g f v, π (φ (h, g) f ⊗ₜ σ h v) = σ' g (π (f ⊗ₜ v))) ∧
    ∀ l : Module.Dual ℂ (F ⊗[ℂ] V), (∀ h f v, l (φ (h, 1) f ⊗ₜ σ h v) = l (f ⊗ₜ v)) → ∀ x, π x = 0 → l x = 0

theorem Contracts.congr {F F' V' W' : Type} [AddCommGroup F] [Module ℂ F] [AddCommGroup F'] [Module ℂ F']
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {φ : Representation ℂ (H × G) F} {σ : Representation ℂ H V} {τ : Representation ℂ G W}
    {φ' : Representation ℂ (H × G) F'} {σ' : Representation ℂ H V'} {τ' : Representation ℂ G W'}
    (h : Contracts φ σ τ) (h1 : Iso φ φ') (h2 : Iso σ σ') (h3 : Iso τ τ') : Contracts φ' σ' τ' := by
  obtain ⟨π, hs, he, hk⟩ := h
  obtain ⟨e1, he1⟩ := h1
  obtain ⟨e2, he2⟩ := h2
  obtain ⟨e3, he3⟩ := h3
  refine ⟨e3.toLinearMap ∘ₗ π ∘ₗ (TensorProduct.congr e1 e2).symm.toLinearMap,
    e3.surjective.comp (hs.comp (TensorProduct.congr e1 e2).symm.surjective), fun h g f v => ?_, fun l hl x hx => ?_⟩
  · obtain ⟨f, rfl⟩ := e1.surjective f
    obtain ⟨v, rfl⟩ := e2.surjective v
    simp [← he1, ← he2, he, he3]
  · obtain ⟨x, rfl⟩ := (TensorProduct.congr e1 e2).surjective x
    refine hk (l ∘ₗ (TensorProduct.congr e1 e2).toLinearMap) (fun h f v => ?_) x ?_
    · simp [he1, he2, hl]
    · simpa using hx

end General

section Outer

variable {ι G H : Type} [Monoid G] [Monoid H] {V W : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]

def outer (ρ : ∀ τ, Representation ℂ G (V τ)) : Representation ℂ (ι → G) (⨂[ℂ] τ, V τ) :=
  piTprod fun τ => (ρ τ).comp (Pi.evalMonoidHom (fun _ : ι => G) τ)

def outer₂ (ρ : ∀ τ, Representation ℂ (H × G) (V τ)) : Representation ℂ ((ι → H) × (ι → G)) (⨂[ℂ] τ, V τ) :=
  piTprod fun τ => (ρ τ).comp ((Pi.evalMonoidHom (fun _ : ι => H) τ).prodMap (Pi.evalMonoidHom (fun _ : ι => G) τ))

theorem piTprod_apply (ρ : ∀ τ, Representation ℂ G (V τ)) (g : G) :
    piTprod ρ g = PiTensorProduct.map fun τ => ρ τ g := rfl

theorem outer_apply (ρ : ∀ τ, Representation ℂ G (V τ)) (g : ι → G) :
    outer ρ g = PiTensorProduct.map fun τ => ρ τ (g τ) := rfl

theorem outer₂_apply (ρ : ∀ τ, Representation ℂ (H × G) (V τ)) (h : ι → H) (g : ι → G) :
    outer₂ ρ (h, g) = PiTensorProduct.map fun τ => ρ τ (h τ, g τ) := rfl

theorem Iso.outer {ρ : ∀ τ, Representation ℂ G (V τ)} {σ : ∀ τ, Representation ℂ G (W τ)} (h : ∀ τ, Iso (ρ τ) (σ τ)) :
    Iso (outer ρ) (outer σ) := by
  choose e he using h
  refine ⟨PiTensorProduct.congr e, fun g x => ?_⟩
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v => simp [outer_apply, he]
  | add a b ha hb => simp only [map_add, ha, hb]

end Outer

abbrev U (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

def conjU (n : ℕ) : U n →* U n where
  toFun g := ⟨(star g.1)ᵀ, by
    rw [Matrix.mem_unitaryGroup_iff]
    have h : star g.1 * g.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 g.2
    have e : star (star g.1)ᵀ = (g.1)ᵀ := by ext i j; simp
    rw [e, ← Matrix.transpose_mul, mul_eq_one_comm.1 h, Matrix.transpose_one]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [star_mul, Matrix.transpose_mul])

@[simp] theorem conjU_coe (n : ℕ) (g : U n) : (conjU n g).1 = (star g.1)ᵀ := rfl

abbrev irr (n : ℕ) (lam : DomWeight n) : Representation ℂ (U n) (nablaSq ℂ n lam) := smallRep (unitaryIncl n) lam

def fockOne (a b : ℕ) (α β : ℤ) : Representation ℂ (U a × U b) (MvPolynomial (Fin b × Fin a) ℂ) :=
  twist ((detU a ^ α).comp (MonoidHom.fst _ _) * (detU b ^ β).comp (MonoidHom.snd _ _))
    (GlobalTheory.GLDuality.polyRep ((unitaryIncl a).comp (conjU a)) (unitaryIncl b))

def StepW {a b : ℕ} (α β : ℤ) (lam : DomWeight a) (lam' : DomWeight b) : Prop :=
  ∀ i : Fin b, lam'.w i = if h : i.1 < a then lam.w ⟨i.1, h⟩ + α + β else β

end GlobalTheory.OneFunctional
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamUnitaryMatrixEqExpLieAlgebra
section
open Matrix

namespace GlobalTheory.OneParamUnitary

open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem oneParam_eq_exp_lieU {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (u : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hc : Continuous u) (h0 : u 0 = 1) (hadd : ∀ s t, u (s + t) = u s * u t)
    (hU : ∀ t, u t ∈ Formalism.QuantumDeterminants.UH G) :
    ∃ Y ∈ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU G, ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have hsm : ContDiff ℝ ∞ u :=
    GlobalTheory.contDiff_of_continuous_oneParameter (Matrix (Fin n) (Fin n) ℂ) u hc h0 hadd
  have hdiff : Differentiable ℝ u := hsm.differentiable (by simp)
  set Y := deriv u 0 with hY
  have hY0 : HasDerivAt u Y 0 := (hdiff 0).hasDerivAt
  have hder : ∀ t, HasDerivAt u (u t * Y) t := by
    intro t
    have h1 : HasDerivAt (fun s => u (s - t)) Y t :=
      (show HasDerivAt u Y (t - t) by simpa using hY0).comp_sub_const t t
    have h2 := h1.const_mul (u t)
    have h3 : (fun s => u t * u (s - t)) = u := by
      funext s
      rw [← hadd]; congr 1; ring
    rwa [h3] at h2

  have hexp : ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
    set v : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => u t * NormedSpace.exp (t • (-Y)) with hv
    have hvd : ∀ t, HasDerivAt v 0 t := by
      intro t
      have hE := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Y) t
      have := (hder t).mul hE
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel] at this
      exact this
    have hvc : ∀ t, v t = v 0 := fun t =>
      is_const_of_deriv_eq_zero (fun s => (hvd s).differentiableAt) (fun s => (hvd s).deriv) t 0
    have hv0 : v 0 = 1 := by simp [hv, h0]
    intro t
    have hcomm : Commute (t • (-Y)) (t • Y) :=
      ((Commute.refl Y).neg_left.smul_left t).smul_right t
    have hinv : NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ hcomm, smul_neg, neg_add_cancel, NormedSpace.exp_zero]
    calc u t = u t * (NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y)) := by rw [hinv, Matrix.mul_one]
      _ = v t * NormedSpace.exp (t • Y) := by rw [hv, Matrix.mul_assoc]
      _ = NormedSpace.exp (t • Y) := by rw [hvc t, hv0, Matrix.one_mul]
  refine ⟨Y, ?_, hexp⟩

  show Yᴴ * G + G * Y = 0
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun A => star A
      map_add' := fun A B => star_add A B
      map_smul' := fun c A => by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul] }
  have hst : HasDerivAt (fun t => star (u t)) (star Y) 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 hY0
  have hw := (hst.mul_const G).mul hY0
  have hconst : ((fun t => star (u t) * G) * u) = fun _ => G := by
    funext t; exact hU t
  rw [hconst] at hw
  have := (hasDerivAt_const (0 : ℝ) G).unique hw
  rw [h0, star_one, Matrix.one_mul, Matrix.mul_one, ← Matrix.star_eq_conjTranspose] at *
  exact this.symm

end GlobalTheory.OneParamUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OuterTensorIntertwiningEqZeroOfLeft
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory

theorem tensor_eq_zero_of_forall_contract_right {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (z : V ⊗[ℂ] W)
    (h : ∀ l : Module.Dual ℂ W, TensorProduct.rid ℂ V (LinearMap.lTensor V l z) = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  apply (TensorProduct.equivFinsuppOfBasisRight (M := V) b).injective
  ext i
  simp [TensorProduct.equivFinsuppOfBasisRight_apply, h]

theorem outerTensor_intertwining_eq_zero_of_left :
    ∀ (G H V W V' W' : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (ρ' : Representation ℂ G V') (σ' : Representation ℂ H W'), (∀ ψ : ρ.IntertwiningMap ρ', ψ = 0) → ∀ φ : (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V ⊗[ℂ] W)).IntertwiningMap (Representation.tprod (ρ'.comp (MonoidHom.fst G H)) (σ'.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V' ⊗[ℂ] W')), φ = 0 := by
  intro G H V W V' W' _ _ _ _ _ _ _ _ _ _ ρ σ ρ' σ' h φ

  have hpure : ∀ (v : V) (w : W), φ (v ⊗ₜ[ℂ] w) = 0 := by
    intro v w
    apply tensor_eq_zero_of_forall_contract_right
    intro l
    let f : V →ₗ[ℂ] V' :=
      (TensorProduct.rid ℂ V').toLinearMap ∘ₗ LinearMap.lTensor V' l ∘ₗ φ.toLinearMap ∘ₗ
        (TensorProduct.mk ℂ V W).flip w
    have hf : ∀ (g : G) (x : V), f (ρ g x) = ρ' g (f x) := by
      intro g x
      have key : ∀ y : V' ⊗[ℂ] W', TensorProduct.rid ℂ V'
          (LinearMap.lTensor V' l (TensorProduct.map (ρ' g) (σ' 1) y)) =
          ρ' g (TensorProduct.rid ℂ V' (LinearMap.lTensor V' l y)) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a c => simp
        | add a c ha hc => simp only [map_add, ha, hc]
      have e1 : ρ g x ⊗ₜ[ℂ] w = (Representation.tprod (ρ.comp (MonoidHom.fst G H))
          (σ.comp (MonoidHom.snd G H))) (g, 1) (x ⊗ₜ[ℂ] w) := by
        simp [Representation.tprod_apply]
      have e2 := Representation.IntertwiningMap.isIntertwining _ _ φ (g, 1) (x ⊗ₜ[ℂ] w)
      simp only [f, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
        Representation.IntertwiningMap.toLinearMap_apply, LinearEquiv.coe_coe]
      rw [e1, e2, Representation.tprod_apply]
      exact key _
    have h0 := h (f.intertwiningMap_of_isIntertwiningMap ρ ρ' hf)
    have hv := congrArg (fun ψ : ρ.IntertwiningMap ρ' => ψ v) h0
    simpa [f] using hv
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro v w
  simp [hpure]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairingEquivariantAndNeZero
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

noncomputable section

namespace GlobalTheory.GLDuality

def pairLmul {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) :
    MvPolynomial (Fin n' × Fin k) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin k) ℂ :=
  aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ))

theorem pairLmul_rowAct {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) (h : Matrix (Fin n') (Fin n') ℂ)
    (f : MvPolynomial (Fin n' × Fin k) ℂ) : pairLmul x (rowAct ℂ h f) = pairLmul (h * x) f := by
  have : (pairLmul x).comp (rowAct ℂ (n := k) h) = pairLmul (h * x) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp only [pairLmul, rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← this]; rfl

theorem rowAct_pairLmul {n n' k : ℕ} (x : Matrix (Fin n') (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : MvPolynomial (Fin n' × Fin k) ℂ) : rowAct ℂ g (pairLmul x f) = pairLmul (x * g) f := by
  have : (rowAct ℂ (n := k) g).comp (pairLmul x) = pairLmul (x * g) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp only [pairLmul, rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← this]; rfl

theorem pair_map_conj_rowAct {n k : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin k) ℂ) :
    map (starRingEnd ℂ) (rowAct ℂ g p) = rowAct ℂ (gᵀ)ᴴ (map (starRingEnd ℂ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [rowAct, map_sum]

theorem pair_map_conj_hw {n k : ℕ} (hn : k ≤ n) (ν : Fin k → ℕ) :
    map (starRingEnd ℂ) (hw ℂ hn ν) = hw ℂ hn ν := by
  simp only [hw, map_prod, map_pow, lpMinor]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 1
  rw [RingHom.map_det]
  congr 1
  ext p q : 1
  simp

theorem pairLmul_hw {n n' k : ℕ} (hn : k ≤ n) (hn' : k ≤ n') (ν : Fin k → ℕ) :
    pairLmul (Matrix.of fun (a : Fin n') (t : Fin n) => if a.val = t.val then (1 : ℂ) else 0) (hw ℂ hn' ν) =
      hw ℂ hn ν := by
  simp only [hw, map_prod, map_pow, lpMinor]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 1
  rw [AlgHom.map_det]
  congr 1
  ext p q : 1
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, pairLmul, aeval_X]
  rw [Finset.sum_eq_single (Fin.castLE (by have := s.2; omega) p)]
  · simp
  · intro b _ hb
    rw [if_neg]
    · simp
    · intro e
      exact hb (Fin.ext (by simpa using e.symm))
  · simp

theorem pairing_equivariant_and_ne_zero : ∀ (n n' k : ℕ) (T : MvPolynomial (Fin n × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin k) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n) ℂ), (∀ (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ) (x : Matrix (Fin n') (Fin n) ℂ), eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (aeval (fun v : Fin n' × Fin k => ∑ t : Fin n, C (x v.1 t) * (X (t, v.2) : MvPolynomial (Fin n × Fin k) ℂ)) f))) → (∀ (g : GL (Fin n) ℂ) (h : GL (Fin n') ℂ) (φ : MvPolynomial (Fin n × Fin k) ℂ) (f : MvPolynomial (Fin n' × Fin k) ℂ), T (rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ φ) (rowAct ℂ (h : Matrix (Fin n') (Fin n') ℂ)ᵀ f) = matRep n n' (g, h) (T φ f)) ∧ ∀ (hn : k ≤ n) (hn' : k ≤ n') (ν : Fin k → ℕ), T (hw ℂ hn ν) (hw ℂ hn' ν) ≠ 0 := by
  intro n n' k T hT
  have hT' : ∀ φ f (x : Matrix (Fin n') (Fin n) ℂ),
      eval (fun v => x v.1 v.2) (T φ f) = fockF φ (map (starRingEnd ℂ) (pairLmul x f)) := hT
  refine ⟨fun g h φ f => ?_, fun hn hn' ν h0 => ?_⟩
  · apply MvPolynomial.funext
    intro p
    have hp : p = fun v => (Matrix.of fun a t => p (a, t)) v.1 v.2 := rfl
    rw [hp, eval_matRep, hT', hT', fockRowAdj, pairLmul_rowAct, ← pair_map_conj_rowAct, rowAct_pairLmul]
  · have h1 := hT' (hw ℂ hn ν) (hw ℂ hn' ν)
      (Matrix.of fun (a : Fin n') (t : Fin n) => if a.val = t.val then (1 : ℂ) else 0)
    rw [h0, map_zero, pairLmul_hw hn hn', pair_map_conj_hw] at h1
    have h2 := (fockPos _ _ (hwNe ℂ n k hn ν)).1
    rw [← h1] at h2
    simp at h2

end GlobalTheory.GLDuality
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowDivEqZeroOfMatRepUnipotentFixed
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

private theorem rowGen_eval_C_eq_rowAct_transvection {n n' : ℕ} (a b : Fin n') (t : ℂ)
    (f : MvPolynomial (Fin n' × Fin n) ℂ) :
    (rowGen ℂ a b f).eval (C t) = rowAct ℂ (Matrix.transvection a b t)ᵀ f := by
  have key : (Polynomial.evalRingHom (C t : MvPolynomial (Fin n' × Fin n) ℂ)).comp
      (rowGen ℂ (n := n) a b).toRingHom = (rowAct ℂ (n := n) (Matrix.transvection a b t)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen, rowAct]
    · rintro ⟨i, s⟩
      by_cases h : i = b
      · subst h
        simp [rowGen, rowAct, Matrix.transvection, Matrix.single, Matrix.one_apply, add_mul,
          Finset.sum_add_distrib, ite_and, add_comm]
        rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp), if_pos rfl, mul_comm]
      · simp [rowGen, rowAct, Matrix.transvection, Matrix.single, Matrix.one_apply, add_mul,
          Finset.sum_add_distrib, h, Ne.symm h]
  exact RingHom.congr_fun key f

theorem rowDiv_eq_zero_of_matRep_unipotent_fixed : ∀ (n n' : ℕ) (v : MvPolynomial (Fin n' × Fin n) ℂ), (∀ g : GL (Fin n') ℂ, (g : Matrix (Fin n') (Fin n') ℂ).BlockTriangular id → (∀ a, (g : Matrix (Fin n') (Fin n') ℂ) a a = 1) → matRep n n' (1, g) v = v) → ∀ a b : Fin n', a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0 := by
  intro n n' v hv a b hab k hk
  have hroot : ∀ t : ℂ, (rowGen ℂ a b v).eval (C t) = v := by
    intro t
    rw [rowGen_eval_C_eq_rowAct_transvection]
    have hdet : IsUnit (Matrix.transvection a b t).det := by
      rw [Matrix.det_transvection_of_ne _ _ (ne_of_lt hab)]
      exact isUnit_one
    let g : GL (Fin n') ℂ := Matrix.nonsingInvUnit _ hdet
    have hgv : (g : Matrix (Fin n') (Fin n') ℂ) = Matrix.transvection a b t := rfl
    have hbt : (g : Matrix (Fin n') (Fin n') ℂ).BlockTriangular id := by
      intro i j hij
      have hne : i ≠ j := fun h => by simp [h] at hij
      have hne' : ¬(a = i ∧ b = j) := by
        rintro ⟨rfl, rfl⟩
        exact absurd (lt_trans hab hij) (lt_irrefl _)
      simp [hgv, Matrix.transvection, Matrix.single, hne, hne']
    have hdiag : ∀ i, (g : Matrix (Fin n') (Fin n') ℂ) i i = 1 := by
      intro i
      have hne' : ¬(a = i ∧ b = i) := by
        rintro ⟨rfl, rfl⟩
        exact lt_irrefl _ hab
      simp [hgv, Matrix.transvection, Matrix.single, hne']
    have hg := hv g hbt hdiag
    rw [matRep_one_left, hgv] at hg
    exact hg
  have hconst : rowGen ℂ a b v = Polynomial.C v := by
    rw [← sub_eq_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_
      (Set.infinite_range_of_injective (MvPolynomial.C_injective (Fin n' × Fin n) ℂ))
    rintro _ ⟨t, rfl⟩
    simp [Polynomial.IsRoot, hroot t]
  show (rowGen ℂ a b v).coeff k = 0
  rw [hconst, Polynomial.coeff_C, if_neg (by omega)]

end GlobalTheory.GLDuality
end

