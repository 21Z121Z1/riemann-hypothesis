import Mathlib

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
section
open Polynomial Module

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity

variable {C : Type} [Field C]

abbrev Int0 (v : AddValuation C (WithTop ℝ)) : Subring C :=
  (AddValuation.toValuation v).integer

theorem mem_addValuationIntegerRing_iff (v : AddValuation C (WithTop ℝ)) (x : C) : x ∈ Int0 v ↔ 0 ≤ v x := Iff.rfl

def RelLen (v : AddValuation C (WithTop ℝ)) {M : Type} [AddCommGroup M] [Module (Int0 v) M]
    (X' X : Submodule (Int0 v) M) (r : ℝ) : Prop :=
  ∃ (n : ℕ) (b : Basis (Fin n) (Int0 v) X) (b' : Basis (Fin n) (Int0 v) X')
    (A : Matrix (Fin n) (Fin n) (Int0 v)),
    (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) ∧ v (A.det : C) = (r : WithTop ℝ)

section Ring

variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

abbrev RS (a : S → O) : Type := AdjoinRoot (∏ s, (X - Polynomial.C (a s)) : O[X])

def lin (a : S → O) (s : S) : RS a := AdjoinRoot.root _ - algebraMap O (RS a) (a s)

def cofac (a : S → O) (τ : S) : RS a := ∏ s ∈ Finset.univ.erase τ, lin a s

def ev (a : S → O) (s : S) : RS a →ₐ[O] O :=
  AdjoinRoot.liftAlgHom _ (AlgHom.id O O) (a s) (by
    rw [Polynomial.eval₂_finset_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp))

def comp (a : S → O) (N : ℕ) (s : S) : (Fin N → RS a) →ₗ[O] (Fin N → O) :=
  (ev a s).toLinearMap.compLeft (Fin N)

def kerMul (a : S → O) (r : RS a) (M : Type) [AddCommGroup M] [Module (RS a) M] [Module O M]
    [IsScalarTower O (RS a) M] : Submodule O M :=
  (LinearMap.ker (LinearMap.lsmul (RS a) M r)).restrictScalars O

def imMul (a : S → O) (r : RS a) (M : Type) [AddCommGroup M] [Module (RS a) M] [Module O M]
    [IsScalarTower O (RS a) M] : Submodule O M :=
  (LinearMap.range (LinearMap.lsmul (RS a) M r)).restrictScalars O

def eigSub (a : S → O) (τ : S) (M : Type) [AddCommGroup M] [Module (RS a) M] [Module O M]
    [IsScalarTower O (RS a) M] : Submodule O M :=
  kerMul a (lin a τ) M

def eigQuot (a : S → O) {N : ℕ} (X : Submodule (RS a) (Fin N → RS a)) (s : S) :
    Submodule O (Fin N → O) :=
  (X.restrictScalars O).map (comp a N s)

def incl (a : S → O) {N : ℕ} (X : Submodule (RS a) (Fin N → RS a)) : X →ₗ[O] (Fin N → RS a) :=
  X.subtype.restrictScalars O

def proj (a : S → O) {N : ℕ} (X : Submodule (RS a) (Fin N → RS a)) :
    (Fin N → RS a) →ₗ[O] ((Fin N → RS a) ⧸ X) :=
  X.mkQ.restrictScalars O

theorem ev_lin (a : S → O) (s t : S) : ev a s (lin a t) = a s - a t := by
  simp [ev, lin]

end Ring

variable {S : Type} [Fintype S] [DecidableEq S]

def eigRank (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (X : Submodule (RS a) (Fin N → RS a)) (s : S) : ℕ :=
  finrank C (Submodule.span C
    ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) '' (eigQuot a X s : Set (Fin N → Int0 v))))

def vd (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) (τ : S) : WithTop ℝ :=
  v (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)))

def yExp (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : WithTop ℝ :=
  ∑ s ∈ Finset.univ.erase τ, eigRank v a Fil s • v ((a s : C) - (a τ : C))

def DetIdentity (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : Prop :=
  ∃ p : ℕ, p + eigRank v a Fil τ = N ∧
    Nonempty (Basis (Fin N) (Int0 v) (eigSub a τ (Fin N → RS a))) ∧
    Nonempty (Basis (Fin p) (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil))) ∧
    Nonempty (Basis (Fin (eigRank v a Fil τ)) (Int0 v) (eigQuot a Fil τ)) ∧
    ∀ (h : Basis (Fin N) (Int0 v) (eigSub a τ (Fin N → RS a)))
      (l : Basis (Fin p) (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)))
      (x : Fin p → (Fin N → RS a))
      (_ : ∀ i, proj a Fil (x i) = (l i : (Fin N → RS a) ⧸ Fil))
      (f : Basis (Fin (eigRank v a Fil τ)) (Int0 v) (eigQuot a Fil τ))
      (e : Fin N ≃ Fin p ⊕ Fin (eigRank v a Fil τ)),
      ∃ c : C, v c = yExp v a Fil τ ∧
        (Matrix.of fun k : Fin N =>
          Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)).det ≠ 0 ∧
        ((Matrix.of fun k : Fin N => comp a N τ (h k : Fin N → RS a)).det : C) =
          c * ((Matrix.of fun k : Fin N =>
            Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)).det : C)

def KernelIdentity (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : Prop :=
  (eigSub a τ (Fin N → RS a)).map (proj a Fil) ≤ eigSub a τ ((Fin N → RS a) ⧸ Fil) ∧
  eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (proj a Fil) = (eigSub a τ Fil).map (incl a Fil)

def LengthIdentities (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : Prop :=
  ∃ δ e₂ m : ℝ,
    RelLen v ((eigSub a τ (Fin N → RS a)).map (proj a Fil))
      (eigSub a τ ((Fin N → RS a) ⧸ Fil)) δ ∧
    RelLen v (imMul a (lin a τ) Fil) (kerMul a (cofac a τ) Fil) δ ∧
    RelLen v (imMul a (cofac a τ) Fil) (eigSub a τ Fil) e₂ ∧
    RelLen v ((eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))) (eigQuot a Fil τ) m ∧
    ((m + e₂ : ℝ) : WithTop ℝ) = eigRank v a Fil τ • vd v a τ ∧
    ((∀ s, eigRank v a Fil s = eigRank v a Fil τ) →
      0 ≤ δ ∧ (δ : WithTop ℝ) ≤ eigRank v a Fil τ • vd v a τ ∧
      0 ≤ m ∧ (m : WithTop ℝ) ≤ eigRank v a Fil τ • vd v a τ)

def HerbrandDet : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a →
    ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)),
      (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) →
      ∀ τ : S, DetIdentity v a Fil τ ∧ KernelIdentity v a Fil τ ∧ LengthIdentities v a Fil τ

theorem v_unit (v : AddValuation C (WithTop ℝ)) {u : Int0 v} (hu : IsUnit u) : v (u : C) = 0 := by
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h1 : v (u : C) + v (w : C) = 0 := by
    rw [← v.map_mul, ← Subring.coe_mul, hw]; simp
  have hu0 : 0 ≤ v (u : C) := u.2
  have hw0 : 0 ≤ v (w : C) := w.2
  refine le_antisymm ?_ hu0
  calc v (u : C) ≤ v (u : C) + v (w : C) := le_add_of_nonneg_right hw0
    _ = 0 := h1

theorem RelLen.unique (v : AddValuation C (WithTop ℝ)) {M : Type} [AddCommGroup M]
    [Module (Int0 v) M] {X' X : Submodule (Int0 v) M} {r r' : ℝ}
    (h : RelLen v X' X r) (h' : RelLen v X' X r') : r = r' := by
  obtain ⟨n, b, b', A, hA, hr⟩ := h
  obtain ⟨m, c, c', B, hB, hr'⟩ := h'
  have hnm : n = m := by simpa using Fintype.card_congr (b.indexEquiv c)
  subst hnm
  have hle : X' ≤ X := by
    intro x hx
    have : (x : M) = ∑ k, b'.repr ⟨x, hx⟩ k • (b' k : M) := by
      have := congrArg X'.subtype (b'.sum_repr ⟨x, hx⟩)
      rw [map_sum] at this
      exact this.symm
    rw [this]
    refine X.sum_mem fun k _ => X.smul_mem _ ?_
    rw [hA k]
    exact X.sum_mem fun i _ => X.smul_mem _ (b i).2
  have key : ∀ (b : Basis (Fin n) (Int0 v) X) (b' : Basis (Fin n) (Int0 v) X')
      (A : Matrix (Fin n) (Fin n) (Int0 v)), (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) →
      LinearMap.toMatrix b' b (Submodule.inclusion hle) = A := by
    intro b b' A hA
    ext i k
    have : Submodule.inclusion hle (b' k) = ∑ i, A i k • b i := by
      apply Subtype.ext
      simpa using hA k
    rw [LinearMap.toMatrix_apply, this]
    simp [Finsupp.single_apply]
  have hAB : A = b.toMatrix c * B * c'.toMatrix b' := by
    rw [← key b b' A hA, ← key c c' B hB, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  have u1 : IsUnit (b.toMatrix c).det := by
    letI := b.invertibleToMatrix c
    exact Matrix.isUnit_det_of_invertible _
  have u2 : IsUnit (c'.toMatrix b').det := by
    letI := c'.invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  have : v (A.det : C) = v (B.det : C) := by
    rw [hAB, Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul, v.map_mul,
      v.map_mul, v_unit v u1, v_unit v u2, zero_add, add_zero]
  rw [hr, hr'] at this
  exact_mod_cast this

end GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorProductAction
section
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorProductAction

section Defs

variable (Λ : Type) [CommRing Λ] (O : Type) [CommRing O] [Algebra Λ O]

noncomputable def tensorAction (R : Type) [CommRing R] [Algebra Λ R]
    (T : Type) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower Λ O T] :
    R ⊗[Λ] O →ₐ[R] Module.End R (R ⊗[Λ] T) :=
  Algebra.TensorProduct.lift (Algebra.ofId R _)
    ((Module.End.baseChangeHom Λ R T).comp (Algebra.lsmul Λ Λ T))
    (fun r _ => Algebra.commute_algebraMap_left r _)

@[reducible] noncomputable def tensorModule (R : Type) [CommRing R] [Algebra Λ R]
    (T : Type) [AddCommGroup T] [Module Λ T] [Module O T] [IsScalarTower Λ O T] :
    Module (R ⊗[Λ] O) (R ⊗[Λ] T) :=
  Module.compHom (R ⊗[Λ] T) (tensorAction Λ O R T).toRingHom

noncomputable def act (R : Type) [CommRing R] [Algebra Λ R]
    (X : Type) [AddCommGroup X] [Module R X] [Module (R ⊗[Λ] O) X]
    [IsScalarTower R (R ⊗[Λ] O) X] (a : O) : X →ₗ[R] X :=
  Algebra.lsmul R R X ((1 : R) ⊗ₜ[Λ] a : R ⊗[Λ] O)

variable {Λ O}
variable {R : Type} [CommRing R] [Algebra Λ R] (C : Type) [Field C] [Algebra R C]
  (τ : O →ₐ[Λ] R)
  (X : Type) [AddCommGroup X] [Module R X] [Module (R ⊗[Λ] O) X] [IsScalarTower R (R ⊗[Λ] O) X]

noncomputable def coeigen : Submodule C (C ⊗[R] X) :=
  Submodule.span C
    {z | ∃ (a : O) (y : C ⊗[R] X),
      z = (act Λ O R X a).baseChange C y - algebraMap R C (τ a) • y}

noncomputable def toEigen : X →ₗ[R] (C ⊗[R] X) ⧸ coeigen C τ X :=
  ((coeigen C τ X).mkQ.restrictScalars R).comp (TensorProduct.mk R C X 1)

noncomputable def eigenQuot : Submodule R ((C ⊗[R] X) ⧸ coeigen C τ X) :=
  LinearMap.range (toEigen C τ X)

noncomputable def eigenProj : X →ₗ[R] eigenQuot C τ X :=
  (toEigen C τ X).rangeRestrict

noncomputable def evalAt : R ⊗[Λ] O →+* R :=
  (Algebra.TensorProduct.lift (AlgHom.id R R) τ (fun _ _ => Commute.all _ _)).toRingHom

noncomputable def reduceRing (O : Type) [CommRing O] [Algebra Λ O] {A : Type} [CommRing A]
    [Algebra Λ A] (θ : A →ₐ[Λ] R) : A ⊗[Λ] O →+* R ⊗[Λ] O :=
  (Algebra.TensorProduct.map θ (AlgHom.id Λ O)).toRingHom

end Defs

def FreenessLemma : Prop :=
  ∀ (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Algebra O E] [IsScalarTower ℤ_[l] O E]
    [IsIntegralClosure O ℤ_[l] E]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k l]
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[l] A]
    (ρ : A →+* WittVector l k)
    (_ : Function.Surjective (WittVector.constantCoeff.comp ρ : A →+* k))
    (μ : A) (_ : μ ∈ A⁰)
    (N : ℕ)
    (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module O T] [IsScalarTower ℤ_[l] O T]
    [Module.Finite ℤ_[l] T] [Module.Free ℤ_[l] T]
    (_ : Module.finrank ℤ_[l] T = Module.finrank ℚ_[l] E * N)
    (M : Type) [AddCommGroup M] [Module A M] [Module (A ⊗[ℤ_[l]] O) M]
    [IsScalarTower A (A ⊗[ℤ_[l]] O) M] [Module.Finite A M] [Module.Free A M]
    (j : Localization.Away μ ⊗[A] M ≃ₗ[Localization.Away μ] Localization.Away μ ⊗[ℤ_[l]] T)
    (_ : ∀ (a : O) (y : Localization.Away μ ⊗[A] M),
      j ((act ℤ_[l] O A M a).baseChange (Localization.Away μ) y) =
        tensorAction ℤ_[l] O (Localization.Away μ) T (1 ⊗ₜ a) (j y)),
    Nonempty (Module.Basis (Fin N) O T) ∧
    Nonempty (Module.Basis (Fin N) (A ⊗[ℤ_[l]] O) M) ∧
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℤ_[l] R]
      (C : Type) [Field C] [Algebra R C] [IsFractionRing R C]
      (θ : A →ₐ[ℤ_[l]] R) (_ : Function.Surjective θ)
      (ξ : A) (_ : RingHom.ker θ = Ideal.span {ξ})
      (H : Type) [AddCommGroup H] [Module R H] [Module (R ⊗[ℤ_[l]] O) H]
      [IsScalarTower R (R ⊗[ℤ_[l]] O) H]
      (q : M →ₛₗ[reduceRing O θ] H) (_ : Function.Surjective q)
      (_ : ∀ m : M, q m = 0 ↔ ∃ m' : M, m = ξ • m'),
      Nonempty (Module.Basis (Fin N) (R ⊗[ℤ_[l]] O) H) ∧
      (letI := tensorModule ℤ_[l] O R T
       Nonempty (Module.Basis (Fin N) (R ⊗[ℤ_[l]] O) (R ⊗[ℤ_[l]] T))) ∧
      ∀ τ : O →ₐ[ℤ_[l]] R,
        Nonempty (Module.Basis (Fin N) R (eigenQuot C τ H)) ∧
        (∃ (f : ⋀[A ⊗[ℤ_[l]] O]^N M →ₛₗ[reduceRing O θ] ⋀[R ⊗[ℤ_[l]] O]^N H)
           (g : ⋀[R ⊗[ℤ_[l]] O]^N H →ₛₗ[evalAt τ] ⋀[R]^N (eigenQuot C τ H)),
          (∀ x : Fin N → M, f (exteriorPower.ιMulti _ N x) =
            exteriorPower.ιMulti _ N (fun i => q (x i))) ∧
          (∀ h : Fin N → H, g (exteriorPower.ιMulti _ N h) =
            exteriorPower.ιMulti _ N (fun i => eigenProj C τ H (h i))) ∧
          Function.Surjective f ∧ Function.Surjective g) ∧
        ∃ d : eigenQuot C τ (⋀[R ⊗[ℤ_[l]] O]^N H) ≃ₗ[R] ⋀[R]^N (eigenQuot C τ H),
          ∀ h : Fin N → H,
            d (eigenProj C τ _ (exteriorPower.ιMulti _ N h)) =
              exteriorPower.ιMulti _ N (fun i => eigenProj C τ H (h i))

example (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k l] :
    IsLocalRing (WittVector l k) ∧
    Function.Surjective
      (WittVector.constantCoeff.comp (RingHom.id (WittVector l k)) : WittVector l k →+* k) ∧
    (l : WittVector l k) ∈ (WittVector l k)⁰ := by
  refine ⟨inferInstance, fun x => ⟨WittVector.teichmuller l x, by simp⟩, ?_⟩
  exact mem_nonZeroDivisors_of_ne_zero (WittVector.p_nonzero l k)

end GlobalTheory.IndefiniteRowSideFullHecke.TensorProductAction
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
section
noncomputable section

open NumberField nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

variable {F : Type} [Field F] [NumberField F]

def traceDual (M : FractionalIdeal (𝓞 F)⁰ F) : Set F :=
  {y | ∀ a ∈ M, ∃ n : ℤ, Algebra.trace ℚ F (y * a) = n}

def covol (M : FractionalIdeal (𝓞 F)⁰ F) : ℝ :=
  Real.sqrt |(discr F : ℝ)| * (FractionalIdeal.absNorm M : ℝ)

def dualCone (M : FractionalIdeal (𝓞 F)⁰ F) (z : (F →+* ℝ) → ℂ) : Set F :=
  {ν | ν ∈ traceDual M ∧ ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν}

def lhsTerm (k : ℕ) (z : (F →+* ℝ) → ℂ) (a : F) : ℂ :=
  (∏ τ : F →+* ℝ, (z τ + ((τ a : ℝ) : ℂ))) ^ (-(k : ℤ))

def rhsTerm (k : ℕ) (z : (F →+* ℝ) → ℂ) (ν : F) : ℂ :=
  ((|∏ τ : F →+* ℝ, τ ν| ^ (k - 1) : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * ∑ τ : F →+* ℝ, ((τ ν : ℝ) : ℂ) * z τ)

def lipConst (k : ℕ) (M : FractionalIdeal (𝓞 F)⁰ F) : ℂ :=
  (2 * Real.pi * Complex.I) ^ (k * Module.finrank ℚ F) /
    ((((k - 1).factorial : ℕ) : ℂ) ^ Module.finrank ℚ F * (covol M : ℂ))

def Lipschitz : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 →
    ∀ (k : ℕ), 2 ≤ k → Even k →
    ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) →
      Summable (fun a : (M : Set F) => lhsTerm k z a) ∧
      Summable (fun ν : dualCone M z => rhsTerm k z ν) ∧
      ∑' a : (M : Set F), lhsTerm k z a = lipConst k M * ∑' ν : dualCone M z, rhsTerm k z ν

open NumberField nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) (y : F) :
    y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.traceDual M ↔ y ∈ FractionalIdeal.dual ℤ ℚ M := by
  change (∀ a ∈ M, ∃ n : ℤ, Algebra.trace ℚ F (y * a) = n) ↔ _
  rw [FractionalIdeal.mem_dual hM]
  refine forall₂_congr fun a _ => ?_
  simp [Algebra.traceForm_apply, eq_comm]

theorem mem_traceDual_iff_different {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) (y : F) :
    y ∈ traceDual M ↔ y ∈ ((differentIdeal ℤ (𝓞 F) : FractionalIdeal (𝓞 F)⁰ F))⁻¹ * M⁻¹ := by
  rw [mem_traceDual_iff hM, FractionalIdeal.dual_eq_mul_inv, coeIdeal_differentIdeal ℤ ℚ F (𝓞 F), inv_inv]

open NumberField nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_pos {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) :
    0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol M := by
  refine mul_pos (Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F)))) ?_
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg M)
    (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.2 hM))

open NumberField nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
open Classical in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_eq_covolume [IsTotallyReal F]
    (M : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol (M : FractionalIdeal (𝓞 F)⁰ F) =
      ZLattice.covolume (mixedEmbedding.idealLattice F M) := by
  rw [mixedEmbedding.covolume_idealLattice, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero,
    mul_one, mul_comm]
  rfl

open NumberField nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.card_realEmb [IsTotallyReal F] :
    Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
  classical
  rw [IsTotallyReal.finrank, ← InfinitePlace.card_real_embeddings]
  convert Fintype.card_congr
    { toFun := fun φ => ⟨Complex.ofRealHom.comp φ, ?_⟩
      invFun := fun φ => φ.2.embedding
      left_inv := ?_
      right_inv := ?_ : (F →+* ℝ) ≃ { φ : F →+* ℂ // ComplexEmbedding.IsReal φ } }
  · rw [ComplexEmbedding.isReal_iff]; ext x; simp [ComplexEmbedding.conjugate]
  · intro φ; ext x
    simpa using ComplexEmbedding.IsReal.coe_embedding_apply (φ := Complex.ofRealHom.comp φ) _ x
  · intro φ; ext x; simp [ComplexEmbedding.IsReal.coe_embedding_apply]

theorem norm_add_ne_zero {z : (F →+* ℝ) → ℂ} (hz : ∀ τ, (z τ).im ≠ 0) (a : F) :
    ∏ τ : F →+* ℝ, (z τ + ((τ a : ℝ) : ℂ)) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun τ _ h => hz τ (by simpa using congrArg Complex.im h)

example (M : FractionalIdeal (𝓞 F)⁰ F) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, 0 < (z τ).im) (ν : F) :
    ν ∈ dualCone M z ↔ ν ∈ traceDual M ∧ ∀ τ : F →+* ℝ, 0 < τ ν := by
  simp [dualCone, hz]

end GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
end
end

