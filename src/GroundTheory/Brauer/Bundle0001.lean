import Mathlib
import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
import GroundTheory.Brauer.BaseChangeCSA
import GroundTheory.Brauer.CrossedProduct
import GroundTheory.Brauer.CrossedProductSimple

-- bundled from GroundTheory.Brauer.BaseChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Brauer

open TensorProduct

universe u v

section Equivalence

variable {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]

theorem IsBrauerEquivalent.baseChange {A B : CSA.{u, v} K} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (baseChangeCSA L A) (baseChangeCSA L B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm, ⟨(baseChangeMatrix K L A (Fin n)).symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e).trans <|
      baseChangeMatrix K L B (Fin m)⟩⟩

end Equivalence

namespace BrauerGroup

section Hom

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]

noncomputable def baseChangeFun : BrauerGroup.{u, u} K → BrauerGroup.{u, u} L :=
  Quotient.map (baseChangeCSA L) fun _ _ h ↦ IsBrauerEquivalent.baseChange L h

noncomputable def baseChange : BrauerGroup.{u, u} K →* BrauerGroup.{u, u} L where
  toFun := baseChangeFun K L
  map_one' := Quotient.sound <|
    isBrauerEquivalent_of_algEquiv (Algebra.TensorProduct.rid K L L)
  map_mul' := by
    rintro ⟨A⟩ ⟨B⟩
    exact Quotient.sound <| isBrauerEquivalent_of_algEquiv (baseChangeCSATensor L A B)

variable {K L} in

@[simp]
theorem baseChange_mk (A : CSA.{u, u} K) :
    baseChange K L ⟦A⟧ = ⟦baseChangeCSA L A⟧ := rfl

theorem baseChange_comp (M : Type u) [Field M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] :
    (baseChange L M).comp (baseChange K L) = baseChange K M := by
  ext x
  induction x using Quotient.inductionOn with
  | h A => exact Quotient.sound <| isBrauerEquivalent_of_algEquiv (baseChangeCSATower L M A)

theorem baseChange_baseChange (M : Type u) [Field M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] (x : BrauerGroup.{u, u} K) :
    baseChange L M (baseChange K L x) = baseChange K M x :=
  DFunLike.congr_fun (baseChange_comp K L M) x

end Hom

section Relative

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]

noncomputable def relBrauer : Subgroup (BrauerGroup.{u, u} K) :=
  (baseChange K L).ker

variable {K L}

theorem mem_relBrauer_iff (x : BrauerGroup.{u, u} K) :
    x ∈ relBrauer K L ↔ baseChange K L x = 1 :=
  MonoidHom.mem_ker

theorem mk_mem_relBrauer_iff (A : CSA.{u, u} K) :
    ⟦A⟧ ∈ relBrauer K L ↔
      ∃ n : ℕ, Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  rw [mem_relBrauer_iff, baseChange_mk, BrauerGroup.one_def, Quotient.eq]
  change IsBrauerEquivalent (baseChangeCSA L A) (oneCSA L) ↔ _
  have : IsArtinianRing (baseChangeCSA L A) := IsArtinianRing.of_finite L _
  obtain ⟨k, hk, D, _, _, _, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite L (baseChangeCSA L A)
  constructor
  · intro h
    obtain ⟨g⟩ := (isBrauerEquivalent_iff_nonempty_algEquiv e
      ((matrixFinOneAlgEquiv (K := L) L).symm)).mp h
    exact ⟨k, ⟨e.trans g.mapMatrix⟩⟩
  · rintro ⟨n, ⟨f⟩⟩
    have hn : n ≠ 0 := by
      rintro rfl
      exact one_ne_zero (f.injective (Subsingleton.elim _ _) : (1 : L ⊗[K] A) = 0)
    have : NeZero n := ⟨hn⟩
    exact isBrauerEquivalent_of_algEquiv_matrix (C := L) f
      ((matrixFinOneAlgEquiv (K := L) L).symm)

end Relative

end BrauerGroup

end GroundTheory.Brauer
end

-- bundled from GroundTheory.Brauer.CrossedProductMaps
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

namespace CrossedProduct

open groupCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}

section lift

variable {A : Type*} [Ring A] [Algebra K A]

def liftAdd (φ : L →ₐ[K] A) (v : (L ≃ₐ[K] L) → A) : CrossedProduct hf →+ A :=
  (Finsupp.liftAddHom fun σ => (AddMonoidHom.mulRight (v σ)).comp (φ : L →+ A)).comp
    coeffAddHom

theorem liftAdd_single (φ : L →ₐ[K] A) (v : (L ≃ₐ[K] L) → A) (σ : L ≃ₐ[K] L) (a : L) :
    liftAdd φ v (single σ a : CrossedProduct hf) = φ a * v σ := by
  simp [liftAdd, coeffAddHom]

def lift (φ : L →ₐ[K] A) (v : (L ≃ₐ[K] L) → A)
    (hcomm : ∀ σ a, v σ * φ a = φ (σ a) * v σ)
    (hmul : ∀ σ τ, v σ * v τ = φ (f (σ, τ)) * v (σ * τ))
    (hone : v 1 = φ (f (1, 1))) : CrossedProduct hf →ₐ[K] A where
  toFun := liftAdd φ v
  map_add' := map_add _
  map_zero' := map_zero _
  map_one' := by
    rw [one_def, liftAdd_single, hone, ← map_mul, Units.inv_mul, map_one]
  map_mul' x y := by
    induction x using induction_on with
    | zero => simp
    | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
    | single σ a =>
    induction y using induction_on with
    | zero => simp
    | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
    | single τ b =>
    rw [single_mul_single, liftAdd_single, liftAdd_single, liftAdd_single, map_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (v σ) (φ b) (v τ), hcomm, mul_assoc (φ (σ b)) (v σ) (v τ), hmul]
  commutes' c := by
    rw [← (incl (hf := hf)).commutes c, incl_apply, liftAdd_single, hone, map_mul, mul_assoc,
      ← map_mul, Units.inv_mul, map_one, mul_one, φ.commutes]

section

variable (φ : L →ₐ[K] A) (v : (L ≃ₐ[K] L) → A) (hcomm : ∀ σ a, v σ * φ a = φ (σ a) * v σ)
    (hmul : ∀ σ τ, v σ * v τ = φ (f (σ, τ)) * v (σ * τ)) (hone : v 1 = φ (f (1, 1)))

@[simp] theorem lift_single (σ : L ≃ₐ[K] L) (a : L) :
    lift (hf := hf) φ v hcomm hmul hone (single σ a) = φ a * v σ :=
  liftAdd_single φ v σ a

@[simp] theorem lift_incl (a : L) : lift (hf := hf) φ v hcomm hmul hone (incl a) = φ a := by
  rw [incl_apply, lift_single, hone, map_mul, mul_assoc, ← map_mul, Units.inv_mul, map_one,
    mul_one]

@[simp] theorem lift_u (σ : L ≃ₐ[K] L) : lift (hf := hf) φ v hcomm hmul hone (u σ) = v σ := by
  rw [u, lift_single, map_one, one_mul]

end

theorem algHom_ext {g₁ g₂ : CrossedProduct hf →ₐ[K] A} (hL : ∀ a, g₁ (incl a) = g₂ (incl a))
    (hu : ∀ σ, g₁ (u σ) = g₂ (u σ)) : g₁ = g₂ := by
  ext x
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single σ a => rw [← incl_mul_u, map_mul, map_mul, hL, hu]

end lift

section coboundary

variable {f' : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}

theorem mul_smul_mul_eq_of_coboundary {x : (L ≃ₐ[K] L) → Lˣ}
    (hx : ∀ σ τ : L ≃ₐ[K] L, σ • x τ / x (σ * τ) * x σ = (f' / f) (σ, τ)) (σ τ : L ≃ₐ[K] L) :
    (f (σ, τ) : L) * σ (x τ) * x σ = f' (σ, τ) * x (σ * τ) := by
  have h := hx σ τ
  rw [Pi.div_apply, div_mul_eq_mul_div, div_eq_div_iff_mul_eq_mul] at h
  have h' := congrArg (fun y : Lˣ => (y : L)) h
  simp only [Units.val_mul, val_smul_units] at h'
  linear_combination h'

def equivOfIsMulCoboundary₂ (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (h : IsMulCoboundary₂ (f' / f)) : CrossedProduct hf ≃ₐ[K] CrossedProduct hf' :=
  have key := mul_smul_mul_eq_of_coboundary h.choose_spec
  have hx0 : ∀ σ, ((h.choose σ : Lˣ) : L) ≠ 0 := fun σ => (h.choose σ).ne_zero
  have key1 : (f (1, 1) : L) * h.choose 1 = f' (1, 1) := by
    have k := key 1 1
    rw [AlgEquiv.one_apply, mul_one, mul_assoc, mul_comm (h.choose 1 : L), ← mul_assoc] at k
    exact mul_right_cancel₀ (hx0 1) k
  AlgEquiv.ofAlgHom
    (lift (hf := hf) (incl : L →ₐ[K] CrossedProduct hf')
      (fun σ => (incl (((h.choose σ)⁻¹ : Lˣ) : L) : CrossedProduct hf') * u σ)
      (fun σ a => by
        rw [mul_assoc, u_mul_incl, ← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, mul_comm])
      (fun σ τ => by
        rw [mul_assoc, ← mul_assoc (u σ), u_mul_incl, mul_assoc, u_mul_u, ← mul_assoc,
          ← mul_assoc, ← map_mul, ← map_mul, ← mul_assoc, ← map_mul]
        congr 2
        simp only [Units.val_inv_eq_inv_val, map_inv₀]
        have ea := mul_inv_cancel₀ (hx0 σ)
        have eb := mul_inv_cancel₀ ((map_ne_zero σ).2 (hx0 τ))
        have ec := mul_inv_cancel₀ (hx0 (σ * τ))
        linear_combination
          (-((h.choose σ : L)⁻¹ * (σ (h.choose τ : L))⁻¹ * f' (σ, τ))) * ec -
          ((h.choose σ : L)⁻¹ * (σ (h.choose τ : L))⁻¹ * (h.choose (σ * τ) : L)⁻¹) * key σ τ +
          ((f (σ, τ) : L) * (h.choose (σ * τ) : L)⁻¹ *
            (σ (h.choose τ : L) * (σ (h.choose τ : L))⁻¹)) * ea +
          ((f (σ, τ) : L) * (h.choose (σ * τ) : L)⁻¹) * eb)
      (by
        rw [u_one, ← map_mul, Units.val_inv_eq_inv_val]
        congr 1
        have e1 := inv_mul_cancel₀ (hx0 1)
        linear_combination (-(h.choose 1 : L)⁻¹) * key1 + (f (1, 1) : L) * e1))
    (lift (hf := hf') (incl : L →ₐ[K] CrossedProduct hf)
      (fun σ => (incl (h.choose σ : L) : CrossedProduct hf) * u σ)
      (fun σ a => by
        rw [mul_assoc, u_mul_incl, ← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, mul_comm])
      (fun σ τ => by
        rw [mul_assoc, ← mul_assoc (u σ), u_mul_incl, mul_assoc, u_mul_u, ← mul_assoc,
          ← mul_assoc, ← map_mul, ← map_mul, ← mul_assoc, ← map_mul]
        congr 2
        linear_combination key σ τ)
      (by
        rw [u_one, ← map_mul]
        congr 1
        linear_combination key1))
    (algHom_ext (fun a => by simp) (fun σ => by
      simp only [AlgHom.comp_apply, lift_u, map_mul, lift_incl, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]))
    (algHom_ext (fun a => by simp) (fun σ => by
      simp only [AlgHom.comp_apply, lift_u, map_mul, lift_incl, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]))

@[simp] theorem equivOfIsMulCoboundary₂_incl (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (h : IsMulCoboundary₂ (f' / f)) (a : L) :
    equivOfIsMulCoboundary₂ hf hf' h (incl a) = incl a := by
  simp [equivOfIsMulCoboundary₂]

theorem exists_algEquiv_of_isMulCoboundary₂ (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f')
    (h : IsMulCoboundary₂ (f' / f)) :
    ∃ e : CrossedProduct hf ≃ₐ[K] CrossedProduct hf', ∀ a : L, e (incl a) = incl a :=
  ⟨equivOfIsMulCoboundary₂ hf hf' h, equivOfIsMulCoboundary₂_incl hf hf' h⟩

end coboundary

section split

theorem isMulCocycle₂_one : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ) :=
  fun _ _ _ => by simp

def toEnd (hf : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)) :
    CrossedProduct hf →ₐ[K] Module.End K L :=
  lift (Algebra.lmul K L) (fun σ => σ.toLinearMap)
    (fun σ a => by
      ext y
      simp)
    (fun σ τ => by
      ext y
      simp)
    (by
      ext y
      simp)

@[simp] theorem toEnd_single (hf : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ))
    (σ : L ≃ₐ[K] L) (a y : L) : toEnd hf (single σ a) y = a * σ y := by
  simp [toEnd]

variable [FiniteDimensional K L] [IsGalois K L]

theorem toEnd_bijective (hf : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)) :
    Function.Bijective (toEnd hf) := by
  have hinj : Function.Injective (toEnd hf) := RingHom.injective (toEnd hf).toRingHom
  refine ⟨hinj, ?_⟩
  have hdim : Module.finrank K (CrossedProduct hf) = Module.finrank K (Module.End K L) := by
    rw [finrank_eq_sq, Module.finrank_linearMap, sq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (toEnd hf).toLinearMap)).1 hinj

def endEquiv (hf : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)) :
    CrossedProduct hf ≃ₐ[K] Module.End K L :=
  AlgEquiv.ofBijective (toEnd hf) (toEnd_bijective hf)

@[simp] theorem endEquiv_apply (hf : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ))
    (x : CrossedProduct hf) : endEquiv hf x = toEnd hf x := rfl

def matrixEquiv (hf : IsMulCocycle₂ (1 : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ)) :
    CrossedProduct hf ≃ₐ[K]
      Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) K :=
  (endEquiv hf).trans (LinearMap.toMatrixAlgEquiv (Module.finBasis K L))

omit [FiniteDimensional K L] [IsGalois K L] in

theorem isMulCoboundary₂_inv {g : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} (h : IsMulCoboundary₂ g) :
    IsMulCoboundary₂ g⁻¹ := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x⁻¹, fun σ τ => ?_⟩
  simp only [Pi.inv_apply]
  rw [← hx σ τ, smul_inv']
  simp only [div_eq_mul_inv, mul_inv, inv_inv]

def endEquivOfIsMulCoboundary₂ (hf : IsMulCocycle₂ f) (h : IsMulCoboundary₂ f) :
    CrossedProduct hf ≃ₐ[K] Module.End K L :=
  (equivOfIsMulCoboundary₂ hf isMulCocycle₂_one (by
    rw [one_div]
    exact isMulCoboundary₂_inv h)).trans (endEquiv isMulCocycle₂_one)

end split

end CrossedProduct

end GroundTheory.Brauer

end
end

-- bundled from GroundTheory.Brauer.Degree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Brauer

open Module TensorProduct

universe u v w

section Degree

variable (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A]

noncomputable def degree : ℕ := Nat.sqrt (finrank K A)

theorem exists_algEquiv_matrix_algebraicClosure [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] :
    ∃ n : ℕ, NeZero n ∧ finrank K A = n ^ 2 ∧
      Nonempty (AlgebraicClosure K ⊗[K] A ≃ₐ[AlgebraicClosure K]
        Matrix (Fin n) (Fin n) (AlgebraicClosure K)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed
    (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
  refine ⟨n, hn, ?_, ⟨e⟩⟩
  rw [← finrank_baseChange_eq K (AlgebraicClosure K) A, e.toLinearEquiv.finrank_eq,
    Module.finrank_matrix, Module.finrank_self]
  simp [sq]

theorem exists_finrank_eq_sq [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] :
    ∃ n : ℕ, finrank K A = n ^ 2 :=
  let ⟨n, _, h, _⟩ := exists_algEquiv_matrix_algebraicClosure K A
  ⟨n, h⟩

theorem finrank_eq_degree_sq [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] :
    finrank K A = degree K A ^ 2 := by
  obtain ⟨n, h⟩ := exists_finrank_eq_sq K A
  rw [degree, h, Nat.sqrt_eq']

theorem degree_eq_iff [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] (n : ℕ) :
    degree K A = n ↔ finrank K A = n ^ 2 := by
  rw [finrank_eq_degree_sq K A]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ Nat.pow_left_injective two_ne_zero h⟩

theorem degree_baseChange (L : Type w) [Field L] [Algebra K L] :
    degree L (L ⊗[K] A) = degree K A := by
  rw [degree, degree, finrank_baseChange_eq]

theorem degree_matrix [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    degree K (Matrix ι ι A) = Fintype.card ι * degree K A := by
  rw [degree, Module.finrank_matrix, finrank_eq_degree_sq K A, ← sq, ← mul_pow, Nat.sqrt_eq']

theorem degree_tensorProduct [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
    (B : Type w) [Ring B] [Algebra K B] [Algebra.IsCentral K B] [IsSimpleRing B]
    [FiniteDimensional K B] :
    degree K (A ⊗[K] B) = degree K A * degree K B := by
  rw [degree, Module.finrank_tensorProduct, finrank_eq_degree_sq K A, finrank_eq_degree_sq K B,
    ← mul_pow, Nat.sqrt_eq']

end Degree

section CSA

variable {K : Type u} [Field K]

@[simp]
theorem degree_baseChangeCSA (L : Type w) [Field L] [Algebra K L] (A : CSA.{u, v} K) :
    degree L (baseChangeCSA L A) = degree K A :=
  degree_baseChange K A L

@[simp]
theorem degree_matrixCSA (A : CSA.{u, v} K) (n : ℕ) [NeZero n] :
    degree K (matrixCSA A n) = n * degree K A := by
  have h := degree_matrix K A (Fin n)
  rw [Fintype.card_fin] at h
  exact h

@[simp]
theorem degree_tensorCSA (A B : CSA.{u, v} K) :
    degree K (tensorCSA A B) = degree K A * degree K B :=
  degree_tensorProduct K A B

end CSA

section Index

variable (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A]

noncomputable def index : ℕ :=
  sInf {d : ℕ | ∃ (n : ℕ) (_ : NeZero n) (D : Type v) (_ : DivisionRing D) (_ : Algebra K D),
    Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) D) ∧ degree K D = d}

variable {K A}

variable (K A)

variable {K A}

variable (K A)

end Index

end GroundTheory.Brauer
end

