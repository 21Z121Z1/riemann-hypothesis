import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
section
noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial Filter Topology

namespace InvAlg

variable {K : UQ} (B : InvAlg K)

def UU (x w : B.A) : ℕ := Nat.card {L : B.X x // w ∈ (L : Submodule K.O B.A)}

def Lin : Set (Submodule K.O B.A) :=
  {M | IsLat K.O K.E M ∧ (∀ y ∈ M, B.g * y ∈ M) ∧ ∀ y ∈ M, B.σ y ∈ M}

def sgnLat (M : Submodule K.O B.A) : ℚ :=
  let m : Fin (Module.finrank K.E B.A) → B.A :=
    Classical.epsilon fun m => Submodule.span K.O (Set.range m) = M
  K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
    Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)).det

def GG (u : B.A) : ℚ :=
  ∑ᶠ M ∈ {M ∈ B.Lin | u ∈ M ∧ ∀ z ∈ M, Algebra.trace K.E B.A z ∈ (algebraMap K.O K.E).range}, B.sgnLat M

def rho (w : B.A) : ℕ :=
  Nat.card {k : B.T ⧸ (intUnits K.O B.A).subgroupOf B.T //
    IsIntegral K.O ((((Quotient.out k : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * w : B.A)}

def LieReg : Prop := B.σ B.g = B.g ∧ B.P.Separable

def Plus (x : B.A) : Prop := IsUnit x ∧ B.σ x = x

def LinLim (a : K.O) (x : B.A) (ℓ : ℝ) : Prop :=
  Tendsto (fun k : ℕ => (B.GG (x * algebraMap K.O B.A a ^ (2 * k)) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))
    atTop (𝓝 ℓ)

end InvAlg

def UQ.Small (K : UQ) (a : K.O) : Prop :=
  a ≠ 0 ∧ a ∈ IsLocalRing.maximalIdeal K.O ∧ K.c (algebraMap K.O K.E a) = algebraMap K.O K.E a

def CountIdentity : Prop :=
  ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ x w : B.A, B.Plus x → IsUnit w →
    B.GG (x * (w * B.σ w)) = (B.UU x w : ℚ)

def UnitaryLimit : Prop :=
  ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∀ x : B.A, B.Plus x →
    Tendsto (fun k : ℕ => (B.UU x (algebraMap K.O B.A a ^ k) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ))
      atTop (𝓝 (B.N x : ℝ))

def LinearDescent : Prop :=
  ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable →
    ∀ a : K.O, K.Small a → ∀ (ℓ : (B₁.prod B₂).A → ℝ) (ℓ₁ : B₁.A → ℝ) (ℓ₂ : B₂.A → ℝ),
    (∀ x, (B₁.prod B₂).Plus x → (B₁.prod B₂).LinLim a x (ℓ x)) →
    (∀ x, B₁.Plus x → B₁.LinLim a x (ℓ₁ x)) → (∀ x, B₂.Plus x → B₂.LinLim a x (ℓ₂ x)) →
    ∑ᶠ k : (B₁.prod B₂).Cl, (K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) : ℝ) * ℓ k.rep =
      (-(K.q : ℝ)) ^ (val K.O (resultant B₁.P B₂.P)) *
        ((∑ᶠ k : B₁.Cl, (K.eta (Algebra.norm K.E k.rep) : ℝ) * ℓ₁ k.rep) * ∑ᶠ k : B₂.Cl, ℓ₂ k.rep)

end GlobalTheory.UnitLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MatMapTmul
section
noncomputable section

open TensorProduct Polynomial IsLocalRing

namespace GlobalTheory.Pat

namespace Det

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

def val (y : E) : A := D.D A (1 ⊗ₜ y)

def chiAt (B : Type) [CommRing B] [Algebra A B] (x : B ⊗[A] E) : B[X] :=
  D.D B[X] (X ⊗ₜ 1 - Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B B[X]) (AlgHom.id A E) x)

def IsCH : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] (x : B ⊗[A] E), Polynomial.aeval x (D.chiAt B x) = 0

def Over {C E' : Type} [CommRing C] [Ring E'] [Algebra C E'] (D' : Det n C E') (φ : A →+* C)
    (π : E →+* E') : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra C B], (algebraMap C B).comp φ = algebraMap A B →
    ∀ (m : ℕ) (b : Fin m → B) (x : Fin m → E),
      D.D B (∑ i, b i ⊗ₜ[A] x i) = D'.D B (∑ i, b i ⊗ₜ[C] π (x i))

def HasRank (e : E) (r : ℕ) : Prop := D.D A[X] (1 ⊗ₜ (1 - e) + X ⊗ₜ e) = X ^ r

def grpMap {G : Type} [Group G] (A : Type) [CommRing A] [Algebra A E] (ρ : G →* E) (B : Type) [CommRing B]
    [Algebra A B] : MonoidAlgebra B G →ₐ[B] B ⊗[A] E :=
  MonoidAlgebra.lift B (B ⊗[A] E) G
    ((Algebra.TensorProduct.includeRight : E →ₐ[A] B ⊗[A] E).toMonoidHom.comp ρ)

def toG {G : Type} [Group G] (ρ : G →* E) : GDet n A G where
  D B _ _ := (D.D B).comp (grpMap A ρ B).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change D.D B' (grpMap A ρ B' _) = f (D.D B (grpMap A ρ B x))
    rw [← D.nat]
    congr 1
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp [grpMap, TensorProduct.smul_tmul']
  homog B _ _ b x := by
    change D.D B (grpMap A ρ B (b • x)) = b ^ n * D.D B (grpMap A ρ B x)
    rw [map_smul, D.homog]

def matMap (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    B ⊗[A] Matrix (Fin n) (Fin n) A →ₐ[B] Matrix (Fin n) (Fin n) B :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) ((Algebra.ofId A B).mapMatrix)
    (fun b _ => Algebra.commutes b _)

theorem matMap_tmul (n : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B)
    (M : Matrix (Fin n) (Fin n) A) : matMap n A B (b ⊗ₜ M) = b • M.map (algebraMap A B) := by
  have h : matMap n A B (b ⊗ₜ M) =
      algebraMap B (Matrix (Fin n) (Fin n) B) b * M.map (algebraMap A B) :=
    Algebra.TensorProduct.lift_tmul (Algebra.ofId B _) ((Algebra.ofId A B).mapMatrix)
      (fun b _ => Algebra.commutes b _) b M
  rw [h, ← Algebra.smul_def]

def mat (n : ℕ) (A : Type) [CommRing A] : Det n A (Matrix (Fin n) (Fin n) A) where
  D B _ _ := Matrix.detMonoidHom.comp (matMap n A B).toMonoidHom
  nat B B' _ _ _ _ f x := by
    change (matMap n A B' _).det = f (matMap n A B x).det
    rw [AlgHom.map_det]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul b M =>
      rw [Algebra.TensorProduct.map_tmul, matMap_tmul, matMap_tmul]
      ext i j
      simp
  homog B _ _ b x := by
    change (matMap n A B (b • x)).det = b ^ n * (matMap n A B x).det
    rw [map_smul, Matrix.det_smul, Fintype.card_fin]

end Det

def qOf {Γ B : Type} [Group Γ] [TopologicalSpace Γ] [CommRing B] [IsLocalRing B]
    (S : Set (MonoidAlgebra B Γ)) {C : Type} [CommRing C] (φ : B →+* C) : Γ →* QAlg S φ :=
  ((TwoSidedIdeal.span (MonoidAlgebra.mapRingHom Γ φ ''
    (closureIdeal (maximalIdeal B) S : Set (MonoidAlgebra B Γ)))).ringCon.mk').toMonoidHom.comp
    (MonoidAlgebra.of C Γ)

def lagIdem {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (M : E) (a : ι → R) (i : ι) : E :=
  Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j)) •
    Polynomial.aeval M (∏ j ∈ Finset.univ.erase i, (X - C (a j)))

def charExt {R Γ : Type} [CommRing R] [Group Γ] (ψ : Γ →* Rˣ) : MonoidAlgebra R Γ →ₐ[R] R :=
  MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp ψ)

def GDet.coef {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (α : G →₀ ℕ) : A :=
  MvPolynomial.coeff α (D.D (MvPolynomial G A)
    (∑ g ∈ α.support, MonoidAlgebra.single g (MvPolynomial.X g)))

end GlobalTheory.Pat
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemCentIffTwConj
section
open Matrix

noncomputable section

namespace GlobalTheory.Tw.Model

variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

omit [StarRing R] in
theorem Phi_apply' (i j : Fin n) : Phi n R i j = if j = i.rev then (-1) ^ (i : ℕ) else 0 := by
  simp only [Phi, Matrix.of_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff, Fin.val_rev]
  have := i.2
  have := j.2
  omega

omit [StarRing R] in
theorem Phi_mul_transpose : Phi n R * (Phi n R)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Phi_apply', ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_inj, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [← pow_add, ← two_mul, pow_mul]; simp
  · simp

omit [StarRing R] in
theorem transpose_mul_Phi : (Phi n R)ᵀ * Phi n R = 1 := mul_eq_one_comm.mp Phi_mul_transpose

theorem Phi_conjTranspose : (Phi n R)ᴴ = (Phi n R)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Phi_apply']
  split_ifs <;> simp

omit [StarRing R] in
theorem Phi_transpose : (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • Phi n R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Phi, Matrix.of_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + (j : ℕ) + 1 = n
  · rw [if_pos h, if_pos (by omega)]
    have : n - 1 = i + j := by omega
    rw [this, ← pow_add, show (i : ℕ) + j + i = 2 * i + j by ring, pow_add, pow_mul]; simp
  · rw [if_neg h, if_neg (by omega)]; simp

theorem theta_one : theta (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp [theta, Phi_mul_transpose]

theorem theta_mul (g h : Matrix (Fin n) (Fin n) R) : theta (g * h) = theta g * theta h := by
  simp only [theta, Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R), transpose_mul_Phi, Matrix.one_mul]

theorem theta_mul_theta_inv {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    theta g * theta g⁻¹ = 1 := by
  rw [← theta_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg), theta_one]

theorem theta_inv_eq {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    (theta g)⁻¹ = Phi n R * gᴴ * (Phi n R)ᵀ := by
  rw [Matrix.inv_eq_right_inv (theta_mul_theta_inv hg), theta,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg)]

theorem theta_theta {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : theta (theta g) = g := by
  rw [theta, theta_inv_eq hg]
  have h2 : ((Phi n R)ᵀ)ᴴ = Phi n R := by rw [← Phi_conjTranspose, conjTranspose_conjTranspose]
  simp only [Matrix.conjTranspose_mul, conjTranspose_conjTranspose, h2, Phi_conjTranspose]
  have hs : ((-1 : R) ^ (n - 1)) * ((-1 : R) ^ (n - 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have hP : Phi n R = ((-1 : R) ^ (n - 1)) • (Phi n R)ᵀ := by
    rw [Phi_transpose, smul_smul, hs, one_smul]
  have h3 : Phi n R * Phi n R = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    conv_lhs => rw [hP]
    nth_rewrite 2 [Phi_transpose]
    rw [smul_smul, hs, one_smul, Matrix.smul_mul, transpose_mul_Phi]
  have h4 : (Phi n R)ᵀ * (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [← Matrix.transpose_mul, h3]; simp
  calc Phi n R * (Phi n R * (g * (Phi n R)ᵀ)) * (Phi n R)ᵀ
      = (Phi n R * Phi n R) * g * ((Phi n R)ᵀ * (Phi n R)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h3, h4]; simp [smul_smul, hs]

theorem nrm_twConj {x δ : Matrix (Fin n) (Fin n) R} (hx : IsUnit x) :
    nrm (twConj x δ) = x⁻¹ * nrm δ * x := by
  have hx' : IsUnit x⁻¹ := by rwa [Matrix.isUnit_nonsing_inv_iff]
  simp only [nrm, twConj, theta_mul, theta_theta hx, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (theta x), theta_mul_theta_inv hx, Matrix.one_mul]

theorem adj_eq {δ g : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (hg : IsUnit g) :
    adj δ g = (δ * theta g * δ⁻¹)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, theta_inv_eq hg,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det δ).mp hδ), adj]
  simp only [Matrix.mul_assoc]

theorem mem_cent_iff_twConj {δ g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    g ∈ cent δ ↔ twConj g δ = δ := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).mp hg
  simp only [cent, Set.mem_setOf_eq, hg, true_and, twConj, Matrix.mul_assoc]
  constructor
  · intro h
    rw [← h, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hd]

theorem Phi_two : Phi 2 ℂ = !![0, 1; -1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Phi]

theorem inv_diag : (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = !![1/2, 0; 0, 1] := by
  apply Matrix.inv_eq_right_inv
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem nrm_diag : nrm (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![2, 1/2] := by
  rw [nrm, theta, inv_diag, Phi_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct, map_ofNat]

theorem reg_diag : Reg (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det]; simp [Matrix.det_fin_two]
  · rw [nrm_diag, Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all <;> norm_num at h

theorem not_reg_one : ¬ Reg (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rintro ⟨-, h⟩
  rw [nrm, theta_one, Matrix.mul_one, ← Matrix.diagonal_one, Matrix.charpoly_diagonal,
    Polynomial.separable_prod_X_sub_C_iff] at h
  exact absurd (@h 0 1 rfl) (by decide)

end GlobalTheory.Tw.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RoundDown
section
noncomputable section

open PowerSeries

namespace GlobalTheory.NB

namespace Fr

variable {l : ℕ} {O : Type} [CommRing O] (R : Fr l O)

def pt (k : ℕ) (τ : Fin R.e) : O⟦X⟧ := (R.φ ^ k) (X - C (R.ϖ τ))

def OrdGe (π : O⟦X⟧) (i : ℤ) (x : R.EE) : Prop :=
  ∃ (f g : O⟦X⟧) (a y : ℕ), (l : O⟦X⟧) ^ y ∈ Ideal.span {f, π} ∧ 0 ≤ (a : ℤ) + i ∧
    R.ι (f * π ^ a) * x = R.ι (π ^ ((a : ℤ) + i).toNat * g)

def ConstMod (π : O⟦X⟧) (i : ℤ) (x : R.EE) : Prop :=
  ∃ (y : ℕ) (c : O), R.OrdGe π i ((l : R.EE) ^ y * x - algebraMap O R.EE c)

def cst {r : ℕ} (a : Fin r → O) : Fin r → R.EE := fun k => algebraMap O R.EE (a k)

def γv {r : ℕ} : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) := R.γE.toLinearMap.compLeft (Fin r)

variable [IsDomain O]

def toD (_R : Fr l O) {r : ℕ} (a : Fin r → O) : Fin r → FractionRing O :=
  fun k => algebraMap O (FractionRing O) (a k)

def InLev {r : ℕ} (π : O⟦X⟧) (Fl : ℤ → Submodule (FractionRing O) (Fin r → FractionRing O))
    (g : Fin r → R.EE) : Prop :=
  ∃ (y N : ℕ) (u : Fin N → ℤ) (a : Fin N → Fin r → O) (x : Fin N → R.EE),
    (∀ t, R.toD (a t) ∈ Fl (u t) ∧ R.OrdGe π (-(u t)) (x t)) ∧
      (l ^ y : ℕ) • g = ∑ t, x t • R.cst (a t)

def InLevC {r : ℕ} (π : O⟦X⟧) (Fl : ℤ → Submodule (FractionRing O) (Fin r → FractionRing O))
    (g : Fin r → R.EE) : Prop :=
  ∃ (y : ℕ) (a : Fin r → O), R.InLev π Fl ((l ^ y : ℕ) • g - R.cst a)

end Fr

def roundUp {K V : Type} [Field K] [AddCommGroup V] [Module K V] (b : ℕ) (Cs : Submodule K V)
    (u : ℤ) : Submodule K V := if u ≤ 0 then ⊤ else if u ≤ b then Cs else ⊥

def roundDown {K V : Type} [Field K] [AddCommGroup V] [Module K V] (b : ℕ) (Fs : Submodule K V)
    (u : ℤ) : Submodule K V := if u ≤ -(b : ℤ) then ⊤ else if u ≤ 0 then Fs else ⊥

def winU (b S η : ℕ) : Set ℤ := Set.Icc (b : ℤ) (b + S) ∪ Set.Icc (-(η : ℤ)) η

def winD (b S η : ℕ) : Set ℤ := Set.Icc (-((b : ℤ) + S)) (-(b : ℤ)) ∪ Set.Icc (-(η : ℤ)) η

def win (up : Bool) (b S η : ℕ) : Set ℤ := if up then winU b S η else winD b S η

def IsCuts {n : ℕ} (cut : ZMod n → Prop) (len : ZMod n → ℕ) : Prop :=
  (∃ c, cut c) ∧ ∀ c, cut c → 1 ≤ len c ∧ len c ≤ n ∧ cut (c - (len c : ZMod n)) ∧
    ∀ k, 0 < k → k < len c → ¬ cut (c - (k : ZMod n))

namespace Fr

variable {l : ℕ} {O : Type} [CommRing O] (R : Fr l O)

def Star (j : ℕ) (f : O⟦X⟧) (g : ℕ) : Prop :=
  ∀ y, 1 ≤ y → InId ((l : O) ^ eF l y) f ((l : O⟦X⟧) ^ g * (R.φ ^ j) X ^ y)

def IsMon (j : ℕ) (f : O⟦X⟧) : Prop := ∃ (m : ℕ) (a : ℕ → ℕ), f = X ^ m * R.pp j a

end Fr

namespace Sys

variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r)

def IsFrame (i : ZMod n) (ρ k : ℕ) (H : Matrix (Fin r) (Fin r) O⟦X⟧) : Prop :=
  (∀ a b, X ∣ (H - (l : O⟦X⟧) ^ k • (1 : Matrix (Fin r) (Fin r) O⟦X⟧)) a b) ∧
    ∀ a b, X ^ ρ ∣ (S.G i * H.map R.γ - H) a b

def Coord (c' : ZMod n) (m : ℕ) (f : O⟦X⟧) (x g : Fin r → R.EE) : Prop :=
  ∃ (ρ k y : ℕ) (H : Matrix (Fin r) (Fin r) O⟦X⟧), S.IsFrame c' ρ k H ∧
    InMul f (R.N0 r) (((R.φ ^ m) X) ^ ρ • g) ∧
    InMul f (S.P c' m) ((l ^ y : ℕ) • ((l ^ k : ℕ) • x - ∑ j, g j • S.φit c' m (fun a => R.ι (H a j))))

variable [IsDomain O]

def FilArc (c' : ZMod n) (m s : ℕ) (τ : Fin R.e) (u : ℤ) :
    Submodule (FractionRing O) (Fin r → FractionRing O) :=
  (S.Fil (c' + ((m - s : ℕ) : ZMod n)) τ u).comap (S.φ0it c' (m - s)).mulVecLin

def InNN (c' : ZMod n) (m : ℕ) (g : Fin r → R.EE) : Prop :=
  ∀ s < m, ∀ τ, R.InLev (R.pt s τ) (S.FilArc c' m s τ) g

def Wid (i : ZMod n) (a b : ℕ) : Prop := ∀ τ, S.JumpsIn i τ (Set.Icc (-(a : ℤ)) b)

def Lat (c : ZMod n) (j : ℕ) : Submodule O (Fin r → FractionRing O) :=
  (D0 O r).map ((S.φ0it c j).mulVecLin.restrictScalars O)

end Sys

def ExtK {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r)
    (K : ZMod n → O⟦X⟧ → Prop) : Prop :=
  ∀ (g : ℕ) (pr : Fin g → DD R n r × DD R n r), (∀ k, pr k ∈ S.Zf) →
    ∃ (Y : Sys R n (r + g)) (F : Hom S Y) (F' : Hom Y (Sys.one R n g)), F.IsSES F' ∧
      (∀ k, F.IsClassOf F' (Pi.single k 1) (pr k)) ∧ (∀ i f, K i f → F'.Kills i f) ∧
      ∀ i, ∃ a : ℕ, F'.Kills i ((l : O⟦X⟧) ^ a)

namespace Hom

variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r r' : ℕ} {S : Sys R n r} {S' : Sys R n r'}
  (F : Hom S S')

def F0 (i : ZMod n) : Matrix (Fin r') (Fin r) O := (F.F i).map constantCoeff

def Good : Prop := F.Onto ∧ ∀ i, ∃ a : ℕ, F.Kills i ((l : O⟦X⟧) ^ a)

def LiftsAt (c' : ZMod n) (m : ℕ) (Λ : O⟦X⟧) (e : ℕ) (g : Fin r' → R.EE) : Prop :=
  ∃ (w₁ : Fin r → R.EE) (v : Fin r' → R.EE), w₁ ∈ S.I (c' + (m : ZMod n)) ∧ Sys.Poles w₁ ∧
    Λ • v ∈ S'.P c' m ∧ S'.Coord c' m (X * Λ) v ((l ^ e : ℕ) • g) ∧
    Sys.InMul X (R.N0 r') (F.fl (c' + (m : ZMod n)) w₁ - v)

end Hom

end GlobalTheory.NB
end
end

