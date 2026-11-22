import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalToGlobal.Divisibility.RowLat

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ExtensionSingularValues
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ExtensionSingularValues

abbrev V (r : ℕ) (μ : Fin r → ℕ) : Type := ↥(dualWeyl ℂ r r μ)

def nrm {r : ℕ} {μ : Fin r → ℕ} (F : V r μ) : ℝ :=
  √((fockS F.1 F.1).re / (fockS (hw ℂ (le_refl r) μ) (hw ℂ (le_refl r) μ)).re)

def subst {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (x : Matrix (Fin n₁) (Fin n₀) ℂ) :
    MvPolynomial (Fin n₀ × Fin n₀) ℂ →ₐ[ℂ] MvPolynomial (Fin n₁ × Fin n₁) ℂ :=
  aeval fun v => ∑ b : Fin n₁, C (x b v.1) * X (b, Fin.castLE h v.2)

def extZero (n₀ n₁ : ℕ) : (Fin n₀ → ℕ) →+ (Fin n₁ → ℕ) where
  toFun ν := rowNu (r := n₁) ν
  map_zero' := by funext a; simp [rowNu]
  map_add' ν μ := by
    funext a
    by_cases ha : a.val < n₀ <;> simp [rowNu, ha]

theorem extZero_single {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (s : Fin n₀) :
    extZero n₀ n₁ (Pi.single s 1) = Pi.single (Fin.castLE h s) 1 := by
  funext a
  change rowNu (r := n₁) (Pi.single s 1) a = _
  by_cases ha : a.val < n₀
  · simp only [rowNu, ha, dite_true, Pi.single_apply, Fin.ext_iff, Fin.val_castLE]
  · have : a ≠ Fin.castLE h s := by
      intro e
      apply ha
      rw [e]
      exact s.2
    simp [rowNu, ha, this]

theorem subst_mem {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (x : Matrix (Fin n₁) (Fin n₀) ℂ) (ν : Fin n₀ → ℕ)
    {F : MvPolynomial (Fin n₀ × Fin n₀) ℂ} (hF : F ∈ dualWeyl ℂ n₀ n₀ ν) :
    subst h x F ∈ dualWeyl ℂ n₁ n₁ (rowNu (r := n₁) ν) := by
  rw [dualWeylPoint] at hF ⊢
  constructor
  · refine isWH_algHom (subst h x) (fun v => extZero n₀ n₁ (colW n₀ n₀ v)) (colW n₁ n₁) ?_ ?_
    · intro v
      rw [subst, aeval_X, colW, extZero_single h]
      exact IsWeightedHomogeneous.sum _ _ _ fun b _ =>
        (isWeightedHomogeneous_X ℂ (colW n₁ n₁) (b, Fin.castLE h v.2)).C_mul _
    · intro m hm
      have h1 := hF.1 hm
      change _ = extZero n₀ n₁ ν
      rw [← h1, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, map_sum]
      simp only [map_nsmul]
  · intro l j hlj c
    by_cases hj : j.val < n₀
    · have hl : l.val < n₀ := lt_trans hlj hj
      have e : (colAdd ℂ l j c).comp (subst h x) =
          (subst h x).comp (colAdd ℂ (⟨l.val, hl⟩ : Fin n₀) ⟨j.val, hj⟩ c) := by
        apply MvPolynomial.algHom_ext
        intro v
        by_cases hv : v.2 = ⟨j.val, hj⟩
        · have h2 : Fin.castLE h v.2 = j := by rw [hv]; rfl
          have h3 : Fin.castLE h (⟨l.val, hl⟩ : Fin n₀) = l := rfl
          simp only [AlgHom.comp_apply, subst, colAdd, aeval_X, map_sum, map_mul, map_add, algHom_C,
            if_pos hv, h2, h3, if_true, algebraMap_eq, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun b _ => rfl) (Finset.sum_congr rfl fun b _ => ?_)
          ring
        · have h2 : Fin.castLE h v.2 ≠ j := by
            intro e
            have e' : v.2.val = j.val := congrArg (fun z : Fin n₁ => z.val) e
            exact hv (Fin.ext e')
          simp only [AlgHom.comp_apply, subst, colAdd, aeval_X, map_sum, map_mul, algHom_C,
            if_neg hv, if_neg h2, algebraMap_eq]
      have := DFunLike.congr_fun e F
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hF.2 _ _ (by exact hlj) c] at this
      exact this
    · have e : (colAdd ℂ l j c).comp (subst h x) = subst h x := by
        apply MvPolynomial.algHom_ext
        intro v
        have h2 : Fin.castLE h v.2 ≠ j := by
          intro e
          apply hj
          rw [← e]
          exact v.2.2
        simp only [AlgHom.comp_apply, subst, colAdd, aeval_X, map_sum, map_mul, algHom_C,
          if_neg h2, algebraMap_eq]
      exact DFunLike.congr_fun e F

def rho {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (ν : Fin n₀ → ℕ) (x : Matrix (Fin n₁) (Fin n₀) ℂ) :
    V n₀ ν →ₗ[ℂ] V n₁ (rowNu (r := n₁) ν) :=
  (subst h x).toLinearMap.restrict fun _ hF => subst_mem h x ν hF

def IsOpNorm {r r' : ℕ} {μ : Fin r → ℕ} {μ' : Fin r' → ℕ} (T : V r μ →ₗ[ℂ] V r' μ') (c : ℝ) : Prop :=
  IsLeast {a : ℝ | 0 ≤ a ∧ ∀ F : V r μ, nrm (T F) ≤ a * nrm F} c

def sv {n₀ n₁ : ℕ} (x : Matrix (Fin n₁) (Fin n₀) ℂ) (i : Fin n₀) : ℝ :=
  (Matrix.toEuclideanLin x).singularValues i.val

def OpNormStatement : Prop :=
  ∀ (n₀ n₁ : ℕ) (h : n₀ ≤ n₁) (ν : Fin n₀ → ℕ), Antitone ν → ∀ x : Matrix (Fin n₁) (Fin n₀) ℂ,
    IsOpNorm (rho h ν x) (∏ i, sv x i ^ ν i) ∧
    IsOpNorm (rho h ν (x.map (starRingEnd ℂ))) (∏ i, sv x i ^ ν i)

end GlobalTheory.IndefiniteRowSideFullHecke.ExtensionSingularValues
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.RationalTransitionKernel
section
open NumberField
open scoped Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RationalTransitionKernel

open Formalism.L2.DIV Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J]

def cx (v : InfinitePlace K) {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  (A.map v.embedding).mulVecLin

open Classical in

def mult (P : Subgroup G) (ψ : P →* Kˣ) (χ : G → K) : K :=
  (Nat.card P : K)⁻¹ * ∑ h : P, ((ψ h⁻¹ : Kˣ) : K) * χ (h : G)

def Generic (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) : Prop := ∀ χ ∈ X, mult P ψ χ ≠ 0

section Data

variable (F : DefFam K G Pl0 T J) {EE : Type} [AddCommGroup EE] [Module ℂ EE]
  (ρ : Representation ℂ G EE) (Θ : ∀ t : T, (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] EE)

def Equivariant : Prop :=
  ∀ (t : T) (g : G), ∀ x ∈ LinearMap.range (cx F.v0 ((F.R t).vE (F.lvl ⊥ 1))),
    Θ t (cx F.v0 ((F.R t).S.actMat (F.R t).r g) x) = ρ g (Θ t x)

variable (Zs : DefSub F.amb) (P : Subgroup G) (ψ : P →* Kˣ)

def onGood (t : T) : (Fin ((F.R t).nV (F.lvl P ψ)) → ℂ) →ₗ[ℂ] EE :=
  Θ t ∘ₗ cx F.v0 ((F.R t).vE (F.lvl P ψ))

def KernelIsTrivial (t : T) : Prop :=
  LinearMap.ker (onGood F Θ P ψ t) = LinearMap.ker (cx F.v0 ((F.R t).Pq (F.lvl P ψ) (Zs.Z t)))

def iota (t : T) : (Fin ((F.R t).dZ (F.lvl P ψ) (Zs.Z t)) → ℂ) →ₗ[ℂ] EE :=
  onGood F Θ P ψ t ∘ₗ cx F.v0 ((F.R t).zE (F.lvl P ψ) (Zs.Z t))

def RatTransition (t : T) : Prop :=
  ∃ Y : Matrix (Fin ((F.R F.μ0).dZ (F.lvl P ψ) (Zs.Z F.μ0))) (Fin ((F.R t).dZ (F.lvl P ψ) (Zs.Z t))) K,
    Function.Bijective Y.mulVec ∧ iota F Θ Zs P ψ t = iota F Θ Zs P ψ F.μ0 ∘ₗ cx F.v0 Y

def OneFormAt : Prop := ∀ t : T, KernelIsTrivial F Θ Zs P ψ t ∧ RatTransition F Θ Zs P ψ t

def OneFormPrincipal : Prop := OneFormAt F Θ Zs ⊥ 1

end Data

def OneFormPassage : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
    (Pl0 T J : Type) [Fintype J] (F : DefFam K G Pl0 T J) (s : ℕ), F.Ok s →
  ∀ (Zs : DefSub F.amb), (∀ (t : T) (g : G), Zs.Z t ≤ (Zs.Z t).comap ((F.R t).r g)) →
  ∀ (EE : Type) [AddCommGroup EE] [Module ℂ EE] (ρ : Representation ℂ G EE)
    (Θ : ∀ t : T, (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] EE), Equivariant F ρ Θ →
  ∀ (P : Subgroup G) (ψ : P →* Kˣ), Generic F.X P ψ →
    OneFormAt F Θ Zs P ψ → OneFormPrincipal F Θ Zs

example (χ : G → K) : mult (⊥ : Subgroup G) 1 χ = χ 1 := by
  classical
  unfold mult
  rw [Finset.sum_eq_single (1 : (⊥ : Subgroup G))]
  · rw [Subgroup.card_bot]; simp only [Nat.cast_one, inv_one, MonoidHom.one_apply, Units.val_one, one_mul,
      OneMemClass.coe_one]
  · intro b _ hb; exact absurd (Subsingleton.elim b 1) hb
  · intro h; exact absurd (@Finset.mem_univ _ (_) _) h

example (F : DefFam K G Pl0 T J) {EE : Type} [AddCommGroup EE] [Module ℂ EE]
    (Θ : ∀ t : T, (Fin (F.R t).S.dim → ℂ) →ₗ[ℂ] EE) (Zs : DefSub F.amb) (P : Subgroup G) (ψ : P →* Kˣ) :
    RatTransition F Θ Zs P ψ F.μ0 := by
  refine ⟨1, ?_, ?_⟩
  · have : (1 : Matrix (Fin ((F.R F.μ0).dZ (F.lvl P ψ) (Zs.Z F.μ0))) _ K).mulVec = id :=
      funext fun x => Matrix.one_mulVec x
    rw [this]; exact Function.bijective_id
  · ext1
    simp [cx, Matrix.map_one]

end GlobalTheory.IndefiniteRowSideFullHecke.RationalTransitionKernel
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorNormBound
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds

open Formalism.BasicNotions Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {n n' : ℕ}

def nsqOne (lam : DomWeight n) (f : nablaSq ℂ n lam) : ℝ :=
  (normFock lam (f : MvPolynomial (Fin n × Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ)).re

def nsqAll (lam : ι → DomWeight n) (F : VV ℂ lam) : ℝ :=
  (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) F F).re

def NormLeOne {lam : DomWeight n} {lam' : DomWeight n'} (A : nablaSq ℂ n lam →ₗ[ℂ] nablaSq ℂ n' lam') (c : ℝ) :
    Prop :=
  0 ≤ c ∧ ∀ f, nsqOne lam' (A f) ≤ c ^ 2 * nsqOne lam f

def NormLeAll {lam : ι → DomWeight n} {lam' : ι → DomWeight n'} (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ F, nsqAll lam' (T F) ≤ c ^ 2 * nsqAll lam F

def tenV (lam : ι → DomWeight n) (f : ∀ τ, nablaSq ℂ n (lam τ)) : VV ℂ lam :=
  ⟨ten fun τ => (f τ : MvPolynomial (Fin n × Fin n) ℂ),
    Submodule.subset_span ⟨fun τ => (f τ : MvPolynomial (Fin n × Fin n) ℂ), fun τ => (f τ).2, rfl⟩⟩

def IsTensorMap {lam : ι → DomWeight n} {lam' : ι → DomWeight n'}
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') : Prop :=
  ∀ f : ∀ τ, nablaSq ℂ n (lam τ), T (tenV lam f) = tenV lam' fun τ => A τ (f τ)

def TensorNormLe : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)),
    (∃ T : VV ℂ lam →ₗ[ℂ] VV ℂ lam', IsTensorMap A T) ∧
    ∀ (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam'), IsTensorMap A T →
      ∀ c : ι → ℝ, (∀ τ, NormLeOne (A τ) (c τ)) → NormLeAll T (∏ τ, c τ)

def TensorNormEq : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam'),
    IsTensorMap A T → ∀ c : ι → ℝ, (∀ τ, IsLeast {d : ℝ | NormLeOne (A τ) d} (c τ)) →
      IsLeast {d : ℝ | NormLeAll T d} (∏ τ, c τ)

theorem IsTensorMap.unique {lam : ι → DomWeight n} {lam' : ι → DomWeight n'}
    {A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)} {T T' : VV ℂ lam →ₗ[ℂ] VV ℂ lam'}
    (h : IsTensorMap A T) (h' : IsTensorMap A T') : T = T' := by
  apply LinearMap.ext
  rintro ⟨F, hF⟩
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    exact (h fun τ => ⟨f τ, hf τ⟩).trans (h' fun τ => ⟨f τ, hf τ⟩).symm
  | zero => exact (map_zero T).trans (map_zero T').symm
  | add x y hx hy ihx ihy =>
    have e : T (⟨x, hx⟩ + ⟨y, hy⟩) = T' (⟨x, hx⟩ + ⟨y, hy⟩) := by rw [map_add, map_add, ihx, ihy]
    exact e
  | smul a x hx ih =>
    have e : T (a • ⟨x, hx⟩) = T' (a • ⟨x, hx⟩) := by rw [map_smul, map_smul, ih]
    exact e

example (lam : ι → DomWeight n) : IsTensorMap (lam := lam) (lam' := lam) (fun _ => LinearMap.id) LinearMap.id :=
  fun _ => rfl

example (lam : DomWeight n) : NormLeOne (lam := lam) (lam' := lam) LinearMap.id 1 :=
  ⟨zero_le_one, fun f => by simp⟩

end GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds
end
end

