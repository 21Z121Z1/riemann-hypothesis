import Mathlib
import Formalism.DegreeFormula.FlagDegFormula
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
section
noncomputable section
open MvPolynomial Finset

namespace GlobalTheory.FlagHook

def altCoeff {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (n : ι → Fin N → ℕ)
    (P : MvPolynomial (ι × Fin N) ℝ) : ℝ :=
  (-1) ^ Formalism.DegreeFormula.dimFl ι N * ∑ σ : ι → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) *
    P.coeff (Finsupp.equivFunOnFinite.symm (fun x : ι × Fin N => n x.1 (σ x.1 x.2)))

def rho (N : ℕ) : Fin N → ℕ := fun c => N - 1 - (c : ℕ)

def hookRho (N k r : ℕ) : Fin N → ℕ :=
  fun c => N - 1 - (c : ℕ) + (if (c : ℕ) = 0 then k - r else if (c : ℕ) ≤ r then 1 else 0)

def detE {N : ℕ} (n : Fin N → ℕ) : MvPolynomial (Fin N) ℝ :=
  Matrix.det (Matrix.of fun i c : Fin N => C (((n c).factorial : ℝ)⁻¹) * X i ^ n c)

def hookR (N k : ℕ) : MvPolynomial (Fin N) ℝ :=
  ∑ r ∈ range k, C ((-1 : ℝ) ^ r) * detE (hookRho N k r)

def hookFl {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ : ι) (k : ℕ)
    (P : MvPolynomial (ι × Fin N) ℝ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ r ∈ range k, (-1 : ℝ) ^ r *
    altCoeff (fun τ' => if τ' = τ then hookRho N k r else rho N) P

def pw {ι : Type} (N : ℕ) (τ : ι) (k : ℕ) : MvPolynomial (ι × Fin N) ℝ := ∑ i : Fin N, X (τ, i) ^ k

def kap {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (u : ι → Fin N → ℝ) (k : ℕ)
    (γ Q : MvPolynomial (ι × Fin N) ℝ) : ℝ :=
  k * Formalism.DegreeFormula.degFl ι N (γ * Q) / (((Formalism.DegreeFormula.dimFl ι N : ℝ) + 1) * Formalism.DegreeFormula.flagDeg ι N u)

def IsDecomp {ι : Type} [Fintype ι] {N : ℕ} (u : ι → Fin N → ℝ)
    (Q : ι → ℕ → MvPolynomial (ι × Fin N) ℝ) : Prop :=
  (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (Formalism.DegreeFormula.dimFl ι N + 1 - k)) ∧
    Formalism.DegreeFormula.linRoot u ^ (Formalism.DegreeFormula.dimFl ι N + 1) = ∑ τ, ∑ k ∈ Icc 1 N, pw N τ k * Q τ k

theorem altCoeff_rho {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (P : MvPolynomial (ι × Fin N) ℝ) :
    altCoeff (fun _ => rho N) P = Formalism.DegreeFormula.degFl ι N P := rfl

end GlobalTheory.FlagHook
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
section
open MvPolynomial Formalism.DegreeFormula

noncomputable section

namespace GlobalTheory.FlagPoly

abbrev Pol (ι : Type) (N : ℕ) : Type := MvPolynomial (ι × Fin N) ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

def pSum (τ : ι) (k : ℕ) : Pol ι N := ∑ i : Fin N, X (τ, i) ^ k

def pLow (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), X (τ, i) ^ k

def pHigh (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), X (τ, i) ^ k

def shF (j : ℕ) (τ : ι) (F : Pol ι N) : ℝ :=
  degFl ι N (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), pderiv (τ, i) F)

def totF (τ : ι) (F : Pol ι N) : ℝ := degFl ι N (∑ i : Fin N, pderiv (τ, i) F)

def swapAt (τ : ι) (a b : Fin N) : ι × Fin N → ι × Fin N :=
  fun x => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x

def AntiL (j : ℕ) (P : Pol ι N) : Prop :=
  ∀ (τ : ι) (a b : Fin N), (b : ℕ) = a + 1 → (b : ℕ) ≠ j → rename (swapAt τ a b) P = -P

def delPol (ι : Type) [Fintype ι] (N : ℕ) : Pol ι N :=
  ∏ τ : ι, ∏ a : Fin N, ∏ b : Fin N, if a < b then X (τ, a) - X (τ, b) else 1

def invForm (j : ℕ) (al be : ι → ℝ) : Pol ι N :=
  ∑ τ : ι, (C (al τ) * pLow j τ 1 + C (be τ) * pHigh j τ 1)

def ev (lam : ι → Fin N → ℝ) (P : Pol ι N) : ℝ := eval (fun x => lam x.1 x.2) P

def CoefLe (P : Pol ι N) (c : ℝ) : Prop := ∀ m, |P.coeff m| ≤ c

def Dom (lam : ι → Fin N → ℝ) : Prop := ∀ τ (a b : Fin N), a ≤ b → lam τ b ≤ lam τ a

def RegDom (lam : ι → Fin N → ℝ) : Prop := ∀ τ (a b : Fin N), a < b → lam τ b < lam τ a

def GapZero (j : ℕ) (τ : ι) (lam : ι → Fin N → ℝ) : Prop :=
  ∀ a b : Fin N, (b : ℕ) = a + 1 → (b : ℕ) = j → lam τ a = lam τ b

def wallSet (j : ℕ) (τ₀ : ι) (c₀ : ℝ) : Set (ι → Fin N → ℝ) :=
  {lam | (∀ τ i, |lam τ i| ≤ 1 / 2) ∧ GapZero j τ₀ lam ∧
    ∀ τ (a b : Fin N), (b : ℕ) = a + 1 → ¬ (τ = τ₀ ∧ (b : ℕ) = j) → c₀ ≤ lam τ a - lam τ b}

def lamA (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := ∑ τ : ι, (pHigh j τ 1 - pLow j τ 1)

def fibPt (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N :=
  ∏ x : ι × Fin N, (-X x) ^ (if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ))

def dimGr (ι : Type) [Fintype ι] (N j : ℕ) : ℕ := Fintype.card ι * (j * (N - j))

def curveCl (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := lamA ι N j ^ (dimGr ι N j - 1) * fibPt ι N j

end GlobalTheory.FlagPoly
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.DiagUnitsEqLocalIdele
section
noncomputable section
open NumberField IsDedekindDomain
namespace GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]

theorem localIdele_snd_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 v = x := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) v = x
  exact Pi.mulSingle_eq_same _ _

theorem localIdele_snd_ne (v w : HeightOneSpectrum (𝓞 L)) (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).2 w = 1 := by
  classical
  change Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) w = 1
  exact Pi.mulSingle_eq_of_ne h _

theorem localIdele_fst (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ((localIdele L v x : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := rfl

theorem infIdele_fst_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 w = x := by
  classical
  change Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) w = x
  exact Pi.mulSingle_eq_same _ _

theorem infIdele_fst_ne (w u : InfinitePlace L) (h : u ≠ w) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).1 u = 1 := by
  classical
  change Pi.mulSingle (M := fun u : InfinitePlace L => u.Completion) w (x : w.Completion) u = 1
  exact Pi.mulSingle_eq_of_ne h _

theorem infIdele_snd (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    ((infIdele L w x : Ideles L) : AdeleRing (𝓞 L) L).2 = 1 := rfl

theorem localIdele_injective (v : HeightOneSpectrum (𝓞 L)) : Function.Injective (localIdele L v) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).2 v) hxy
  simpa only [localIdele_snd_self] using h

theorem infIdele_injective (w : InfinitePlace L) : Function.Injective (infIdele L w) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).1 w) hxy
  simpa only [infIdele_fst_self] using h

theorem diagUnits_injective : Function.Injective (diagUnits L) := by
  intro a b hab
  apply Units.ext
  apply NumberField.AdeleRing.algebraMap_injective (R := 𝓞 L) (K := L)
  exact congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L)) hab

theorem diagUnits_snd (v : HeightOneSpectrum (𝓞 L)) (a : Lˣ) :
    ((diagUnits L a : Ideles L) : AdeleRing (𝓞 L) L).2 v = algebraMap L (v.adicCompletion L) a := rfl

theorem infIdele_continuous (w : InfinitePlace L) : Continuous (infIdele L w) := by
  classical
  exact Continuous.units_map _ ((continuous_mulSingle w).prodMk continuous_const)

example : IsTopologicalGroup (Ideles L) := inferInstance
example : CommGroup (Ideles L) := inferInstance

theorem diagUnits_fst (w : InfinitePlace L) (a : Lˣ) :
    ((diagUnits L a : Ideles L) : AdeleRing (𝓞 L) L).1 w = algebraMap L w.Completion a := rfl

theorem finSingle_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (finSingle L v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 L))) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let g : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal {v}ᶜ) :=
    fun x => ⟨Pi.mulSingle v x, Filter.eventually_principal.2 fun w hw => by
      rw [Pi.mulSingle_eq_of_ne (Set.mem_compl_singleton_iff.mp hw)]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.2 (continuous_mulSingle v)
  have hfg : (finSingle L v : v.adicCompletion L → FiniteAdeleRing (𝓞 L) L) =
      RestrictedProduct.inclusion _ _ hS ∘ g := by
    funext x
    rfl
  rw [hfg]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

theorem localIdele_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  exact Continuous.units_map _ (continuous_const.prodMk (finSingle_continuous L v))

theorem diagUnits_eq_localIdele (v : HeightOneSpectrum (𝓞 L)) (a : Lˣ) (x : (v.adicCompletion L)ˣ)
    (h : diagUnits L a = localIdele L v x) : a = 1 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace L))
  have h1 := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).1 w) h
  simp only [diagUnits_fst, localIdele_fst] at h1
  apply Units.ext
  apply (algebraMap L w.Completion).injective
  rw [h1, Units.val_one, map_one]
  rfl

theorem localIdele_eq_infIdele (v : HeightOneSpectrum (𝓞 L)) (w : InfinitePlace L) (x : (v.adicCompletion L)ˣ)
    (y : (w.Completion)ˣ) (h : localIdele L v x = infIdele L w y) : x = 1 ∧ y = 1 := by
  have h1 := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).2 v) h
  have h2 := congrArg (fun z : Ideles L => (z : AdeleRing (𝓞 L) L).1 w) h
  simp only [localIdele_snd_self, infIdele_snd, localIdele_fst, infIdele_fst_self] at h1 h2
  exact ⟨Units.ext (h1.trans rfl), Units.ext (h2.symm.trans rfl)⟩

theorem diagUnits_neg_one_ne : diagUnits L (-1) ≠ 1 := by
  intro h
  have h1 : (-1 : Lˣ) = 1 := diagUnits_injective L (h.trans (map_one _).symm)
  have h2 : ((-1 : Lˣ) : L) = ((1 : Lˣ) : L) := congrArg Units.val h1
  simp only [Units.val_neg, Units.val_one] at h2
  have h3 : (2 : L) = 0 := by linear_combination -h2
  exact two_ne_zero h3

end GlobalTheory.Mem.Chr.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.EtaSixProductDifferentiable
section
noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace GlobalTheory.HeckeFamilyMatrices

def ev (k : ℤ) (F : ℍ → ℂ) (τ : ℍ) : SL(2, ℤ) → ℂ := fun x => (F ∣[k] x) τ

def lead (M : ℕ) (k : ℤ) (F : ℍ → ℂ) : SL(2, ℤ) → Fin M → ℂ := fun x a =>
  (qExpansion (M : ℝ) (F ∣[k] x)).coeff (a : ℕ)

def Vodd (Γ : Subgroup SL(2, ℤ)) : Submodule ℂ (SL(2, ℤ) → ℂ) where
  carrier := {v | (∀ γ ∈ Γ, ∀ x, v (γ * x) = v x) ∧ ∀ x, v (-x) = -v x}
  add_mem' := by
    rintro v v' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨fun γ hγ x => by simp [h1 γ hγ x, h1' γ hγ x], fun x => by simp [h2 x, h2' x]; abel⟩
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => by simp⟩
  smul_mem' := by
    rintro c v ⟨h1, h2⟩
    exact ⟨fun γ hγ x => by simp [h1 γ hγ x], fun x => by simp [h2 x]⟩

def VoddT (Γ : Subgroup SL(2, ℤ)) : Submodule ℂ (SL(2, ℤ) → ℂ) where
  carrier := {v | v ∈ Vodd Γ ∧ ∀ x, v (x * ModularGroup.T) = v x}
  add_mem' := by
    rintro v v' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨Submodule.add_mem _ h1 h1', fun x => by simp [h2 x, h2' x]⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun _ => rfl⟩
  smul_mem' := by
    rintro c v ⟨h1, h2⟩
    exact ⟨Submodule.smul_mem _ c h1, fun x => by simp [h2 x]⟩

def n0 (Γ : Subgroup SL(2, ℤ)) : ℕ := Module.finrank ℂ (VoddT Γ)

structure Frame (Γ : Subgroup SL(2, ℤ)) (M r : ℕ) where
  wt : Fin r → ℕ
  F : ∀ i, ModularForm Γ (wt i : ℤ)
  odd : ∀ i, Odd (wt i)
  pt : ∀ τ : ℍ, LinearIndependent ℂ (fun i => ev (wt i : ℤ) (F i) τ)
  cusp : LinearIndependent ℂ (fun i => lead M (wt i : ℤ) (F i))

section EtaSix

open Complex Function ModularForm
open scoped Manifold Real

def eta6 (z : ℍ) : ℂ := ModularForm.eta z ^ 6

lemma eta_six_ne_zero (z : ℍ) : eta6 z ≠ 0 := pow_ne_zero _ (eta_ne_zero z.2)

lemma eta_six_product_formula (z : ℍ) : eta6 z = Periodic.qParam 4 z * (∏' n, (1 - eta_q n z)) ^ 6 := by
  simp only [eta6, ModularForm.eta, mul_pow]
  congr
  simp [Periodic.qParam, ← Complex.exp_nsmul, nsmul_eq_mul]
  congr 1
  ring

lemma eta6_slash_three_T_eq_I_smul : eta6 ∣[(3 : ℤ)] ModularGroup.T = (Complex.I : ℂ) • eta6 := by
  ext z
  rw [SL_slash_apply, ModularGroup.denom_apply, modular_T_smul]
  have h1 : ∀ n, eta_q n (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = eta_q n z := by
    intro n
    simp only [eta_q, Periodic.qParam, coe_vadd]
    rw [← exp_periodic (2 * π * Complex.I * z / ((1:ℝ):ℂ))]
    congr 2
    push_cast; ring
  have h2 : Periodic.qParam 4 (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = Complex.I * Periodic.qParam 4 z := by
    simp only [Periodic.qParam, coe_vadd]
    rw [← exp_pi_div_two_mul_I, ← Complex.exp_add, exp_pi_div_two_mul_I]
    congr 1
    push_cast; ring
  simp only [eta_six_product_formula, h1, h2, Pi.smul_apply, smul_eq_mul]
  simp [ModularGroup.T, mul_assoc]

lemma sqrt_pow_six (z : ℂ) : Complex.sqrt z ^ 6 = z ^ 3 := by
  have : Complex.sqrt z ^ 2 = z := by
    simp [Complex.sqrt]
  rw [show 6 = 2 * 3 by rfl, pow_mul, this]

lemma eta_six_slash_S : eta6 ∣[(3 : ℤ)] ModularGroup.S = (Complex.I : ℂ) • eta6 := by
  ext z
  rw [SL_slash_apply, UpperHalfPlane.modular_S_smul, ModularGroup.denom_S]
  have he : η (-(↑z)⁻¹) = (Complex.sqrt Complex.I)⁻¹ * (Complex.sqrt z * η z) := by
    simpa [neg_div] using eta_comp_eq_csqrt_I_inv z.2
  have hz := z.ne_zero
  simp only [eta6, inv_neg, he, mul_pow, inv_pow, sqrt_pow_six, Pi.smul_apply, smul_eq_mul]
  have : (Complex.I : ℂ) ^ 3 = -Complex.I := by rw [pow_succ, I_sq]; ring
  rw [this, zpow_neg, inv_neg, inv_I]
  field_simp

lemma eta_six_slash_root_of_unity (γ : SL(2, ℤ)) : ∃ c : ℂ, c ^ 4 = 1 ∧ eta6 ∣[(3 : ℤ)] γ = c • eta6 := by
  have hγ : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨Complex.I, I_pow_four, eta_six_slash_S⟩
    · exact ⟨Complex.I, I_pow_four, eta6_slash_three_T_eq_I_smul⟩
  | one => exact ⟨1, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, by rw [mul_pow, ha, hb, one_mul], ?_⟩
    rw [SlashAction.slash_mul, hx, SL_smul_slash, hy, smul_smul]
  | inv x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    refine ⟨a⁻¹, by rw [inv_pow, ha, inv_one], ?_⟩
    have : eta6 = a • eta6 ∣[(3 : ℤ)] x⁻¹ := by
      rw [← SL_smul_slash, ← hx, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    conv_rhs => rw [this]
    rw [smul_smul, inv_mul_cancel₀ ha0, one_smul]

def eta6MultiplierFunction (γ : SL(2, ℤ)) : ℂ := (eta6 ∣[(3 : ℤ)] γ) UpperHalfPlane.I / eta6 UpperHalfPlane.I

lemma eta6Mult0_eq {γ : SL(2, ℤ)} {c : ℂ} (h : eta6 ∣[(3 : ℤ)] γ = c • eta6) : eta6MultiplierFunction γ = c := by
  simp [eta6MultiplierFunction, h, eta_six_ne_zero]

lemma eta_six_slash_multiplier (γ : SL(2, ℤ)) : eta6 ∣[(3 : ℤ)] γ = eta6MultiplierFunction γ • eta6 := by
  obtain ⟨c, -, h⟩ := eta_six_slash_root_of_unity γ
  rw [eta6Mult0_eq h, h]

def eta6Mult : SL(2, ℤ) →* ℂ where
  toFun := eta6MultiplierFunction
  map_one' := eta6Mult0_eq (by simp)
  map_mul' x y := eta6Mult0_eq (by
    rw [SlashAction.slash_mul, eta_six_slash_multiplier, SL_smul_slash, eta_six_slash_multiplier, smul_smul])

lemma eta6Mult_T_eq_I : eta6Mult ModularGroup.T = Complex.I := eta6Mult0_eq eta6_slash_three_T_eq_I_smul

lemma eta6Mult_S : eta6Mult ModularGroup.S = Complex.I := eta6Mult0_eq eta_six_slash_S

lemma eta6Mult_neg_one : eta6Mult (-1) = -1 := by
  have : (-1 : SL(2, ℤ)) = ModularGroup.S * ModularGroup.S := by decide
  rw [this, map_mul, eta6Mult_S, I_mul_I]

def eta6Group : Subgroup SL(2, ℤ) := eta6Mult.toHomUnits.ker

lemma mem_eta6Group (γ : SL(2, ℤ)) : γ ∈ eta6Group ↔ eta6Mult γ = 1 := by
  simp [eta6Group, MonoidHom.mem_ker, Units.ext_iff]

lemma T_pow_four_mem_eta6Group : ModularGroup.T ^ 4 ∈ eta6Group := by
  rw [mem_eta6Group, map_pow, eta6Mult_T_eq_I, I_pow_four]

lemma neg_one_not_mem_eta6Group : (-1 : SL(2, ℤ)) ∉ eta6Group := by
  rw [mem_eta6Group, eta6Mult_neg_one]; norm_num

lemma eta_six_holomorphic : MDiff eta6 := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine .congr (fun z hz ↦ (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow
    6 |>.differentiableWithinAt) fun z hz ↦ ?_
  simp [eta6, ofComplex_apply_of_im_pos hz]

lemma eta_six_zero_at_infinity : IsZeroAtImInfty eta6 := by
  have h := discriminant_isZeroAtImInfty
  unfold IsZeroAtImInfty Filter.ZeroAtFilter at *
  rw [tendsto_zero_iff_norm_tendsto_zero] at *
  have h2 := h.rpow_const (p := (1/4 : ℝ)) (Or.inr (by norm_num))
  rw [Real.zero_rpow (by norm_num)] at h2
  refine h2.congr fun z => ?_
  have : ModularForm.discriminant z = eta6 z ^ 4 := by
    simp [ModularForm.discriminant, eta6, ← pow_mul]
  rw [this, norm_pow, show (1/4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast (norm_nonneg _) (by norm_num)]

def eta6Form : ModularForm eta6Group (3 : ℤ) where
  toFun := eta6
  slash_action_eq' A hA := by
    obtain ⟨A, hA, rfl⟩ := hA
    have := eta_six_slash_multiplier A
    rw [show eta6MultiplierFunction A = 1 from (mem_eta6Group A).1 hA, one_smul] at this
    exact this
  holo' := eta_six_holomorphic
  bdd_at_cusps' hc := by
    have hc' := hc.mono
      (show (eta6Group : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ from Subgroup.map_le_range _ _)
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
    intro γ _
    rw [eta_six_slash_multiplier]
    exact (eta_six_zero_at_infinity.isBoundedAtImInfty).smul _

lemma coe_eta6Form : (eta6Form : ℍ → ℂ) = eta6 := rfl

lemma eta_six_cusp_function : Set.EqOn (cuspFunction 4 eta6)
    (fun q ↦ q * (∏' i, (1 - (q ^ 4) ^ (i + 1))) ^ 6) (Metric.ball 0 1) := by
  intro q hq
  by_cases hq0 : q = 0
  · simpa [hq0] using eta_six_zero_at_infinity.cuspFunction_apply_zero (by norm_num)
  · have him := Periodic.im_invQParam_pos_of_norm_lt_one (h := 4) (by norm_num)
      (by simpa [dist_zero_right] using hq) hq0
    have h4 : Periodic.qParam 1 (Periodic.invQParam 4 q) = q ^ 4 := by
      conv_rhs => rw [← Periodic.qParam_right_inv (h := 4) (by norm_num) hq0]
      simp only [Periodic.qParam, ← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero 4 _ hq0,
      ofComplex_apply_of_im_pos him, eta_six_product_formula ⟨_, him⟩,
      Periodic.qParam_right_inv (h := 4) (by norm_num) hq0, eta_q, h4]

lemma eta_six_product_differentiable :
    DifferentiableOn ℂ (fun q : ℂ ↦ (∏' i, (1 - (q ^ 4) ^ (i + 1))) ^ 6) (Metric.ball 0 1) := by
  refine DifferentiableOn.fun_pow ?_ 6
  refine differentiableOn_tprod_one_sub_pow.comp (f := fun q : ℂ => q ^ 4) (by fun_prop) ?_
  intro q hq
  simp only [Metric.mem_ball, dist_zero_right, norm_pow] at hq ⊢
  exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)

lemma eta_six_first_coefficient : (qExpansion 4 eta6).coeff 1 = 1 := by
  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  calc (qExpansion 4 eta6).coeff 1
      = derivWithin (cuspFunction 4 eta6) (Metric.ball 0 1) 0 := by
        simp [qExpansion_coeff, ← derivWithin_of_isOpen Metric.isOpen_ball hmem]
    _ = derivWithin (fun q ↦ q * (∏' i, (1 - (q ^ 4) ^ (i + 1))) ^ 6) (Metric.ball 0 1) 0 :=
        derivWithin_congr eta_six_cusp_function (eta_six_cusp_function hmem)
    _ = 1 := by
        rw [derivWithin_fun_mul differentiableWithinAt_fun_id (eta_six_product_differentiable _ hmem),
          derivWithin_id' _ _ (Metric.isOpen_ball.uniqueDiffWithinAt hmem)]
        simp

def eta6Frame : Frame eta6Group 4 1 where
  wt := fun _ => 3
  F := fun _ => eta6Form
  odd _ := by decide
  pt τ := by
    refine linearIndependent_unique_iff.2 fun h => eta_six_ne_zero τ ?_
    have := congrFun h 1
    simpa [ev, coe_eta6Form] using this
  cusp := by
    refine linearIndependent_unique_iff.2 fun h => one_ne_zero (α := ℂ) ?_
    have := congrFun (congrFun h 1) 1
    simp only [lead, SlashAction.slash_one, Pi.zero_apply, coe_eta6Form, Nat.cast_ofNat] at this
    rw [show ((1 : Fin 4) : ℕ) = 1 from rfl, eta_six_first_coefficient] at this
    exact this

example : eta6Frame.wt 0 = 3 := rfl
example : eta6Mult ModularGroup.T = Complex.I := eta6Mult_T_eq_I
example : (-1 : SL(2, ℤ)) ∉ eta6Group := neg_one_not_mem_eta6Group

end EtaSix

end GlobalTheory.HeckeFamilyMatrices
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.Imports
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.Sieg

def th (z : ℂ) (τ : ℍ) : ℂ :=
  ee ((τ : ℂ) / 12) * (ee (z / 2) - ee (-z / 2)) *
    ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹)

def act (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : Fin 2 → ℚ := fun i => ∑ j, x j * (((γ : Matrix (Fin 2) (Fin 2) ℤ) j i : ℤ) : ℚ)

end GlobalTheory.Sieg
end
end

