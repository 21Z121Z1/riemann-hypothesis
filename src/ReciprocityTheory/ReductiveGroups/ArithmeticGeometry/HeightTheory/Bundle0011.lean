import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0009
import ReciprocityTheory.SemistableReduction.Bundle0006
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0008
import ReciprocityTheory.SemistableReduction.Bundle0023
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SectionSheafQuotient
import Mathlib

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraicIndependentScaledForms
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence

open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence

theorem algebraicIndependent_scaledForms {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    (y : Fin (N + 1) → Ω) (jc : Fin (N + 1)) (hy : y jc = 1)
    (J : Fin D → Fin N) (δ : Fin D → Derivation K Ω Ω)
    (hδ : ∀ a b, δ a (y (jc.succAbove (J b))) = if a = b then 1 else 0)
    (ρ : Option (Fin D) → Fin (D + 2)) (hρ : Function.Injective ρ) :
    AlgebraicIndependent K (Sum.elim
      (fun p : Fin (D + 2) × Fin (N + 1) =>
        (X (some p) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω))
      (fun o : Option (Fin D) => X none * ∑ j, X (some (ρ o, j)) * C (y j))) := by
  classical
  refine algebraicIndependent_of_derivations _ (Sum.elim
    (fun o => (pderiv o :
      Derivation Ω (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)
        (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)).restrictScalars K)
    (fun a => coeffDer (σ := Option (Fin (D + 2) × Fin (N + 1))) (δ a))) ?_
  intro c H
  have hZ : ∀ o, pderiv (none : Option (Fin (D + 2) × Fin (N + 1)))
      (∑ j, X (some (ρ o, j)) * C (y j) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) = 0 := by
    intro o; simp [pderiv_X]
  have hpn : ∀ o, pderiv (none : Option (Fin (D + 2) × Fin (N + 1)))
      (X none * ∑ j, X (some (ρ o, j)) * C (y j) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) =
        ∑ j, X (some (ρ o, j)) * C (y j) := by
    intro o; rw [Derivation.leibniz, hZ, smul_zero, zero_add, pderiv_X]; simp
  have hcd : ∀ a o, coeffDer (σ := Option (Fin (D + 2) × Fin (N + 1))) (δ a)
      (X none * ∑ j, X (some (ρ o, j)) * C (y j)) =
        X none * ∑ j, X (some (ρ o, j)) * C (δ a (y j)) := by
    intro a o
    simp [Derivation.leibniz, coeffDer_X, coeffDer_C, map_sum]
  let M : Matrix (Option (Fin D)) (Option (Fin D))
      (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) := fun r o =>
    match r with
    | none => ∑ j, X (some (ρ o, j)) * C (y j)
    | some a => X none * ∑ j, X (some (ρ o, j)) * C (δ a (y j))
  have e1 : ∑ o, c (Sum.inr o) * ∑ j, (X (some (ρ o, j)) * C (y j) :
      MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) = 0 := by
    have := H (Sum.inl none)
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, Derivation.coe_restrictScalars, hpn] at this
    rwa [Finset.sum_eq_zero (fun p _ => by simp [pderiv_X]), zero_add] at this
  have e2 : ∀ a, ∑ o, c (Sum.inr o) * (X none * ∑ j, (X (some (ρ o, j)) * C (δ a (y j)) :
      MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)) = 0 := by
    intro a
    have := H (Sum.inr a)
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, hcd] at this
    rwa [Finset.sum_eq_zero (fun p _ => by simp [coeffDer_X]), zero_add] at this
  have hv : M.mulVec (fun o => c (Sum.inr o)) = 0 := by
    funext r
    cases r with
    | none =>
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← e1]
      exact Finset.sum_congr rfl fun o _ => mul_comm _ _
    | some a =>
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← e2 a]
      exact Finset.sum_congr rfl fun o _ => mul_comm _ _
  let pt : Option (Fin (D + 2) × Fin (N + 1)) → Ω := fun v =>
    match v with
    | none => 1
    | some q => ∑ o : Option (Fin D), if ρ o = q.1 then
        (match o with
          | none => if q.2 = jc then 1 else 0
          | some b => (if q.2 = jc then -y (jc.succAbove (J b)) else 0) +
              (if q.2 = jc.succAbove (J b) then 1 else 0))
        else 0
  have hpt0 : ∀ j, pt (some (ρ none, j)) = if j = jc then 1 else 0 := by
    intro j
    show (∑ o : Option (Fin D), _) = _
    rw [Finset.sum_eq_single none]
    · simp
    · intro o _ ho; rw [if_neg]; exact fun h => ho (hρ h)
    · simp
  have hpt1 : ∀ b j, pt (some (ρ (some b), j)) = (if j = jc then -y (jc.succAbove (J b)) else 0) +
      (if j = jc.succAbove (J b) then 1 else 0) := by
    intro b j
    show (∑ o : Option (Fin D), _) = _
    rw [Finset.sum_eq_single (some b)]
    · simp
    · intro o _ ho; rw [if_neg]; exact fun h => ho (hρ h)
    · simp
  have hptn : pt none = 1 := rfl
  have hne : ∀ b, jc.succAbove (J b) ≠ jc := fun b => Fin.succAbove_ne jc (J b)
  have hev : (MvPolynomial.eval pt).mapMatrix M = 1 := by
    ext r o
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    cases r with
    | none =>
      cases o with
      | none => simp [M, hpt0, hy]
      | some b =>
        simp [M, hpt1, add_mul, Finset.sum_add_distrib, hy, Matrix.one_apply]
    | some a =>
      cases o with
      | none =>
        simp [M, hpt0, hy, hptn, Matrix.one_apply]
      | some b =>
        simp [M, hpt1, add_mul, Finset.sum_add_distrib, hy, hδ, Matrix.one_apply, hptn]
  have hdet : M.det ≠ 0 := by
    intro h0
    have := RingHom.map_det (MvPolynomial.eval pt) M
    rw [h0, map_zero, hev, Matrix.det_one] at this
    exact zero_ne_one this
  have hc2 : ∀ o, c (Sum.inr o) = 0 := fun o =>
    congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hv) o
  intro i
  rcases i with p | o
  · have := H (Sum.inl (some p))
    simpa [Fintype.sum_sum_type, hc2, pderiv_X, Pi.single_apply] using this
  · exact hc2 o

theorem scalarRatio_self {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V}
    (hf : f ≠ 0) : ratio (Ω := Ω) f f = 1 := by
  unfold ratio
  split_ifs with h
  · have hc : f = h.choose • f := h.choose_spec
    have h0 : (h.choose - 1) • f = 0 := by
      rw [sub_smul, one_smul, ← hc, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hf
  · exact absurd ⟨1, (one_smul Ω f).symm⟩ h

def hupa1Row (D : ℕ) (o : Option (Fin D)) : Fin (D + 2) := Fin.castSucc ((finSuccEquiv D).symm o)

def hupa1Eqv (D N : ℕ) :
    Option ((Fin (D + 2) × Fin (N + 1)) ⊕ Option (Fin D)) ≃ ((Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)) where
  toFun v := match v with
    | none => Sum.inr (Fin.last (D + 1))
    | some (Sum.inl p) => Sum.inl p
    | some (Sum.inr o) => Sum.inr (hupa1Row D o)
  invFun v := match v with
    | Sum.inl p => some (Sum.inl p)
    | Sum.inr i => match finSuccEquivLast i with
      | none => none
      | some t => some (Sum.inr (finSuccEquiv D t))
  left_inv v := by
    rcases v with _ | p | o
    · simp
    · rfl
    · simp [hupa1Row]
  right_inv v := by
    rcases v with p | i
    · rfl
    · dsimp only
      rcases h : finSuccEquivLast i with _ | t
      · have : i = finSuccEquivLast.symm none := (Equiv.eq_symm_apply _).2 h
        simp [this]
      · have : i = finSuccEquivLast.symm (some t) := (Equiv.eq_symm_apply _).2 h
        simp [this, hupa1Row]

theorem optionEquivLeft_rename_some' {R S : Type*} [CommRing R] (a : MvPolynomial S R) :
    MvPolynomial.optionEquivLeft R S (MvPolynomial.rename some a) = Polynomial.C a := by
  induction a using MvPolynomial.induction_on
  next r => simp [MvPolynomial.optionEquivLeft_C]
  next p q hp hq => simp [hp, hq]
  next p s hp => simp [hp, MvPolynomial.optionEquivLeft_X_some]

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CoeffPsiPNeZero
section
namespace ReciprocityTheory.ChartRestriction.G.T0.WH

open MvPolynomial

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] (p : σ → Prop) [DecidablePred p]

def wt (s : σ →₀ ℕ) : ℕ := ∑ v, if p v then s v else 0

theorem wt_add (s t : σ →₀ ℕ) : wt p (s + t) = wt p s + wt p t := by
  simp only [wt, Finsupp.coe_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

theorem wt_single (v : σ) (e : ℕ) : wt p (Finsupp.single v e) = if p v then e else 0 := by
  simp only [wt]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Finsupp.single_apply, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ v) h

noncomputable def psiP : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun v => if p v then Polynomial.C (X v) * Polynomial.X else Polynomial.C (X v)

theorem psiP_monomial (s : σ →₀ ℕ) (a : K) :
    psiP p (monomial s a) = Polynomial.C (monomial s a) * Polynomial.X ^ wt p s := by
  have key : ∀ v, (if p v then Polynomial.C (X v : MvPolynomial σ K) * Polynomial.X
      else Polynomial.C (X v)) ^ (s v)
      = Polynomial.C ((X v : MvPolynomial σ K) ^ s v) * Polynomial.X ^ (if p v then s v else 0) := by
    intro v
    split_ifs <;> simp [mul_pow]
  rw [psiP, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Finset.prod_congr rfl (fun v _ => key v), Finset.prod_mul_distrib, ← map_prod,
    Finset.prod_pow_eq_pow_sum, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul, wt]
  ring

theorem psiP_eq_of_isWeightedHomogeneous (n : ℕ) (f : MvPolynomial σ K) (hf : ∀ s ∈ f.support, wt p s = n) :
    psiP p f = Polynomial.C f * Polynomial.X ^ n := by
  have h : ∀ s ∈ f.support, psiP p (monomial s (coeff s f))
      = Polynomial.C (monomial s (coeff s f)) * Polynomial.X ^ n := fun s hs => by
    rw [psiP_monomial, hf s hs]
  conv_lhs => rw [f.as_sum]
  rw [map_sum, Finset.sum_congr rfl h, ← Finset.sum_mul, ← map_sum, ← f.as_sum]

private theorem psiP_eq_sum_monomial (f : MvPolynomial σ K) :
    psiP p f = ∑ s ∈ f.support, Polynomial.C (monomial s (coeff s f)) * Polynomial.X ^ wt p s := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  simp only [psiP_monomial]

private theorem coeff_psiP (f : MvPolynomial σ K) (k : ℕ) :
    (psiP p f).coeff k = ∑ s ∈ f.support.filter (fun s => wt p s = k), monomial s (coeff s f) := by
  rw [psiP_eq_sum_monomial, Polynomial.finset_sum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases h : wt p s = k
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem coeff_psiP_ne_zero (f : MvPolynomial σ K) (s : σ →₀ ℕ) (hs : s ∈ f.support) :
    (psiP p f).coeff (wt p s) ≠ 0 := by
  intro h
  have h' := congrArg (MvPolynomial.coeff s) h
  rw [coeff_psiP, MvPolynomial.coeff_sum, Finset.sum_eq_single s] at h'
  · classical
    rw [coeff_monomial, if_pos rfl, coeff_zero] at h'
    exact (mem_support_iff.mp hs) h'
  · classical
    intro t _ hts
    rw [coeff_monomial, if_neg hts]
  · intro hn
    exact (hn (Finset.mem_filter.mpr ⟨hs, rfl⟩)).elim

theorem hom_of_psiP (n : ℕ) (f : MvPolynomial σ K) (hf : psiP p f = Polynomial.C f * Polynomial.X ^ n) :
    ∀ s ∈ f.support, wt p s = n := by
  intro s hs
  by_contra hne
  apply coeff_psiP_ne_zero p f s hs
  rw [hf, Polynomial.coeff_C_mul_X_pow, if_neg hne]

theorem hom_of_dvd (n : ℕ) (H A : MvPolynomial σ K) (hH0 : H ≠ 0)
    (hH : ∀ s ∈ H.support, wt p s = n) (hA : A ∣ H) : ∃ m, ∀ s ∈ A.support, wt p s = m := by
  obtain ⟨B, rfl⟩ := hA
  have hA0 : A ≠ 0 := left_ne_zero_of_mul hH0
  have hB0 : B ≠ 0 := right_ne_zero_of_mul hH0
  have hne : ∀ F : MvPolynomial σ K, F ≠ 0 → psiP p F ≠ 0 := by
    intro F hF h0
    obtain ⟨s, hs⟩ := MvPolynomial.ne_zero_iff.mp hF
    exact coeff_psiP_ne_zero p F s (mem_support_iff.mpr hs) (by rw [h0, Polynomial.coeff_zero])
  have hprod : psiP p A * psiP p B = Polynomial.C (A * B) * Polynomial.X ^ n := by
    rw [← map_mul]
    exact psiP_eq_of_isWeightedHomogeneous p n _ hH
  have hd := congrArg Polynomial.natDegree hprod
  have ht := congrArg Polynomial.natTrailingDegree hprod
  rw [Polynomial.natDegree_mul (hne A hA0) (hne B hB0),
    Polynomial.natDegree_C_mul_X_pow _ _ hH0] at hd
  rw [Polynomial.natTrailingDegree_mul (hne A hA0) (hne B hB0),
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.natTrailingDegree_monomial hH0] at ht
  have h1 := Polynomial.natTrailingDegree_le_natDegree (p := psiP p A)
  have h2 := Polynomial.natTrailingDegree_le_natDegree (p := psiP p B)
  refine ⟨(psiP p A).natDegree, fun s hs => ?_⟩
  have hc := coeff_psiP_ne_zero p A s hs
  have h3 := Polynomial.le_natDegree_of_ne_zero hc
  have h4 := Polynomial.natTrailingDegree_le_of_ne_zero hc
  omega

end ReciprocityTheory.ChartRestriction.G.T0.WH
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GenericSectionOfAxioms
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def htOf (hd : d.AxH 𝒜) (h : d.S1) : Formalism.MainNotions.Gaps.HeightData.HtData where
  K := K
  D := d.D
  δ := d.del
  i := d.i
  g0 := d.g0
  L := d.wsize d.wL
  G := d.Gc
  PH := d.PHc
  Prw := d.Prw
  Pet := d.Pet
  S := fun k => meanK fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))
  etaPart := True
  Op := fun la => Op d.D d.N la
  SectionSheafQuotient := fun _ => ∀ c, OmS (Ω c) d.D d.N
  mA := fun la =>
    letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
    inferInstance
  A0 := fun la =>
    letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
    Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)
  t := fun _ => d.bvecG hd.sel hd.a4.choose
  Pts := fun la => Σ c, {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) // w ∈ d.PlOver la c}
  ep := fun _ _ => 1
  f := fun _ ζ => d.fze h ζ.1 ζ.2.1
  vEt := fun _ ζ => (d.ord ζ.1 (d.Wres ζ.1 ζ.2.1) (d.n1 • d.wde) (d.et ζ.1) : ℝ)

theorem genericSection_of_axioms (hd : d.AxH 𝒜) : d.S1 := by
  intro c
  have hS := (ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K (Ω c) d.D d.N (d.x c) (hd.fg c) (hd.trdeg c)
    (hd.a1 c)).1
  have key : ∀ {M : Type} (j0 : Fin (d.N + 1)) (a : M) (f : Fin d.N → M),
      Fin.succAboveCases (α := fun _ => M) j0 a f j0 = a ∧
      ∀ k, Fin.succAboveCases (α := fun _ => M) j0 a f (j0.succAbove k) = f k :=
    fun j0 a f => ⟨by exact Fin.insertNth_apply_same (α := fun _ => _) j0 a f,
      fun k => by exact Fin.insertNth_apply_succAbove (α := fun _ => _) j0 a f k⟩
  let σ : Fin (d.N + 1) → Fin (d.N + 1) :=
    Fin.succAboveCases (α := fun _ => Fin (d.N + 1)) (d.jc c) 0 Fin.succ
  let ρ : Fin (d.N + 1) → Fin (d.N + 1) :=
    Fin.cases (motive := fun _ => Fin (d.N + 1)) (d.jc c) (d.jc c).succAbove
  have hρσ : Function.LeftInverse ρ σ := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
    · simp only [σ, ρ, (key _ _ _).1, Fin.cases_zero]
    · simp only [σ, ρ, (key _ _ _).2, Fin.cases_succ]
  let g : TVar d.D d.N → Fin (d.D + 1) × Fin (d.N + 1) := fun p => (p.1, σ p.2)
  have hg : Function.Injective g := by
    intro p q hpq
    simp only [g, Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (hρσ.injective hpq.2)
  have heq : ∀ p, sImg (d.jc c) (d.x c) p = ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c) (g p) := by
    rintro ⟨i, j⟩
    rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
    · simp only [sImg, ReciprocityTheory.MultiplicativeHeights.sImage, g, σ, (key _ _ _).1, Fin.cases_zero]
    · simp only [sImg, ReciprocityTheory.MultiplicativeHeights.sImage, g, σ, (key _ _ _).2, Fin.cases_succ]
  have hfun : sImg (d.jc c) (d.x c) = ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c) ∘ g := funext heq
  have hI : AlgebraicIndependent K (sImg (D := d.D) (d.jc c) (d.x c)) := by
    rw [hfun]
    exact hS.comp g hg
  exact hI

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAA
section
namespace ReciprocityTheory.ChartRestriction.G.T0

namespace HDiscLat

open Module

theorem det_blockDiagonal' {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {κ : ι → Type*} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)]
    (M : ∀ c, Matrix (κ c) (κ c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by
  classical

  have hblk : ∀ c, (Matrix.toSquareBlock (Matrix.blockDiagonal' M) Sigma.fst c).det =
      (M c).det := by
    intro c
    let e : κ c ≃ {s : (Σ c, κ c) // s.1 = c} :=
      { toFun := fun k => ⟨⟨c, k⟩, rfl⟩
        invFun := fun s => cast (congrArg κ s.2) s.1.2
        left_inv := fun k => rfl
        right_inv := by
          rintro ⟨⟨a, k⟩, rfl⟩
          rfl }
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext k k'
    show Matrix.blockDiagonal' M ⟨c, k⟩ ⟨c, k'⟩ = M c k k'
    first
      | exact Matrix.blockDiagonal'_apply_eq M c k k'
      | simp [Matrix.blockDiagonal'_apply]
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  first
    | rw [(Matrix.blockTriangular_blockDiagonal' M).det]
    | rw [Matrix.BlockTriangular.det (Matrix.blockTriangular_blockDiagonal' M)]
  rw [Finset.prod_congr rfl (fun c _ => hblk c)]
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro c _ hc
  haveI : IsEmpty (κ c) :=
    ⟨fun k => hc (Finset.mem_image.2 ⟨⟨c, k⟩, Finset.mem_univ _, rfl⟩)⟩
  exact Matrix.det_isEmpty

theorem gram_mul {F L : Type*} [Field F] [Field L] [Algebra F L] {κ : Type*} [Fintype κ]
    [DecidableEq κ] (a : Basis κ F L) (h : L) :
    (Matrix.of fun p q => Algebra.trace F L (h * a p * a q)).det =
      Algebra.norm F h * Algebra.discr F a := by

  rw [Algebra.discr_def, Algebra.norm_eq_matrix_det a h,
    ← Matrix.det_transpose (Algebra.leftMulMatrix a h), ← Matrix.det_mul]
  congr 1
  ext p q
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [← a.sum_repr (h * a p)]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]

theorem length_quot {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ)
    {CC V : Type*} [AddCommGroup CC] [Module R CC] [AddCommGroup V] [Module R V]
    {κ : Type*} [Fintype κ] [DecidableEq κ] (α : Basis κ R CC) (φ : CC →ₗ[R] V)
    (hφ : Function.Injective φ) (SA : Submodule R V) (hSA : SA = LinearMap.range φ)
    {m : ℕ} (b' : Fin m → CC) (hli : LinearIndependent R b') (σ : κ ≃ Fin m) :
    ∃ n : ℕ, ∃ u : Rˣ,
      Module.length R (SA ⧸ (Submodule.span R (Set.range (φ ∘ b'))).comap SA.subtype) = n ∧
      α.det (b' ∘ σ) = u * ϖ ^ n := by
  classical
  set N := Submodule.span R (Set.range b')
  have hrank : finrank R N = finrank R CC := by
    rw [finrank_span_eq_card hli, finrank_eq_card_basis α, Fintype.card_fin, Fintype.card_congr σ,
      Fintype.card_fin]
  set s := Submodule.smithNormalFormCoeffs α hrank
  have hlen : Module.length R (CC ⧸ N) = ∑ i, IsDiscreteValuationRing.addVal R (s i) := by
    rw [(Submodule.quotientEquivPiSpan N α hrank).length_eq, Module.length_pi_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Ring.ord_eq_addVal]
    rfl
  have hdet : Associated (α.det (b' ∘ σ)) (∏ i, s i) := by
    have key := ReciprocityTheory.MultiplicativeHeights.det_subtype_comp_associated_prod α N hrank (α.equiv (Basis.span hli) σ)
    convert key using 1
    rw [← LinearMap.det_toMatrix α, Basis.det_apply]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, Basis.toMatrix_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Basis.equiv_apply,
      Submodule.subtype_apply]
    rw [Module.Basis.span_apply]
  have hne : (∏ i, s i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Submodule.smithNormalFormCoeffs_ne_zero α hrank i
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hval : ∑ i, IsDiscreteValuationRing.addVal R (s i) = n := by
    rw [← ReciprocityTheory.MultiplicativeHeights.addVal_prod, hu, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simp
  let E : CC ≃ₗ[R] SA := (LinearEquiv.ofInjective φ hφ).trans (LinearEquiv.ofEq _ _ hSA.symm)
  have hE : ∀ y, (E y : V) = φ y := fun y => rfl
  have hmap : N.map (E : CC →ₗ[R] SA) =
      (Submodule.span R (Set.range (φ ∘ b'))).comap SA.subtype := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    rw [Set.range_comp, ← Submodule.map_span]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change φ y ∈ _
      exact Submodule.mem_map_of_mem hy
    · rintro ⟨y, hy, hyx⟩
      exact ⟨y, hy, Subtype.ext (by change φ y = _; exact hyx)⟩
  obtain ⟨v, hv⟩ := hdet.symm
  refine ⟨n, u * v, ?_, ?_⟩
  · rw [← (Submodule.Quotient.equiv N _ E hmap).length_eq, hlen, hval]
  · rw [← hv, hu, Units.val_mul]
    ring

end HDiscLat

end ReciprocityTheory.ChartRestriction.G.T0
end

