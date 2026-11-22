import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0596
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TensorCoordinateForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
section
noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds
open scoped ComplexOrder

section Ops

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def OpLe (S S' : GSD K) (v : InfinitePlace K) (T : S.V →ₗ[K] S'.V) (t : ℝ) : Prop :=
  ∀ x : S.V, (S'.pairAt v (T x) (T x)).re ≤ t * (S.pairAt v x x).re

def PosAt (S : GSD K) (v : InfinitePlace K) : Prop := (S.gramV.map v.embedding).PosSemidef

end Ops

section Coef

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι]

def sqAt (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) : ℝ :=
  (∑ i, ∑ j, starRingEnd ℂ (σ ((bVV K lam).repr x i)) *
    σ (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) (bVV K lam i) (bVV K lam j)) * σ ((bVV K lam).repr x j)).re

def CoefOpLe (σ : K →+* ℂ) {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K lam') (t : ℝ) : Prop :=
  ∀ x, sqAt σ lam' (T x) ≤ t * sqAt σ lam x

open Classical in

def degAt {a b : ℕ} (e : DVar ι a b →₀ ℕ) (τ : ι) : ℕ := ∑ k ∈ e.support.filter (fun k => k.1 = τ), e k

end Coef

section Data

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}

def LocSmall (q : ℕ) (M : Submodule (𝓞 E) (Sp E a)) (M' : Submodule (𝓞 E) (Sp E b)) (Φ : HomE E a b → K) (β : ℝ) : Prop :=
  (∀ x, Φ x ≠ 0 → ∀ y ∈ M, x y ∈ M') ∧ (∀ x z : HomE E a b, (∀ y ∈ M, z y ∈ M') → Φ (x + (q : E) • z) = Φ x) ∧
    ∀ (σ : K →+* ℂ) (x : HomE E a b), ‖σ (Φ x)‖ ≤ β

def SmallDatum (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (c : ℕ)
    (Ξ : HomE E a b → K) (β : ℝ) : Prop :=
  (∀ x, Ξ x ≠ 0 → x ∈ homAt S N N') ∧ (∀ x, ∀ y ∈ mulLat c (homAt S N N'), Ξ (x + y) = Ξ x) ∧
    ∀ (σ : K →+* ℂ) (x : HomE E a b), ‖σ (Ξ x)‖ ≤ β

end Data

def Pres (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (G F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ) : Prop :=
  ∃ (k : ℕ) (r : Fin k → ℂ) (y : Fin k → TaylorLogMetric.VC D a b), (∀ i, r i ∈ TaylorLogMetric.Qbar) ∧ (∀ i, StandardLatticesGL3.LaQ D T L L' (y i)) ∧
    (∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ∑ i, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (r i)‖ ≤ n) ∧ F = StandardLatticesGL3.comb D T r y G

def toHost {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ} (F : VCx X.Tau a b → ℂ) : TaylorLogMetric.VC D a b → ℂ :=
  fun w => F fun τ => w (s.iT τ)

def supConst (D : D7) (a b : ℕ) : ℝ :=
  3 * (2 * ((TaylorLogMetric.fF D * a * b : ℕ) : ℝ) * D.host.rdE + 1) ^ (TaylorLogMetric.fF D * a * b)

def errUnit (N : NumDatum) (T : ℕ) : ℝ :=
  N.R.f * (N.R.m : ℝ) ^ 2 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * T)

def Hyp {D : D7} (N : NumDatum) {X : Fields} (s : Seam D X) {Pr : Primes X} (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m)
    (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (mu : Tup X.F X.E X.K Sg)
    (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K)))
    (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) : Prop :=
  HostTie N s Pr ∧ WeightTie N W pl u δ ∧ CharTie N s W Ch G sel ∧ AnalyticTie D dl χ cD ∧ mu = 1 ∧ cst.sharp = true ∧
    I.Ok Ch sel mu cst G (N.R.m - 2) ∧ Sizes Pr W N.sc.a ∧ SizeRows N δ (Pr.T u)

def FamilyTie : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → StandardLatticesGL3.natTie D cc δ (B.eNat χ)

def FamilyVectors : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → B.VecP χ

def FamilyNorms : Prop :=
  ∃ C : ℝ, ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D →
    TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → B.kc.YFinite → B.ThP C χ

def PeriodLattices : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    TaylorLogMetric.IsChi D χ → IsDgen D cD → B.kc.YFinite → ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))), Even a → Even b →
    (∀ P ∈ S, conjPrime₂ P ∉ S) → (ambOf s B χ cD).AAUnit S → (ambOf s B χ cD).LaHyp a b S

def CosetRefinement : Prop :=
  ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (Md : ℕ), X.Ok →
    (∀ P ∈ S, (2 : 𝓞 X.E) ∉ P.asIdeal) → Odd Md → A.LaHyp a b S → A.IndAdd a b S Md

end GlobalTheory.ColNorms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorBoundWeierstrassCmTorsion
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.CMSize

theorem mulStable_one_add {L : PeriodPair} {w : ℂ} (h : MulStable L w) : MulStable L (1 + w) := by
  intro x hx
  rw [add_mul, one_mul]
  exact add_mem hx (h x hx)

theorem mulStable_one_sub {L : PeriodPair} {w : ℂ} (h : MulStable L w) : MulStable L (1 - w) := by
  intro x hx
  rw [sub_mul, one_mul]
  exact sub_mem hx (h x hx)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (L : PeriodPair) (Ω P : ℂ) (M : ℕ), d.Prime → 4 < d → MulStable L (Complex.I * (Real.sqrt d : ℝ)) → Ω ^ 12 = latDisc L → ¬ l ∣ M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((s2 L + L.weierstrassP P) / Ω ^ 2) := by
  intro l hl lam d L Ω P M hd hd4 hw hΩ hM hP hMP
  have hlp : l.Prime := hl.out
  have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact hM (dvd_zero _))
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hs0 : Real.sqrt d ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd.pos
    exact (Real.sqrt_pos.mpr this).ne'
  set w : ℂ := Complex.I * (Real.sqrt d : ℝ) with hwdef
  have hre : w.re = 0 := by simp [hwdef]
  have him : w.im = Real.sqrt d := by simp [hwdef]
  have him0 : w.im ≠ 0 := by rw [him]; exact hs0
  have hw2 : w ^ 2 = -(d : ℂ) := by
    have h1 : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = d := by
      rw [← Complex.ofReal_mul, hs]; simp
    rw [hwdef, mul_pow, Complex.I_sq, sq, h1]; ring
  have hn0 : Complex.normSq w = (d : ℕ) := by
    rw [Complex.normSq_apply, hre, him, hs]; simp
  have hn1 : Complex.normSq (1 + w) = ((1 + d : ℕ) : ℝ) := by
    rw [Complex.normSq_apply]; simp [hre, him, hs]
  have hn2 : Complex.normSq (1 - w) = ((1 + d : ℕ) : ℝ) := by
    rw [Complex.normSq_apply]; simp [hre, him, hs]
  have hsz := (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1
  have hp : Sz l lam 0 (12 * (L.weierstrassP P / Ω ^ 2)) := by
    refine hsz (M ^ 2) _ (fun h => hM (hlp.dvd_of_dvd_pow h)) ?_
    have := ((GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier L w Ω M hw him0 hΩ hM0).1 P hMP).1
    convert this using 1
    push_cast; ring
  have key : ∀ (α : ℂ) (n : ℕ), MulStable L α → Complex.normSq α = n → ¬ l ∣ n →
      Sz l lam 0 ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2) -
        (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2)) := by
    intro α n hα hn hln
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hln (dvd_zero _))
    refine hsz ((M * n) ^ 2) _ (fun h => ?_) ?_
    · rcases (Nat.Prime.dvd_mul hlp).1 (hlp.dvd_of_dvd_pow h) with h | h
      · exact hM h
      · exact hln h
    · have := GlobalTheory.T.isogeny_formula_weierstrassP_integral L α w Ω P M n hw him0 hΩ hα hn hn0 hM0 hP hMP
      rwa [Nat.cast_pow]
  by_cases hld : l = d
  · subst hld
    rw [if_neg (by omega), if_pos rfl]
    have hnd : ¬ l ∣ 1 + l := by
      intro h
      have : l ∣ 1 := (Nat.dvd_add_left (dvd_refl l)).1 h
      exact hlp.one_lt.ne' (Nat.dvd_one.1 this)
    have h1 := key (1 + w) (1 + l) (mulStable_one_add hw) hn1 hnd
    refine GlobalTheory.T.algebraicValuation_bound_at_ramified_prime l lam w _ _ hd4 hw2 hp ?_
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  · rw [if_neg hld]
    by_cases h3 : l = 3 ∧ d % 3 = 1
    · obtain ⟨rfl, h3⟩ := h3
      rw [if_neg (by omega)]
      have hnd : ¬ 3 ∣ 1 + d := by omega
      have h1 := key (1 + w) (1 + d) (mulStable_one_add hw) hn1 hnd
      have h2 := key (1 - w) (1 + d) (mulStable_one_sub hw) hn2 hnd
      refine GlobalTheory.T.valuation_bound_three_inert lam d w _ (L.weierstrassP P / Ω ^ 2) h3 hw2 ?_ ?_
      · simpa only [Nat.cast_add, Nat.cast_one] using h1
      · simpa only [Nat.cast_add, Nat.cast_one] using h2
    · have hnd : ¬ l ∣ d := fun h => hld ((Nat.prime_dvd_prime_iff_eq hlp hd).1 h)
      have h1 := key w d hw hn0 hnd
      refine GlobalTheory.T.valuation_bound_multiplier_sqrt_neg_d l lam d _ _ hd hd4 hld hp ?_ ?_
      · convert h1 using 1
        rw [hw2]; ring
      · rintro rfl
        have : ¬ d % 3 = 1 := fun h => h3 ⟨rfl, h⟩
        omega

end GlobalTheory.CMSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDIsTestAndIntegralParts
section
open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff
open GlobalTheory.HenQ

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HenQ.DetDParts

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def wD (w : List E) (g : E → ℂ) : E → ℂ :=
  List.foldr (fun (u : E) (f : E → ℂ) (x : E) => fderiv ℝ f x u) g w

theorem top_add_one_le : (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := le_of_eq rfl

theorem fderiv_fderiv_comm {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    {x : E} (hx : x ∈ U) (u v : E) :
    fderiv ℝ (fun y => fderiv ℝ g y u) x v = fderiv ℝ (fun y => fderiv ℝ g y v) x u := by
  have hgx : ContDiffAt ℝ (⊤ : ℕ∞) g x := hg.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hgx.fderiv_right (m := 1) (by norm_cast)).differentiableAt one_ne_zero
  have key : ∀ a b : E, fderiv ℝ (fun y => fderiv ℝ g y a) x b = fderiv ℝ (fderiv ℝ g) x b a := by
    intro a b
    rw [fderiv_clm_apply hd (differentiableAt_const a)]
    simp
  rw [key, key]
  exact (hgx.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)).eq v u

variable {μ : Measure E} [μ.IsAddHaarMeasure]

theorem continuous_mul_of_tsupport {U : Set E} (hU : IsOpen U) {u χ : E → ℂ}
    (hu : ContinuousOn u U) (hχ : Continuous χ) (hs : tsupport χ ⊆ U) :
    Continuous fun x => χ x * u x :=
  (hχ.continuousOn.mul hu).continuous_of_tsupport_subset hU (tsupport_mul_subset_left.trans hs)

theorem integrable_mul_of_tsupport {U : Set E} (hU : IsOpen U) {u χ : E → ℂ}
    (hu : ContinuousOn u U) (hχ : Continuous χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ U) :
    Integrable (fun x => χ x * u x) μ :=
  (continuous_mul_of_tsupport hU hu hχ hs).integrable_of_hasCompactSupport hc.mul_right

theorem integral_partial_mul {U : Set E} (hU : IsOpen U) {Ψ g : E → ℂ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hc : HasCompactSupport Ψ) (hs : tsupport Ψ ⊆ U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (u : E) :
    ∫ x, fderiv ℝ Ψ x u * g x ∂μ = -∫ x, Ψ x * fderiv ℝ g x u ∂μ := by
  have h1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by exact_mod_cast le_top)
  have hg1 : ContDiffOn ℝ 1 g U := hg.of_le (by exact_mod_cast le_top)
  have hg' : ContDiffOn ℝ 0 (fun x => fderiv ℝ g x u) U :=
    (hg1.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const
  rw [eq_neg_iff_add_eq_zero, add_comm, ← eq_neg_iff_add_eq_zero]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_tsupport hU hg1.continuousOn
      ((h1.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hc.fderiv_apply ℝ _)
      ((tsupport_fderiv_apply_subset ℝ _).trans hs))
    (integrable_mul_of_tsupport hU hg'.continuousOn h1.continuous hc hs)
    (integrable_mul_of_tsupport hU hg1.continuousOn h1.continuous hc hs)
    (fun x _ => h1.differentiable one_ne_zero x)
    (fun x hx => (hg1.contDiffAt (hU.mem_nhds (hs hx))).differentiableAt one_ne_zero)

end General

section Specific

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

open Classical in

def wordOf (v : InfinitePlace K) (p : Equiv.Perm (Fin n)) (l : List (Fin n)) : List (Lie K n) :=
  l.map fun j => toL (Matrix.single (p j) j (Pi.single v 1))

theorem foldr_pdL_eq (v : InfinitePlace K) (p : Equiv.Perm (Fin n)) (F : Lie K n → ℂ) (l : List (Fin n)) :
    l.foldr (fun j G => pdL v (p j) j G) F = wD (wordOf v p l) F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons, wordOf, List.map_cons]
    rw [ih]
    rfl

theorem detD_eq (v : InfinitePlace K) (G : Lie K n → ℂ) :
    detD v G = fun x => ∑ p : Equiv.Perm (Fin n),
      (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) * wD (wordOf v p (List.finRange n)) G x := by
  funext x
  simp only [detD, foldr_pdL_eq]

end Specific

end GlobalTheory.HenQ.DetDParts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfUnitCoord
section
open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GlobalTheory.JetFrameCompare

open GlobalTheory.IndefiniteRowSideFullHecke Formalism.DimensionVariation

section Calculus

variable {E κ W : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem wordDeriv_eq_lineDerivList (v : κ → E) {F : E → ℂ} (hF : Differentiable ℂ F) (w : List κ) :
    TensorCoordinateForms.wordDeriv v w F = lineDerivList ℂ (w.map v) F := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    funext z
    have h := (analyticAt_lineDerivList
      (SCV.analyticOnNhd_of_differentiable hF Set.univ z (Set.mem_univ z)) (w.map v)).differentiableAt
    rw [List.map_cons, lineDerivList_cons]
    change TensorCoordinateForms.dirDeriv (v x) (TensorCoordinateForms.wordDeriv v w F) z = _
    rw [ih]
    exact h.lineDeriv_eq_fderiv.symm

theorem wordDeriv_perm (v : κ → E) {F : E → ℂ} (hF : Differentiable ℂ F) {w w' : List κ}
    (h : w.Perm w') : TensorCoordinateForms.wordDeriv v w F = TensorCoordinateForms.wordDeriv v w' F := by
  funext z
  rw [wordDeriv_eq_lineDerivList v hF, wordDeriv_eq_lineDerivList v hF]
  exact lineDerivList_perm (SCV.analyticOnNhd_of_differentiable hF Set.univ z (Set.mem_univ z)) (h.map v)

def stdWord [Fintype κ] (e : κ → ℕ) : List κ :=
  (univ : Finset κ).toList.flatMap fun x => List.replicate (e x) x

omit [FiniteDimensional ℂ E] in

theorem monoDeriv_eq_wordDeriv [Fintype κ] (v : κ → E) (e : κ → ℕ) (F : E → ℂ) :
    TaylorCoefficientForms.monoDeriv v e F = TensorCoordinateForms.wordDeriv v (stdWord e) F := by
  unfold TaylorCoefficientForms.monoDeriv TensorCoordinateForms.wordDeriv stdWord
  induction (univ : Finset κ).toList with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, List.flatMap_cons, List.foldr_append, ← ih]
    generalize List.foldr (fun x G => (TaylorCoefficientForms.dirDeriv (v x))^[e x] G) F l = G
    induction e x with
    | zero => rfl
    | succ n ihn => rw [Function.iterate_succ_apply', List.replicate_succ, List.foldr_cons, ← ihn]; rfl

theorem isSpelling_stdWord [Fintype κ] [DecidableEq κ] : TensorCoordinateForms.IsSpelling (stdWord (κ := κ)) := by
  intro e x
  rw [stdWord, List.count_flatMap, Finset.sum_map_toList]
  simp [List.count_replicate]

theorem wordDeriv_eq_monoDeriv [Fintype κ] [DecidableEq κ] {w : (κ → ℕ) → List κ}
    (hw : TensorCoordinateForms.IsSpelling w) (v : κ → E) {F : E → ℂ} (hF : Differentiable ℂ F) (e : κ → ℕ) :
    TensorCoordinateForms.wordDeriv v (w e) F = TaylorCoefficientForms.monoDeriv v e F := by
  rw [monoDeriv_eq_wordDeriv]
  exact wordDeriv_perm v hF (List.perm_iff_count.2 fun x => (hw e x).trans (isSpelling_stdWord e x).symm)

theorem coordVec_eq [DecidableEq κ] : (TensorCoordinateForms.coordVec : κ → κ → ℂ) = TaylorCoefficientForms.coordVec := by
  funext p
  unfold TensorCoordinateForms.coordVec TaylorCoefficientForms.coordVec
  congr
  exact Subsingleton.elim _ _

theorem hasSum_taylorCoeff [Fintype κ] {F : (κ → ℂ) → ℂ} (hF : Differentiable ℂ F) (u : κ → ℂ) :
    HasSum (fun e => TaylorCoefficientForms.taylorCoeff F e * mono u e) (F u) := by
  classical
  have han := SCV.analyticOnNhd_of_differentiable hF Set.univ 0 (Set.mem_univ _)
  have hw : TensorCoordinateForms.IsSpelling fun e : κ → ℕ =>
      (Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm e)).toList := fun e x => by
    rw [← Multiset.coe_count, Multiset.coe_toList, Finsupp.count_toMultiset]
    rfl
  have key : ∀ α : κ →₀ ℕ, TaylorCoefficientForms.monoDeriv TaylorCoefficientForms.coordVec α F =
      lineDerivList ℂ ((Finsupp.toMultiset α).toList.map fun k => Pi.single k (1 : ℂ)) F := fun α => by
    rw [← wordDeriv_eq_monoDeriv hw _ hF, wordDeriv_eq_lineDerivList _ hF, ← coordVec_eq]
    simp only [Finsupp.equivFunOnFinite_symm_coe]
    rfl
  have hne : ∀ α : κ →₀ ℕ, ((∏ i, (α i).factorial : ℕ) : ℂ) ≠ 0 := cast_prod_factorial_ne_zero
  have hc : ∀ α : κ →₀ ℕ,
      (∏ j, ((α j).factorial : ℂ)) * TaylorCoefficientForms.taylorCoeff F α = pderivIter α F 0 := fun α => by
    rw [TaylorCoefficientForms.taylorCoeff, key, mfact,
      ← Nat.cast_prod, mul_div_cancel₀ _ (hne α)]
    rfl
  have hc' : ∀ α : κ →₀ ℕ,
      TaylorCoefficientForms.taylorCoeff F α = MvPowerSeries.coeff α (GlobalTheory.taylor F) := fun α => by
    rw [GlobalTheory.taylor, coeff_taylorDir_eq_lineDerivList _ han (Multiset.coe_toList _), TaylorCoefficientForms.taylorCoeff, key,
      mfact, div_eq_inv_mul]
  have h1 := EntireTaylor.summable_of_entire hF (fun α => TaylorCoefficientForms.taylorCoeff F α) hc u
  have h2 := ProdThetaConj.tsum_of_entire hF (fun α => TaylorCoefficientForms.taylorCoeff F α) hc hc' u
  rw [← h2, ← (Finsupp.equivFunOnFinite (α := κ) (M := ℕ)).hasSum_iff]
  exact h1.hasSum

end Calculus

section Objects

variable {Pl : Type} [Fintype Pl] [DecidableEq Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ} (ξ D : Pl → ℂ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
  (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ))

end Objects

section Clauses

variable {Pl : Type} [Fintype Pl] {X₀ X₁ : Pl → Type}
  [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
  [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
  {n₀ n₁ : ℕ}

def ClausesFixedOrder (ξ D lam : Pl → ℂ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
    (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)) : Prop :=
  (∀ z, TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁ (TaylorCoefficientForms.unitCoord ξ b₀ b₁ z) = z) ∧
  (∀ u, TaylorCoefficientForms.unitCoord ξ b₀ b₁ (TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁ u) = u) ∧
  (∀ z, (nsq (TaylorCoefficientForms.unitCoord ξ b₀ b₁ z) : ℂ) = π * TaylorCoefficientForms.bigForm ξ z z) ∧
  (∀ (τ : Pl) (d d' : ℂ) (x x' : X₀ τ →L[ℂ] X₁ τ),
    TaylorCoefficientForms.bigForm ξ (TaylorCoefficientForms.letterTensor τ d x) (TaylorCoefficientForms.letterTensor τ d' x') =
      TaylorCoefficientForms.lineForm (ξ τ) d d' * TaylorCoefficientForms.homForm x x') ∧
  ∀ Θ : (∀ τ, X₀ τ →L[ℂ] X₁ τ) → ℂ, Differentiable ℂ Θ →
    (∀ (x : Pl × (Fin n₁ × Fin n₀)) (z : ∀ τ, X₀ τ →L[ℂ] X₁ τ),
      TaylorCoefficientForms.dirDeriv (TaylorCoefficientForms.letterUnit D b₀ b₁ x) Θ z =
        lam x.1 * TaylorCoefficientForms.dirDeriv (TaylorCoefficientForms.coordVec x) (Θ ∘ TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁)
          (TaylorCoefficientForms.unitCoord ξ b₀ b₁ z)) ∧
    (∀ u, HasSum (fun e => TaylorCoefficientForms.taylorCoeff (Θ ∘ TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁) e * mono u e)
      (Θ (TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁ u))) ∧
    ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] (n : Pl → ℕ)
      (Rc : (Pl × (Fin n₁ × Fin n₀) → ℕ) →₀ W),
      (∀ e ∈ Rc.support, ∀ τ, ∑ p, e (τ, p) = n τ) →
      TaylorCoefficientForms.polyJet (TaylorCoefficientForms.letterUnit D b₀ b₁) Rc Θ =
          (∏ τ, lam τ ^ n τ) • TaylorCoefficientForms.polyJet TaylorCoefficientForms.coordVec Rc (Θ ∘ TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁) ∧
        TaylorCoefficientForms.polyJet (TaylorCoefficientForms.letterUnit D b₀ b₁) Rc Θ =
          liftBlock (TaylorCoefficientForms.taylorCoeff (Θ ∘ TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁)) Rc lam ∧
        ∀ c : (Pl × (Fin n₁ × Fin n₀) → ℕ) → ℂ,
          (∀ u, HasSum (fun e => c e * mono u e) (Θ (TaylorCoefficientForms.ofUnitCoord ξ b₀ b₁ u))) →
          TaylorCoefficientForms.polyJet (TaylorCoefficientForms.letterUnit D b₀ b₁) Rc Θ = liftBlock c Rc lam

def ClausesAllOrders [DecidableEq Pl] (a : Pl → ℝ) (D lam : Pl → ℂ)
    (b : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ)) (b' : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)) : Prop :=
  (∀ u, TensorCoordinateForms.unitCoord a b b' (TensorCoordinateForms.ofUnitCoord a b b' u) = u) ∧
  (∀ z, TensorCoordinateForms.ofUnitCoord a b b' (TensorCoordinateForms.unitCoord a b b' z) = z) ∧
  (∀ z, ((nsq (TensorCoordinateForms.unitCoord a b b' z) : ℝ) : ℂ) = (π : ℂ) * TensorCoordinateForms.totalForm a z z) ∧
  (∀ (τ : Pl) (d d' : ℂ) (x x' : X₀ τ →L[ℂ] X₁ τ),
    TensorCoordinateForms.totalForm a (TensorCoordinateForms.tensorVec τ d x) (TensorCoordinateForms.tensorVec τ d' x') =
      TensorCoordinateForms.lineForm (a τ) d d' * TensorCoordinateForms.traceForm x x') ∧
  ∀ Th : (∀ τ, X₀ τ →L[ℂ] X₁ τ) → ℂ, Differentiable ℂ Th →
    (∀ (p : Pl × (Fin n₁ × Fin n₀)) (z : ∀ τ, X₀ τ →L[ℂ] X₁ τ),
      TensorCoordinateForms.dirDeriv (TensorCoordinateForms.frameVec D b b' p) Th z =
        lam p.1 * TensorCoordinateForms.dirDeriv (TensorCoordinateForms.coordVec p) (Th ∘ TensorCoordinateForms.ofUnitCoord a b b')
          (TensorCoordinateForms.unitCoord a b b' z)) ∧
    ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
      (Rc : (Pl × (Fin n₁ × Fin n₀) → ℕ) →₀ W) (n : Pl → ℕ)
      (w : (Pl × (Fin n₁ × Fin n₀) → ℕ) → List (Pl × (Fin n₁ × Fin n₀))),
      TensorCoordinateForms.IsSpelling w → (∀ e ∈ Rc.support, ∀ τ, ∑ q, e (τ, q) = n τ) →
      TensorCoordinateForms.substJet w (TensorCoordinateForms.frameVec D b b') Rc Th =
          (∏ τ, lam τ ^ n τ) • TensorCoordinateForms.substJet w TensorCoordinateForms.coordVec Rc (Th ∘ TensorCoordinateForms.ofUnitCoord a b b') ∧
      ∀ c : (Pl × (Fin n₁ × Fin n₀) → ℕ) → ℂ,
        (∀ u, HasSum (fun e => c e * mono u e) (Th (TensorCoordinateForms.ofUnitCoord a b b' u))) →
        TensorCoordinateForms.substJet w (TensorCoordinateForms.frameVec D b b') Rc Th = liftBlock c Rc lam

end Clauses

def ConclusionFixedOrder (Pl : Type) [Fintype Pl] (ξ D : Pl → ℂ) : Prop :=
  (∀ τ, 0 < TaylorCoefficientForms.period (ξ τ) (D τ)) ∧
  ∃ lam : Pl → ℂ, (∀ τ, ‖lam τ‖ ^ 2 = (TaylorCoefficientForms.period (ξ τ) (D τ))⁻¹) ∧
    ∀ (X₀ X₁ : Pl → Type)
      [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
      [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
      (n₀ n₁ : ℕ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
      (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)), ClausesFixedOrder ξ D lam b₀ b₁

def ConclusionAllOrders (Pl : Type) [Fintype Pl] [DecidableEq Pl] (a : Pl → ℝ) (D : Pl → ℂ) : Prop :=
  ∃ ζ : Pl → ℂ,
    (∀ τ, ‖ζ τ‖ = 1) ∧ (∀ τ, 0 < TensorCoordinateForms.omega (a τ) (D τ)) ∧
    (∀ τ, ‖TensorCoordinateForms.letter (TensorCoordinateForms.omega (a τ) (D τ)) (ζ τ)‖ ^ 2 = (TensorCoordinateForms.omega (a τ) (D τ))⁻¹) ∧
    ∀ (X₀ X₁ : Pl → Type)
      [∀ τ, NormedAddCommGroup (X₀ τ)] [∀ τ, InnerProductSpace ℂ (X₀ τ)] [∀ τ, FiniteDimensional ℂ (X₀ τ)]
      [∀ τ, NormedAddCommGroup (X₁ τ)] [∀ τ, InnerProductSpace ℂ (X₁ τ)] [∀ τ, FiniteDimensional ℂ (X₁ τ)]
      (n₀ n₁ : ℕ) (b₀ : ∀ τ, OrthonormalBasis (Fin n₀) ℂ (X₀ τ))
      (b₁ : ∀ τ, OrthonormalBasis (Fin n₁) ℂ (X₁ τ)),
      ClausesAllOrders a D (fun τ => TensorCoordinateForms.letter (TensorCoordinateForms.omega (a τ) (D τ)) (ζ τ)) b₀ b₁

end GlobalTheory.JetFrameCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylWeightSpreadBoundProofStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylWeightSpreadBound_proof : GlobalTheory.LeviCut.NablaBdd := by
  first | exact @GlobalTheory.LeviCut.nablaBdd | exact GlobalTheory.LeviCut.nablaBdd | (intros; apply GlobalTheory.LeviCut.nablaBdd <;> assumption)
end

