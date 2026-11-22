import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0488
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroZeroFormPolynomialIsAlgClosed
section
open IsLocalRing

namespace GlobalTheory
namespace TsenCount

open Polynomial

variable {σ k : Type} [CommRing k]

def CoeffHom (e : ℕ) (p : (MvPolynomial σ k)[X]) : Prop := ∀ j, (p.coeff j).IsHomogeneous e

theorem CoeffHom.mul {a b : ℕ} {p q : (MvPolynomial σ k)[X]} (hp : CoeffHom a p)
    (hq : CoeffHom b q) : CoeffHom (a + b) (p * q) := fun j => by
  rw [coeff_mul]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun c _ => (hp _).mul (hq _)

theorem coeffHom_map (g : k[X]) :
    CoeffHom 0 (g.map (MvPolynomial.C : k →+* MvPolynomial σ k)) := fun j => by
  rw [coeff_map]
  exact MvPolynomial.isHomogeneous_C _ _

theorem coeffHom_one : CoeffHom 0 (1 : (MvPolynomial σ k)[X]) := by
  simpa using coeffHom_map (σ := σ) (1 : k[X])

theorem CoeffHom.pow {p : (MvPolynomial σ k)[X]} (hp : CoeffHom 1 p) (m : ℕ) :
    CoeffHom m (p ^ m) := by
  induction m with
  | zero => simpa using coeffHom_one
  | succ m ih => rw [pow_succ]; exact ih.mul hp

theorem CoeffHom.prod {ι : Type} (s : Finset ι) (e : ι → ℕ) (p : ι → (MvPolynomial σ k)[X])
    (h : ∀ i, CoeffHom (e i) (p i)) : CoeffHom (∑ i ∈ s, e i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coeffHom_one
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha]; exact (h a).mul ih

theorem CoeffHom.sum {ι : Type} (s : Finset ι) (e : ℕ) (p : ι → (MvPolynomial σ k)[X])
    (h : ∀ i ∈ s, CoeffHom e (p i)) : CoeffHom e (∑ i ∈ s, p i) := fun j => by
  rw [finsetSum_coeff]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => h i hi j

theorem sum_eq_of_mem_support {n d : ℕ} {R : Type} [CommRing R] {f : MvPolynomial (Fin n) R}
    (hf : f.IsHomogeneous d) {s : Fin n →₀ ℕ} (hs : s ∈ f.support) : ∑ i, s i = d := by
  have h := hf (MvPolynomial.mem_support_iff.1 hs)
  rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp

theorem coeffHom_eval₂ {n d : ℕ} {f : MvPolynomial (Fin n) k[X]} (hf : f.IsHomogeneous d)
    (y : Fin n → (MvPolynomial σ k)[X]) (hy : ∀ i, CoeffHom 1 (y i)) :
    CoeffHom d (MvPolynomial.eval₂ (mapRingHom (MvPolynomial.C : k →+* MvPolynomial σ k)) y f) := by
  rw [MvPolynomial.eval₂_eq']
  refine CoeffHom.sum _ _ _ fun s hs => ?_
  have h := (coeffHom_map (σ := σ) (MvPolynomial.coeff s f)).mul
    (CoeffHom.prod Finset.univ (fun i => s i) (fun i => y i ^ s i) fun i => (hy i).pow _)
  rwa [zero_add, sum_eq_of_mem_support hf hs] at h

theorem natDegree_eval_le {n d N D : ℕ} {f : MvPolynomial (Fin n) k[X]} (hf : f.IsHomogeneous d)
    (hD : ∀ s ∈ f.support, (MvPolynomial.coeff s f).natDegree ≤ D)
    (x : Fin n → k[X]) (hx : ∀ i, (x i).natDegree ≤ N) :
    (MvPolynomial.eval x f).natDegree ≤ D + d * N := by
  rw [MvPolynomial.eval_eq']
  refine natDegree_sum_le_of_forall_le _ _ fun s hs => natDegree_mul_le.trans ?_
  refine add_le_add (hD s hs) ((natDegree_prod_le _ _).trans ?_)
  rw [← sum_eq_of_mem_support hf hs, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hx i))

end TsenCount

open Polynomial TsenCount in

theorem exists_nonzero_zero_polynomial_of_isAlgClosed (k : Type) [Field k] [IsAlgClosed k] (n d : ℕ)
    (f : MvPolynomial (Fin n) (Polynomial k)) (hf : f.IsHomogeneous d) (hd : 0 < d) (hn : d < n) :
    ∃ x : Fin n → Polynomial k, x ≠ 0 ∧ MvPolynomial.eval x f = 0 := by
  classical
  obtain ⟨D, hD⟩ : ∃ D, ∀ s ∈ f.support, (MvPolynomial.coeff s f).natDegree ≤ D :=
    ⟨f.support.sup fun s => (MvPolynomial.coeff s f).natDegree, fun s hs =>
      Finset.le_sup (f := fun s => (MvPolynomial.coeff s f).natDegree) hs⟩
  let y : Fin n → (MvPolynomial (Fin (n * (D + 1))) k)[X] := fun i =>
    ∑ m : Fin (D + 1), monomial (m : ℕ) (MvPolynomial.X (finProdFinEquiv (i, m)))
  have hy : ∀ i, CoeffHom 1 (y i) := fun i => CoeffHom.sum _ _ _ fun m _ j => by
    rw [coeff_monomial]
    split_ifs
    · exact MvPolynomial.isHomogeneous_X _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  have hP := coeffHom_eval₂ hf y hy
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.exists_ne_zero_common_zero_of_isHomogeneous' k (n * (D + 1)) (D + d * D + 1)
    (fun j => (MvPolynomial.eval₂ (mapRingHom MvPolynomial.C) y f).coeff j)
    (fun j => ⟨d, hd, hP j⟩) (by nlinarith)
  let x : Fin n → k[X] := fun i => (y i).map (MvPolynomial.eval c)
  have hx : ∀ i, x i = ∑ m : Fin (D + 1), monomial (m : ℕ) (c (finProdFinEquiv (i, m))) := fun i => by
    simp [x, y, Polynomial.map_sum]
  have hdeg : ∀ i, (x i).natDegree ≤ D := fun i => by
    rw [hx]
    exact natDegree_sum_le_of_forall_le _ _ fun m _ =>
      (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 m.2)
  have hev : MvPolynomial.eval x f =
      (MvPolynomial.eval₂ (mapRingHom MvPolynomial.C) y f).map (MvPolynomial.eval c) := by
    rw [← coe_mapRingHom, MvPolynomial.eval₂_comp_left, mapRingHom_comp]
    have : (MvPolynomial.eval c).comp (MvPolynomial.C : k →+* MvPolynomial (Fin (n * (D + 1))) k)
        = RingHom.id k := by ext; simp
    rw [this, mapRingHom_id]
    rfl
  refine ⟨x, fun h0 => hc0 ?_, ?_⟩
  · funext a
    obtain ⟨⟨i, m⟩, rfl⟩ := finProdFinEquiv.surjective a
    have h1 : (x i).coeff m = 0 := by rw [h0]; simp
    rw [hx, finsetSum_coeff, Finset.sum_eq_single m] at h1
    · simpa using h1
    · intro b _ hb
      rw [coeff_monomial, if_neg fun h => hb (Fin.ext h)]
    · simp
  · ext j
    rw [coeff_zero]
    by_cases hj : j < D + d * D + 1
    · rw [hev, coeff_map]
      exact hc ⟨j, hj⟩
    · exact coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_eval_le hf hD x hdeg) (by omega))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRadiusMoebiusPerturbationUpperHalfPlane
section
namespace GlobalTheory.HilbFam

theorem exists_radius_moebius_perturbation :
    ∀ (τ c t : ℂ), 0 < τ.im → ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      1 / 2 ≤ ‖1 + z * c‖ ∧ τ.im / 2 ≤ (τ + t * z / (1 + z * c)).im := by
  intro τ c t hτ
  have h1 : ContinuousAt (fun z : ℂ => ‖1 + z * c‖) 0 := by fun_prop
  have h2' : ContinuousAt (fun z : ℂ => τ + t * z / (1 + z * c)) 0 := by
    refine continuousAt_const.add (ContinuousAt.div (by fun_prop) (by fun_prop) (by simp))
  have h2 : ContinuousAt (fun z : ℂ => (τ + t * z / (1 + z * c)).im) 0 :=
    Complex.continuous_im.continuousAt.comp h2'
  have e1 : ∀ᶠ z in nhds (0 : ℂ), (1 / 2 : ℝ) < ‖1 + z * c‖ :=
    h1.eventually (lt_mem_nhds (by norm_num))
  have e2 : ∀ᶠ z in nhds (0 : ℂ), τ.im / 2 < (τ + t * z / (1 + z * c)).im :=
    h2.eventually (lt_mem_nhds (by simp; linarith))
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  refine ⟨r, hr, fun z hz => ?_⟩
  have := h (y := z) (by simpa using hz)
  exact ⟨this.1.le, this.2.le⟩

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecVectorFieldOfDualNumberSection
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS

noncomputable section

namespace GlobalTheory.SpecField

open AlgebraicGeometry

variable {A : Type} [CommRing A]

theorem dualMap_fst {B : Type} [CommRing B] (f : A →+* B) (x : DualNumber A) :
    (Formalism.L2.Pj.dualMap f x).fst = f x.fst := by
  simp [Formalism.L2.Pj.dualMap]

theorem dualMap_snd {B : Type} [CommRing B] (f : A →+* B) (x : DualNumber A) :
    (Formalism.L2.Pj.dualMap f x).snd = f x.snd := by
  simp [Formalism.L2.Pj.dualMap]

variable (σ : A →+* DualNumber A) (hσ : ∀ a, (σ a).fst = a) (S : Submonoid A)

def liftLoc : LocalizedModule S A →+* DualNumber (LocalizedModule S A) :=
  IsLocalization.lift (M := S) (g := (Formalism.L2.Pj.dualMap (algebraMap A (LocalizedModule S A))).comp σ)
    (fun y => by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, RingHom.comp_apply, dualMap_fst, hσ]
      exact IsLocalization.map_units _ y)

theorem liftLoc_algebraMap (a : A) :
    liftLoc σ hσ S (algebraMap A _ a) = Formalism.L2.Pj.dualMap (algebraMap A (LocalizedModule S A)) (σ a) :=
  IsLocalization.lift_eq _ _

theorem liftLoc_fst (b : LocalizedModule S A) : (liftLoc σ hσ S b).fst = b := by
  have h : ((TrivSqZeroExt.fstHom (LocalizedModule S A) (LocalizedModule S A) (LocalizedModule S A)).toRingHom.comp
      (liftLoc σ hσ S)) = RingHom.id _ :=
    IsLocalization.ringHom_ext S (RingHom.ext fun a => by
      simp [liftLoc_algebraMap, dualMap_fst, hσ])
  exact congrArg (fun φ => φ b) h

def dloc (b : LocalizedModule S A) : LocalizedModule S A := (liftLoc σ hσ S b).snd

theorem dloc_add (b b' : LocalizedModule S A) : dloc σ hσ S (b + b') = dloc σ hσ S b + dloc σ hσ S b' := by
  simp [dloc]

theorem dloc_mul (b b' : LocalizedModule S A) :
    dloc σ hσ S (b * b') = b * dloc σ hσ S b' + b' * dloc σ hσ S b := by
  simp only [dloc, map_mul, TrivSqZeroExt.snd_mul, liftLoc_fst, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  ring

theorem dloc_algebraMap (a : A) : dloc σ hσ S (algebraMap A _ a) = algebraMap A _ (σ a).snd := by
  simp [dloc, liftLoc_algebraMap, dualMap_snd]

theorem mk_mul_algebraMap (m : A) (u : S) :
    LocalizedModule.mk m u * algebraMap A (LocalizedModule S A) u = algebraMap A _ m := by
  rw [show algebraMap A (LocalizedModule S A) u = LocalizedModule.mk (u : A) 1 from rfl]
  erw [LocalizedModule.mk_mul_mk]
  rw [show algebraMap A (LocalizedModule S A) m = LocalizedModule.mk m 1 from rfl, LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def, smul_eq_mul]; ring⟩

theorem dloc_mk (r : A) (t : S) :
    dloc σ hσ S (LocalizedModule.mk r t) =
      LocalizedModule.mk (t * (σ r).snd - r * (σ t).snd) (t * t) := by
  have h1 := mk_mul_algebraMap S r t
  have h2 := congrArg (dloc σ hσ S) h1
  rw [dloc_mul, dloc_algebraMap, dloc_algebraMap] at h2
  have hu : IsUnit (algebraMap A (LocalizedModule S A) ((t * t : S) : A)) := IsLocalization.map_units _ (t * t)
  refine (hu.mul_left_inj).1 ?_
  rw [mk_mul_algebraMap]
  simp only [Submonoid.coe_mul, map_mul, map_sub]
  linear_combination (algebraMap A (LocalizedModule S A) t) * h2 -
    (algebraMap A (LocalizedModule S A) (σ t).snd) * h1

def dsec (O : (Sp A).Opens) (s : Γ(Sp A, O)) : Γ(Sp A, O) :=
  ⟨fun x => dloc σ hσ _ (s.1 x), fun x => by
    obtain ⟨V, hxV, i, r, t, w⟩ := s.2 x
    refine ⟨V, hxV, i, t * (σ r).snd - r * (σ t).snd, t * t, fun y => ?_⟩
    obtain ⟨ht, hs⟩ := w y
    refine ⟨fun h => ((PrimeSpectrum.isPrime (y.1 : PrimeSpectrum A)).mem_or_mem h).elim ht ht, ?_⟩
    exact (congrArg (dloc σ hσ _) hs).trans (dloc_mk σ hσ _ r ⟨t, ht⟩)⟩

theorem isField_dsec : IsField ⊤ (dsec σ hσ) :=
  ⟨fun _ _ f f' => Subtype.ext (funext fun x => dloc_add σ hσ _ (f.1 x) (f'.1 x)),
    fun _ _ f f' => Subtype.ext (funext fun x => dloc_mul σ hσ _ (f.1 x) (f'.1 x)),
    fun _ _ _ _ _ => rfl⟩

theorem dsec_top (a : A) :
    dsec σ hσ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd :=
  Subtype.ext (funext fun x => dloc_algebraMap σ hσ _ a)

end GlobalTheory.SpecField

theorem GlobalTheory.SpecField.exists_isField (A : Type) [CommRing A] (σ : A →+* DualNumber A) (hσ : ∀ a, (σ a).fst = a) :
    ∃ d : ∀ O : (Sp A).Opens, Γ(Sp A, O) → Γ(Sp A, O), IsField ⊤ d ∧
      ∀ a : A, d ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd :=
  ⟨GlobalTheory.SpecField.dsec σ hσ, GlobalTheory.SpecField.isField_dsec σ hσ, GlobalTheory.SpecField.dsec_top σ hσ⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevel
section
set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

variable {F : Type} [Field F] [NumberField F]

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in

theorem _root_.GlobalTheory.HilbFam.exists_eq_split_of_hasLevel (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (hN : 0 < N) (hL : _root_.GlobalTheory.HilbFam.HasLevel N L) :
    ∃ (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (x : F), L = _root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x := by
  obtain ⟨hNL, hLstd⟩ := hL
  have hLint : ∀ v ∈ L, ∀ i, v i ∈ (1 : Submodule (𝓞 F) F) := fun v hv i =>
    (Submodule.mem_pi.1 (hLstd hv)) i (Set.mem_univ i)
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hsingle : ∀ i, Pi.single i (N : F) ∈ L := by
    intro i
    have hstd : (Pi.single i (1 : F) : Fin 2 → F) ∈ _root_.GlobalTheory.HilbFam.stdLat F := by
      refine Submodule.mem_pi.2 fun j _ => ?_
      by_cases hj : j = i
      · subst hj; simpa using (1 : Submodule (𝓞 F) F).one_le.1 le_rfl
      · simp [hj]
    have := hNL _ hstd
    convert this using 1
    ext j
    by_cases hj : j = i
    · subst hj
      simp [Algebra.smul_def]
    · simp [hj]
  let B0 : Submodule (𝓞 F) F := L.map (LinearMap.proj (R := 𝓞 F) (φ := fun _ : Fin 2 => F) 0)
  let C0 : Submodule (𝓞 F) F := L.comap (LinearMap.single (𝓞 F) (fun _ : Fin 2 => F) 1)
  have hB0 : B0 ≤ 1 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hLint v hv 0
  have hC0 : C0 ≤ 1 := by
    intro c hc
    simpa using hLint _ hc 1
  let Bf : FractionalIdeal (𝓞 F)⁰ F := ⟨B0, FractionalIdeal.isFractional_of_le_one B0 hB0⟩
  let Cf : FractionalIdeal (𝓞 F)⁰ F := ⟨C0, FractionalIdeal.isFractional_of_le_one C0 hC0⟩
  have hBne : Bf ≠ 0 := by
    intro h
    have hmem : (N : F) ∈ Bf := by
      show (N : F) ∈ B0
      exact ⟨_, hsingle 0, by simp⟩
    rw [h] at hmem
    exact hN0 ((FractionalIdeal.mem_zero_iff _).1 hmem)
  have hCne : Cf ≠ 0 := by
    intro h
    have hmem : (N : F) ∈ Cf := by
      show Pi.single 1 (N : F) ∈ L
      exact hsingle 1
    rw [h] at hmem
    exact hN0 ((FractionalIdeal.mem_zero_iff _).1 hmem)
  have key : ∀ t ∈ (Bf : Submodule (𝓞 F) F) * ((Bf⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F),
      ∃ y : F, ∀ b ∈ Bf, (![t * b, y * b] : Fin 2 → F) ∈ L := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b' hb' c hc
      obtain ⟨w, hw, hw0⟩ := (show b' ∈ B0 from hb')
      refine ⟨c * w 1, fun b hb => ?_⟩
      have hcb : c * b ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [← inv_mul_cancel₀ hBne]
        exact FractionalIdeal.mul_mem_mul hc hb
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hcb
      convert L.smul_mem r hw using 1
      ext i
      fin_cases i
      · simp [Algebra.smul_def, hr, ← hw0]
        ring
      · simp [Algebra.smul_def, hr]
        ring
    · rintro t₁ t₂ ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩
      refine ⟨y₁ + y₂, fun b hb => ?_⟩
      convert L.add_mem (hy₁ b hb) (hy₂ b hb) using 1
      ext i
      fin_cases i <;> simp <;> ring
  have h1 : (1 : F) ∈ (Bf : Submodule (𝓞 F) F) *
      ((Bf⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hBne]
    exact FractionalIdeal.one_mem_one _
  obtain ⟨x, hx⟩ := key 1 h1
  refine ⟨Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne),
    Units.mk0 Bf hBne, x, ?_⟩
  have hlat : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
      (Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne)) = Cf := by
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, Units.val_mk0, FractionalIdeal.dual_dual]
  ext v
  unfold _root_.GlobalTheory.HilbFam.split
  rw [Submodule.mem_mk]
  change v ∈ L ↔ v 0 ∈ ((Units.mk0 Bf hBne : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ∧
    v 1 - v 0 * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
      (Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne))
  rw [hlat, Units.val_mk0]
  change v ∈ L ↔ v 0 ∈ B0 ∧ Pi.single 1 (v 1 - v 0 * x) ∈ L
  constructor
  · intro hv
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    convert L.sub_mem hv (hx (v 0) ⟨v, hv, rfl⟩) using 1
    ext i
    fin_cases i <;> simp <;> ring
  · rintro ⟨hb, hc⟩
    convert L.add_mem (hx (v 0) hb) hc using 1
    ext i
    fin_cases i <;> simp <;> ring

end GlobalTheory.HilbFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFiniteEtaleGaloisCoverLadic
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TrGal

open GlobalTheory.EtC.Tr GlobalTheory.EtC.TrDeg

variable (R : Type) [CommRing R]

theorem splitBy_of_equiv {Y X V : Scheme.{0}} (f : Y ⟶ X) (y : V ⟶ X) {G : Type} {m : ℕ} (e : Fin m ≃ G)
    (a : G → (V ⟶ Y)) (ha : ∀ g, a g ≫ f = y)
    (h : IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 V) (by rw [ha g, Category.id_comp])) :
      ∐ (fun _ : G => V) ⟶ pullback f y)) : SplitBy f y (fun j => a (e j)) := by
  refine ⟨fun j => ha _, ?_⟩
  let w : ∐ (fun _ : Fin m => V) ≅ ∐ (fun _ : G => V) := Sigma.reindex e (fun _ : G => V)
  have hw : ∀ j, Sigma.ι (fun _ : Fin m => V) j ≫ w.hom = Sigma.ι (fun _ : G => V) (e j) := fun j =>
    Sigma.ι_reindex_hom e (fun _ : G => V) j
  convert (inferInstance : IsIso (w.hom ≫ (Sigma.desc (fun g => pullback.lift (a g) (𝟙 V) (by rw [ha g, Category.id_comp])) :
      ∐ (fun _ : G => V) ⟶ pullback f y)))
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_desc, reassoc_of% (hw j), Sigma.ι_desc]

theorem along_sum {X Y : Scheme.{0}} (F : Shv R) (n : ℤ) {ι : Type} (s : Finset ι) (t : ι → (freeSch R X ⟶ freeSch R Y))
    (x : H R (sch.obj Y) F n) : along R F n (∑ j ∈ s, t j) x = ∑ j ∈ s, along R F n (t j) x :=
  map_sum (AddMonoidHom.mk' (fun u : freeSch R X ⟶ freeSch R Y => along R F n u x) (fun u v => along_add R F n u v x)) t s

theorem pull_trH {Y X V : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] {y : V ⟶ X} {m : ℕ}
    {s : Fin m → (V ⟶ Y)} (hs : SplitBy f y s) (F : Shv R) (n : ℤ) (x : H R (sch.obj Y) F n) :
    pull R (sch.map y) F n (trH R f F n x) = ∑ j, pull R (sch.map (s j)) F n x := by
  rw [trH, ← along_free, ← along_comp,
    (transfer_spec R (existsUnique_isTransfer R f).exists).apply_of_splitBy R hs, along_sum]
  simp only [along_free]

theorem exists_trace_galois : ∀ (l : ℕ) [Fact l.Prime] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Etale f] [Surjective f] (G : Type) [Fintype G]
  (a : G → (Y ⟶ Y)) (ha : ∀ g, a g ≫ f = f),
  IsIso (Sigma.desc (fun g => pullback.lift (a g) (𝟙 Y) (by rw [ha g, Category.id_comp])) : ∐ (fun _ : G => Y) ⟶ pullback f f) → ∀ n i : ℤ, ∃ tr : Hl l (sch.obj Y) n i →ₗ[ℤ_[l]] Hl l (sch.obj X) n i,
  (∀ x, tr (pullHl l (sch.map f) n i x) = Fintype.card G • x) ∧ ∀ y, pullHl l (sch.map f) n i (tr y) = ∑ g, pullHl l (sch.map (a g)) n i y := by
  intro l _ Y X f _ _ _ G _ a ha hiso n i
  have hs := splitBy_of_equiv f f (Fintype.equivFin G).symm a ha hiso
  have h := trHl_spec l (redCompat_of_finite_etale l f (fun R _ => existsUnique_isTransfer R f) n i)
  refine ⟨trHl l f n i, fun x => Subtype.ext (funext fun k => ?_), fun y => Subtype.ext (funext fun k => ?_)⟩
  · exact (h _ k).trans (trH_pull (ZMod (l ^ k)) f hs (tw (l ^ k) i) n (x.1 k))
  · rw [← Equiv.sum_comp (Fintype.equivFin G).symm, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    exact (congrArg (pull (ZMod (l ^ k)) (sch.map f) (tw (l ^ k) i) n) (h y k)).trans
      (pull_trH (ZMod (l ^ k)) f hs (tw (l ^ k) i) n (y.1 k))

end GlobalTheory.EtC.TrGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypicalCurveBasisAdaptedToSaturatedFrameStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_typicalCurve_basis_adapted_to_saturated_frame : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (τ : ZMod h) (j i : ℕ), (Finset.univ.filter fun a => ty a = τ + 1).card ≤ j → ∀ u : Fin i → Fin d → C, IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) → ∃ (γ : Fin d → Fin d → PowerSeries C) (r : Fin i ↪ Fin d) (g : Matrix (Fin i) (Fin i) C), IsBasis G p ty γ ∧ (∀ a b, IsIntV v (g a b)) ∧ v g.det = 0 ∧ (∀ a, tangent (γ (r a)) = ∑ a', g a a' • u a') ∧ ∀ a : Fin i, j ≤ a.val → G.lc p (γ (r a)) 1 = 0 := by
  first | exact @GlobalTheory.FGDepth.exists_basis_adapted_frame | exact GlobalTheory.FGDepth.exists_basis_adapted_frame | (intros; apply GlobalTheory.FGDepth.exists_basis_adapted_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldAffineOpenTransport
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS

namespace GlobalTheory.FieldTransport

theorem exists_isField_transport : ∀ (Z : Scheme.{0}) (W : Z.Opens) (hW : IsAffineOpen W) (δ : Γ(Z, W) → Γ(Z, W)) (d' : ∀ O : (Spec Γ(Z, W)).Opens, Γ(Spec Γ(Z, W), O) → Γ(Spec Γ(Z, W), O)), IsField ⊤ d' → (∀ a, d' ⊤ ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom a) = (Scheme.ΓSpecIso Γ(Z, W)).inv.hom (δ a)) → ∃ d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField W d ∧ ∀ a, d W a = δ a := by
  intro Z W hW δ d' hd hδ
  classical
  have hiso : ∀ O : Z.Opens, O ≤ W → IsIso (hW.fromSpec.app O) := fun O h =>
    hW.fromSpec.isIso_app O (by rwa [hW.opensRange_fromSpec])
  let e : ∀ O : Z.Opens, O ≤ W → Γ(Z, O) ≃+* Γ(Spec Γ(Z, W), hW.fromSpec ⁻¹ᵁ O) := fun O h =>
    haveI := hiso O h; (asIso (hW.fromSpec.app O)).commRingCatIsoToRingEquiv
  have he : ∀ O (h : O ≤ W) f, e O h f = (hW.fromSpec.app O).hom f := fun _ _ _ => rfl
  have hres : ∀ O O' (h : O' ≤ O) (f : Γ(Z, O)),
      (hW.fromSpec.app O').hom (resG Z h f) =
        resG (Spec Γ(Z, W)) (hW.fromSpec.preimage_mono h) ((hW.fromSpec.app O).hom f) := by
    intro O O' h f
    have := congrArg (fun g => g.hom f) (hW.fromSpec.naturality (homOfLE h).op)
    simpa [resG] using this
  refine ⟨fun O f => if h : O ≤ W then (e O h).symm (d' (hW.fromSpec ⁻¹ᵁ O) (e O h f)) else 0,
    ⟨?_, ?_, ?_⟩, ?_⟩
  · intro O h f f'
    simp only [dif_pos h, map_add, hd.1 _ le_top]
  · intro O h f f'
    simp only [dif_pos h, map_mul, hd.2.1 _ le_top, map_add, RingEquiv.symm_apply_apply]
  · intro O O' h hO f
    have hO' : O' ≤ W := h.trans hO
    simp only [dif_pos hO, dif_pos hO']
    apply (e O' hO').injective
    simp only [RingEquiv.apply_symm_apply, he O' hO', hres]
    rw [← he O hO, ← he O hO, RingEquiv.apply_symm_apply, hd.2.2 _ _ _ le_top]
    exact (e O' hO').apply_symm_apply _
  · intro a
    simp only [dif_pos (le_refl W)]
    apply (e W (le_refl W)).symm_apply_eq.mpr
    have hs : hW.fromSpec ⁻¹ᵁ W ≤ ⊤ := le_top
    have key : ∀ x, e W (le_refl W) x = resG (Spec Γ(Z, W)) hs ((Scheme.ΓSpecIso Γ(Z, W)).inv.hom x) := by
      intro x
      rw [he W (le_refl W), IsAffineOpen.fromSpec_app_self, CommRingCat.comp_apply]
      rfl
    rw [key, key, hd.2.2 _ _ hs le_rfl, hδ]

end GlobalTheory.FieldTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodTorsorModelOfFilteredColimitStatement
section
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)), GlobalTheory.LocAcyc.IsZModTorsor c.pt D q act →
    ∃ (j : J), letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
    ∃ (Dj : Type) (_ : CommRing Dj) (_ : Algebra (F.obj j) Dj)
      (actj : Multiplicative (ZMod q) →* (Dj ≃ₐ[F.obj j] Dj)),
      GlobalTheory.LocAcyc.IsZModTorsor (F.obj j) Dj q actj ∧
      Nonempty (TensorProduct (F.obj j) c.pt Dj ≃ₐ[c.pt] D) := by
  first | (exact @GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit) | (exact GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit) | (intros; apply GlobalTheory.TorsorColim.exists_torsor_model_of_isColimit  <;> assumption)
end

