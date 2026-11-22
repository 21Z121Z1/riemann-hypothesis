import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeDegreeEqNegLogFrameHeight
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

noncomputable section

namespace GlobalTheory.FrameDeg

theorem form_eq_of_re_diag {K V : Type} [Field K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ)
    (F G : V → V → ℂ)
    (hFa : ∀ x y z, F x (y + z) = F x y + F x z) (hGa : ∀ x y z, G x (y + z) = G x y + G x z)
    (hFs : ∀ (a : K) x y, F x (a • y) = σ a * F x y) (hGs : ∀ (a : K) x y, G x (a • y) = σ a * G x y)
    (hFc : ∀ x y, starRingEnd ℂ (F x y) = F y x) (hGc : ∀ x y, starRingEnd ℂ (G x y) = G y x)
    (hd : ∀ x, (F x x).re = (G x x).re) (ha : ∃ a : K, (σ a).im ≠ 0) (x y : V) : F x y = G x y := by
  have hFl : ∀ x x' y, F (x + x') y = F x y + F x' y := by
    intro x x' y
    rw [← hFc y (x + x'), hFa, map_add, hFc, hFc]
  have hGl : ∀ x x' y, G (x + x') y = G x y + G x' y := by
    intro x x' y
    rw [← hGc y (x + x'), hGa, map_add, hGc, hGc]
  have hre : ∀ x y, (F x y).re = (G x y).re := by
    intro x y
    have h1 := hd (x + y)
    rw [hFl, hFa, hFa, hGl, hGa, hGa, ← hFc x y, ← hGc x y] at h1
    simp only [Complex.add_re, Complex.conj_re] at h1
    linarith [hd x, hd y]
  obtain ⟨a, ha⟩ := ha
  have h2 := hre x (a • y)
  rw [hFs, hGs, Complex.mul_re, Complex.mul_re, hre x y] at h2
  have him : (F x y).im = (G x y).im := by
    have : (σ a).im * (F x y).im = (σ a).im * (G x y).im := by linarith
    exact mul_left_cancel₀ ha this
  exact Complex.ext (hre x y) him

section Maj

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem majAt_add_right (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y z : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (y + z) = Formalism.HermitianLatticesTheory.majAt b X v x y + Formalism.HermitianLatticesTheory.majAt b X v x z := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem majAt_smul_right (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (a • y) = v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  have hv : Formalism.HermitianLatticesTheory.vecAt b v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v y := by
    funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem majAt_conj (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) :
    starRingEnd ℂ (Formalism.HermitianLatticesTheory.majAt b X v x y) = Formalism.HermitianLatticesTheory.majAt b X v y x := by
  simp only [Formalism.HermitianLatticesTheory.majAt, map_sum, map_mul, Complex.star_def, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem majAt_self_re (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x : V) :
    (Formalism.HermitianLatticesTheory.majAt b X v x x).re = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (by positivity)]
  simp only [Formalism.HermitianLatticesTheory.majAt, Complex.re_sum, Complex.star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  ring

end Maj

theorem form_self_re_nonneg {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (x : V) : 0 ≤ (nm.form σ x x).re := by
  by_cases hx : x = 0
  · subst hx
    have h0 : nm.form σ 0 0 = 0 := by
      have := nm.add_right σ 0 0 0
      simp only [add_zero] at this
      linear_combination -this
    simp [h0]
  · have hli : LinearIndependent K ![x] := by
      rw [linearIndependent_unique_iff]; simpa using hx
    have hp := (nm.posDef σ 1 ![x] hli).det_pos
    rw [Matrix.det_unique] at hp
    simpa using (Complex.pos_iff.1 hp).1.le

theorem finrank_eq_two_mul_nPl' {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] :
    Module.finrank ℚ K = 2 * Formalism.HN.nPl K := by
  rw [IsTotallyComplex.finrank, Formalism.HN.nPl, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

end GlobalTheory.FrameDeg

namespace GlobalTheory.FrameDeg

theorem deg_eq_neg_log_ht : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [StarRing K] [IsTotallyComplex K] [FiniteDimensional K V] (nm : HermFam K V), nm.IsConjInv → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) → (∀ v x, Formalism.HermitianLatticesTheory.normAt b X v x = nm.nrm v.embedding x) → ∀ L : Submodule (𝓞 K) V, L.FG → deg nm L = -Real.log (Formalism.HN.ht b X L) / (2 * (Formalism.HN.nPl K : ℝ)) := by
  intro K V _ _ _ _ _ _ _ _ _ nm hinv ι _ _ b X hX hnorm L hL
  classical

  have hform : ∀ (v : InfinitePlace K) (x y : V),
      Formalism.HermitianLatticesTheory.majAt b X v x y = nm.form v.embedding x y := by
    intro v
    refine form_eq_of_re_diag v.embedding _ _ (majAt_add_right b X v) (nm.add_right _)
      (majAt_smul_right b X v) (nm.smul_right _) (majAt_conj b X v) (nm.conj_symm _) ?_ ?_
    · intro x
      rw [majAt_self_re, hnorm, HermFam.nrm, Real.sq_sqrt (form_self_re_nonneg nm _ x)]
    · have hc : v.IsComplex := IsTotallyComplex.isComplex v
      rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hc
      by_contra hall
      push_neg at hall
      apply hc
      ext a
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_eq_iff_im.mpr (hall a)
  obtain ⟨e, he⟩ := exists_isFrame L hL
  have hdeg := arakelovDegree_eq_degreeOfFamily nm hL he
  obtain ⟨hS, hSL⟩ := Formalism.HN.htGram K V ι b X hX _ e he.2.1
  have hle : Submodule.span (𝓞 K) (Set.range e) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact he.1 i)
  have hidx := hSL L hL hle rfl
  have hne := he.relIndex_ne_zero hL
  have hgram : ∀ v, Formalism.HN.gramPl b X v e = nm.gram v.embedding e := by
    intro v; ext a c; simp [Formalism.HN.gramPl, HermFam.gram, hform]
  have hpos : ∀ σ, 0 < (nm.gram σ e).det.re := fun σ =>
    (Complex.pos_iff.1 (Matrix.PosDef.det_pos (nm.posDef σ _ e he.2.1))).1
  have hsum : ∑ σ : K →+* ℂ, Real.log (nm.gram σ e).det.re =
      2 * ∑ w : InfinitePlace K, Real.log (nm.gram w.embedding e).det.re := by
    rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hc : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w),
        Real.log (nm.gram σ e).det.re = Real.log (nm.gram w.embedding e).det.re := by
      intro σ hσ
      rw [Finset.mem_filter] at hσ
      rcases InfinitePlace.mk_eq_iff.mp (hσ.2.trans (InfinitePlace.mk_embedding w).symm) with h | h
      · rw [h]
      · rw [← h, det_gram_conj_re nm hinv]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
      (IsTotallyComplex.isComplex w).mult_eq_two, nsmul_eq_mul]
    push_cast; ring
  have hprod : 0 < ∏ w : InfinitePlace K, (nm.gram w.embedding e).det.re :=
    Finset.prod_pos fun w _ => hpos _
  have hidx' : (0 : ℝ) < ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex
      L.toAddSubgroup : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne
  have hht : Formalism.HN.ht b X L = (∏ w : InfinitePlace K, (nm.gram w.embedding e).det.re) /
      ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := by
    rw [eq_div_iff hidx'.ne', hidx, hS]
    exact Finset.prod_congr rfl fun w _ => by rw [hgram]
  rw [hdeg, degreeOfFamily, hsum, finrank_eq_two_mul_nPl', hht, Real.log_div hprod.ne' hidx'.ne',
    Real.log_prod (fun w _ => (hpos _).ne')]
  push_cast
  ring

end GlobalTheory.FrameDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.ProjLift

theorem exists_factor {A B X I : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup X] [Module ℂ X]
    (L₁ : A →ₗ[ℂ] X) (L₂ : B →ₗ[ℂ] X) (j : I → B) (hj : Submodule.span ℂ (Set.range j) = ⊤) (h : ∀ x, ∃ t, L₁ t = L₂ (j x)) :
    ∃ φ : B →ₗ[ℂ] A, ∀ y, L₁ (φ y) = L₂ y := by
  have h1 : ∀ y, L₂ y ∈ LinearMap.range L₁ := fun y =>
    (Submodule.span_le (p := (LinearMap.range L₁).comap L₂)).2 (by rintro _ ⟨x, rfl⟩; exact h x) (hj.ge Submodule.mem_top)
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property L₁.rangeRestrict (L₂.codRestrict _ h1) L₁.surjective_rangeRestrict
  exact ⟨φ, fun y => congrArg Subtype.val (LinearMap.congr_fun hφ y)⟩

section Low

open Matrix Formalism.MainNotions.S GlobalTheory.DefLift

variable {D : D7}

open Classical in

theorem eq_on_low {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ)
    {U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M} (hU : KEquiv θ M U) (e : ∀ τ, lowT M τ) (he : ∀ τ, e τ ≠ 0)
    (h : T (fun τ => (e τ : M.sm τ)) = U e) (v : ∀ τ, lowT M τ) : T (fun τ => (v τ : M.sm τ)) = U v := by
  have hT' : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ (v : M.Vec) (w : M.sm τ),
      (w : M.H τ) = M.rep τ g (v τ) → T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
    intro τ g hg v w hw
    clear h
    induction hT using Submodule.span_induction with
    | mem T hT => exact hT.equiv τ g hg v w hw
    | zero => rfl
    | add x y _ _ hx hy => exact (congrArg₂ (· + ·) hx hy).trans rfl
    | smul a x _ hx => exact (congrArg (a • ·) hx).trans rfl
  have key := mem_of_translates h1 h2 (T.compLinearMap (fun τ => (lowT M τ).subtype) - U) ⊥ e he
    (by simpa [sub_eq_zero] using h) (fun τ k hk v u hu hv => ?_) v
  · simpa [sub_eq_zero] using key
  · have hv' : T (fun τ => (v τ : M.sm τ)) = U v := by simpa [sub_eq_zero] using hv
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
      have e1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
      change ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D V τ
      calc ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D V τ * ((M.fr τ)⁻¹ * k * M.fr τ)
          = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
              M.fr τ := by
            rw [← M.fr_gram τ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D V τ := by rw [e1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk', M.fr_gram]
    have e2 : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hd, Matrix.mul_one]
    have e3 := hT' τ _ hg (fun τ => (v τ : M.sm τ)) (u : M.sm τ) (by
      rw [hu, DSModel.rep, e2])
    have e4 : (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) =
        Function.update (fun ρ => (v ρ : M.sm ρ)) τ (u : M.sm τ) :=
      funext fun ρ => Function.apply_update (fun ρ (y : lowT M ρ) => (y : M.sm ρ)) v τ u ρ
    have e5 : T (fun ρ => ((Function.update v τ u ρ : lowT M ρ) : M.sm ρ)) = U (Function.update v τ u) := by
      rw [e4, e3, hv', hU τ k hk v u hu]
    simpa [sub_eq_zero] using e5

theorem kEquiv_thetaP {θ : InfFam D} {V W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {c : CoefA V}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {pt : PolF D W.rank V.rank → (WO V W → ℂ)}
    {Δ : PolF D W.rank V.rank} {io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D W.rank V.rank} (hio : IsIoW θ M c ω pt Δ io)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} {B : Submodule ℂ (GA D V → c.W)}
    {thP : B →ₗ[ℂ] (LowT M →ₗ[ℂ] (GA D W → ℂ))}
    (hth : Lift.IsThetaP ν 𝓕 (fun g h φ => thetaKO ω h g φ) pt io B thP) (y : B) :
    KEquiv θ M ((thP y).compMultilinearMap (PiTensorProduct.tprod ℂ)) := by
  intro τ k hk v u hu
  have hmul : ∀ h g k φ, thetaKO ω h (g * k) φ = thetaKO ω h g (ω (1, k) φ) := fun h g k φ => by
    unfold thetaKO
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  funext g
  simp only [LinearMap.compMultilinearMap_apply, rTr, hth.eq, Lift.thetaPInt, hmul, hio.2.1 τ k hk v u hu]

theorem exists_lift {θ : InfFam D} {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} (h1 : LowSm M)
    (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) {J : Set (GA D W)} {χ : GA D W → ℂ} {A B I : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (e : A →ₗ[ℂ] MMap M) (he : ∀ t, e t ∈ Mult θ M J χ)
    (L : B →ₗ[ℂ] (LowT M →ₗ[ℂ] (GA D W → ℂ)))
    (hL : ∀ y, KEquiv θ M ((L y).compMultilinearMap (PiTensorProduct.tprod ℂ))) (j : I → B)
    (hj : Submodule.span ℂ (Set.range j) = ⊤) (v : ∀ τ, lowT M τ) (hv : ∀ τ, v τ ≠ 0)
    (h : ∀ x, ∃ t, e t (fun τ => (v τ : M.sm τ)) = L (j x) (PiTensorProduct.tprod ℂ v)) :
    ∃ φ : B →ₗ[ℂ] A, ∀ y (u : ∀ τ, lowT M τ), e (φ y) (fun τ => (u τ : M.sm τ)) = L y (PiTensorProduct.tprod ℂ u) := by
  let L₁ : A →ₗ[ℂ] ((∀ τ, lowT M τ) → GA D W → ℂ) :=
    { toFun := fun t u => e t (fun τ => (u τ : M.sm τ))
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun a b => by rw [map_smul]; rfl }
  let L₂ : B →ₗ[ℂ] ((∀ τ, lowT M τ) → GA D W → ℂ) :=
    { toFun := fun y u => L y (PiTensorProduct.tprod ℂ u)
      map_add' := fun a b => by rw [map_add]; rfl
      map_smul' := fun a b => by rw [map_smul]; rfl }
  obtain ⟨φ, hφ⟩ := exists_factor L₁ L₂ j hj fun x => (h x).imp fun t ht =>
    funext fun u => eq_on_low h1 h2 (he t) (hL (j x)) v hv ht u
  exact ⟨φ, fun y u => congrFun (hφ y) u⟩

end Low

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem holShape_of_overK (R : RealDat D A Ks) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) :
    GlobalTheory.HolDict.HolShape (R.MW i σ) := by
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    rw [rank_Wc i]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have key : ∀ ρ a, (R.MW i σ).lam ρ a = (Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) a : ℝ) ∧
      (R.MW i σ).ε ρ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun ρ a => by
    have he := (R.MW i σ).enum ρ
    unfold Links.parAt at he
    rw [if_pos (((labels_overK σ).1 hσ).2 ρ)] at he
    rw [← hs ρ]
    exact GlobalTheory.HolDict.isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs ρ]; exact hr) he a
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i σ).lam ρ) := fun ρ => by
    refine ⟨((R.MW i σ).enum ρ).1, fun a => ?_⟩
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) a
    obtain ⟨s, hs'⟩ := Formalism.L2.NTheta.odd_r D.R
    refine ⟨z - s, ?_⟩
    have hn : (((Wc D i).rank : ℕ) : ℝ) = 2 * s + 1 := by rw [rank_Wc i, hs']; push_cast; rfl
    rw [(key ρ a).1, hz, hn]
    push_cast
    ring
  exact fun ρ => ⟨hc ρ, _, by omega, fun a => (key ρ a).2⟩

theorem proj_apply (R : RealDat D A Ks) (hg : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (t : (R.HW i σ).H)
    (v : (R.MW i σ).Vec) :
    (R.HW i σ).e ((∑ g, RealDat.eC (A := A) σ g • R.gW i σ g) t) v = R.eWf i σ ((R.HW i σ).e t v) := by
  simp only [RealDat.eWf, gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply, hg i σ, postOn_apply]
  rfl

set_option maxHeartbeats 1600000 in

theorem exists_isProjOf : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, IsExtVec (R.MW i σ) (fun ρ => v ρ) → (∀ x, ∃ t : (R.HW i σ).H, (R.HW i σ).e t (fun ρ => v ρ) = thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) (PiTensorProduct.tprod ℂ v)) → ∃ th, IsProjOf R i σ thP th := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i gramR c0R c0L hT σ hσ μ' η' c c₁ H j hj ω f₀ f B io thP hL v hv h
  have hspan := GlobalTheory.ConjSpan.span_conjForms R hC.models.jV gramR c0R c0L hT i σ c c₁ H j hj
  have hlow := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (holShape_of_overK R i hσ)
  have he : ∀ τ, v τ ≠ 0 := fun τ h0 => by
    have := (hv τ).1
    simp [h0] at this
  have hex := exists_lift hlow.1 hlow.2 (R.HW i σ).e
    (fun t => (hC.models.HW i σ).2.1.le (LinearMap.mem_range_self _ t)) (thP ∘ₗ (c.ext ∘ₗ H.e).rangeRestrict)
    (fun y => kEquiv_thetaP hL.2.2.1 hL.2.2.2 _) j hspan v he h
  obtain ⟨φ, hφ⟩ := hex
  exact ⟨(∑ g, RealDat.eC (A := A) σ g • R.gW i σ g) ∘ₗ φ, fun x u =>
    (proj_apply R hC.models.gW i σ (φ x) _).trans (congrArg (R.eWf i σ) (hφ x u))⟩

end GlobalTheory.GalLift.ProjLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupRowsEigenpartsPrincipalLevelEqTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.SpanParts

theorem iSup_rows_eigenparts_principal_level_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) → (⨆ p, R.EEp3 p) = ⊤ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW hEx hS hC
  obtain ⟨hCore, hSF, hE, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  obtain ⟨h, -, -, hTop, -⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 hCore hS R.SF hSF
  rw [eq_top_iff, ← hTop]
  refine iSup_le fun c => ?_
  by_cases h0 : R.EEc c = ⊥
  · rw [← hE c, h0]; exact bot_le
  · obtain ⟨p, hp⟩ := hC c h0
    rw [← hE c]
    refine le_trans ?_ (le_iSup _ p)
    exact le_iSup₂_of_le c hp le_rfl

end GlobalTheory.SpanParts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideRest
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.LocGL.LExist

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ Δ : Segment k, ∃ x : IrrGL k, IsLSeg Δ x.rep) →
      ∀ 𝔪 : Multiset (Segment k), ∃ x : IrrGL k, IsL 𝔪 x.rep := by
  intro k _ _ _ _ _ hS hL 𝔪
  obtain ⟨Δ, hΔ⟩ := ((precedes_and_orderedForms k).1.2.2) 𝔪
  choose y hy using hL
  let x : Fin 𝔪.card → IrrGL k := fun i => y (Δ i)
  have hx : LFactors 𝔪 x := ⟨Δ, hΔ, fun i => hy (Δ i)⟩
  obtain ⟨π, hπ⟩ := hS k 𝔪 𝔪.card _ x rfl hx
  refine ⟨IrrGL.of π.ρ π.smooth π.irr, 𝔪.card, x, rfl, hx, ?_⟩
  exact hπ.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr) (.refl _)

end GlobalTheory.LocGL.LExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceNormGramInverseEqMulMatrixStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_norm_gramInverse_eq_mulMatrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u β : B.A, IsUnit (GlobalTheory.TwLat.gram e b β) → B.σ β = β * ((-1) ^ (m - 1) * u) → (nrmL m w (GlobalTheory.TwLat.dlt e b β)).val = GlobalTheory.TwLat.mulMat e b u := by
  first | exact @GlobalTheory.TwLat.nrmL_dlt | exact GlobalTheory.TwLat.nrmL_dlt | (intros; apply GlobalTheory.TwLat.nrmL_dlt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfFixedVectorsAdelicLevelNeBotOfLocalLevelStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_fixedVectors_adelicLevel_ne_bot_of_localLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → HasLevel S π K' → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ := by
  first | exact @GlobalTheory.FixLev.inf_fixed_globLev_ne_bot | exact GlobalTheory.FixLev.inf_fixed_globLev_ne_bot | (intros; apply GlobalTheory.FixLev.inf_fixed_globLev_ne_bot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarJacobianDetEqZeroOfCompactSupportStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_dbarJacobian_det_eq_zero_of_compactSupport : ∀ {n : ℕ} (U K : Set (V n)) (f : Fin n → V n → ℂ) (j : Fin n), IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (f i) U) → (∀ v ∈ U, v ∉ K → f j v = 0) → ∫ v in U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  first | exact @GlobalTheory.GoodTop.integral_dbarJacobian_eq_zero | exact GlobalTheory.GoodTop.integral_dbarJacobian_eq_zero | (intros; apply GlobalTheory.GoodTop.integral_dbarJacobian_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLiftSymbol
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.HSCore.IntLift

variable {K : Type} [Field K] [NumberField K]

theorem mulPow_mem_global (G : Geo K) (s : Fin G.D → Fin G.N → K) {a j l : ℕ} (h : j + a = l)
    (α : MonoDeg (Fin G.D) a) {m : G.Sec j} (hm : m ∈ G.global j) : mulPow G s h α m ∈ G.global l := by
  obtain ⟨F, rfl⟩ := hm
  refine ⟨(Vanishing.powChart (isLB_tens G.K.isLB G.isLBA) G.isLB ((Nat.cast_add j a).symm.trans (congrArg _ h))).mul
    (H0.ofSec G.str ⊤ (monoSec (G.sec s) α)) F, ?_⟩
  rw [ProdChart.restr_mul, H0.restr_ofSec]
  rfl

end GlobalTheory.HSCore.IntLift

namespace GlobalTheory.HSCore

end GlobalTheory.HSCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarHasHhUnique
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ

theorem isArithVar_hasHh_unique : ∀ (ι : Type) [Fintype ι] (N : ℕ), GlobalTheory.IsArithVar (flStr ι N) (dimFl ι N) ∧
    (GlobalTheory.Published.ArExists → HasHh ι N) ∧
    ∀ (h : HasHh ι N) (Φ : Pol ι N →ₗ[ℝ] ℝ), IsHh ι N Φ → Φ = hh h := by
  intro ι _ N
  have hd := GlobalTheory.T.partial_flag_smooth_arithmetic ι (ι × Fin (N + 1)) N Prod.fst Prod.snd
  rw [(GlobalTheory.T.cell_variety_dimension_counts ι N).1] at hd
  exact ⟨hd.2.2, fun H => ((H ℤ _ _ _ hd.2.2).2 _ grLine).1, fun _ _ hΦ => hΦ.eq_hh hd.2.1⟩

end GlobalTheory.FlagZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenTopFormEtaleTowerTranscendenceBasisStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFreeGen_topForm_etaleTower_transcendenceBasis : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  IsFreeGen L (dForm cL (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  first | exact @GlobalTheory.FieldPair.isFreeGen_dForm_tower | exact GlobalTheory.FieldPair.isFreeGen_dForm_tower | (intros; apply GlobalTheory.FieldPair.isFreeGen_dForm_tower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptyGenericMemberLinearSystemStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_or_isEmpty_generic_member_linearSystem : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) → ∀ (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec), ⨆ i, nonzeroLocus (b i) = ⊤ → ∃ t : (L.pull π).Sec, t ≠ 0 ∧ (IsIntegral (secIdeal (LB.isLB_pull hL π) t).subscheme ∨ IsEmpty (secIdeal (LB.isLB_pull hL π) t).subscheme) := by
  first | exact @GlobalTheory.GenericMember.isIntegral_or_isEmpty_zeroScheme | exact GlobalTheory.GenericMember.isIntegral_or_isEmpty_zeroScheme | (intros; apply GlobalTheory.GenericMember.isIntegral_or_isEmpty_zeroScheme <;> assumption)
end

