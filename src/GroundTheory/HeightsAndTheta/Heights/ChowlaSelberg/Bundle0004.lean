import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.DedekindZetaEqSumRealEisenstein
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmClassPeriodInvConj
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.CotangentSumStatement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

def CotangentSum.Statement : Prop :=
  ∀ (a u : ℝ), 0 < a →
    ∑' n : ℤ, (((n : ℝ) + u) ^ 2 + a ^ 2) ^ (-1 : ℝ) =
      π / a * (1 + 2 * (∑' k : ℕ,
        Complex.exp (2 * π * Complex.I * ((u : ℂ) + (a : ℂ) * Complex.I)) ^ (k + 1)).re)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.GammaZetaLimitStatement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

def GammaZetaLimit.Statement : Prop :=
  ∀ y : ℝ, 0 < y →
    Tendsto (fun s : ℝ ↦ 2 * (√π * Real.Gamma (s - 1 / 2) / Real.Gamma s) * y ^ (1 - s) *
        (∑' m : ℕ, 1 / ((m + 1 : ℝ) ^ (2 * s - 1))) - π / (s - 1)) (𝓝[>] 1)
      (𝓝 (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log y))

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.HeckeRatios
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm
open scoped Real

noncomputable section

def mulPoint (n : ℕ+) (τ : ℍ) : ℍ := (⟨(n : ℝ), by positivity⟩ : {x : ℝ // 0 < x}) • τ

def divPoint (n : ℕ+) (a : ℕ) (τ : ℍ) : ℍ :=
  (⟨(n : ℝ)⁻¹, by positivity⟩ : {x : ℝ // 0 < x}) • ((a : ℝ) +ᵥ τ)

theorem coe_mulPoint (n : ℕ+) (τ : ℍ) : (mulPoint n τ : ℂ) = (n : ℂ) * τ := by
  simp [mulPoint, coe_pos_real_smul, Complex.real_smul]

theorem coe_divPoint (n : ℕ+) (a : ℕ) (τ : ℍ) : (divPoint n a τ : ℂ) = ((a : ℂ) + τ) / n := by
  simp [divPoint, coe_pos_real_smul, coe_vadd, Complex.real_smul, div_eq_inv_mul]
  ring

def heckeRatios (n : ℕ+) (τ : ℍ) : Multiset ℂ :=
  ((n : ℂ) ^ 12 * discriminant (mulPoint n τ) / discriminant τ) ::ₘ
    (Multiset.range n).map fun a ↦ discriminant (divPoint n a τ) / discriminant τ

def HasIntegralLaurentQExpansion (f : ℍ → ℂ) : Prop :=
  ∃ (N : ℕ) (c : ℕ → ℤ) (A : ℝ), ∀ τ : ℍ, A < τ.im →
    HasSum (fun n ↦ (c n : ℂ) * Function.Periodic.qParam 1 τ ^ n)
      (Function.Periodic.qParam 1 τ ^ N * f τ)

theorem hasIntegralLaurentQExpansion_const (m : ℤ) :
    HasIntegralLaurentQExpansion fun _ ↦ (m : ℂ) := by
  refine ⟨0, fun n ↦ if n = 0 then m else 0, 0, fun τ _ ↦ ?_⟩
  convert hasSum_ite_eq 0 ((m : ℂ) * Function.Periodic.qParam 1 τ ^ 0) using 1
  · ext n; split_ifs <;> simp_all
  · simp

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.KroneckerSplitStatement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

def KroneckerSplit.Statement : Prop :=
  ∀ (τ : ℍ) (s : ℝ), 1 < s →
    kroneckerSum τ s =
      2 * τ.im ^ s * ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ (2 * s)) +
      2 * ∑' m : ℕ, τ.im ^ s * ∑' n : ℤ,
        (((n : ℝ) + (m + 1) * τ.re) ^ 2 + ((m + 1) * τ.im) ^ 2) ^ (-s)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.LogEtaStatement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open Filter Topology
open scoped Real UpperHalfPlane ModularForm

noncomputable section

def LogEta.Statement : Prop :=
  ∀ τ : ℍ, HasSum (fun m : ℕ ↦ (1 / (m + 1 : ℝ)) *
      (∑' k : ℕ, Complex.exp (2 * π * Complex.I * (τ : ℂ)) ^ ((m + 1) * (k + 1))).re)
    (-(π * τ.im / 12) - Real.log ‖η (τ : ℂ)‖)

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PClassEpstein
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors Real UpperHalfPlane

noncomputable section

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in

theorem coe_idealLattice (σ : K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice σ I : Set ℂ) = σ '' (I : Set K) := by
  ext z
  exact Iff.rfl

theorem exists_im_ne_zero [Algebra.IsQuadraticExtension ℚ K] (S : PrimeDiscriminant K)
    (σ : K →+* ℂ) : ∃ x : K, (σ x).im ≠ 0 := by
  by_contra h
  push Not at h
  have hreal : (InfinitePlace.mk σ).IsReal := by
    rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.mpr (h x)
  have h1 : 0 < InfinitePlace.nrRealPlaces K := by
    classical
    exact Fintype.card_pos_iff.mpr ⟨⟨_, hreal⟩⟩
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at h2
  have h3 : InfinitePlace.nrComplexPlaces K = 0 := by omega
  have h4 := sign_discr K
  rw [h3, pow_zero, S.discr_eq] at h4
  have hd := S.prime.pos
  have : (-(S.d : ℤ)).sign = -1 := Int.sign_eq_neg_one_of_neg (by omega)
  rw [this] at h4
  exact absurd h4 (by decide)

theorem latticeArea_periodPair (L : PeriodPair) :
    latticeArea L.lattice = |L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re| := by
  have hvol : MeasureTheory.volume.real (ZSpan.fundamentalDomain Complex.basisOneI) = 1 := by
    rw [← Complex.toBasis_orthonormalBasisOneI,
      MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _)]
    rw [MeasureTheory.measureReal_def, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.volume_parallelepiped]
    simp
  unfold latticeArea
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ L.latticeBasis Complex.basisOneI, hvol, mul_one,
    Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr]
  congr 1
  ring

theorem epsteinSum_eq_realEisenstein {Λ : Submodule ℤ ℂ} {τ : ℍ} {c : ℂ} (hc : c ≠ 0)
    (h : (fun z => c * z) '' (Λ : Set ℂ) = Theta.latticeOf (τ : ℂ)) (s : ℝ) :
    epsteinSum Λ s = Theta.realEisenstein τ s := by
  have hind : LinearIndependent ℝ ![c⁻¹ * (τ : ℂ), c⁻¹] := by
    refine LinearIndependent.pair_iff.2 fun a b hab => ?_
    refine LinearIndependent.pair_iff.1 (latticeOfTau τ).indep a b ?_
    have e : a • (latticeOfTau τ).ω₁ + b • (latticeOfTau τ).ω₂ =
        c * (a • (c⁻¹ * (τ : ℂ)) + b • c⁻¹) := by
      simp only [latticeOfTau, Complex.real_smul]
      field_simp
    rw [e, hab, mul_zero]
  let P : PeriodPair := ⟨c⁻¹ * (τ : ℂ), c⁻¹, hind⟩
  have hmem : ∀ z : ℂ, z ∈ Λ ↔ c * z ∈ Theta.latticeOf (τ : ℂ) := by
    intro z
    rw [← h]
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨y, hy, e⟩
      rwa [← mul_left_cancel₀ hc e]
  have hP : P.lattice = Λ := by
    ext z
    rw [PeriodPair.mem_lattice, hmem, Theta.latticeOf, SetLike.mem_coe, Submodule.mem_span_pair]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨n, m, ?_⟩
      simp only [P, zsmul_eq_mul]
      field_simp
      ring
    · rintro ⟨a, b, e⟩
      refine ⟨b, a, mul_left_cancel₀ hc ?_⟩
      rw [← e]
      simp only [P, zsmul_eq_mul]
      field_simp
      ring
  subst hP
  have harea : latticeArea P.lattice = ‖c⁻¹‖ ^ 2 * τ.im := by
    rw [latticeArea_periodPair]
    have e : P.ω₁.re * P.ω₂.im - P.ω₁.im * P.ω₂.re = -(Complex.normSq c⁻¹ * τ.im) := by
      simp only [P, Complex.mul_re, Complex.mul_im, Complex.normSq_apply, UpperHalfPlane.coe_im]
      ring
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg (Complex.normSq_nonneg _) τ.im_pos.le),
      Complex.normSq_eq_norm_sq]
  unfold epsteinSum Theta.realEisenstein
  rw [harea, ← P.latticeEquivProd.symm.toEquiv.tsum_eq]
  refine tsum_congr fun p => ?_
  have hcoe : ((P.latticeEquivProd.symm.toEquiv p : P.lattice) : ℂ) =
      c⁻¹ * ((p.1 : ℂ) * τ + p.2) := by
    rw [LinearEquiv.coe_toEquiv, PeriodPair.latticeEquiv_symm_apply]
    simp only [P]
    ring
  by_cases hp : p = 0
  · subst hp
    simp
  · have hne : ((P.latticeEquivProd.symm.toEquiv p : P.lattice) : ℂ) ≠ 0 := by
      rw [ne_eq, ZeroMemClass.coe_eq_zero, LinearEquiv.coe_toEquiv,
        LinearEquiv.map_eq_zero_iff]
      exact hp
    have hz : (p.1 : ℂ) * τ + p.2 ≠ 0 := by
      intro h0
      apply hne
      rw [hcoe, h0, mul_zero]
    rw [if_neg hne, if_neg hp, hcoe, norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      Real.mul_rpow (by positivity) τ.im_pos.le, ← Real.rpow_natCast_mul (norm_nonneg _)]
    have ht : 0 < ‖c⁻¹‖ ^ ((2 : ℕ) * s) :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (inv_ne_zero hc)) _
    push_cast at ht ⊢
    rw [mul_div_mul_left _ _ ht.ne']

theorem realEisenstein_negConj (τ : ℍ) (s : ℝ) :
    Theta.realEisenstein (Theta.negConj τ) s = Theta.realEisenstein τ s := by
  unfold Theta.realEisenstein
  rw [← (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).tsum_eq]
  refine tsum_congr fun p => ?_
  have hneg : ((Theta.negConj τ : ℍ) : ℂ) = -(starRingEnd ℂ) (τ : ℂ) := rfl
  have him : (Theta.negConj τ).im = τ.im := by
    show ((Theta.negConj τ : ℍ) : ℂ).im = (τ : ℂ).im
    rw [hneg]
    simp
  by_cases hp : p = 0
  · subst hp
    have h00 : (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) (0 : ℤ × ℤ) = 0 := by
      ext <;> simp
    rw [if_pos h00, if_pos rfl]
  · have hp' : (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) p ≠ 0 := by
      intro h0
      apply hp
      simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.neg_apply, Prod.map,
        Prod.mk_eq_zero, id, neg_eq_zero] at h0
      exact Prod.ext h0.1 h0.2
    rw [if_neg hp', if_neg hp, him]
    congr 2
    have e : (((Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) p).1 : ℂ) * (Theta.negConj τ : ℂ) +
        (((Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)) p).2 : ℂ) =
          -(starRingEnd ℂ) ((p.1 : ℂ) * τ + p.2) := by
      simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.neg_apply, Prod.map, id, hneg,
        map_add, map_mul, map_intCast, Int.cast_neg]
      ring
    rw [e, norm_neg, Complex.norm_conj]

theorem partialZeta_eq_toReal (A : ClassGroup (𝓞 K)) (s : ℝ) :
    partialZeta A s = (∑' t : (ClassGroup.mk0 ⁻¹' {A} : Set (Ideal (𝓞 K))⁰),
      ENNReal.ofReal ((Ideal.absNorm ((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : ℝ) ^ (-s))).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  unfold partialZeta
  refine tsum_congr fun t => ?_
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.rpow_neg (Nat.cast_nonneg _)]

theorem ClassEpstein.proof [Algebra.IsQuadraticExtension ℚ K] (S : PrimeDiscriminant K) :
    ClassEpstein.Statement S := by
  intro σ C 𝔟 hC s hs
  subst hC
  have hK : Module.finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  have hσ := exists_im_ne_zero S σ
  obtain ⟨τ, c, hc, himg⟩ := Theta.exists_isLatticeParam_fractionalIdeal hK σ hσ 𝔟
  obtain ⟨w, hw, hinv⟩ := Theta.ClassPeriodInv.exists_inv_eq_conj hK σ hσ 𝔟
  obtain ⟨c', hc', himg'⟩ : Theta.IsLatticeParam
      (σ '' (((𝔟⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) : Set K))
      (Theta.negConj τ) := by
    rw [hinv]
    exact Theta.ClassPeriodInv.isLatticeParam_conj ⟨c, hc, himg⟩ hw
  have key := Theta.projectiveLineClassData.class_sum hK σ hσ 𝔟⁻¹ (Theta.negConj τ) c' hc' himg' hs
  have hE : epsteinSum (idealLattice σ 𝔟) s = Theta.realEisenstein τ s :=
    epsteinSum_eq_realEisenstein hc (by rw [coe_idealLattice]; exact himg) s
  have hD : Real.sqrt |(discr K : ℝ)| = Real.sqrt S.d := by
    rw [S.discr_eq]
    push_cast
    rw [abs_neg, Nat.abs_cast]
  rw [realEisenstein_negConj, hD] at key
  have hw0 : (Units.torsionOrder K : ENNReal) ≠ 0 := by
    exact_mod_cast Units.torsionOrder_ne_zero K
  have hsum := (ENNReal.eq_div_iff hw0 (ENNReal.natCast_ne_top _)).mpr key
  have hcl : ClassGroup.mk K 𝔟 = (ClassGroup.mk K 𝔟⁻¹)⁻¹ := by rw [map_inv, inv_inv]
  rw [hcl, partialZeta_eq_toReal]
  erw [hsum]
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (mul_nonneg (by positivity) (Theta.realEisenstein_nonneg _ _)), hE]
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PDeltaEta
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open GroundTheory.Global.Elliptic
open scoped Real ModularForm UpperHalfPlane

theorem DeltaEta.proof : DeltaEta.Statement := by
  intro τ
  rw [latticeDiscr_lattice, discr_latticeOfTau]
  simp only [ModularForm.discriminant]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PPhConj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem mem_conjLattice_iff (Λ : Submodule ℤ ℂ) (z : ℂ) : z ∈ conjLattice Λ ↔ conj z ∈ Λ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨conj z, h, by simp⟩

theorem eisensteinSum_conjLattice (Λ : Submodule ℤ ℂ) (n : ℕ) :
    eisensteinSum (conjLattice Λ) n = conj (eisensteinSum Λ n) := by
  unfold eisensteinSum
  let e : Λ ≃ conjLattice Λ :=
    (Submodule.equivMapOfInjective _ (star_injective (R := ℂ)) Λ).toEquiv
  rw [← e.tsum_eq, Complex.conj_tsum]
  congr 1
  ext l
  change ((conj (l : ℂ)) ^ n)⁻¹ = conj (((l : ℂ) ^ n)⁻¹)
  simp [map_inv₀, map_pow]

theorem latticeDiscr_conjLattice (Λ : Submodule ℤ ℂ) :
    latticeDiscr (conjLattice Λ) = conj (latticeDiscr Λ) := by
  simp [latticeDiscr, latticeG₂, latticeG₃, eisensteinSum_conjLattice, map_sub, map_mul, map_pow, map_ofNat]

theorem conjLattice_eq_comap (Λ : Submodule ℤ ℂ) :
    conjLattice Λ =
      ZLattice.comap ℝ Λ Complex.conjLIE.toLinearEquiv.toLinearMap := by
  ext z
  rw [mem_conjLattice_iff]
  exact Iff.rfl

theorem latticeArea_conjLattice (L : PeriodPair) :
    latticeArea (conjLattice L.lattice) = latticeArea L.lattice := by
  unfold latticeArea
  rw [conjLattice_eq_comap]
  exact ZLattice.covolume_comap L.lattice volume volume
    (e := Complex.conjLIE.toContinuousLinearEquiv) Complex.conjLIE.measurePreserving

theorem PhConj.proof : PhConj.Statement := by
  intro L
  unfold logPeriod
  rw [latticeArea_conjLattice, latticeDiscr_conjLattice, Complex.norm_conj]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PPhScale
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open GroundTheory.Global.Elliptic

noncomputable section

namespace PhScale

theorem eisensteinSum_scaleLattice (Λ : Submodule ℤ ℂ) {c : ℂ} (hc : c ≠ 0) (n : ℕ) :
    eisensteinSum (scaleLattice c Λ) n = (c ^ n)⁻¹ * eisensteinSum Λ n := by
  have hinj : Function.Injective (LinearMap.mulLeft ℤ c) := fun x y h ↦ mul_left_cancel₀ hc h
  let e := Submodule.equivMapOfInjective _ hinj Λ
  unfold eisensteinSum scaleLattice
  refine (e.toEquiv.tsum_eq (fun l ↦ ((l : ℂ) ^ n)⁻¹)).symm.trans ?_
  rw [← tsum_mul_left]
  congr 1
  funext x
  simp [e, mul_pow]
  ring

theorem latticeDiscr_scaleLattice (Λ : Submodule ℤ ℂ) {c : ℂ} (hc : c ≠ 0) :
    latticeDiscr (scaleLattice c Λ) = (c ^ 12)⁻¹ * latticeDiscr Λ := by
  simp only [latticeDiscr, latticeG₂, latticeG₃, eisensteinSum_scaleLattice Λ hc]
  ring

def scalePair (L : PeriodPair) {c : ℂ} (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have := L.indep
    rw [LinearIndependent.pair_iff] at this ⊢
    intro s t hst
    apply this s t
    have hst' : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.1 hst').resolve_left hc

theorem lattice_scalePair (L : PeriodPair) {c : ℂ} (hc : c ≠ 0) :
    (scalePair L hc).lattice = scaleLattice c L.lattice := by
  simp [PeriodPair.lattice, scaleLattice, Submodule.map_span, Set.image_pair, scalePair]

theorem det_mulLeft (c : ℂ) : LinearMap.det (LinearMap.mulLeft ℝ c) = ‖c‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Algebra.norm_complex_apply, Algebra.norm_apply]
  rfl

theorem latticeArea_scaleLattice (L : PeriodPair) {c : ℂ} (hc : c ≠ 0) :
    latticeArea (scaleLattice c L.lattice) = ‖c‖ ^ 2 * latticeArea L.lattice := by
  rw [← lattice_scalePair L hc]
  unfold latticeArea
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ (scalePair L hc).latticeBasis Complex.basisOneI,
    ZLattice.covolume_eq_det_mul_measureReal _ _ L.latticeBasis Complex.basisOneI]
  have hv : ((↑) ∘ (scalePair L hc).latticeBasis : Fin 2 → ℂ) =
      (LinearMap.mulLeft ℝ c) ∘ ((↑) ∘ L.latticeBasis) := by
    funext i
    fin_cases i <;> simp <;> rfl
  rw [hv, Module.Basis.det_comp, abs_mul, det_mulLeft, abs_of_nonneg (by positivity), mul_assoc]

theorem proof : PhScale.Statement := by
  intro L c hc
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  have hA : 0 < latticeArea L.lattice := ZLattice.covolume_pos _ _
  have hAπ : latticeArea L.lattice / Real.pi ≠ 0 := (div_pos hA Real.pi_pos).ne'
  have hD : ‖latticeDiscr L.lattice‖ ≠ 0 := by
    rw [latticeDiscr_lattice]
    exact norm_ne_zero_iff.2 (discr_ne_zero L)
  unfold logPeriod
  rw [latticeArea_scaleLattice L hc, latticeDiscr_scaleLattice _ hc, norm_mul, norm_inv, norm_pow,
    mul_div_assoc, Real.log_mul (pow_ne_zero _ hn) hAπ,
    Real.log_mul (inv_ne_zero (pow_ne_zero _ hn)) hD, Real.log_inv, Real.log_pow, Real.log_pow]
  push_cast
  ring

end PhScale

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

