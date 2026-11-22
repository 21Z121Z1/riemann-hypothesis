import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.CpRegPhRegOfNonneg
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.WeightedUnfoldingIntegral
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.DivisionPairOfAdelicFormsFaceColumnsData
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Objects
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.BRegWeightLevi
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open Filter Topology Metric ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.AnForm (levi)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {a : K → ℤ}
  {w : ((Σ k, ι k) → ℂ) → ℝ}

theorem BoundedRegularisationSetting.eventually_closedBall_subset (S : BoundedRegularisationSetting M Xo a w) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ closure (S.B.mid j),
      closedBall (S.B.chart j x) t ⊆ (S.B.chart j).target := by
  refine Filter.eventually_all.2 fun j => ?_
  have hc : IsCompact (closure (S.B.mid j)) := isClosed_closure.isCompact
  have himg : IsCompact (S.B.chart j '' closure (S.B.mid j)) :=
    hc.image_of_continuousOn ((S.B.chart j).continuousOn.mono (S.B.closure_mid j))
  have hsub : S.B.chart j '' closure (S.B.mid j) ⊆ (S.B.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (S.B.chart j).map_source (S.B.closure_mid j hx)
  obtain ⟨δ, hδ, hδs⟩ := himg.exists_cthickening_subset_open (S.B.chart j).open_target hsub
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht x hx
  exact (closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans
    ((cthickening_mono ht.2.le _).trans hδs)

theorem BoundedRegularisationSetting.eventually_chartLevi (S : BoundedRegularisationSetting M Xo a w) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.bregWeight t) ∧
      ∀ k : Fin S.B.N, ∀ x ∈ S.B.mid k, ∀ v : Fin d → ℂ,
        -(4 * S.Cη * S.e1 t) * ‖v‖ ^ 2 ≤
          levi (S.B.chartFun (S.bregWeight t) k) (S.B.chart k x) v := by
  filter_upwards [self_mem_nhdsWithin, S.eventually_closedBall_subset, hS.compare] with t ht hball hcmp
  have hε : 0 < S.e1 t := lt_of_lt_of_le ht (S.e1_ge t ht)
  exact GroundTheory.Heights₂.Heights.Regular.BoundedGlue.proof M.Xc d M.atlas S.B S.ρ S.η S.Cη t (S.e1 t)
    S.cutoff ht hε hball hcmp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.CocycleZeroMemInvariants
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

def IsZBasis {Em : Type} [Field Em] [NumberField Em] {N : ℕ} (I : Submodule (𝓞 Em) (Fin N → Em)) {m : ℕ}
    (b : Fin m → Fin N → Em) : Prop :=
  LinearIndependent ℤ b ∧ ∀ v, v ∈ I ↔ v ∈ Submodule.span ℤ (Set.range b)

theorem UnitaryCovolumeLowerBound.one_le_rootDiscr (Em : Type) [Field Em] [NumberField Em] : 1 ≤ rootDiscr Em := by
  unfold rootDiscr
  refine Real.one_le_rpow ?_ (by positivity)
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs (discr_ne_zero Em)

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def hodgeInner (z : (Σ k, ι k) → ℂ) (v w : Fin D.N → Em) : ℝ :=
  ∑ τ, 2 * ‖D.herm.emb τ D.herm.ξ‖ *
    (∑ a, starRingEnd ℂ (((D.per z τ)⁻¹ *ᵥ fun b => D.herm.emb τ (v b)) a) *
      ((D.per z τ)⁻¹ *ᵥ fun b => D.herm.emb τ (w b)) a).re

theorem hodgeInner_self (z : (Σ k, ι k) → ℂ) (v : Fin D.N → Em) : D.hodgeInner z v v = D.hodgeNormSq z v := by
  unfold hodgeInner hodgeNormSq
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

open Classical in

def covolZ (z : (Σ k, ι k) → ℂ) (I : Submodule (𝓞 Em) (Fin D.N → Em)) : ℝ :=
  if h : ∃ m, ∃ b : Fin m → Fin D.N → Em, IsZBasis I b then
    Real.sqrt (Matrix.of fun k l => D.hodgeInner z (h.choose_spec.choose k) (h.choose_spec.choose l)).det
  else 0

theorem firstMinimum_le_period_norm (z : (Σ k, ι k) → ℂ) {v : Fin D.N → Em} (hv : v ∈ D.herm.L) (hv0 : v ≠ 0) :
    D.lam1 z ≤ Real.sqrt (D.hodgeNormSq z v) :=
  csInf_le ⟨0, by rintro r ⟨w, -, -, rfl⟩; exact Real.sqrt_nonneg _⟩ ⟨v, hv, hv0, rfl⟩

end FullerData

namespace UnitaryIsotropicLineExample

open GroundTheory.Heights₂.Heights.NineStatements.Gauss

abbrev z0 : (Σ _ : Unit, Fin 2) → ℂ := Line.chartBase 0

abbrev e11 : Fin 2 → Em := fun _ => 1

def isoLine : Submodule (𝓞 Em) (Fin 2 → Em) := Submodule.span (𝓞 Em) {e11}

end UnitaryIsotropicLineExample

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.EigenLatDifferent
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

section DiffLat

variable {Em : Type} [Field Em] [NumberField Em] {K : Type} [Field K] [NumberField K] {N : ℕ}

def diffLat (s : Em →+* K) (I : Submodule (𝓞 Em) (Fin N → Em)) : Submodule (𝓞 K) (Fin N → K) :=
  Submodule.span (𝓞 K) ((fun u i => s (u i)) ''
    {u | ∃ x ∈ differentIdeal ℤ (𝓞 Em), ∃ y ∈ I, u = (x : Em) • y})

end DiffLat

def EigenLatDifferent.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ),
    (∀ σ : Em →+* ℂ, ∃ t : Em →+* K, ι.comp t = σ) →
    ∀ (N : ℕ) (I : Submodule (𝓞 Em) (Fin N → Em)), I.FG → ∀ s : Em →+* K,
      eigenLat I s = diffLat s I

example : (∀ σ : Gauss.Em →+* ℂ, ∃ t : Gauss.Em →+* Gauss.Em, Gauss.φ₀.comp t = σ) ∧ Gauss.isoLine.FG :=
  ⟨Gauss.split Gauss.φ₀, Submodule.fg_span_singleton _⟩

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PWeightedUnfolding
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField MeasureTheory GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FiniteCovolume
open scoped ENNReal Matrix ComplexOrder

theorem hf_smul {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (σ : R →+* R) (r : R)
    (J : Matrix ι ι R) (x y : ι → R) :
    ReciprocityTheory.ChartRestriction.G.SA.hf σ (r • J) x y = r * ReciprocityTheory.ChartRestriction.G.SA.hf σ J x y := by
  simp only [ReciprocityTheory.ChartRestriction.G.SA.hf, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem unitaryOf_smul_eq {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : K →+* K)
    (J : Matrix ι ι K) {r : K} (hr : r ≠ 0) : unitaryOf σ (r • J) = unitaryOf σ J := by
  ext g
  change (g : Matrix ι ι K)ᵀ * (r • J) * (g : Matrix ι ι K).map σ = r • J ↔
    (g : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K).map σ = J
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact (smul_right_injective _ hr).eq_iff

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem conjE_h (V : HermSpace E N) (x y : Fin N → E) : conjE E (V.h y x) = V.h x y := by
  have hJ : ∀ i j, conjE E (V.J i j) = V.J j i := fun i j =>
    (congrFun (congrFun V.herm i) j).symm
  simp only [HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf, map_sum, map_mul, hJ, conjE_apply,
    IsCMField.complexConj_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def scaleSpace (V : HermSpace E N) (n : ℕ) (hn : 0 < n) : HermSpace E N where
  J := (n : E) • V.J
  herm := by
    rw [Matrix.transpose_smul, V.herm]
    ext i j
    simp [Matrix.map_apply, map_natCast]
  nondeg := by
    rw [Matrix.det_smul]
    exact ((Nat.cast_ne_zero.2 hn.ne' : (n : E) ≠ 0).isUnit.pow _).mul V.nondeg

theorem scaleSpace_h (V : HermSpace E N) (n : ℕ) (hn : 0 < n) (x y : Fin N → E) :
    (scaleSpace V n hn).h x y = n * V.h x y :=
  hf_smul _ _ _ _ _

theorem unitaryGroup_scale (V : HermSpace E N) (n : ℕ) (hn : 0 < n) :
    unitaryGroup (scaleSpace V n hn) = unitaryGroup V :=
  unitaryOf_smul_eq _ _ (Nat.cast_ne_zero.2 hn.ne')

theorem placeJ_scale (V : HermSpace E N) (n : ℕ) (hn : 0 < n) (w : InfinitePlace E) :
    placeJ (scaleSpace V n hn) w = (n : ℂ) • placeJ V w := by
  ext i j
  simp [placeJ, scaleSpace, Matrix.map_apply]

theorem realPoints_scale (V : HermSpace E N) (n : ℕ) (hn : 0 < n) :
    realPoints (scaleSpace V n hn) = realPoints V := by
  unfold realPoints
  congr 1
  funext w
  rw [placeJ_scale]
  exact unitaryOf_smul_eq _ _ (Nat.cast_ne_zero.2 hn.ne')

def scaleMaj {V : HermSpace E N} (M : Majorant V) (n : ℕ) (hn : 0 < n) : Majorant (scaleSpace V n hn) where
  H w := (n : ℂ) • M.H w
  posDef w := (M.posDef w).smul (Nat.cast_pos.2 hn)
  involution w := by
    have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hH : IsUnit (M.H w).det := isUnit_iff_ne_zero.2 (M.posDef w).det_pos.ne'
    have hinv : ((n : ℂ) • M.H w)⁻¹ = (n : ℂ)⁻¹ • (M.H w)⁻¹ :=
      Matrix.inv_eq_left_inv (by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hH, smul_smul,
          inv_mul_cancel₀ hne, one_smul])
    rw [placeJ_scale, hinv]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [M.involution w]
    congr 1
    field_simp

theorem wNorm_scale {V : HermSpace E N} (M : Majorant V) (n : ℕ) (hn : 0 < n) (c : InfinitePlace E → ℝ)
    (x : InfinitePlace E → Fin N → ℂ) :
    wNorm (scaleMaj M n hn) (fun w => c w / n) x = wNorm M c x := by
  unfold wNorm
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  change c w / n * (ReciprocityTheory.ChartRestriction.G.SA.hf (starRingEnd ℂ) ((n : ℂ) • M.H w) (x w) (x w)).re = _
  rw [hf_smul]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  field_simp

theorem exists_scale_integral (V : HermSpace E N) (L : Submodule (𝓞 E) (Fin N → E)) (hL : IsLattice L) :
    ∃ (n : ℕ) (hn : 0 < n), ∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ ((scaleSpace V n hn).h x y) := by
  classical
  obtain ⟨S, hS⟩ := hL.1
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ((S ×ˢ S).image fun p => V.h p.1 p.2)
  have hn : 0 < y.natAbs := Int.natAbs_pos.2 hy0
  have hden : ∀ a ∈ (S ×ˢ S).image (fun p => V.h p.1 p.2), IsIntegral ℤ ((y.natAbs : E) * a) := by
    intro a ha
    have h1 := hy a ha
    rcases Int.natAbs_eq y with h | h
    · rw [h] at h1
      simpa [zsmul_eq_mul] using h1
    · rw [h] at h1
      simpa [zsmul_eq_mul] using h1.neg
  refine ⟨y.natAbs, hn, ?_⟩
  set V' := scaleSpace V y.natAbs hn
  have hgen : ∀ x ∈ S, ∀ z ∈ S, IsIntegral ℤ (V'.h x z) := fun x hx z hz => by
    rw [scaleSpace_h]
    exact hden _ (Finset.mem_image.2 ⟨(x, z), Finset.mem_product.2 ⟨hx, hz⟩, rfl⟩)
  have key1 : ∀ z ∈ S, ∀ x ∈ L, IsIntegral ℤ (V'.h x z) := by
    intro z hz x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hgen x hx z hz
    | zero => simpa [HermSpace.h, ReciprocityTheory.ChartRestriction.G.SA.hf] using (isIntegral_zero : IsIntegral ℤ (0 : E))
    | add a b _ _ ha hb => rw [h_add_left]; exact ha.add hb
    | smul r a _ ha =>
      rw [← IsScalarTower.algebraMap_smul E r a, h_smul_left]
      exact (show IsIntegral ℤ (algebraMap (𝓞 E) E r) from r.isIntegral_coe).mul ha
  have key2 : ∀ x ∈ L, x ∈ dual V' L := by
    intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      intro z hz
      rw [← conjE_h]
      exact (key1 x hx z hz).map (conjE E).toIntAlgHom
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul r a _ ha => exact Submodule.smul_mem _ r ha
  exact fun x hx z hz => key2 x hx z hz

section Transport

variable (V : HermSpace E N) (n : ℕ) (hn : 0 < n)

def realScale : RealPts V ≃* RealPts (scaleSpace V n hn) where
  toFun g := ⟨g.1, by rw [realPoints_scale]; exact g.2⟩
  invFun g := ⟨g.1, by rw [← realPoints_scale V n hn]; exact g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem realScale_eq_mk (g : RealPts V) :
    realScale V n hn g = ⟨g.1, by rw [realPoints_scale]; exact g.2⟩ := rfl

theorem coe_realScale (g : RealPts V) :
    ((realScale V n hn g : RealPts (scaleSpace V n hn)) : InfinitePlace E → GL (Fin N) ℂ) = g := by
  rw [realScale_eq_mk, Subtype.coe_mk]

theorem gAct_realScale (g : RealPts V) (x : InfinitePlace E → Fin N → ℂ) :
    gAct (realScale V n hn g) x = gAct g x := by
  unfold gAct
  rw [coe_realScale]

theorem continuous_realScale : Continuous (realScale V n hn) :=
  continuous_subtype_val.subtype_mk _

theorem continuous_realScale_symm : Continuous (realScale V n hn).symm :=
  continuous_subtype_val.subtype_mk _

def realScaleMeas : RealPts V ≃ᵐ RealPts (scaleSpace V n hn) :=
  (Homeomorph.mk (realScale V n hn).toEquiv (continuous_realScale V n hn)
    (continuous_realScale_symm V n hn)).toMeasurableEquiv

theorem realScaleMeas_apply (g : RealPts V) : realScaleMeas V n hn g = realScale V n hn g := rfl

theorem mem_gammaVecInf_scale (L : Submodule (𝓞 E) (Fin N → E)) (v₀ : Fin N → E) (g : RealPts V) :
    g ∈ gammaVecInf V L v₀ ↔ realScale V n hn g ∈ gammaVecInf (scaleSpace V n hn) L v₀ := by
  have hU := unitaryGroup_scale V n hn
  rw [Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    rw [Subgroup.mem_inf] at hδ
    refine ⟨⟨δ.1, by rw [hU]; exact δ.2⟩, Subgroup.mem_inf.2 ⟨hδ.1, hδ.2⟩, ?_⟩
    apply Subtype.ext
    funext w
    rfl
  · rintro ⟨δ, hδ, h⟩
    rw [Subgroup.mem_inf] at hδ
    refine ⟨⟨δ.1, by rw [← hU]; exact δ.2⟩, Subgroup.mem_inf.2 ⟨hδ.1, hδ.2⟩, ?_⟩
    apply Subtype.ext
    have h' := congrArg (fun x : RealPts (scaleSpace V n hn) => (x : InfinitePlace E → GL (Fin N) ℂ)) h
    rw [coe_realScale] at h'
    rw [← h']
    funext w
    rfl

end Transport

theorem WeightedUnfolding.proof (h₁ : WeightedUnfoldingIntegral.Statement) : WeightedUnfolding.Statement := by
  intro E _ _ _ N V M c hc L v₀ hL hv₀ hne hiso μ hμ
  obtain ⟨n, hn, hint⟩ := exists_scale_integral V L hL
  have hψ : ⇑(realScaleMeas V n hn) = ⇑(realScale V n hn) := funext (realScaleMeas_apply V n hn)
  have : μ.IsHaarMeasure := hμ
  have hμ' : (μ.map (realScaleMeas V n hn)).IsHaarMeasure := by
    rw [hψ]
    exact (realScale V n hn).isHaarMeasure_map μ (continuous_realScale V n hn)
      (continuous_realScale_symm V n hn)
  have hc' : ∀ w, 0 < c w / n := fun w => div_pos (hc w) (Nat.cast_pos.2 hn)
  have hiso' : (scaleSpace V n hn).h v₀ v₀ = 0 := by rw [scaleSpace_h, hiso, mul_zero]
  obtain ⟨s', hs'm, hs', hfin, hhom⟩ := h₁ E N (scaleSpace V n hn) (scaleMaj M n hn) (fun w => c w / n) hc'
    L v₀ hL hint hv₀ hne hiso' _ hμ'

  let e : gammaVecInf (scaleSpace V n hn) L v₀ → gammaVecInf V L v₀ := fun γ =>
    ⟨(realScale V n hn).symm γ, (mem_gammaVecInf_scale V n hn L v₀ _).2 (by
      rw [MulEquiv.apply_symm_apply]; exact γ.2)⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b hab => Subtype.ext ((realScale V n hn).symm.injective (congrArg Subtype.val hab)),
      fun γ => ⟨⟨realScale V n hn γ, (mem_gammaVecInf_scale V n hn L v₀ _).1 γ.2⟩, ?_⟩⟩
    apply Subtype.ext
    exact (realScale V n hn).symm_apply_apply _
  have hfd : IsFundamentalDomain (gammaVecInf V L v₀) (realScaleMeas V n hn ⁻¹' s') μ := by
    refine hs'.preimage_of_equiv ((realScaleMeas V n hn).measurable.measurePreserving μ).quasiMeasurePreserving
      he ?_
    intro γ x
    change realScaleMeas V n hn (((realScale V n hn).symm γ : RealPts V) * x) =
      (γ : RealPts (scaleSpace V n hn)) * realScaleMeas V n hn x
    rw [hψ, map_mul, MulEquiv.apply_symm_apply]

  have hpt : ∀ (t : ℝ) (g : RealPts V),
      wBelowInd (scaleMaj M n hn) (fun w => c w / n) v₀ t (realScaleMeas V n hn g) = wBelowInd M c v₀ t g := by
    intro t g
    unfold wBelowInd
    rw [realScaleMeas_apply, ← map_inv, gAct_realScale, wNorm_scale]
  have hint_eq : ∀ t : ℝ, (∫⁻ g in realScaleMeas V n hn ⁻¹' s', wBelowInd M c v₀ t g ∂μ) =
      ∫⁻ g in s', wBelowInd (scaleMaj M n hn) (fun w => c w / n) v₀ t g ∂(μ.map (realScaleMeas V n hn)) := by
    intro t
    rw [MeasurableEquiv.restrict_map, lintegral_map_equiv]
    simp_rw [hpt]
  refine ⟨realScaleMeas V n hn ⁻¹' s', (realScaleMeas V n hn).measurable hs'm, hfd, ?_, fun t ht => ?_⟩
  · rw [hint_eq]
    exact hfin
  · rw [hint_eq, hint_eq, hhom t ht]

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StIsotropicRank
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField
open scoped Matrix

def IsotropicRank.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] [IsCMField Em] (Ψ : Type) [Fintype Ψ] (N j : ℕ)
    (A : HermDatum Em Ψ N j) (S : Set (Fin N → Em)),
      (∀ v ∈ S, ∀ w ∈ S, hermForm Em A.H v w = 0) → Module.finrank Em (Submodule.span Em S) ≤ N - j

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StatementsMeanLogPlus
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree MeasureTheory
open scoped Matrix

def HasSpanningBound (Em : Type) [Field Em] [NumberField Em] (vr : ℝ) : Prop :=
  ∃ (m : ℕ) (a : Fin m → 𝓞 Em), Submodule.span ℚ (Set.range fun i => (a i : Em)) = ⊤ ∧
    ∀ (σ : Em →+* ℂ) (i : Fin m), ‖σ (a i)‖ ≤ vr

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def isoCount (t : ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ({v | v ∈ D.herm.L ∧ v ≠ 0 ∧ hermForm Em D.herm.H v v = 0 ∧ D.hodgeNormSq z v < t ^ 2}.ncard : ℝ)

def meanX (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ :=
  ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu D.mu) g / degMu D.mu

abbrev XoPts : Type := {z : (Σ k, ι k) → ℂ // z ∈ D.Xo}

end FullerData

def IsTorusInv {K : Type} {ι : K → Type} (g : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ z, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → g (torusSmul c z) = g z

section Statements

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]

def MeanLogPlus.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  3 * D.j' + 1 ≤ D.N → ∀ vr : ℝ, HasSpanningBound Em vr →
    D.meanX (fun z => max 0 (Real.log (vr ^ (-(1 / 2 : ℝ)) / D.lam1 z))) ≤ 3

def InvariantMean.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∃ ν : Measure D.XoPts, IsProbabilityMeasure ν ∧
    (∀ t : ℝ, 0 < t → Integrable (fun z : D.XoPts => D.isoCount t z) ν) ∧
    ∀ g : ((Σ k, ι k) → ℂ) → ℝ, IsTorusInv g → Integrable (fun z : D.XoPts => g z) ν →
      D.meanX g = ∫ z, g z ∂ν

def FirstMinPos.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∀ z ∈ D.Xo, 0 < D.lam1 z

def CountMeasurable.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  Measurable (fun z : D.XoPts => D.lam1 z) ∧ ∀ t : ℝ, Measurable (fun z : D.XoPts => D.isoCount t z)

def ShortVectors.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∀ vr : ℝ, HasSpanningBound Em vr → ∀ t : ℝ, 0 < t → t ≤ vr ^ (-(1 / 2 : ℝ)) → ∀ z ∈ D.Xo, D.lam1 z < t →
    1 ≤ D.isoCount t z ∧ D.isoCount t z ≤ (3 * t / D.lam1 z) ^ (2 * D.f * D.j')

def CountScaling.Statement (D : FullerData II Ψ K ι Ω E Em) : Prop :=
  ∀ θ t : ℝ, 0 < θ → 0 < t →
    D.meanX (D.isoCount (θ * t)) = θ ^ ((2 * D.f * (D.N - 1) : ℕ) : ℝ) * D.meanX (D.isoCount t)

end Statements

namespace Gauss

end Gauss

end GroundTheory.Heights₂.Heights.NineStatements
end
end

