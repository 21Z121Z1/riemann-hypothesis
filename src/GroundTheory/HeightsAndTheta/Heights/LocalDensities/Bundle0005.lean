import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.LeviFormGbPotOne
import GroundTheory.ArithmeticGeometry.ToricVarieties.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.OneChartAtlasIndexEq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

namespace MACompact

variable {D : ℕ} {Ω : Set (Fin D → ℂ)}

theorem maDens_eq_topDens (f ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (h : f =ᶠ[𝓝 z] fun y => ψ y / 2) : maDens (fun _ : Fin D => f) z = topDens ψ z := by
  have h2 : fderiv ℝ (fderiv ℝ f) z = fderiv ℝ (fderiv ℝ fun y => ψ y / 2) z :=
    h.fderiv.fderiv_eq
  have h3 : hessC f z = cxHessian (fun y => ψ y / 2) z := by
    unfold hessC cxHessian
    rw [h2]
  simp only [maDens, topDens, maDensity, mdisc, mixedDisc, h3]

theorem topDens_congr {ψ ψ' : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (h : ψ =ᶠ[𝓝 z] ψ') :
    topDens ψ z = topDens ψ' z := by
  have h1 : (fun y => ψ y / 2) =ᶠ[𝓝 z] fun y => ψ' y / 2 := h.fun_comp (· / 2)
  exact (maDens_eq_topDens _ ψ z EventuallyEq.rfl).symm.trans (maDens_eq_topDens _ ψ' z h1)

theorem topDens_continuousOn {ψ : (Fin D → ℂ) → ℝ} (hΩ : IsOpen Ω) (hψ : ContDiffOn ℝ ∞ ψ Ω) :
    ContinuousOn (topDens ψ) Ω := by
  have e : topDens ψ = maDens (fun _ : Fin D => fun y => ψ y / 2) :=
    funext fun z => (maDens_eq_topDens _ ψ z EventuallyEq.rfl).symm
  rw [e]
  exact maDens_continuousOn _ Ω hΩ fun _ => (hψ.div_const 2).of_le (WithTop.coe_le_coe.2 le_top)

def inclChart (hΩ : IsOpen Ω) [Nonempty Ω] : OpenPartialHomeomorph Ω (Fin D → ℂ) :=
  hΩ.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val

theorem inclChart_source (hΩ : IsOpen Ω) [Nonempty Ω] : (inclChart hΩ).source = Set.univ := by
  simp [inclChart]

theorem inclChart_target (hΩ : IsOpen Ω) [Nonempty Ω] : (inclChart hΩ).target = Ω := by
  simp [inclChart]

theorem inclChart_symm (hΩ : IsOpen Ω) [Nonempty Ω] (y : Fin D → ℂ) (hy : y ∈ Ω) :
    (((inclChart hΩ).symm y : Ω) : Fin D → ℂ) = y := by
  have h := (inclChart hΩ).right_inv (by rw [inclChart_target]; exact hy)
  simpa [inclChart] using h

def oneChartAtlas (hΩ : IsOpen Ω) [Nonempty Ω] : FinHolAtlas D Ω where
  n := 1
  chart _ := inclChart hΩ
  cover x := ⟨⟨0, Nat.one_pos⟩, by rw [inclChart_source]; trivial⟩
  holo := by
    intro _ _ y hy
    have hyΩ : y ∈ Ω := by rw [← inclChart_target hΩ]; exact hy.1
    refine analyticAt_id.congr ?_
    filter_upwards [hΩ.mem_nhds hyΩ] with z hz
    exact ((inclChart hΩ).right_inv (by rw [inclChart_target]; exact hz)).symm

def j0 (hΩ : IsOpen Ω) [Nonempty Ω] : Fin (oneChartAtlas hΩ).n := ⟨0, Nat.one_pos⟩

theorem oneChartAtlas_index_eq (hΩ : IsOpen Ω) [Nonempty Ω] (j : Fin (oneChartAtlas hΩ).n) : j = j0 hΩ :=
  Fin.ext (by have h1 : j.val < 1 := j.isLt; show j.val = 0; omega)

theorem oneChartAtlas_smooth (hΩ : IsOpen Ω) [Nonempty Ω] {f : (Fin D → ℂ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) : (oneChartAtlas hΩ).Smooth (fun x : Ω => f x) := by
  intro j
  have hs : (inclChart hΩ).target ∩ (inclChart hΩ).symm ⁻¹' Set.univ = Ω := by
    simp [inclChart_target]
  show ContDiffOn ℝ ∞ ((fun x : Ω => f x) ∘ (inclChart hΩ).symm)
    ((inclChart hΩ).target ∩ (inclChart hΩ).symm ⁻¹' Set.univ)
  rw [hs]
  exact hf.congr fun y hy => by simp only [Function.comp_apply, inclChart_symm hΩ y hy]

theorem oneChartAtlas_mInt (hΩ : IsOpen Ω) [Nonempty Ω] (Φ : Fin D → LocPot Ω) (g : Ω → ℝ) :
    mInt (oneChartAtlas hΩ) Φ g =
      ∫ y in Ω, g ((inclChart hΩ).symm y) * locDens (oneChartAtlas hΩ) Φ (j0 hΩ) y := by
  have hne : Nonempty (ChartPartition (oneChartAtlas hΩ)) :=
    ⟨{ χ := fun _ _ => 1
       smooth := fun _ _ => contDiffOn_const
       nonneg := fun _ _ => zero_le_one
       tsupport_subset := fun _ => by
         show _ ⊆ (inclChart hΩ).source
         rw [inclChart_source]; exact Set.subset_univ _
       sum_eq_one := fun _ => by show ∑ _j : Fin 1, (1 : ℝ) = 1; simp }⟩
  rw [mInt, dif_pos hne, integralWith]
  have hχ : ∀ j x, hne.some.χ j x = 1 := by
    intro j x
    have h := hne.some.sum_eq_one x
    rwa [Finset.sum_eq_single j (fun b _ hb => absurd ((oneChartAtlas_index_eq hΩ b).trans (oneChartAtlas_index_eq hΩ j).symm) hb)
      (by simp)] at h
  have hterm : ∀ j : Fin (oneChartAtlas hΩ).n,
      (∫ y in ((oneChartAtlas hΩ).chart j).target,
        hne.some.χ j (((oneChartAtlas hΩ).chart j).symm y) * g (((oneChartAtlas hΩ).chart j).symm y) *
          locDens (oneChartAtlas hΩ) Φ j y) =
      ∫ y in Ω, g ((inclChart hΩ).symm y) * locDens (oneChartAtlas hΩ) Φ (j0 hΩ) y := by
    intro j
    rw [oneChartAtlas_index_eq hΩ j]
    simp only [hχ, one_mul]
    show (∫ y in (inclChart hΩ).target, _) = _
    rw [inclChart_target]
    rfl
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  exact one_smul _ _

theorem oneChartAtlas_locDens (hΩ : IsOpen Ω) [Nonempty Ω] (L : LocPot Ω) (ψ : (Fin D → ℂ) → ℝ)
    (hL : ∀ x x', L.φ x x' = ψ x' / 2) (y : Fin D → ℂ) (hy : y ∈ Ω) :
    locDens (oneChartAtlas hΩ) (fun _ => L) (j0 hΩ) y = topDens ψ y := by
  unfold locDens
  simp only [hL]
  apply maDens_eq_topDens
  filter_upwards [hΩ.mem_nhds hy] with z hz
  show ψ ((inclChart hΩ).symm z : Fin D → ℂ) / 2 = ψ z / 2
  rw [inclChart_symm hΩ z hz]

end MACompact

open MACompact in

theorem MACompact.of_manifold
    (hA : GroundTheory.Heights₂.Heights.FourB.MongeAmpereCompactChange.Statement) :
    MACompact.Statement := by
  rintro D Ω φ v ⟨hΩ, hφ, hv, hvc, hvΩ⟩
  rcases Ω.eq_empty_or_nonempty with rfl | hne
  · simp
  have : Nonempty Ω := hne.to_subtype
  set T := tsupport v with hT
  let P : LocPot Ω := LocPot.ofFun fun x => φ x / 2
  let w : Ω → ℝ := fun x => v x / 2
  let K : Set Ω := Subtype.val ⁻¹' T
  have hKc : IsCompact K := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.2 hvΩ]
    exact hvc
  have hwK : tsupport w ⊆ K := by
    refine closure_minimal ?_ ((isClosed_tsupport v).preimage continuous_subtype_val)
    intro x hx
    exact subset_tsupport v fun h0 => hx (by simp [w, h0])
  have hmain := hA (oneChartAtlas hΩ) P w K
    ⟨isPotential_ofFun _ _ (oneChartAtlas_smooth hΩ (hφ.div_const 2)),
      oneChartAtlas_smooth hΩ (hv.div_const 2),
      hKc.of_isClosed_subset (isClosed_tsupport w) hwK, hKc, hwK⟩
  rw [oneChartAtlas_mInt, oneChartAtlas_mInt] at hmain
  have hind : ∀ y ∈ Ω, K.indicator (1 : Ω → ℝ) ((inclChart hΩ).symm y) =
      T.indicator (1 : (Fin D → ℂ) → ℝ) y := by
    intro y hy
    have hm : (inclChart hΩ).symm y ∈ K ↔ y ∈ T := by
      show (((inclChart hΩ).symm y : Ω) : Fin D → ℂ) ∈ T ↔ y ∈ T
      rw [inclChart_symm hΩ y hy]
    by_cases h : y ∈ T
    · rw [Set.indicator_of_mem (hm.2 h), Set.indicator_of_mem h]; rfl
    · rw [Set.indicator_of_notMem (mt hm.1 h), Set.indicator_of_notMem h]
  have hL1 : Set.EqOn (fun y => K.indicator 1 ((inclChart hΩ).symm y) *
      locDens (oneChartAtlas hΩ) (fun _ => P + LocPot.ofFun w) (j0 hΩ) y)
      (T.indicator (topDens (φ + v))) Ω := by
    intro y hy
    simp only
    rw [hind y hy, oneChartAtlas_locDens hΩ _ (φ + v) (fun x x' => by
      show φ x' / 2 + v x' / 2 = (φ + v) x' / 2
      rw [Pi.add_apply, add_div]) y hy]
    by_cases h : y ∈ T <;> simp [h]
  have hL2 : Set.EqOn (fun y => K.indicator 1 ((inclChart hΩ).symm y) *
      locDens (oneChartAtlas hΩ) (fun _ => P) (j0 hΩ) y) (T.indicator (topDens φ)) Ω := by
    intro y hy
    simp only
    rw [hind y hy, oneChartAtlas_locDens hΩ _ φ (fun x x' => rfl) y hy]
    by_cases h : y ∈ T <;> simp [h]
  rw [setIntegral_congr_fun hΩ.measurableSet hL1, setIntegral_congr_fun hΩ.measurableSet hL2]
    at hmain
  have hint : ∀ ψ : (Fin D → ℂ) → ℝ, ContDiffOn ℝ ∞ ψ Ω →
      IntegrableOn (T.indicator (topDens ψ)) Ω := fun ψ hψ =>
    (((topDens_continuousOn hΩ hψ).mono hvΩ).integrableOn_compact hvc).integrable_indicator
      (isClosed_tsupport v).measurableSet |>.integrableOn
  have heq : Set.EqOn (fun z => topDens (φ + v) z - topDens φ z)
      (fun z => T.indicator (topDens (φ + v)) z - T.indicator (topDens φ) z) Ω := by
    intro z _
    by_cases hz : z ∈ T
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, sub_zero, sub_eq_zero]
      exact topDens_congr ((notMem_tsupport_iff_eventuallyEq.1 hz).mono fun y hy => by
        simp only [Pi.add_apply, hy, Pi.zero_apply, add_zero])
  rw [setIntegral_congr_fun hΩ.measurableSet heq, integral_sub (hint (φ + v) (hφ.add hv)) (hint φ hφ),
    hmain, sub_self]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.PHermitianDetMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open Matrix
open scoped ComplexOrder MatrixOrder

theorem HermitianDetMono.one_le_det_one_add {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosSemidef) : 1 ≤ (1 + M).det := by
  have hH : (1 + M).IsHermitian := isHermitian_one.add hM.isHermitian
  have hev : ∀ i, (1 : ℝ) ≤ hH.eigenvalues i := by
    intro i
    rw [hH.eigenvalues_eq i]
    have hv : star ⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis i) = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hH.eigenvectorBasis.orthonormal.1 i]
      simp
    rw [add_mulVec, one_mulVec, dotProduct_add, map_add, hv, RCLike.one_re]
    linarith [hM.re_dotProduct_nonneg (hH.eigenvectorBasis i)]
  rw [hH.det_eq_prod_eigenvalues]
  have hprod : (1 : ℝ) ≤ ∏ i, hH.eigenvalues i := by
    calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ ∏ i, hH.eigenvalues i :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hev i)
  have key : ((1 : ℝ) : ℂ) ≤ ((∏ i, hH.eigenvalues i : ℝ) : ℂ) := Complex.real_le_real.mpr hprod
  convert key using 1
  · simp
  · simp [Complex.ofReal_prod]

theorem HermitianDetMono.proof : HermitianDetMono.Statement := by
  intro n A B hB hAB
  have hA : A.PosSemidef := by simpa using hB.add hAB
  suffices h : B.det ≤ A.det from (Complex.le_def.mp h).1
  by_cases hdet : B.det = 0
  · rw [hdet]; exact hA.det_nonneg
  · obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
    have hy : IsUnit y.det := by
      rw [det_mul] at hdet
      exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
    set M := (y⁻¹)ᴴ * (A - star y * y) * y⁻¹ with hMdef
    have hM : M.PosSemidef := hAB.conjTranspose_mul_mul_same y⁻¹
    have hfac : A = star y * (1 + M) * y := by
      have h1 : star y * (y⁻¹)ᴴ = 1 := by
        rw [star_eq_conjTranspose, ← conjTranspose_mul, nonsing_inv_mul y hy, conjTranspose_one]
      rw [hMdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
        nonsing_inv_mul y hy, Matrix.mul_one]
      abel
    have hdA : A.det = (1 + M).det * (star y * y).det := by
      conv_lhs => rw [hfac]
      rw [det_mul, det_mul, det_mul]; ring
    rw [hdA]
    exact le_mul_of_one_le_left hB.det_nonneg (HermitianDetMono.one_le_det_one_add hM)

end GroundTheory.Heights₂.Heights.FourB
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.PIntegralOnModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

theorem exists_prime_mul_eq_of_not_dvd {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a b : A} (hab : ¬ b ∣ a) :
    ∃ P : Ideal A, P.IsPrime ∧ ∃ w ∉ P, ∃ c ∈ P, w * b = c * a := by
  classical
  by_cases hb : b = 0
  · refine ⟨⊥, Ideal.isPrime_bot, 1, ?_, 0, (⊥ : Ideal A).zero_mem, by simp [hb]⟩
    rw [Submodule.mem_bot]
    exact one_ne_zero
  let N : Submodule A (A ⧸ Ideal.span {b}) := Submodule.span A {Ideal.Quotient.mk _ a}
  let n₀ : N := ⟨Ideal.Quotient.mk _ a, Submodule.subset_span rfl⟩
  have hn₀ : n₀ ≠ 0 := by
    intro h
    apply hab
    have : Ideal.Quotient.mk (Ideal.span {b}) a = 0 := congrArg Subtype.val h
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A n₀ hn₀
  obtain ⟨hPp, ⟨m, hm⟩, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.1 hm
  obtain ⟨y, hy⟩ : ∃ y, y = x * a := ⟨_, rfl⟩
  have hmem : ∀ r, r ∈ P ↔ b ∣ r * y := by
    intro r
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Subtype.coe_inj]
    show r • (x • Ideal.Quotient.mk (Ideal.span {b}) a) = 0 ↔ b ∣ r * y
    rw [smul_smul, GroundTheory.Arith.Toric.smul_mk_eq_zero_iff, hy, mul_assoc]
  have hbP : b ∈ P := (hmem b).2 (dvd_mul_right b y)
  by_cases hcase : ∀ r s : A, r ∈ P → r * y = b * s → s ∈ P
  · exfalso
    let K := FractionRing A
    have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
    let M : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hMfg : M.FG := (IsNoetherian.noetherian P).map _
    have hM0 : M ≠ ⊥ := by
      intro h
      have : algebraMap A K b ∈ M := Submodule.mem_map.2 ⟨b, hbP, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hb (hinj (by rw [this, map_zero]))
    have hbK : algebraMap A K b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hint : IsIntegral A (algebraMap A K y / algebraMap A K b) := by
      refine isIntegral_of_smul_mem_submodule M hM0 hMfg _ ?_
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨s, hs⟩ := (hmem r).1 hr
      refine Submodule.mem_map.2 ⟨s, hcase r s hr hs, ?_⟩
      change algebraMap A K s = (algebraMap A K y / algebraMap A K b) * algebraMap A K r
      rw [div_mul_eq_mul_div, eq_div_iff hbK, ← map_mul, ← map_mul, mul_comm y r, hs, mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hyz : y = b * z := by
      apply hinj
      rw [map_mul, hz, mul_div_cancel₀ _ hbK]
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, hmem, one_mul, hyz]
    exact dvd_mul_right b z
  · push Not at hcase
    obtain ⟨r₀, s₀, hr₀, hrs, hs₀⟩ := hcase
    refine ⟨P, hPp, s₀, hs₀, r₀ * x, P.mul_mem_right x hr₀, ?_⟩
    rw [mul_assoc, ← hy, hrs, mul_comm]

theorem IntegralOnModel.proof (hpt : IntegralPointThroughPrime.Statement) :
    IntegralOnModel.Statement := by
  intro F _ _ R _ _ _ _ _ _ r g s ⟨hs, hg, hpts⟩
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing (𝓞 F) R
  by_contra hndvd
  have hnd : ¬ algebraMap (𝓞 F) R s ∣ r := fun ⟨r', h⟩ => hndvd ⟨r', h⟩
  obtain ⟨P, hP, w, hw, c, hc, hwc⟩ := exists_prime_mul_eq_of_not_dvd hnd
  have hsP : algebraMap (𝓞 F) R s ∈ P := by
    have : w * algebraMap (𝓞 F) R s ∈ P := hwc ▸ P.mul_mem_right r hc
    exact (hP.mem_or_mem this).resolve_left hw
  have hpP : (P.comap (algebraMap (𝓞 F) R)).IsPrime := Ideal.comap_isPrime _ P
  have hp0 : P.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
    intro h
    have : s ∈ P.comap (algebraMap (𝓞 F) R) := hsP
    rw [h, Submodule.mem_bot] at this
    exact hs this
  let v : HeightOneSpectrum (𝓞 F) := ⟨P.comap (algebraMap (𝓞 F) R), hpP, hp0⟩
  obtain ⟨L, _, _, _, y, hcomp, hint, hyg, ⟨bw, hbw, hbwint⟩, hPnon⟩ :=
    hpt F R v P w g ⟨hP, rfl, hw, hg⟩
  have hys : y (algebraMap (𝓞 F) R s) ≠ 0 := by
    rw [← RingHom.comp_apply, hcomp]
    simp only [RingHom.comp_apply, ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    exact hs
  have hyr := hpts v L y hcomp hint hyg
  apply hPnon c hc (y r / y (algebraMap (𝓞 F) R s) * bw) _ (RingHom.IsIntegralElem.mul _ hyr hbwint)
  have h1 : y w * y (algebraMap (𝓞 F) R s) = y c * y r := by rw [← map_mul, ← map_mul, hwc]
  calc y r / y (algebraMap (𝓞 F) R s) * bw * y c
      = bw * y w * ((y c * y r) / (y w * y (algebraMap (𝓞 F) R s))) := by
        have hyw : y w ≠ 0 := fun h0 => by simp [h0] at hbw
        field_simp
    _ = 1 := by rw [hbw, ← h1, div_self (mul_ne_zero (fun h0 => by simp [h0] at hbw) hys), one_mul]

end GroundTheory.Heights₂.Heights.FourB
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.PRhoBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open Finset

theorem card_window_fin (n a b : ℕ) (hb : b ≤ n) :
    ∑ i : Fin n, (if a ≤ i.val ∧ i.val < b then (1 : ℝ) else 0) = ((b - a : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if a ≤ i ∧ i < b then (1 : ℝ) else 0) n,
    Finset.sum_boole]
  congr 2
  have : (Finset.range n).filter (fun i => a ≤ i ∧ i < b) = Finset.Ico a b := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico]

theorem RhoBound.proof (h : DegreeRatio.Statement) : RhoBound.Statement := by
  intro f k j j' x g₁ T w hH
  obtain ⟨hk, hg, hT, hw, hdec, hacr, hcloud⟩ := hH
  intro N ρ
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hg0 : 0 < g₁ := lt_of_le_of_lt (by positivity) hg
  have hδ : DegreeRatio.Hyp (k + j + j' - 1) j' x (3 * N) :=
    ⟨by positivity, hdec, fun τ i l hil => lt_of_lt_of_le hg (hacr τ i l hil)⟩
  obtain ⟨-, -, hle1, hsum⟩ := h f (k + j + j' - 1) j' x (3 * N) hδ

  have key : ∀ τ, ∑ i : Fin (k + j + j' - 1), ∑ l : Fin (k + j + j' - 1),
      (if Across (k + j + j' - 1) j' i l then 3 * N / (x τ i - x τ l) else 0) ≤
      3 * N * ((j : ℝ) * j' / g₁ + 2 * ((k : ℝ) - 1) * j' * T / w τ) := by
    intro τ
    set A : Fin (k + j + j' - 1) → ℝ := fun i => if 0 ≤ i.val ∧ i.val < k - 1 then 1 else 0
    set C : Fin (k + j + j' - 1) → ℝ := fun i => if k - 1 ≤ i.val ∧ i.val < k + j - 1 then 1 else 0
    set B : Fin (k + j + j' - 1) → ℝ :=
      fun l => if k + j - 1 ≤ l.val ∧ l.val < k + j + j' - 1 then 1 else 0
    have hterm : ∀ i l : Fin (k + j + j' - 1),
        (if Across (k + j + j' - 1) j' i l then 3 * N / (x τ i - x τ l) else 0) ≤
          3 * N * (2 * T / w τ) * (A i * B l) + 3 * N * (1 / g₁) * (C i * B l) := by
      intro i l
      have hT' : 0 ≤ 3 * N * (2 * T / w τ) := by have := hw τ; positivity
      have hg' : 0 ≤ 3 * N * (1 / g₁) := by positivity
      have hA0 : 0 ≤ A i := by simp only [A]; split_ifs <;> norm_num
      have hB0 : 0 ≤ B l := by simp only [B]; split_ifs <;> norm_num
      have hC0 : 0 ≤ C i := by simp only [C]; split_ifs <;> norm_num
      by_cases hA : Across (k + j + j' - 1) j' i l
      · rw [if_pos hA]
        have hd : g₁ ≤ x τ i - x τ l := hacr τ i l hA
        have hdpos : 0 < x τ i - x τ l := lt_of_lt_of_le hg0 hd
        have hB1 : B l = 1 := by
          simp only [B]; rw [if_pos]; unfold Across at hA; have := l.isLt; omega
        by_cases hc : i.val < k - 1
        · have hA1 : A i = 1 := by simp only [A]; rw [if_pos]; omega
          have hC1 : C i = 0 := by simp only [C]; rw [if_neg]; omega
          rw [hA1, hB1, hC1]
          have hwd : w τ / (2 * T) ≤ x τ i - x τ l := hcloud τ i l hc hA
          have hwpos : 0 < w τ / (2 * T) := by have := hw τ; positivity
          have : 1 / (x τ i - x τ l) ≤ 2 * T / w τ := by
            rw [div_le_div_iff₀ hdpos (hw τ)]
            rw [div_le_iff₀ (by positivity)] at hwd
            linarith
          calc 3 * N / (x τ i - x τ l) = 3 * N * (1 / (x τ i - x τ l)) := by ring
            _ ≤ 3 * N * (2 * T / w τ) := mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
        · have hA1 : A i = 0 := by simp only [A]; rw [if_neg]; omega
          have hC1 : C i = 1 := by
            simp only [C]; rw [if_pos]; unfold Across at hA; omega
          rw [hA1, hB1, hC1]
          have : 1 / (x τ i - x τ l) ≤ 1 / g₁ := one_div_le_one_div_of_le hg0 hd
          calc 3 * N / (x τ i - x τ l) = 3 * N * (1 / (x τ i - x τ l)) := by ring
            _ ≤ 3 * N * (1 / g₁) := mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
      · rw [if_neg hA]; positivity
    have hAs : ∑ i, A i = ((k - 1 - 0 : ℕ) : ℝ) := card_window_fin _ 0 (k - 1) (by omega)
    have hCs : ∑ i, C i = ((k + j - 1 - (k - 1) : ℕ) : ℝ) := card_window_fin _ _ _ (by omega)
    have hBs : ∑ l, B l = ((k + j + j' - 1 - (k + j - 1) : ℕ) : ℝ) :=
      card_window_fin _ _ _ le_rfl
    have e1 : k - 1 - 0 = k - 1 := by omega
    have e2 : k + j - 1 - (k - 1) = j := by omega
    have e3 : k + j + j' - 1 - (k + j - 1) = j' := by omega
    rw [e1] at hAs; rw [e2] at hCs; rw [e3] at hBs
    calc _ ≤ ∑ i : Fin (k + j + j' - 1), ∑ l : Fin (k + j + j' - 1),
          (3 * N * (2 * T / w τ) * (A i * B l) + 3 * N * (1 / g₁) * (C i * B l)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => hterm i l
      _ = 3 * N * (2 * T / w τ) * ((∑ i, A i) * ∑ l, B l) +
            3 * N * (1 / g₁) * ((∑ i, C i) * ∑ l, B l) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_mul_sum]
      _ = _ := by
          rw [hAs, hBs, hCs, Nat.cast_sub hk]
          have := hw τ
          field_simp
          ring
  refine ⟨by simp only [ρ]; linarith, ?_, ?_⟩
  · calc ρ ≤ ∑ τ, ∑ i : Fin (k + j + j' - 1), ∑ l : Fin (k + j + j' - 1),
          (if Across (k + j + j' - 1) j' i l then 3 * N / (x τ i - x τ l) else 0) := hsum
      _ ≤ ∑ τ, 3 * N * ((j : ℝ) * j' / g₁ + 2 * ((k : ℝ) - 1) * j' * T / w τ) :=
          Finset.sum_le_sum fun τ _ => key τ
      _ = _ := by rw [Finset.mul_sum]
  · rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    have hwτ := hw τ
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hj' : (0 : ℝ) ≤ j' := Nat.cast_nonneg _
    have h1 : (j : ℝ) * j' / g₁ ≤ 2 * (((j : ℝ) + j') ^ 2 / g₁) := by
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hg0]; nlinarith
    have h2 : 2 * ((k : ℝ) - 1) * j' * T / w τ ≤ 2 * (((j : ℝ) + j') * k * T / w τ) := by
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hwτ]
      have : ((k : ℝ) - 1) * j' ≤ ((j : ℝ) + j') * k := by nlinarith
      nlinarith
    nlinarith

end GroundTheory.Heights₂.Heights.FourB
end

