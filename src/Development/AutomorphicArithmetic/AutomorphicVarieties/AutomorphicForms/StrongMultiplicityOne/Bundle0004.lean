import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.SeedConv
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem exists_schwartz_integral_eq_one {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (F : X → ℂ) (U : Set X) (x₀ : X)
    (hU : U ∈ 𝓝 x₀) (hF : ContinuousOn F U) (h0 : F x₀ ≠ 0) : ∃ α : 𝓢(X, ℂ), ∫ x, F x * α x ∂μ = 1 := by
  have hc : ContinuousAt (fun x => (F x / F x₀).re) x₀ :=
    Complex.continuous_re.continuousAt.comp ((hF.continuousAt hU).div_const _)
  have hp : ∀ᶠ x in 𝓝 x₀, 0 < (F x / F x₀).re :=
    hc.eventually (lt_mem_nhds (by simp [div_self h0]))
  obtain ⟨r, hr, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (interior_mem_nhds.2 hU) hp)
  let b : ContDiffBump x₀ := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hs : tsupport b = Metric.closedBall x₀ r := b.tsupport_eq
  have hs' : Function.support b = Metric.ball x₀ r := b.support_eq
  have hG : Continuous fun x => b x • (F x / F x₀) := by
    refine continuous_of_tsupport fun x hx => ?_
    have hx' : x ∈ Metric.closedBall x₀ r := hs ▸ tsupport_smul_subset_left _ _ hx
    exact b.continuous.continuousAt.smul ((hF.continuousAt (mem_interior_iff_mem_nhds.1 (hb hx').1)).div_const _)
  have hK : HasCompactSupport fun x => b x • (F x / F x₀) := b.hasCompactSupport.smul_right
  have hI : Integrable (fun x => b x • (F x / F x₀)) μ := hG.integrable_of_hasCompactSupport hK
  have hpos : 0 < ∫ x, (b x • (F x / F x₀)).re ∂μ := by
    refine (Complex.continuous_re.comp hG).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x₀)
      (hK.comp_left (g := Complex.re) rfl) (fun x => ?_) ?_
    · by_cases hx : b x = 0
      · simp [hx]
      · have hx' : x ∈ Metric.closedBall x₀ r := Metric.ball_subset_closedBall (hs' ▸ hx)
        have h1 : 0 < (F x / F x₀).re := (hb hx').2
        simpa using mul_nonneg b.nonneg h1.le
    · have h1 : b x₀ = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
      simp [h1, div_self h0]
  have hne : ∫ x, b x • (F x / F x₀) ∂μ ≠ 0 := by
    intro h
    have h2 := integral_re hI
    rw [h] at h2
    simp only [RCLike.re_to_complex, Complex.zero_re] at h2
    exact hpos.ne' h2
  set c := ∫ x, b x • (F x / F x₀) ∂μ with hc'
  have hd : ContDiff ℝ ∞ fun x => b x • ((F x₀)⁻¹ * c⁻¹) := b.contDiff.smul contDiff_const
  have hk : HasCompactSupport fun x => b x • ((F x₀)⁻¹ * c⁻¹) := b.hasCompactSupport.smul_right
  refine ⟨hk.toSchwartzMap hd, ?_⟩
  have e : ∀ x, F x * (hk.toSchwartzMap hd) x = (b x • (F x / F x₀)) * c⁻¹ := fun x => by
    change F x * (b x • ((F x₀)⁻¹ * c⁻¹)) = _
    simp only [Complex.real_smul, div_eq_mul_inv]
    ring
  simp only [e]
  rw [integral_mul_const, ← hc', mul_inv_cancel₀ hne]

theorem UpperTheory.V.Af.StrongMultiplicityOne.seedConv :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.SeedConv := by
  intro h E _ _ _ n W hW y hy
  haveI i1 : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  refine exists_schwartz_integral_eq_one volume (chart W 1) (invSet E n) (toL y.val) ?_ ?_ ?_
  · exact GlobalTheory.CuspRep.isOpen_invSet.mem_nhds (GlobalTheory.CuspRep.val_mem_invSet y)
  · exact (h E n W hW).1.comp (f := fun x => ((1 : GA E n), x)) (by fun_prop) fun x hx => ⟨trivial, hx⟩
  · rw [GlobalTheory.CuspRep.chart_val, one_mul]
    exact hy
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.TrDual
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.trDual :
    UpperTheory.V.Af.StrongMultiplicityOne.TrDual := by
  classical
  intro E _ _
  let B : LinearMap.BilinForm ℝ (Cinf E) := (LinearMap.mul ℝ (Cinf E)).compr₂ (TG.tr E)
  have hl : ∀ x : Cinf E, (∀ y, B x y = 0) → x = 0 := fun x h => by
    have h1 : ∑ w, 2 * (x w * starRingEnd ℂ (x w)).re = 0 := h fun w => starRingEnd ℂ (x w)
    simp only [Complex.mul_conj, Complex.ofReal_re] at h1
    have b' := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg (x w))).1 h1
    exact funext fun w => Complex.normSq_eq_zero.1 ((mul_eq_zero.1 (b' w (Finset.mem_univ _))).resolve_left two_ne_zero)
  have hB : B.Nondegenerate := ⟨hl, fun x h => hl x fun y => by
    have := h y
    change TG.tr E (_ * _) = 0 at this ⊢
    rwa [mul_comm]⟩
  let b := Module.finBasis ℝ (Cinf E)
  refine ⟨_, b, B.dualBasis hB b, fun x y => ?_⟩
  conv_lhs => rw [← b.sum_repr y]
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Vanish
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem isY_map {R T : Type} [CommRing R] [CommRing T] {n m : ℕ} (φ : R →+* T) {p : GL (Fin n) R}
    (h : IsY m p.val) : IsY m (GeneralLinearGroup.map φ p).val := fun i hi =>
  ⟨by change φ (p.val i i) = 1; rw [(h i hi).1, map_one],
    fun j hj => by change φ (p.val i j) = 0; rw [(h i hi).2 j hj, map_zero]⟩

private theorem isY_one {R : Type} [CommRing R] {n m : ℕ} : IsY m (1 : GL (Fin n) R).val := fun i _ =>
  ⟨by simp, fun j hj => by simp [Matrix.one_apply_ne hj.ne']⟩

private theorem isY_mul {R : Type} [CommRing R] {n m : ℕ} {p q : GL (Fin n) R}
    (hp : IsY m p.val) (hq : IsY m q.val) : IsY m (p * q).val := by
  intro i hi
  have key : ∀ j, j ≤ i → (p * q).val i j = q.val i j := by
    intro j hj
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, (hp i hi).1, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hp i hi).2 k h, zero_mul]
      · rw [(hq k (hi.trans h.le)).2 j (hj.trans_lt h), mul_zero]
    · simp
  exact ⟨by rw [key i le_rfl, (hq i hi).1], fun j hj => by rw [key j hj.le, (hq i hi).2 j hj]⟩

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem exists_part (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (Af E)) :
    ∃ s : GL (Fin n) (Af E), SuppIn S s ∧ ∀ w ∈ S, cmp w s = cmp w g := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun w _ => map_one _, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert v S hv ih =>
    obtain ⟨s, h1, h2⟩ := ih
    refine ⟨s * locGL E n v (cmp v g), fun w hw => ?_, fun w hw => ?_⟩
    · rw [Finset.mem_insert, not_or] at hw
      rw [map_mul, h1 w hw.2, one_mul]
      exact GlobalTheory.CuspRep.pLoc_locGL_of_ne hw.1 _
    · rw [map_mul]
      rcases Finset.mem_insert.1 hw with rfl | h
      · rw [h1 w hv, one_mul]
        exact GlobalTheory.CuspRep.pLoc_locGL _ _
      · rw [h2 w h, show cmp w (locGL E n v (cmp v g)) = 1 from
          GlobalTheory.CuspRep.pLoc_locGL_of_ne (fun e : w = v => hv (e ▸ h)) _, mul_one]

private theorem af_ext {x y : Af E} (h : ∀ w, pLoc E w x = pLoc E w y) : x = y :=
  DFunLike.ext _ _ h

private theorem isY_af {m : ℕ} {s : GL (Fin n) (Af E)} (h : ∀ w, IsY m (cmp w s).val) : IsY m s.val := fun i hi =>
  ⟨af_ext fun w => by rw [map_one]; exact (h w i hi).1,
    fun j hj => af_ext fun w => by rw [map_zero]; exact (h w i hi).2 j hj⟩

private theorem pFin_finGL (k : GL (Fin n) (Af E)) : GeneralLinearGroup.map (pFin E) (finGL E n k) = k := by
  rw [finGL, GlobalTheory.CuspRep.map_cornerGL_of_hom _ _ (RingHom.id _) fun x => rfl]
  rfl

variable [IsTotallyComplex E]

private theorem isY_ad {m : ℕ} {g : GA E n} (h1 : IsY m (GeneralLinearGroup.map (pInf E) g).val)
    (h2 : IsY m (GeneralLinearGroup.map (pFin E) g).val) : IsY m g.val := fun i hi =>
  ⟨GlobalTheory.CuspRep.ad_ext (by rw [map_one]; exact (h1 i hi).1) (by rw [map_one]; exact (h2 i hi).1),
    fun j hj => GlobalTheory.CuspRep.ad_ext (by rw [map_zero]; exact (h1 i hi).2 j hj) (by rw [map_zero]; exact (h2 i hi).2 j hj)⟩

private theorem exists_dec (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E n)
    (h1 : IsY (n - 1) (GeneralLinearGroup.map (pInf E) g).val)
    (h2 : ∀ w ∈ S, IsY (n - 1) (cmp w (GeneralLinearGroup.map (pFin E) g)).val) :
    ∃ p k, InPS S p ∧ Away S k ∧ g = p * finGL E n k := by
  obtain ⟨s, hs, hg⟩ := exists_part S (GeneralLinearGroup.map (pFin E) g)
  have e : GeneralLinearGroup.map (pFin E) (infGL E n (GeneralLinearGroup.map (pInf E) g) * finGL E n s) = s := by
    rw [map_mul, GlobalTheory.CuspRep.pFin_infGL, pFin_finGL, one_mul]
  refine ⟨infGL E n (GeneralLinearGroup.map (pInf E) g) * finGL E n s, s⁻¹ * GeneralLinearGroup.map (pFin E) g,
    ⟨isY_ad ?_ ?_, ?_⟩, fun w hw => ?_, ?_⟩
  · rw [map_mul, GlobalTheory.CuspRep.pInf_infGL, GlobalTheory.CuspRep.pInf_finGL, mul_one]
    exact h1
  · rw [e]
    refine isY_af fun w => ?_
    by_cases hw : w ∈ S
    · rw [hg w hw]; exact h2 w hw
    · rw [hs w hw]; exact isY_one
  · rw [e]; exact hs
  · rw [map_mul, map_inv, hg w hw, inv_mul_cancel]
  · rw [mul_assoc, ← map_mul, mul_inv_cancel_left, GlobalTheory.CuspRep.infGL_mul_finGL]

end

theorem UpperTheory.V.Af.StrongMultiplicityOne.vanish :
    UpperTheory.V.Af.StrongMultiplicityOne.SphAll → UpperTheory.V.Af.Smo.InjP → UpperTheory.V.Af.Smo.DenseAway → UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.StrongMultiplicityOne.EigMap → UpperTheory.V.Af.StrongMultiplicityOne.Vanish := by
  intro hSA hI hD hWB hEM E _ _ _ n hn S B f hf hS hK h0
  have hW : ∀ p, InPS S p → ∀ k, Away S k → whittaker f (p * finGL E n k) = 0 := fun p hp =>
    hSA E n S B (whittaker f) (hWB E n f hf).2.2
      (fun w hw => ⟨(hS w hw).1, (hEM E n w (B w) f (hS w hw).2).1 hf⟩)
      (fun g k hk => by
        unfold whittaker
        simp only [← mul_assoc, hK _ k hk]) p hp.2 (h0 p hp)
  have hX := hI E n hn f hf {g | IsY (n - 1) (GeneralLinearGroup.map (pInf E) g).val ∧
      ∀ w ∈ S, IsY (n - 1) (cmp w (GeneralLinearGroup.map (pFin E) g)).val}
    (fun γ hγ g hg => by
      have h : IsY (n - 1) (ratGL E n γ).val := isY_map _ hγ
      refine ⟨?_, fun w hw => ?_⟩
      · rw [map_mul]; exact isY_mul (isY_map _ h) hg.1
      · rw [map_mul, map_mul]; exact isY_mul (isY_map _ (isY_map _ h)) (hg.2 w hw))
    (fun g hg => by
      obtain ⟨p, k, hp, hk, rfl⟩ := exists_dec S g hg.1 hg.2
      exact hW p hp k hk)
  refine Continuous.ext_on (hD E n S) hf.cont continuous_const ?_
  rintro _ ⟨γ, k, hk, rfl⟩
  have h : f (finGL E n k) = 0 := hX _ ⟨by rw [GlobalTheory.CuspRep.pInf_finGL]; exact isY_one, fun w hw => by
    rw [pFin_finGL, hk w hw]; exact isY_one⟩
  exact (hf.left γ _).trans h
end

