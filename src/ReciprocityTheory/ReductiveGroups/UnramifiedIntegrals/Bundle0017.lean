import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0016
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0013
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonD
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Tools

variable {R : Type} [CommRing R]

theorem constCoeff_subst_zero {g s : PowerSeries R} (hs : constantCoeff s = 0) :
    constantCoeff (g.subst s) = constantCoeff g := by
  have ha : HasSubst s := HasSubst.of_constantCoeff_zero hs
  rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, hs, zero_pow hd]

theorem coeffOne_subst_zero {f s : PowerSeries R} (hs : constantCoeff s = 0) :
    coeff 1 (f.subst s) = coeff 1 f * coeff 1 s := by
  have ha : HasSubst s := HasSubst.of_constantCoeff_zero hs
  have hX : X ∣ s := X_dvd_iff.mpr hs
  rw [PowerSeries.coeff_subst' ha, finsum_eq_single _ 1]
  · simp [smul_eq_mul]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have : d = 0 := by omega
      subst this
      simp
    · have h2 : X ^ d ∣ s ^ d := pow_dvd_pow_of_dvd hX d
      have h3 := X_pow_dvd_iff.mp h2 1 h
      simp [h3]

theorem subst_C_mul_mv {ι : Type} {P : MvPowerSeries ι R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = MvPowerSeries.C c * f.subst P := by
  rw [← smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ← coe_substAlgHom hP, map_smul]

theorem subst_C_mul_ps {P : PowerSeries R} (hP : HasSubst P) (c : R)
    (f : PowerSeries R) : (C c * f).subst P = C c * f.subst P := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, ← coe_substAlgHom hP, map_smul]

end Tools

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}

variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem LawD.map (hF : FrobField K l σ) (h : LawD lam Φ) :
    LawD (PowerSeries.map σ lam) (MvPowerSeries.map σ Φ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.lam0,
      map_zero]
  · rw [coeff_map, h.lam1, map_one]
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, map_zero]
  · have h1 := h.Φint
    unfold IntegralMv at h1 ⊢
    intro e
    rw [MvPowerSeries.coeff_map, hF.isom]
    exact h1 e
  · have h1 := congrArg (MvPowerSeries.map σ) h.log
    unfold atX atY at h1 ⊢
    rw [map_add] at h1
    erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero h.Φ0),
      PowerSeries.map_subst (HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)),
      PowerSeries.map_subst (HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)),
      MvPowerSeries.map_X, MvPowerSeries.map_X] at h1
    exact h1

theorem HD.map (hF : FrobField K l σ) (h : HD σ lam Φ A a) :
    HD σ (PowerSeries.map σ lam) (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) (σ a) := by
  refine ⟨h.toLawD.map hF, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.A0,
      map_zero]
  · have h1 := h.Aint
    unfold IntegralPS at h1 ⊢
    intro n
    rw [coeff_map, hF.isom]
    exact h1 n
  · have h1 := congrArg (PowerSeries.map σ) h.Alog
    erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero h.A0)] at h1
    rw [map_mul, map_C] at h1
    exact h1
  · rw [h.a_sq, norm_sub_rev]
    exact h.a_ne
  · rw [h.a_sq]

theorem HD.coeff_one_A (h : HD σ lam Φ A a) : coeff 1 A = a := by
  have h1 := congrArg (coeff 1) h.Alog
  rw [coeffOne_subst_zero h.A0, coeff_C_mul, h.lam1, one_mul, mul_one] at h1
  exact h1

theorem HD.norm_a (h : HD σ lam Φ A a) : ‖a‖ ≤ 1 := by
  have h1 := h.Aint
  unfold IntegralPS at h1
  rw [← h.coeff_one_A]
  exact h1 1

theorem HD.qcls_lam (h : HD σ lam Φ A a) : QCls l Φ A a lam := by
  refine ⟨h.lam0, h.toLawD.deriv_integral, ?_, ?_⟩
  · have h0 : lam.subst Φ - atX lam - atY lam = 0 := by rw [h.log]; ring
    rw [h0]
    unfold DivByMv
    intro e
    simp
  · have h0 : lam.subst A - C a * lam = 0 := by rw [h.Alog]; ring
    rw [h0]
    unfold DivBy
    intro n
    simp

theorem eigen_trick {A : PowerSeries K} {b : K} (hA0 : constantCoeff A = 0) (D : PowerSeries K)
    (hD0 : constantCoeff D = 0) (h : DivBy (l : K) (D.subst A - C b * D))
    (hb : ‖coeff 1 A - b‖ = 1) : ‖coeff 1 D‖ ≤ ‖(l : K)‖ := by
  have h0 := h
  unfold DivBy at h0
  have h1 := h0 1
  have e : coeff 1 D * coeff 1 A - b * coeff 1 D = coeff 1 D * (coeff 1 A - b) := by ring
  rw [map_sub, coeffOne_subst_zero hA0, coeff_C_mul, e, norm_mul, hb, mul_one] at h1
  exact h1

theorem divBy_C_mul {x c : K} (hc : ‖c‖ ≤ 1) {f : PowerSeries K} (hf : DivBy x f) :
    DivBy x (C c * f) := by
  unfold DivBy at *
  intro n
  rw [coeff_C_mul, norm_mul]
  calc ‖c‖ * ‖coeff n f‖ ≤ 1 * ‖x‖ := mul_le_mul hc (hf n) (norm_nonneg _) zero_le_one
    _ = ‖x‖ := one_mul _

theorem divBy_C_mul' {x c : K} (hc : ‖c‖ ≤ ‖x‖) {f : PowerSeries K} (hf : IntegralPS f) :
    DivBy x (C c * f) := by
  unfold DivBy IntegralPS at *
  intro n
  rw [coeff_C_mul, norm_mul]
  calc ‖c‖ * ‖coeff n f‖ ≤ ‖x‖ * 1 := mul_le_mul hc (hf n) (norm_nonneg _) (norm_nonneg _)
    _ = ‖x‖ := mul_one _

theorem derivative_C_mul' (c : K) (f : PowerSeries K) :
    derivative K (C c * f) = C c * derivative K f := by
  rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul]

theorem QCls.norm_coeff_one {b : K} {D : PowerSeries K} (hD : QCls l Φ A b D) :
    ‖coeff 1 D‖ ≤ 1 := by
  have h0 := hD.dInt
  unfold IntegralPS at h0
  have h1 := h0 0
  rw [coeff_derivative] at h1
  simpa using h1

theorem HD.qcls_sub (h : HD σ lam Φ A a) {D : PowerSeries K} (hD : QCls l Φ A a D) :
    QCls l Φ A a (D - C (coeff 1 D) * lam) := by
  set c := coeff 1 D with hc
  have hc1 : ‖c‖ ≤ 1 := hD.norm_coeff_one
  have hΦ : HasSubst Φ := HasSubst.of_constantCoeff_zero h.Φ0
  have hA : HasSubst A := HasSubst.of_constantCoeff_zero h.A0
  have hX0 : HasSubst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)
  have hX1 : HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)
  have sub_subst : ∀ {P : MvPowerSeries (Fin 2) K} (_ : HasSubst P) (f g : PowerSeries K),
      (f - g).subst P = f.subst P - g.subst P := fun hP f g => by
    rw [← coe_substAlgHom hP, map_sub]
  have sub_substA : (D - C c * lam).subst A = D.subst A - C c * lam.subst A := by
    rw [← coe_substAlgHom hA, map_sub, coe_substAlgHom hA, subst_C_mul_ps hA]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hD.D0, h.lam0]
  · have hd := hD.dInt
    have hl := h.toLawD.deriv_integral
    unfold IntegralPS at hd hl ⊢
    intro n
    rw [map_sub, derivative_C_mul', map_sub, coeff_C_mul, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hd n) ?_)
    rw [norm_neg, norm_mul]
    calc ‖c‖ * ‖coeff n (derivative K lam)‖ ≤ 1 * 1 :=
          mul_le_mul hc1 (hl n) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have e : (D - C c * lam).subst Φ - atX (D - C c * lam) - atY (D - C c * lam) =
        (D.subst Φ - atX D - atY D) - MvPowerSeries.C c * (lam.subst Φ - atX lam - atY lam) := by
      unfold atX atY
      rw [sub_subst hΦ, sub_subst hX0, sub_subst hX1, subst_C_mul_mv hΦ, subst_C_mul_mv hX0,
        subst_C_mul_mv hX1]
      ring
    have e2 : lam.subst Φ - atX lam - atY lam = 0 := by rw [h.log]; ring
    rw [e, e2, mul_zero, sub_zero]
    exact hD.add
  · have e : (D - C c * lam).subst A - C a * (D - C c * lam) = D.subst A - C a * D := by
      rw [sub_substA, h.Alog]
      ring
    rw [e]
    exact hD.eig

theorem lemmaQ (hF : FrobField K l σ) (h : HD σ lam Φ A a) {D : PowerSeries K}
    (hD : QCls l Φ A a D) :
    ∃ Dp : PowerSeries K,
      QCls l (MvPowerSeries.map (σ.comp σ) Φ) (PowerSeries.map (σ.comp σ) A) a Dp ∧
      DivBy (l : K) (D - C (coeff 1 D) * lam - Dp.subst ((X : PowerSeries K) ^ (l ^ 2))) := by
  have hl0 : l ≠ 0 := hF.prime.ne_zero
  set E : PowerSeries K := D - C (coeff 1 D) * lam with hE
  have hEq : QCls l Φ A a E := h.qcls_sub hD
  have hE' : DivBy (l : K) (derivative K E) := by
    have := hon_deriv h.toLawD (l : K) D hD.add
    rwa [hE, map_sub, derivative_C_mul']
  have h1 : QCls l (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) a (desc l E) :=
    desc_QCls hF h.Φ0 h.Φint h.A0 h.Aint h.norm_a hEq hE'
  have c1 := (desc_congr hF.prime hF.norm_l E hE').1
  have hσ := h.map hF
  have hs : ‖coeff 1 (desc l E)‖ ≤ ‖(l : K)‖ :=
    eigen_trick hσ.A0 _ h1.D0 h1.eig (by rw [hσ.coeff_one_A]; exact h.a_ne)
  have h1' : DivBy (l : K) (derivative K (desc l E)) := by
    have h2 := hon_deriv hσ.toLawD (l : K) _ h1.add
    have h3 := divBy_add h2 (divBy_C_mul' hs hσ.toLawD.deriv_integral)
    rwa [sub_add_cancel] at h3
  have h2 : QCls l (MvPowerSeries.map σ (MvPowerSeries.map σ Φ))
      (PowerSeries.map σ (PowerSeries.map σ A)) a (desc l (desc l E)) :=
    desc_QCls hF hσ.Φ0 hσ.Φint hσ.A0 hσ.Aint h.norm_a h1 h1'
  have c2 := (desc_congr hF.prime hF.norm_l _ h1').1
  refine ⟨desc l (desc l E), ?_, ?_⟩
  · have e1 : MvPowerSeries.map (σ.comp σ) Φ = MvPowerSeries.map σ (MvPowerSeries.map σ Φ) := by
      ext d; simp
    have e2 : PowerSeries.map (σ.comp σ) A = PowerSeries.map σ (PowerSeries.map σ A) := by
      ext d; simp
    rw [e1, e2]; exact h2
  · have hXl : HasSubst ((X : PowerSeries K) ^ l) :=
      HasSubst.of_constantCoeff_zero' (by simp [hl0])
    have c3 := (divBy_expand_iff (l : K) l hl0 _).2 c2
    rw [subst_sub hXl, subst_comp_subst_apply hXl hXl, subst_pow hXl, subst_X hXl, ← pow_mul,
      ← sq] at c3
    have c4 := divBy_add c1 c3
    rwa [sub_add_sub_cancel] at c4

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFixJ
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem fixJ_nonunits_add {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : a ∈ A.nonunits)
    (hb : b ∈ A.nonunits) : a + b ∈ A.nonunits := by
  exact add_mem ha hb

def fixJRoots {Ω : Type*} [Field Ω] (P : Polynomial ℤ) : Finset Ω := (P.map (Int.castRingHom Ω)).roots.toFinset

theorem mem_fixJRoots {Ω : Type*} [Field Ω] {P : Polynomial ℤ} (hP : P.Monic) (r : Ω) :
    r ∈ fixJRoots (Ω := Ω) P ↔ P.eval₂ (Int.castRingHom Ω) r = 0 := by
  rw [fixJRoots, Multiset.mem_toFinset, Polynomial.mem_roots (hP.map _).ne_zero, Polynomial.IsRoot.def,
    Polynomial.eval_map]

theorem map_mem_fixJRoots {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} (hP : P.Monic)
    (g : Ω ≃ₐ[E] Ω) {r : Ω} (hr : r ∈ fixJRoots (Ω := Ω) P) : g r ∈ fixJRoots (Ω := Ω) P := by
  rw [mem_fixJRoots hP] at hr ⊢
  have h := Polynomial.hom_eval₂ P (Int.castRingHom Ω) (g : Ω →+* Ω) r
  rw [hr, map_zero, RingHom.ext_int ((g : Ω →+* Ω).comp (Int.castRingHom Ω)) (Int.castRingHom Ω)] at h
  exact h.symm

theorem isIntegral_of_mem_fixJRoots {Ω : Type*} [Field Ω] {P : Polynomial ℤ} (hP : P.Monic) {r : Ω}
    (hr : r ∈ fixJRoots (Ω := Ω) P) : IsIntegral ℤ r := by
  refine ⟨P, hP, ?_⟩
  rw [algebraMap_int_eq]
  exact (mem_fixJRoots hP r).1 hr

def fixJStab (E Ω : Type*) [Field E] [Field Ω] [Algebra E Ω] (P : Polynomial ℤ) : Subgroup (Ω ≃ₐ[E] Ω) where
  carrier := {g | ∀ r ∈ fixJRoots (Ω := Ω) P, g r = r}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb r hr
    rw [AlgEquiv.mul_apply, hb r hr, ha r hr]
  inv_mem' := by
    intro a ha r hr
    have := ha r hr
    calc a⁻¹ r = a⁻¹ (a r) := by rw [this]
      _ = r := by rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl

theorem mem_fixJStab {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} {g : Ω ≃ₐ[E] Ω} :
    g ∈ fixJStab E Ω P ↔ ∀ r ∈ fixJRoots (Ω := Ω) P, g r = r := Iff.rfl

theorem fixJStab_normal {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} (hP : P.Monic) :
    (fixJStab E Ω P).Normal := by
  constructor
  intro n hn g
  rw [mem_fixJStab] at hn ⊢
  intro r hr
  have h1 : g⁻¹ r ∈ fixJRoots (Ω := Ω) P := map_mem_fixJRoots hP g⁻¹ hr
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel]
  rfl

theorem fixJStab_isOpen {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] [Algebra.IsAlgebraic E Ω]
    {P : Polynomial ℤ} : IsOpen (fixJStab E Ω P : Set (Ω ≃ₐ[E] Ω)) := by
  let K : IntermediateField E Ω := IntermediateField.adjoin E ((fixJRoots (Ω := Ω) P : Finset Ω) : Set Ω)
  haveI : FiniteDimensional E K := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral)
  refine Subgroup.isOpen_mono (H₁ := K.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen K)
  intro g hg
  rw [mem_fixJStab]
  intro r hr
  exact hg ⟨r, IntermediateField.subset_adjoin E _ hr⟩

theorem fixJ_ker_isOpen (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E)) (hk : art.ker = hilbertSubgroup E Ω) :
    IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) := by
  refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
  rw [hk]
  exact Subgroup.isClosed_topologicalClosure _

theorem fixJ (hH : _root_.Neutral.HilbertClassField.Statement) (hC : ChebOmSt)
    {d : ℕ} {L : PeriodPair} (hsf : Squarefree d) (hd : d % 4 = 3) (hL : HasCMBy d L)
    (x : Om d) (hx : (x : ℂ) = jInv L) (σ : Om d ≃ₐ[KQ d] Om d) (hσ : σ ∈ hilbertSubgroup (KQ d) (Om d)) :
    σ x = x := by
  obtain ⟨art, -, hker, hfrob⟩ := hH (KQ d) (Om d)
  have hxi : IsIntegral ℤ x := by
    obtain ⟨y, hy, hyi⟩ := exists_Om d (cm1 d L hsf hd hL)
    have : y = x := Subtype.ext (hy.trans hx.symm)
    rwa [this] at hyi
  obtain ⟨P, hP, hPx⟩ := hxi
  have hxs : x ∈ fixJRoots (Ω := Om d) P := by
    rw [mem_fixJRoots hP]
    rwa [show algebraMap ℤ (Om d) = Int.castRingHom (Om d) from RingHom.ext_int _ _] at hPx
  obtain ⟨n, hn0, hn⟩ := sepInt (fixJRoots (Ω := Om d) P) (fun r hr => isIntegral_of_mem_fixJRoots hP hr)
  set S : Set (HeightOneSpectrum (𝓞 (KQ d))) := {v | (n : 𝓞 (KQ d)) ∈ v.asIdeal} with hS
  have hSfin : S.Finite := finite_places (KQ d) hn0

  have key : ∀ (A : ValuationSubring (Om d)) (v : HeightOneSpectrum (𝓞 (KQ d))), LiesAbove A v → v ∉ S →
      ∀ r ∈ fixJRoots (Ω := Om d) P, ∀ r' ∈ fixJRoots (Ω := Om d) P, r - r' ∈ A.nonunits → r = r' := by
    intro A v hA hv r hr r' hr' h
    by_contra hne
    have h1 := hn r hr r' hr' hne A h
    apply hv
    rw [hS, Set.mem_ofPred_eq, ← hA]
    simpa using h1
  set H : Subgroup (Om d ≃ₐ[KQ d] Om d) := art.ker ⊓ fixJStab (KQ d) (Om d) P with hH
  have := fixJStab_normal (E := KQ d) (Ω := Om d) hP
  have hHn : H.Normal := inferInstance
  have hHo : IsOpen (H : Set (Om d ≃ₐ[KQ d] Om d)) := by
    rw [hH, Subgroup.coe_inf]
    exact (fixJ_ker_isOpen _ _ art hker).inter fixJStab_isOpen
  obtain ⟨A, v, φ, hA, hv, hp, hφ, hσφ⟩ := hC (KQ d) (Om d) S hSfin H hHn hHo (by
    intro A v hA hv g hg
    refine ⟨by rw [hker]; exact inertiaEl_mem_hilbert hg, fun r hr => ?_⟩
    exact key A v hA hv _ (map_mem_fixJRoots hP g hr) _ hr
      (hg.2 r (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hr)))) σ
  have hσ1 : art σ = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hσ
  have hφ1 : art φ = 1 := by
    have : σ⁻¹ * φ ∈ art.ker := hσφ.1
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ1, inv_one, one_mul] at this
    exact this
  have hcl := hfrob v A φ hA hφ
  rw [hφ1] at hcl
  have h1 := frobCong hsf hd hL x hx A v hA hp hcl.symm
  have h2 := hφ.2 x (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hxs))
  have h3 : φ x - x ∈ A.nonunits := by
    have := fixJ_nonunits_add A h2 h1
    simpa using this
  have h4 : φ x = x := key A v hA hv _ (map_mem_fixJRoots hP φ hxs) _ hxs h3
  have h5 := hσφ.2 x hxs
  rw [AlgEquiv.mul_apply, h4] at h5
  calc σ x = σ (σ⁻¹ x) := by rw [h5]
    _ = x := by rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocA
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem fixed_mem_Kur {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hK : FiniteDimensional ℚ_[l] K) (y : PadicAlgCl l)
    (h : ∀ ρ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l, (∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖ρ z - z‖ < 1) → ρ y = y) :
    y ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l K := by
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_iff_fixed (ReciprocityTheory.DiscreteGroups.LocalClassField.le_Kur (p := l) (K := K)) y]
  intro σ hσ
  exact h σ ((ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_Kur_iff hK σ).1 hσ)

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

def redSqD (d : ℕ) : ℂ := 2 * omegaK d - 1

def IsHalfReps (L : PeriodPair) (α : ℂ) (T : Finset ℂ) : Prop :=
  (∀ P ∈ T, α * P ∈ L.lattice ∧ 2 * P ∉ L.lattice) ∧
  (∀ P ∈ T, ∀ Q ∈ T, (P - Q ∈ L.lattice ∨ P + Q ∈ L.lattice) → P = Q) ∧
  (∀ z, α * z ∈ L.lattice → z ∉ L.lattice → ∃ P ∈ T, z - P ∈ L.lattice ∨ z + P ∈ L.lattice)

def xsOf (L : PeriodPair) (T : Finset ℂ) : Finset ℂ := T.image L.weierstrassP

section Alg

variable {K : Type} [Field K]

def rootPoly (xs : Finset K) : K[X] := ∏ x ∈ xs, (X - C x)

def fW (g2 g3 x : K) : K := 4 * x ^ 3 - g2 * x - g3

def fW' (g2 x : K) : K := 12 * x ^ 2 - g2

def veluFun (g2 g3 : K) (xs : Finset K) (t : K) : K :=
  t + ∑ x ∈ xs, (fW g2 g3 x / (t - x) ^ 2 + fW' g2 x / (2 * (t - x)))

def veluNum [DecidableEq K] (g2 g3 : K) (xs : Finset K) : K[X] :=
  X * rootPoly xs ^ 2
    + ∑ x ∈ xs, (C (fW g2 g3 x) + C (fW' g2 x / 2) * (X - C x)) * rootPoly (xs.erase x) ^ 2

def homS (U : PowerSeries K) (m : ℕ) (Q : K[X]) : PowerSeries K :=
  ∑ i ∈ Finset.range (m + 1), PowerSeries.C (Q.coeff i) * U ^ i * PowerSeries.X ^ (2 * (m - i))

end Alg

def KerProdAt (d : ℕ) (L : PeriodPair) (l e : ℕ) : Prop :=
  ∃ (N : ℕ) (T : Finset ℂ), ¬ l ∣ N ∧ ¬ e ∣ N ∧ ¬ e ∣ T.card ∧
    (∀ z ∈ T, z ∉ L.lattice ∧ (N : ℂ) * z ∈ L.lattice) ∧
    ∀ k : Subfield ℂ, L.g₂ ∈ k → L.g₃ ∈ k → omegaK d ∈ k → ∏ z ∈ T, L.weierstrassP z ∈ k

end ReciprocityTheory.ChartRestriction.L1
end
end

