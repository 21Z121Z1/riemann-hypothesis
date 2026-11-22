import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0737

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PoissonCutoffAlgebra
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PoissonCutoffAlgebra

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

theorem exists_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField E)⟩⟩

theorem psi_nontriv {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) : ∃ a : Ad E, ψ a ≠ 1 := by
  obtain ⟨w⟩ := exists_pl (E := E)
  obtain ⟨y, hy⟩ := hψ.loc w
  exact ⟨_, hy⟩

theorem alg_inj {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) : Function.Injective (algebraMap E (Ad E)) := by
  obtain ⟨a, ha⟩ := psi_nontriv hψ
  haveI : Nontrivial (Ad E) := ⟨⟨a, 0, fun h => ha (by rw [h, AddChar.map_zero_eq_one])⟩⟩
  exact (algebraMap E (Ad E)).injective

noncomputable def eL (hi : Function.Injective (algebraMap E (Ad E))) : (Fin k → E) ≃ vecLattice E (Fin k) :=
  Equiv.ofBijective (fun ξ => ⟨fun i => algebraMap E (Ad E) (ξ i), ξ, rfl⟩)
    ⟨fun a b h => funext fun i => hi (congrFun (congrArg Subtype.val h) i),
     fun γ => by obtain ⟨ξ, hξ⟩ := γ.2; exact ⟨ξ, Subtype.ext hξ⟩⟩

theorem eL_val (hi : Function.Injective (algebraMap E (Ad E))) (ξ : Fin k → E) :
    ((eL hi ξ : vecLattice E (Fin k)) : Fin k → Ad E) = fun i => algebraMap E (Ad E) (ξ i) := rfl

def B (ψ : AddChar (Ad E) ℂ) (x y : Fin k → Ad E) : ℂ := ψ (∑ i, x i * y i)

theorem B_cont {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (y : Fin k → Ad E) : Continuous fun x => B ψ x y :=
  hψ.cont.comp (continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const)

theorem B_symm (ψ : AddChar (Ad E) ℂ) (x y : Fin k → Ad E) : B ψ x y = B ψ y x := by
  simp only [B, mul_comm]

theorem B_add (ψ : AddChar (Ad E) ℂ) (x x' y : Fin k → Ad E) : B ψ (x + x') y = B ψ x y * B ψ x' y := by
  simp only [B, ← AddChar.map_add_eq_mul, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem B_ker {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (x : Fin k → Ad E) :
    (∀ γ ∈ vecLattice E (Fin k), B ψ γ x = 1) ↔ x ∈ vecLattice E (Fin k) := by
  classical
  constructor
  · intro h
    have : ∀ i, ∃ d : E, x i = algebraMap E (Ad E) d := by
      intro i
      refine hψ.ann (x i) fun c => ?_
      have := h (fun j => algebraMap E (Ad E) ((Pi.single i c : Fin k → E) j)) (algebraMap_mem_vecLattice _)
      have e : (∑ j, (fun j => algebraMap E (Ad E) ((Pi.single i c : Fin k → E) j)) j * x j) =
          x i * algebraMap E (Ad E) c := by
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj])
          (fun h => absurd (Finset.mem_univ i) h)]
        simp [mul_comm]
      simp only [B] at this
      rwa [e] at this
    choose d hd using this
    exact ⟨d, funext fun i => (hd i).symm⟩
  · rintro ⟨d, rfl⟩ γ ⟨ξ, rfl⟩
    have : (∑ i, (fun i => algebraMap E (Ad E) (ξ i)) i * (fun i => algebraMap E (Ad E) (d i)) i) =
        algebraMap E (Ad E) (∑ i, ξ i * d i) := by simp [map_sum, map_mul]
    simp only [B]
    exact this ▸ hψ.rat _

theorem B_inj {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (γ : Fin k → Ad E) (hγ : γ ∈ vecLattice E (Fin k))
    (h : ∀ x, B ψ γ x = 1) : γ = 0 := by
  classical
  obtain ⟨ξ, hξ⟩ := hγ
  have hξ' : γ = fun i => algebraMap E (Ad E) (ξ i) := hξ.symm
  subst hξ'
  by_contra hne
  have : ∃ i, ξ i ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hne (funext fun i => by simp [h0 i])
  obtain ⟨i, hi⟩ := this
  obtain ⟨a, ha⟩ := psi_nontriv hψ
  apply ha
  have := h (Pi.single i (algebraMap E (Ad E) (ξ i)⁻¹ * a) : Fin k → Ad E)
  have e : (∑ j, (fun j => algebraMap E (Ad E) (ξ j)) j * (Pi.single i (algebraMap E (Ad E) (ξ i)⁻¹ * a) : Fin k → Ad E) j) = a := by
    simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  simp only [B] at this
  rwa [e] at this

noncomputable def T (g : GA E k) : (Fin k → Ad E) ≃ₜ (Fin k → Ad E) where
  toFun x := x ᵥ* g.val
  invFun x := x ᵥ* g⁻¹.val
  left_inv x := by simp [Matrix.vecMul_vecMul]
  right_inv x := by simp [Matrix.vecMul_vecMul]
  continuous_toFun := Continuous.matrix_vecMul continuous_id continuous_const
  continuous_invFun := Continuous.matrix_vecMul continuous_id continuous_const

theorem cov (hD : D0) (hM : AdelicLinearChange) (g : GA E k) (h : (Fin k → Ad E) → ℂ) :
    ∫ x, h (x ᵥ* g.val) ∂vecMeasure E (Fin k) = ((Dt g)⁻¹ : ℝ) • ∫ y, h y ∂vecMeasure E (Fin k) := by
  have hpos : 0 < Dt g := (hD E k).1 g
  have hmap : Measure.map (T g) (vecMeasure E (Fin k)) = ENNReal.ofReal (Dt g)⁻¹ • vecMeasure E (Fin k) := by
    ext A hA
    rw [Measure.smul_apply, smul_eq_mul, ← lintegral_indicator_one hA, ← lintegral_indicator_one hA,
      lintegral_map (measurable_one.indicator hA) (T g).continuous.measurable]
    exact (hM E k g (A.indicator 1) (measurable_one.indicator hA)).2
  have := integral_map_equiv (T g).toMeasurableEquiv h (μ := vecMeasure E (Fin k))
  rw [Homeomorph.toMeasurableEquiv_coe, hmap, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.2 hpos.le)] at this
  exact this.symm

def eR : RowT E k k ≃ {ξ : Fin k → E // ξ ≠ 0} where
  toFun ξ := ⟨ξ.1, ξ.2.1⟩
  invFun ξ := ⟨ξ.1, ξ.2, fun i hi => absurd hi (not_le.2 i.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def Ps (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k) (φ : XB E k) (g : GA E k) (y : Fin k → Ad E) : ℂ :=
  (η y : ℂ) * φ (g * (s y)⁻¹)

def Jf (ψ : AddChar (Ad E) ℂ) (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k) (φ : XB E k) (g : GA E k)
    (ξ : Fin k → E) : ℂ :=
  ∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) * ψ (∑ i, y i * ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)
    ∂vecMeasure E (Fin k)

theorem alg_zero : (fun i => algebraMap E (Ad E) ((0 : Fin k → E) i)) = 0 := by
  ext i; simp

theorem stepA (hD : D0) (hM : AdelicLinearChange) (ψ : AddChar (Ad E) ℂ) (η : (Fin k → Ad E) → ℝ) (s : (Fin k → Ad E) → GA E k)
    (φ : XB E k) (g : GA E k) (ξ : Fin k → E) :
    ∫ x, Ps η s φ g (x ᵥ* g.val) * B ψ x (fun i => algebraMap E (Ad E) (ξ i)) ∂vecMeasure E (Fin k) =
      ((Dt g)⁻¹ : ℝ) • Jf ψ η s φ g ξ := by
  have e := cov hD hM g (fun y => (η y : ℂ) * φ (g * (s y)⁻¹) *
    ψ (∑ i, y i * ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i))
  refine Eq.trans ?_ e
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Ps, B]
  congr 2
  change x ⬝ᵥ _ = (x ᵥ* g.val) ⬝ᵥ (_ ᵥ* (g⁻¹.val)ᵀ)
  rw [Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  simp

end PoissonCutoffAlgebra

open PoissonCutoffAlgebra in
theorem poisson_cutoff_of : D0 → AdelicLinearChange → N0 → H0 → ThetaSeriesBound → K1 → PoissonCutoffFormula := by
  intro hD hM hN _hH hG hK E _ _ _ k hk ψ hψ S U φ η s hcut hinv g
  classical
  have hi := alg_inj hψ
  have hDpos : ∀ h : GA E k, 0 < Dt h := (hD E k).1
  have hΨc : Continuous (Ps η s φ g) := by
    have := (continuous_eval_const g).comp hcut.contV
    refine this.congr fun y => ?_
    simp [Rt_apply, Ps]
  have hΨs : HasCompactSupport (Ps η s φ g) := by
    have : HasCompactSupport fun y => (η y : ℂ) := hcut.cpt.comp_left Complex.ofReal_zero
    exact this.mul_right
  have hΨ0 : Ps η s φ g 0 = 0 := by simp [Ps, hcut.zero]
  have hfc : Continuous fun x : Fin k → Ad E => Ps η s φ g (x ᵥ* g.val) := hΨc.comp (T g).continuous
  have hfs : HasCompactSupport fun x : Fin k → Ad E => Ps η s φ g (x ᵥ* g.val) := hΨs.comp_homeomorph (T g)

  obtain ⟨Cf, hCf, hft⟩ := hcut.ft
  obtain ⟨M, C0, hG3⟩ := hG E k Cf hCf k le_rfl
  obtain ⟨C, hC⟩ := hft M
  obtain ⟨-, hdpos, hdle, -⟩ := hK E k hk
  have hp : 0 < Dt (invT g) ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos (hDpos _) _
  have hr : 0 < dmin (invT g) * Dt (invT g) ^ ((k : ℝ)⁻¹) := mul_pos (hdpos _) hp
  have hrle : ∀ ξ : Fin k → E, ξ ≠ 0 → dmin (invT g) * Dt (invT g) ^ ((k : ℝ)⁻¹) ≤ height (invT g) ξ := by
    intro ξ hξ
    have := hdle (invT g) ξ hξ
    rwa [ht, le_div_iff₀ hp] at this
  have hsumG := hG3 (invT g) _ hr hrle
  have hu0 : ∀ ξ : Fin k → E, 0 ≤ Cf.indicator (fun _ => ((1 + ‖fun i => pInf E
      (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)‖) ^ M)⁻¹)
      (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)) := fun ξ =>
    Set.indicator_nonneg (fun _ _ => inv_nonneg.2 (pow_nonneg (by positivity) _)) _
  have hus : Summable fun ξ : Fin k → E => Cf.indicator (fun _ => ((1 + ‖fun i => pInf E
      (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)‖) ^ M)⁻¹)
      (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)) := by
    have hne := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsumG
    have h1 := (ENNReal.summable_toReal hne).congr fun ξ => ENNReal.toReal_ofReal (hu0 ξ.1)
    exact (Set.finite_singleton (0 : Fin k → E)).summable_compl_iff.1 h1
  have hJs : Summable fun ξ => ‖Jf ψ η s φ g ξ‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => (hC _ g).trans (le_of_eq ?_)) (hus.mul_left C)
    by_cases hx : (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* (invT g).val) i)) ∈ Cf <;> simp [hx]
  have hsumΓ : Summable fun γ : vecLattice E (Fin k) =>
      ‖∫ x, Ps η s φ g (x ᵥ* g.val) * B ψ x γ ∂vecMeasure E (Fin k)‖ := by
    refine (eL hi).summable_iff.1 ((hJs.mul_left (Dt g)⁻¹).congr fun ξ => ?_)
    rw [Function.comp_apply, eL_val, stepA hD hM, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hDpos g))]

  obtain ⟨hdisc, K, hK, hcov⟩ := isCoLat_ratV E (Fin k)
  haveI : DiscreteTopology (vecLattice E (Fin k)) := hdisc
  have hP := GlobalTheory.CovolumeOneSelfDual.poisson (vecLattice E (Fin k)) K hK hcov (B ψ) (B_cont hψ) (B_symm ψ)
    (B_add ψ) (fun x y => hψ.norm _) (B_ker hψ) (fun γ hγ h => B_inj hψ γ hγ h) (vecMeasure E (Fin k))
    (vecDomain E (Fin k)) isAddFundamentalDomain_vecDomain vecMeasure_vecDomain hfc hfs hsumΓ
  obtain ⟨-, -, -, -, -, -, -, -, -, hlast⟩ := hN E k k hk le_rfl
  have hL : sumF (fun h => (η (lastRow h) : ℂ) * φ (h * (s (lastRow h))⁻¹)) g =
      ∑' ξ : Fin k → E, Ps η s φ g ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) := by
    unfold sumF
    rw [← (eR (E := E) (k := k)).symm.tsum_eq]
    rw [← tsum_subtype_eq_of_support_subset (s := {ξ : Fin k → E | ξ ≠ 0})]
    · refine tsum_congr fun ξ => ?_
      beta_reduce
      rw [hlast, mul_assoc, hinv (gam (eR.symm ξ))]
      rfl
    · intro ξ hξ
      simp only [Set.mem_setOf_eq]
      rintro rfl
      apply hξ
      simp only [alg_zero, Matrix.zero_vecMul, hΨ0]
  have hR : ∑' ξ : Fin k → E, Ps η s φ g ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) =
      ∑' ξ : Fin k → E, ((Dt g)⁻¹ : ℝ) • Jf ψ η s φ g ξ := by
    have h1 := (eL hi).tsum_eq fun γ : vecLattice E (Fin k) => Ps η s φ g ((γ : Fin k → Ad E) ᵥ* g.val)
    have h2 := (eL hi).tsum_eq fun γ : vecLattice E (Fin k) =>
      ∫ x, Ps η s φ g (x ᵥ* g.val) * B ψ x γ ∂vecMeasure E (Fin k)
    simp only [eL_val] at h1 h2
    rw [h1, hP, ← h2]
    exact tsum_congr fun ξ => stepA hD hM ψ η s φ g ξ
  have hJsum : Summable (Jf ψ η s φ g) := hJs.of_norm
  have hJ0 : Jf ψ η s φ g 0 = ∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂vecMeasure E (Fin k) := by
    rw [Jf, alg_zero]
    simp
  rw [hL, hR]
  simp only [Complex.real_smul, tsum_mul_left, Complex.ofReal_inv]
  rw [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.2 (hDpos g).ne'),
    ← hJsum.tsum_subtype_add_tsum_subtype_compl {0}, tsum_singleton, hJ0]
  rfl

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.PrimePairSetFirst
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace primePairSetFirst

variable {E : Type} [Field E] [NumberField E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}

theorem cont_colT (hψ : StdPsi ψ) (m : ℕ) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g) :
    Continuous (colT ψ (m + 1) f) := by
  have key := GlobalTheory.T.continuous_quotientAverage_periodic_family (UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex k (m + 1) (m + 1)))
    (isCoLat_ratV E _) (GA E k)
    (fun p => ψ (-dot (eLast k (m + 1)) p.2) * f (blkU p.2 * p.1)) ?_ ?_
  · exact key
  · exact (hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul
      (hc.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))
  · intro g γ hγ y
    exact (per_coef hψ (eLast k (m + 1)) hc hl g).2 γ hγ y

theorem colT_blkU (hψ : StdPsi ψ) (m : ℕ) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g)
    (y : UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (g : GA E k) :
    colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast k (m + 1)) y) * colT ψ (m + 1) f g := by
  have hper := per_coef (a := k) hψ (eLast k (m + 1)) hc hl g
  have hT := GlobalTheory.T.quotientAverage_translate_invariant (UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E) (ratV E (UnipotentBlockColumnIndex k (m + 1) (m + 1)))
    (isCoLat_ratV E _) _ hper y
  have hpt : (fun x : UnipotentBlockColumnIndex k (m + 1) (m + 1) → Ad E =>
        ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) =
      fun x => ψ (dot (eLast k (m + 1)) y) *
        (ψ (-dot (eLast k (m + 1)) (x + y)) * f (blkU (x + y) * g)) := by
    funext x
    have hd : dot (eLast k (m + 1)) (x + y) = dot (eLast k (m + 1)) x + dot (eLast k (m + 1)) y := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hu : (blkU (x + y) : GA E k) = blkU x * blkU y := posU_add _ x y
    have h1 : ψ (dot (eLast k (m + 1)) y) * ψ (-dot (eLast k (m + 1)) y) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [hd, hu, neg_add, AddChar.map_add_eq_mul, mul_assoc (blkU x)]
    calc ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))
        = (ψ (dot (eLast k (m + 1)) y) * ψ (-dot (eLast k (m + 1)) y)) *
            (ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) := by rw [h1, one_mul]
      _ = _ := by ring
  change avg _ (fun x => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * (blkU y * g))) =
    _ * avg _ (fun x => ψ (-dot (eLast k (m + 1)) x) * f (blkU x * g))
  rw [hpt, avg_const_mul]
  exact congrArg _ hT

theorem colT_law (m : ℕ) (f : GA E k → ℂ) (j : ℕ) (hj : m + 1 < j)
    (hlaw : ∀ (y : UnipotentBlockColumnIndex k j j → Ad E) (g : GA E k), f (blkU y * g) = ψ (dot (eLast k j) y) * f g)
    (y : UnipotentBlockColumnIndex k j j → Ad E) (g : GA E k) :
    colT ψ (m + 1) f (blkU y * g) = ψ (dot (eLast k j) y) * colT ψ (m + 1) f g := by
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  have e1 : f (blkU x * (blkU y * g)) = ψ (dot (eLast k j) y) * f (blkU x * g) := by
    rw [← mul_assoc, blkU_mul_blkU hj x y, mul_assoc, hlaw, dot_eLast_shift hj x y]
  rw [e1]
  ring

theorem colT_rat (hψ : StdPsi ψ) (m : ℕ) (hmk : m + 1 < k) (f : GA E k → ℂ) (hc : Continuous f)
    (hl : ∀ γ : GL (Fin k) E, IsMir (m + 1) γ → ∀ g, f (ratGL E k γ * g) = f g)
    (γ : GL (Fin k) E) (hγ : IsMir (m + 1) γ) (g : GA E k) :
    colT ψ (m + 1) f (ratGL E k γ * g) = coefF ψ (m + 1) (fun t => γ.val ⟨m, by omega⟩ t.1.1) f g := by
  unfold colT
  rw [GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E k ψ hψ m f hc hl γ hγ (eLast k (m + 1)) g]
  congr 1
  funext t
  let s0 : UnipotentBlockColumnIndex k (m + 1) (m + 1) := ⟨(⟨m, by omega⟩, ⟨m + 1, hmk⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩
  rw [Finset.sum_eq_single s0]
  · have h1 : eLast (E := E) k (m + 1) s0 = 1 := by simp [eLast, s0]
    rw [h1, one_mul]
  · intro s _ hs
    have h0 : eLast (E := E) k (m + 1) s = 0 := by
      simp only [eLast]
      rw [if_neg]
      intro e
      apply hs
      have h2 := s.2.2
      apply Subtype.ext
      exact Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem blk_eta {m : ℕ} (hmk : m + 1 < k) (t : UnipotentBlockColumnIndex k (m + 1) (m + 1)) :
    (⟨(t.1.1, ⟨m + 1, hmk⟩), t.2.1, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex k (m + 1) (m + 1)) = t := by
  have h := t.2.2
  exact Subtype.ext (Prod.ext rfl (Fin.ext (by show m + 1 = (t.1.2 : ℕ); omega)))

def rowEquiv (m : ℕ) (hmk : m + 1 < k) : RowT E k (m + 1) ≃ {ξ : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E // ξ ≠ 0} where
  toFun ξ := ⟨fun t => ξ.1 t.1.1, by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ξ.2.1
    have him : (i : ℕ) < m + 1 := by
      by_contra h
      exact hi (ξ.2.2 i (by omega))
    intro h0
    exact hi (congrFun h0 ⟨(i, ⟨m + 1, hmk⟩), him, le_rfl, le_rfl⟩)⟩
  invFun η := ⟨fun i => if h : (i : ℕ) < m + 1 then η.1 ⟨(i, ⟨m + 1, hmk⟩), h, le_rfl, le_rfl⟩ else 0, by
    refine ⟨fun h0 => η.2 ?_, fun i hi => dif_neg (by omega)⟩
    funext t
    have h1 := congrFun h0 t.1.1
    simp only [Pi.zero_apply] at h1
    rw [dif_pos t.2.1, blk_eta hmk t] at h1
    exact h1⟩
  left_inv ξ := by
    apply Subtype.ext
    funext i
    by_cases h : (i : ℕ) < m + 1
    · exact dif_pos h
    · exact (dif_neg h).trans (ξ.2.2 i (by omega)).symm
  right_inv η := by
    apply Subtype.ext
    funext t
    show (if h : (t.1.1 : ℕ) < m + 1 then η.1 ⟨(t.1.1, ⟨m + 1, hmk⟩), h, le_rfl, le_rfl⟩ else 0) = η.1 t
    rw [dif_pos t.2.1, blk_eta hmk t]

end primePairSetFirst

theorem p1_holds : N0 → P0 → P1 := by
  intro hN _ E _ _ _ k ψ hψ m hm1 hmk f hf
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hl : ∀ (c : UnipotentBlockColumnIndex k (m + 1) (m + 1) → E) g, f (ratGL E k (blkU c) * g) = f g :=
    fun c g => hf.left _ (isMir_blkU c) g
  simp only [Nat.add_sub_cancel]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ⟨primePairSetFirst.rowEquiv m hmk, fun ξ t => rfl⟩⟩
  · exact primePairSetFirst.cont_colT hψ m f hf.cont hl
  · intro γ hγ g
    have hγ1 : IsMir (m + 1) γ := fun i c h => hγ i c (by omega)
    rw [primePairSetFirst.colT_rat hψ m hmk f hf.cont hf.left γ hγ1 g]
    unfold colT
    congr 1
    funext t
    rw [hγ ⟨m, by omega⟩ t.1.1 (Or.inl le_rfl)]
    have ht := t.2.1
    simp only [eLast, Matrix.one_apply]
    by_cases h : (t.1.1 : ℕ) = m
    · rw [if_pos (Fin.ext h.symm), if_pos (by omega)]
    · rw [if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]
  · intro j hj y g
    rcases Nat.lt_or_ge (m + 1) j with h1 | h1
    · exact primePairSetFirst.colT_law m f j h1 (hf.law j h1) y g
    · obtain rfl : j = m + 1 := by omega
      exact primePairSetFirst.colT_blkU hψ m f hf.cont hl y g
  · intro ξ g
    obtain ⟨hB, hrow⟩ := (hN E k (m + 1) (by omega) (by omega)).1 ξ
    have hγ : IsMir (m + 1) (gam ξ) := fun i c h => hB i c (by omega)
    rw [primePairSetFirst.colT_rat hψ m hmk f hf.cont hf.left _ hγ g]
    congr 1
    funext t
    exact (hrow _ _ rfl).symm
  · intro χ hχ
    funext g
    simp only [colT, coefF]
    rw [← avg_const_mul]
    congr 1
    funext x
    rw [hχ]
    ring

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.TableDegreeOneUnipotent
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace tableDegreeOneUnipotent

theorem mul_le_sq_add (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ _ := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ _ := le_self_add

theorem integ {X : Type} [MeasurableSpace X] {ν : Measure X} {f φ : X → ℂ}
    (hf : AEStronglyMeasurable f ν) (hφ : AEStronglyMeasurable φ ν)
    (h1 : ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν < ∞) (h2 : ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν < ∞) :
    Integrable (fun g => f g * conj (φ g)) ν := by
  refine ⟨hf.mul (Complex.continuous_conj.comp_aestronglyMeasurable hφ), ?_⟩
  show ∫⁻ g, ‖f g * conj (φ g)‖ₑ ∂ν < ∞
  calc ∫⁻ g, ‖f g * conj (φ g)‖ₑ ∂ν ≤ ∫⁻ g, (‖f g‖ₑ ^ 2 + ‖φ g‖ₑ ^ 2) ∂ν := by
        refine lintegral_mono fun g => ?_
        have hc : ‖conj (φ g)‖ₑ = ‖φ g‖ₑ := by simp [enorm_eq_nnnorm]
        rw [enorm_mul, hc]
        exact mul_le_sq_add _ _
    _ = ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν + ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν := lintegral_add_left' (hf.enorm.pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨h1, h2⟩

theorem pre_of_good {E : Type} [Field E] [NumberField E] {k : ℕ} {ψ : AddChar (Ad E) ℂ} {m : ℕ}
    {f : GA E k → ℂ} (h : Good ψ m f) : Pre ψ m f :=
  ⟨h.cont, h.left, h.law⟩

theorem main (hU1 : U1) (hP1 : P1) (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ)
    (μ : Measure (GA E k)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ) (hψ : StdPsi ψ) :
    ∀ m, m < k → ∀ β, IsWt (nuP E k m) β → ∃ β', IsWt (nuP E k 0) β' ∧
      ∀ f φ, Pre ψ m f → Good ψ m φ → ∫⁻ g, ‖f g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
        ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
        Integrable (fun g => whit ψ m f g * conj (whit ψ m φ g)) (μ.withDensity β') ∧
        ∫ g, f g * conj (φ g) ∂μ.withDensity β = ∫ g, whit ψ m f g * conj (whit ψ m φ g) ∂μ.withDensity β' := by
  intro m
  induction m with
  | zero =>
    intro _ β hβ
    refine ⟨β, hβ, fun f φ hf hφ h1 h2 => ⟨?_, rfl⟩⟩
    exact integ hf.cont.aestronglyMeasurable (pre_of_good hφ).cont.aestronglyMeasurable h1 h2
  | succ m ih =>
    intro hm β hβ
    obtain ⟨β1, hβ1, hL2, hip⟩ := hU1 E k μ ψ hψ (m + 1) (by omega) hm β hβ
    obtain ⟨β', hβ', h⟩ := ih (by omega) β1 hβ1
    refine ⟨β', hβ', fun f φ hf hφ h1 h2 => ?_⟩
    have hf' : Pre ψ m (colT ψ (m + 1) f) := (hP1 E k ψ hψ (m + 1) (by omega) hm f hf).1
    have hφ' : Good ψ m (colT ψ (m + 1) φ) := GlobalTheory.CuspRep.Generic.good_colT hψ hm hφ
    obtain ⟨hi, he⟩ := h _ _ hf' hφ' ((hL2 f hf).trans_lt h1) ((hL2 φ (pre_of_good hφ)).trans_lt h2)
    exact ⟨hi, (hip f φ hf hφ h1 h2).trans he⟩

end tableDegreeOneUnipotent

theorem unitaryGroupGeometricSide_of_quotient_identities : U1 → P1 → U2 := by
  intro hU1 hP1 E _ _ _ k μ _ ψ hψ
  exact tableDegreeOneUnipotent.main hU1 hP1 E k μ ψ hψ

end PositivityTheory.AdelicQuotientData

end
end

