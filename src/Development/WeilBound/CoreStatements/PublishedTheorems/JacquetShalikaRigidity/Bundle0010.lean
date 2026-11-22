import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import GroundTheory.AutomorphicForms.ReductionMahler
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SepSum
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SeparatedThetaSum
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SeparatedThetaSum

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

omit [IsTotallyComplex E] in
theorem isOpen_fInt (S : Finset (HeightOneSpectrum (𝓞 E))) :
    IsOpen {y : Fin k → Af E | ∀ v, v ∉ S → ∀ i, y i v ∈ v.adicCompletionIntegers E} := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (A := fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
    (fun v => Valued.isOpen_integer _) (p := fun v => v ∉ S)
  have e : {y : Fin k → Af E | ∀ v, v ∉ S → ∀ i, y i v ∈ v.adicCompletionIntegers E} =
      ⋂ i, (fun y : Fin k → Af E => y i) ⁻¹' {x | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers E} := by
    ext y; simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h i v hv => h v hv i, fun h v hv i => h i v hv⟩
  rw [e]
  exact isOpen_iInter_of_finite fun i => h.preimage (continuous_apply i)

omit [IsTotallyComplex E] in
theorem exists_finite_fInt {C : Set (Fin k → Af E)} (hC : IsCompact C) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ y ∈ C, ∀ v, v ∉ S → ∀ i, y i v ∈ v.adicCompletionIntegers E := by
  classical
  obtain ⟨T, hT⟩ := hC.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 E)) =>
      {y : Fin k → Af E | ∀ v, v ∉ S → ∀ i, y i v ∈ v.adicCompletionIntegers E})
    (fun S => isOpen_fInt S) (fun y _ => by
      have hfin : (⋃ i, {v : HeightOneSpectrum (𝓞 E) | y i v ∉ v.adicCompletionIntegers E}).Finite :=
        Set.finite_iUnion fun i => Filter.eventually_cofinite.1 (y i).2
      refine Set.mem_iUnion.2 ⟨hfin.toFinset, fun v hv i => ?_⟩
      by_contra h
      exact hv (hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨i, h⟩)))
  refine ⟨T.sup id, fun y hy v hv => ?_⟩
  obtain ⟨S, hS, hyS⟩ := Set.mem_iUnion₂.1 (hT hy)
  exact hyS v fun h => hv (Finset.mem_sup.2 ⟨S, hS, h⟩)

omit [IsTotallyComplex E] in
theorem fin_bd (C : Set (Fin k → Af E)) (hC : IsCompact C) : ∃ B : ℝ, 1 ≤ B ∧ ∀ (g : GA E k) (ξ : Fin k → E), ξ ≠ 0 →
    (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) i)) ∈ C →
      ∏ᶠ v, ‖finComp v ((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val)‖ ≤ B := by
  classical
  obtain ⟨S, hS⟩ := exists_finite_fInt hC
  have hfin : ∀ v : HeightOneSpectrum (𝓞 E), ∃ m : ℝ, 1 ≤ m ∧ ∀ y ∈ C, ‖fun i => y i v‖ ≤ m := fun v =>
    exists_one_le_bound hC (f := fun y => ‖fun i => y i v‖)
      (continuous_norm.comp (continuous_pi fun i =>
        (RestrictedProduct.continuous_eval v).comp (continuous_apply i)))
  choose b hb1 hb using hfin
  refine ⟨∏ v ∈ S, b v, by simpa using Finset.prod_le_prod (s := S) (f := fun _ => (1:ℝ)) (fun _ _ => zero_le_one) (fun v _ => hb1 v), fun g ξ hξ hy => ?_⟩
  have hfc := hasFiniteContent_height g hξ
  set y : Fin k → Ad E := (fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val with hy'
  set b' : HeightOneSpectrum (𝓞 E) → ℝ := fun v => if v ∈ S then b v else 1 with hb'
  have hsub : Function.mulSupport b' ⊆ (S : Set _) := fun v hv => by
    by_contra h
    exact hv (by simp only [hb', if_neg (show v ∉ S from h)])
  refine (finprod_le_finprod_of_nonneg hfc.finite_mulSupport ((S.finite_toSet).subset hsub)
    (fun v => norm_nonneg _) fun v => ?_).trans (le_of_eq ?_)
  · simp only [hb']
    split_ifs with hv
    · exact hb v _ hy
    · exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => norm_le_one_of_mem v (hS _ hy v hv i)
  · rw [finprod_eq_prod_of_mulSupport_subset b' hsub]
    exact Finset.prod_congr rfl fun v hv => by simp only [hb', if_pos hv]

theorem norm_pInf (a : Ad E) (w : InfinitePlace E) : ‖pInf E a w‖ = ‖a.1 w‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

theorem ht_le (C : Set (Fin k → Af E)) (hC : IsCompact C) : ∃ B : ℝ, 0 < B ∧ ∀ (g : GA E k) (ξ : Fin k → E), ξ ≠ 0 →
    (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) i)) ∈ C →
      height g ξ ≤ B * ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) i)‖ ^
        (∑ w : InfinitePlace E, w.mult) := by
  obtain ⟨Bf, hBf, hf⟩ := fin_bd C hC
  refine ⟨Bf * (√k + 1) ^ (∑ w : InfinitePlace E, w.mult), by positivity, fun g ξ hξ hy => ?_⟩
  set y : Fin k → Ad E := (fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val with hy'
  set z := fun i => pInf E (y i) with hz
  have e : height g ξ = adelicNorm y := rfl
  rw [e, adelicNorm]
  have hw : ∀ w : InfinitePlace E, euclidNorm (infComp w y) ≤ (√k + 1) * ‖z‖ := fun w => by
    refine (euclidNorm_le_sqrt_mul _).trans (mul_le_mul (by linarith) ?_ (norm_nonneg _) (by positivity))
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    change ‖(y i).1 w‖ ≤ ‖z‖
    rw [← norm_pInf]
    exact (norm_le_pi_norm (z i) w).trans (norm_le_pi_norm z i)
  have h1 : (∏ w : InfinitePlace E, euclidNorm (infComp w y) ^ w.mult) ≤
      ((√k + 1) * ‖z‖) ^ (∑ w : InfinitePlace E, w.mult) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun w _ => pow_nonneg (euclidNorm_nonneg _) _)
      fun w _ => pow_le_pow_left₀ (euclidNorm_nonneg _) (hw w) _
  have h2 := hf g ξ hξ hy
  have h3 : 0 ≤ ∏ᶠ v, ‖finComp v y‖ := finprod_nonneg fun _ => norm_nonneg _
  calc (∏ w : InfinitePlace E, euclidNorm (infComp w y) ^ w.mult) * ∏ᶠ v, ‖finComp v y‖
      ≤ ((√k + 1) * ‖z‖) ^ (∑ w : InfinitePlace E, w.mult) * Bf :=
        mul_le_mul h1 h2 h3 (by positivity)
    _ = _ := by rw [mul_pow]; ring

end SeparatedThetaSum

namespace SeparatedThetaSum

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

theorem real_ineq (ρ : ℝ) (hρ : 0 < ρ) (d k a : ℕ) (hka : k ≤ a) :
    ((ρ ^ d) ^ k)⁻¹ * ((1 + ρ) ^ (d * a))⁻¹ ≤ ((ρ ^ d) ^ a)⁻¹ := by
  have ht : 0 < ρ ^ d := pow_pos hρ d
  have h1 : 1 ≤ (1 + ρ) ^ (d * a) := one_le_pow₀ (by linarith)
  have h2 : (ρ ^ d) ^ a ≤ (1 + ρ) ^ (d * a) := by
    rw [pow_mul]; exact pow_le_pow_left₀ ht.le (pow_le_pow_left₀ hρ.le (by linarith) d) a
  rcases le_total (ρ ^ d) 1 with h | h
  · have h3 : ((ρ ^ d) ^ k)⁻¹ ≤ ((ρ ^ d) ^ a)⁻¹ :=
      inv_anti₀ (pow_pos ht a) (pow_le_pow_of_le_one ht.le h hka)
    have h4 : ((1 + ρ) ^ (d * a))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    calc ((ρ ^ d) ^ k)⁻¹ * ((1 + ρ) ^ (d * a))⁻¹ ≤ ((ρ ^ d) ^ a)⁻¹ * 1 :=
          mul_le_mul h3 h4 (by positivity) (by positivity)
      _ = _ := mul_one _
  · have h3 : ((ρ ^ d) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h)
    have h4 : ((1 + ρ) ^ (d * a))⁻¹ ≤ ((ρ ^ d) ^ a)⁻¹ := inv_anti₀ (pow_pos ht a) h2
    calc ((ρ ^ d) ^ k)⁻¹ * ((1 + ρ) ^ (d * a))⁻¹ ≤ 1 * ((ρ ^ d) ^ a)⁻¹ :=
          mul_le_mul h3 h4 (by positivity) zero_le_one
      _ = _ := one_mul _

theorem dim_eq : Module.finrank ℝ (Fin k → Cinf E) = k * ∑ w : InfinitePlace E, w.mult := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, IsTotallyComplex.mult_eq]

open Classical in
theorem core {ι X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] (C0 : ℝ)
    (hsep : ∀ ρ : ℝ, 0 < ρ → ∀ P : Finset X, (∀ p ∈ P, ρ ≤ ‖p‖) → (∀ p ∈ P, ∀ q ∈ P, p ≠ q → ρ ≤ ‖p - q‖) →
      ∑ p ∈ P, ((1 + ‖p‖) ^ (Module.finrank ℝ X + 1))⁻¹ ≤ C0 * (ρ ^ Module.finrank ℝ X)⁻¹)
    (z : ι → X) (p : ι → Prop) (ρ : ℝ) (hρ : 0 < ρ) (hn : ∀ i, p i → ρ ≤ ‖z i‖)
    (hs : ∀ i j, p i → p j → i ≠ j → ρ ≤ ‖z i - z j‖) (m : ℕ) :
    ∑' i, ENNReal.ofReal (if p i then ((1 + ‖z i‖) ^ (Module.finrank ℝ X + 1 + m))⁻¹ else 0) ≤
      ENNReal.ofReal (C0 * (ρ ^ Module.finrank ℝ X)⁻¹ * ((1 + ρ) ^ m)⁻¹) := by
  classical
  refine tsum_le_of_sum_le' (by simp) fun s => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs <;> positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.sum_filter]
  set t := s.filter p with ht
  have hp : ∀ i ∈ t, p i := fun i hi => (Finset.mem_filter.1 hi).2
  have hinj : Set.InjOn z t := fun i hi j hj hij => by
    by_contra h
    have := hs i j (hp i hi) (hp j hj) h
    rw [hij, sub_self, norm_zero] at this
    linarith
  calc ∑ i ∈ t, ((1 + ‖z i‖) ^ (Module.finrank ℝ X + 1 + m))⁻¹
      ≤ ∑ i ∈ t, ((1 + ‖z i‖) ^ (Module.finrank ℝ X + 1))⁻¹ * ((1 + ρ) ^ m)⁻¹ := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [pow_add, mul_inv]
        have h0 : 0 < 1 + ‖z i‖ := by positivity
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
          (pow_le_pow_left₀ (by linarith) (by linarith [hn i (hp i hi)]) m)) (by positivity)
    _ = (∑ x ∈ t.image z, ((1 + ‖x‖) ^ (Module.finrank ℝ X + 1))⁻¹) * ((1 + ρ) ^ m)⁻¹ := by
        rw [Finset.sum_image hinj, Finset.sum_mul]
    _ ≤ C0 * (ρ ^ Module.finrank ℝ X)⁻¹ * ((1 + ρ) ^ m)⁻¹ := by
        refine mul_le_mul_of_nonneg_right (hsep ρ hρ _ ?_ ?_) (by positivity)
        · intro x hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
          exact hn i (hp i hi)
        · intro x hx y hy hxy
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
          exact hs i j (hp i hi) (hp j hj) fun h => hxy (h ▸ rfl)

end SeparatedThetaSum

theorem theta_bound_holds : ThetaSeriesBound := by
  intro E _ _ _ k Cf hCf a hka
  classical
  set K : Set (Fin k → Af E) := Cf ∪ (fun p : (Fin k → Af E) × (Fin k → Af E) => p.1 - p.2) '' (Cf ×ˢ Cf) with hK
  have hKc : IsCompact K := hCf.union ((hCf.prod hCf).image (continuous_fst.sub continuous_snd))
  obtain ⟨B, hB, hht⟩ := SeparatedThetaSum.ht_le K hKc
  obtain ⟨C0, hC0, hsep⟩ := SeparatedThetaSum.sep_sum (Fin k → Cinf E)
  set d := ∑ w : InfinitePlace E, w.mult with hd
  have hdpos : 0 < d := by rw [hd, InfinitePlace.sum_mult_eq]; exact Module.finrank_pos
  refine ⟨Module.finrank ℝ (Fin k → Cinf E) + 1 + d * a, C0 * B ^ a, fun g r hr hrh => ?_⟩
  set ρ : ℝ := (r / B) ^ ((d : ℝ)⁻¹) with hρdef
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (div_pos hr hB) _
  have hρd : ρ ^ d = r / B := Real.rpow_inv_natCast_pow (div_pos hr hB).le hdpos.ne'
  have hY : ∀ ξ ξ' : Fin k → E, (fun i => algebraMap E (Ad E) ((ξ - ξ') i)) ᵥ* g.val =
      (fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val - (fun i => algebraMap E (Ad E) (ξ' i)) ᵥ* g.val := by
    intro ξ ξ'
    rw [← sub_vecMul]; congr 1; ext i; simp [map_sub]
  have key : ∀ ξ : Fin k → E, ξ ≠ 0 →
      (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) i)) ∈ K →
      ρ ≤ ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) i)‖ := fun ξ hξ hK => by
    have h1 := (hrh ξ hξ).trans (hht g ξ hξ hK)
    have h2 : ρ ^ d ≤ ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ i)) ᵥ* g.val) i)‖ ^ d := by
      rw [hρd, div_le_iff₀ hB]; linarith
    exact (pow_le_pow_iff_left₀ hρ0.le (norm_nonneg _) hdpos.ne').1 h2
  have hcore := SeparatedThetaSum.core (ι := {ξ : Fin k → E // ξ ≠ 0}) C0 hsep
    (fun ξ => fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))
    (fun ξ => (fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)) ∈ Cf) ρ hρ0
    (fun ξ hξ => key ξ.1 ξ.2 (Or.inl hξ))
    (fun ξ ξ' h h' hne => by
      have hne' : ξ.1 - ξ'.1 ≠ 0 := sub_ne_zero.2 fun h => hne (Subtype.ext h)
      have := key (ξ.1 - ξ'.1) hne' (Or.inr ⟨(_, _), ⟨h, h'⟩, by
        simp only [hY]; ext i; simp [map_sub]⟩)
      refine this.trans_eq (congrArg norm ?_)
      rw [hY]; ext i; simp [map_sub]) (d * a)
  refine le_trans ?_ (hcore.trans (ENNReal.ofReal_le_ofReal ?_))
  · refine le_of_eq (tsum_congr fun ξ => ?_)
    simp only [Set.indicator_apply]
  · rw [SeparatedThetaSum.dim_eq, ← hd, mul_comm k d, pow_mul]
    have h := SeparatedThetaSum.real_ineq ρ hρ0 d k a hka
    have e : ((ρ ^ d) ^ a)⁻¹ = B ^ a * (r ^ a)⁻¹ := by rw [hρd, div_pow, inv_div, div_eq_mul_inv]
    rw [e] at h
    calc _ = C0 * (((ρ ^ d) ^ k)⁻¹ * ((1 + ρ) ^ (d * a))⁻¹) := by ring
      _ ≤ C0 * (B ^ a * (r ^ a)⁻¹) := mul_le_mul_of_nonneg_left h hC0
      _ = _ := by ring

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SmoothVectorHyp
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SmoothVectorHyp

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

structure Hyp (E : Type) [Field E] [NumberField E] (k : ℕ) : Prop where
  cont : Continuous (dmin : GA E k → ℝ)
  pos : ∀ g : GA E k, 0 < dmin g
  rt : ∀ h : GA E k, ∃ B : ℝ, 1 ≤ B ∧ ∀ g, dmin (g * h) ≤ B * dmin g

lemma min_le_of (a b D : ℝ) (hD : 1 ≤ D) (h : a ≤ D * b) : min 1 a ≤ D * min 1 b := by
  rcases le_total 1 b with h1 | h1
  · rw [min_eq_left h1]; exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right h1]; exact (min_le_right _ _).trans h

lemma wt_pos (H : Hyp E k) (M : ℕ) (g : GA E k) : 0 < wt M g :=
  pow_pos (lt_min one_pos (H.pos g)) M

lemma wt_le_one (H : Hyp E k) (M : ℕ) (g : GA E k) : wt M g ≤ 1 :=
  pow_le_one₀ (le_min zero_le_one (H.pos g).le) (min_le_left _ _)

lemma wt_cont (H : Hyp E k) (M : ℕ) : Continuous (wt M : GA E k → ℝ) :=
  (continuous_const.min H.cont).pow M

lemma wt_le (H : Hyp E k) (M : ℕ) (g c : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (h : dmin (g * c) ≤ D * dmin g) : wt M (g * c) ≤ D ^ M * wt M g := by
  unfold wt
  rw [← mul_pow]
  exact pow_le_pow_left₀ (le_min zero_le_one (H.pos _).le) (min_le_of _ _ _ hD h) M

def W (H : Hyp E k) (M : ℕ) : XB E k :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => ((wt M g : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (wt_cont H M)) 1 fun g => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_pos H M g).le]
      exact wt_le_one H M g

lemma ratio_cont (H : Hyp E k) (M : ℕ) (h : GA E k) :
    Continuous fun g : GA E k => ((wt M (g * h) / wt M g : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp
    (((wt_cont H M).comp (continuous_mul_const h)).div (wt_cont H M) fun g => (wt_pos H M g).ne')

lemma ratio_le (H : Hyp E k) (M : ℕ) (h g : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (hd : dmin (g * h) ≤ D * dmin g) : ‖((wt M (g * h) / wt M g : ℝ) : ℂ)‖ ≤ D ^ M := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (wt_pos H M _).le (wt_pos H M g).le), div_le_iff₀ (wt_pos H M g)]
  exact wt_le H M g h D hD hd

def Q (H : Hyp E k) (M : ℕ) (h : GA E k) : XB E k :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => ((wt M (g * h) / wt M g : ℝ) : ℂ))
    (ratio_cont H M h) ((H.rt h).choose ^ M) fun g =>
      ratio_le H M h g _ (H.rt h).choose_spec.1 ((H.rt h).choose_spec.2 g)

lemma norm_Q_le (H : Hyp E k) (M : ℕ) (h : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (hd : ∀ g, dmin (g * h) ≤ D * dmin g) : ‖Q H M h‖ ≤ D ^ M :=
  (BoundedContinuousFunction.norm_le (pow_nonneg (zero_le_one.trans hD) M)).mpr fun g =>
    ratio_le H M h g D hD (hd g)

def rho (H : Hyp E k) (M : ℕ) : GA E k →* (XB E k →L[ℂ] XB E k) where
  toFun h := (ContinuousLinearMap.mul ℂ (XB E k) (Q H M h)).comp (Rt E k h)
  map_one' := by
    ext x g
    change ((wt M (g * 1) / wt M g : ℝ) : ℂ) * x (g * 1) = x g
    rw [mul_one, div_self (wt_pos H M g).ne', Complex.ofReal_one, one_mul]
  map_mul' h h' := by
    ext x g
    change ((wt M (g * (h * h')) / wt M g : ℝ) : ℂ) * x (g * (h * h')) =
      ((wt M (g * h) / wt M g : ℝ) : ℂ) * (((wt M (g * h * h') / wt M (g * h) : ℝ) : ℂ) * x (g * h * h'))
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    have := (wt_pos H M (g * h)).ne'
    field_simp

lemma rho_apply (H : Hyp E k) (M : ℕ) (h g : GA E k) (x : XB E k) :
    rho H M h x g = ((wt M (g * h) / wt M g : ℝ) : ℂ) * x (g * h) := rfl

def J (H : Hyp E k) (M : ℕ) : XB E k →L[ℂ] XB E k := ContinuousLinearMap.mul ℂ (XB E k) (W H M)

lemma J_apply (H : Hyp E k) (M : ℕ) (x : XB E k) (g : GA E k) : J H M x g = (wt M g : ℂ) * x g := rfl

lemma inter (H : Hyp E k) (M : ℕ) (h : GA E k) (x : XB E k) : J H M (rho H M h x) = Rt E k h (J H M x) := by
  ext g
  rw [J_apply, rho_apply, Rt_apply, J_apply, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  have := (wt_pos H M g).ne'
  field_simp

lemma inj (H : Hyp E k) (M : ℕ) : Function.Injective (J H M) := by
  intro x y hxy
  ext g
  have e := congrArg (fun z : XB E k => z g) hxy
  simp only [J_apply] at e
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (wt_pos H M g).ne') e

variable [IsTotallyComplex E]

lemma smv (H : Hyp E k) (M : ℕ) (x : XB E k) (hx : SmV ((rho H M).comp (infGL E k)) x) :
    SmV (repI E k) (J H M x) := by
  have e : orb (repI E k) (J H M x) = fun A => J H M (orb ((rho H M).comp (infGL E k)) x A) := by
    funext A
    unfold orb
    split_ifs with hA
    · exact (inter H M _ x).symm
    · exact (map_zero (J H M)).symm
  unfold SmV
  rw [e]
  exact hx.continuousLinearMap_comp ((J H M).restrictScalars ℝ)

end SmoothVectorHyp

theorem secondCohomologyBound_of_boundaryBound : H0 → K1 → K2 := by
  intro hH hK E _ _ _ k hk M
  obtain ⟨h1, -, -, -, -, ⟨B, N, -, h6⟩, -⟩ := hH E k
  obtain ⟨kc, kpos, kle, -, kcpt, -⟩ := hK E k hk
  have H : SmoothVectorHyp.Hyp E k := ⟨kc, kpos, fun h => by
    obtain ⟨B, hB, hB'⟩ := kcpt {h} isCompact_singleton
    exact ⟨B, hB, hB' h rfl⟩⟩
  refine ⟨SmoothVectorHyp.rho H M, SmoothVectorHyp.J H M, ⟨fun x g => rfl, SmoothVectorHyp.inter H M, SmoothVectorHyp.inj H M, ?_⟩,
    fun x hx => SmoothVectorHyp.smv H M x hx⟩
  have hne : Nonempty {ξ : Fin k → E // ξ ≠ 0} :=
    ⟨⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hk⟩)⟩⟩
  refine ⟨max B 1 ^ M, N * M, pow_nonneg (zero_le_one.trans (le_max_right _ _)) M, fun y x => ?_⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 1 + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ := ⟨_, rfl⟩
  rw [← hP]
  have hP1 : 1 ≤ P := by
    rw [hP]
    linarith [norm_nonneg (Matrix.of.symm y.val : LieI (InfinitePlace E) k),
      norm_nonneg (Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)]
  have hPinv : 1 + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm y⁻¹⁻¹.val : LieI (InfinitePlace E) k)‖ = P := by
    rw [inv_inv, hP]; ring
  have hD : 1 ≤ max B 1 * P ^ N := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hP1)
  have hDpos : 0 < max B 1 * P ^ N := zero_lt_one.trans_le hD
  have hd : ∀ g, dmin (g * infGL E k y) ≤ max B 1 * P ^ N * dmin g := by
    intro g
    rw [← div_le_iff₀' hDpos]
    show _ ≤ ⨅ ξ : {ξ : Fin k → E // ξ ≠ 0}, ht g ξ.1
    refine le_ciInf fun ξ => ?_
    rw [div_le_iff₀' hDpos]
    calc dmin (g * infGL E k y) ≤ ht (g * infGL E k y) ξ.1 := kle _ _ ξ.2
      _ ≤ B * (1 + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ +
          ‖(Matrix.of.symm y⁻¹⁻¹.val : LieI (InfinitePlace E) k)‖) ^ N *
            ht (g * infGL E k y * infGL E k y⁻¹) ξ.1 := h6 y⁻¹ _ ξ.1 ξ.2
      _ = B * P ^ N * ht g ξ.1 := by
          rw [hPinv, mul_assoc g, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ ≤ max B 1 * P ^ N * ht g ξ.1 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (zero_le_one.trans hP1) _))
            (h1 g ξ.1 ξ.2).le
  change ‖SmoothVectorHyp.Q H M (infGL E k y) * Rt E k (infGL E k y) x‖ ≤ _
  calc ‖SmoothVectorHyp.Q H M (infGL E k y) * Rt E k (infGL E k y) x‖
        ≤ ‖SmoothVectorHyp.Q H M (infGL E k y)‖ * ‖Rt E k (infGL E k y) x‖ := norm_mul_le _ _
    _ = ‖SmoothVectorHyp.Q H M (infGL E k y)‖ * ‖x‖ := by rw [norm_Rt]
    _ ≤ (max B 1 * P ^ N) ^ M * ‖x‖ :=
        mul_le_mul_of_nonneg_right (SmoothVectorHyp.norm_Q_le H M _ _ hD hd) (norm_nonneg _)
    _ = max B 1 ^ M * P ^ (N * M) * ‖x‖ := by rw [mul_pow, ← pow_mul]

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.VectorMeasureTranspose
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace VectorMeasureTranspose

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def trM (g : GA E k) : GA E k :=
  ⟨(g.val)ᵀ, (g⁻¹.val)ᵀ, by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

theorem det_trM (g : GA E k) : GeneralLinearGroup.det (trM g) = GeneralLinearGroup.det g := by
  exact Units.ext (Matrix.det_transpose g.val)

theorem Dt_trM (g : GA E k) : Dt (trM g) = Dt g := by
  unfold Dt
  rw [det_trM]

theorem vecMeasure_eq : vecMeasure E (Fin k) = GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := rfl

theorem vecMul_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (x ᵥ* g.val) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have hm : Measurable fun x : Fin k → Ad E => x ᵥ* g.val := GroundTheory.Automorphic.GJGlobal.Modulus.measurable_vecMul' g
  have e1 : ∫⁻ x, F x ∂((GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E).map fun x : Fin k → Ad E => x ᵥ* g.val) =
      ∫⁻ x, F (x ᵥ* g.val) ∂GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E := lintegral_map hF hm
  have h := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi g
  unfold Dt
  rw [vecMeasure_eq, ← e1, h, lintegral_smul_measure]
  try rw [smul_eq_mul]

theorem mulVec_eq (g : GA E k) (F : (Fin k → Ad E) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F (g.val *ᵥ x) ∂vecMeasure E (Fin k) = ENNReal.ofReal (Dt g)⁻¹ * ∫⁻ x, F x ∂vecMeasure E (Fin k) := by
  have e : ∀ x : Fin k → Ad E, F (g.val *ᵥ x) = F (x ᵥ* (trM g).val) := fun x => by
    show F (g.val *ᵥ x) = F (x ᵥ* (g.val)ᵀ)
    rw [Matrix.vecMul_transpose]
  refine (lintegral_congr e).trans ?_
  rw [vecMul_eq (trM g) F hF, Dt_trM]

end VectorMeasureTranspose

theorem linear_change_variables_of : D0 → AdelicLinearChange := by
  intro _ E _ _ _ k g F hF
  exact ⟨VectorMeasureTranspose.mulVec_eq g F hF, VectorMeasureTranspose.vecMul_eq g F hF⟩

end PositivityTheory.AdelicQuotientData

end
end

