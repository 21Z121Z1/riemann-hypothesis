import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecomposition
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousFirstMinimumFamily
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FirstMin

theorem sInf_range_le_mul {S : Type} [Nonempty S] (f h : S → ℝ) (hf : ∀ s, 0 ≤ f s) (c : ℝ) (hc : 0 < c)
    (hle : ∀ s, f s ≤ c * h s) : sInf (Set.range f) ≤ c * sInf (Set.range h) := by
  have hb : BddBelow (Set.range f) := ⟨0, by rintro _ ⟨s, rfl⟩; exact hf s⟩
  have key : sInf (Set.range f) / c ≤ sInf (Set.range h) := by
    apply le_csInf (Set.range_nonempty h)
    rintro _ ⟨s, rfl⟩
    rw [div_le_iff₀' hc]
    exact (csInf_le hb ⟨s, rfl⟩).trans (hle s)
  rwa [div_le_iff₀' hc] at key

theorem eventually_form_comparison {X ι : Type} [TopologicalSpace X] [Fintype ι]
    (Q : X → (ι → ℝ) → ℝ) (hQ : Continuous fun p : X × (ι → ℝ) => Q p.1 p.2)
    (hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a)
    (hpos : ∀ x a, a ≠ 0 → 0 < Q x a) (x₀ : X) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ x in 𝓝 x₀, ∀ a, a ≠ 0 → (1 - δ) ^ 2 * Q x₀ a ≤ Q x a ∧ Q x a ≤ (1 + δ) ^ 2 * Q x₀ a := by
  have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere _ _
  have hQ0 : Continuous fun p : X × (ι → ℝ) => Q x₀ p.2 :=
    hQ.comp (continuous_const.prodMk continuous_snd)
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ a ∈ Metric.sphere (0 : ι → ℝ) 1,
      (1 - δ) ^ 2 * Q x₀ a < Q x a ∧ Q x a < (1 + δ) ^ 2 * Q x₀ a := by
    apply hK.eventually_forall_of_forall_eventually
    intro a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    have hp := hpos x₀ a ha0
    have hl : (1 - δ) ^ 2 < 1 := by nlinarith
    have hu : 1 < (1 + δ) ^ 2 := by nlinarith
    have h1 : (1 - δ) ^ 2 * Q x₀ a < Q x₀ a := by nlinarith
    have h2 : Q x₀ a < (1 + δ) ^ 2 * Q x₀ a := by nlinarith
    exact ((isOpen_lt (continuous_const.mul hQ0) hQ).inter
      (isOpen_lt hQ (continuous_const.mul hQ0))).mem_nhds ⟨h1, h2⟩
  filter_upwards [hev] with x hx a ha
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hu : ‖a‖⁻¹ • a ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hau : a = ‖a‖ • (‖a‖⁻¹ • a) := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  obtain ⟨h1, h2⟩ := hx _ hu
  have hn2 : 0 < ‖a‖ ^ 2 := by positivity
  rw [hau, hhom x, hhom x₀]
  generalize ‖a‖⁻¹ • a = u at h1 h2
  constructor
  · nlinarith [mul_lt_mul_of_pos_left h1 hn2]
  · nlinarith [mul_lt_mul_of_pos_left h2 hn2]

theorem continuous_sInf_sqrt_form {X ι S : Type} [TopologicalSpace X] [Fintype ι]
    (Q : X → (ι → ℝ) → ℝ) (hQ : Continuous fun p : X × (ι → ℝ) => Q p.1 p.2)
    (hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a)
    (hpos : ∀ x a, a ≠ 0 → 0 < Q x a) (c : S → ι → ℝ) (hc : ∀ s, c s ≠ 0) :
    Continuous fun x => sInf (Set.range fun s => Real.sqrt (Q x (c s))) := by
  rcases isEmpty_or_nonempty S with hS | hS
  · simp only [Set.range_eq_empty]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  set m := sInf (Set.range fun s => Real.sqrt (Q x₀ (c s))) with hm
  have hm0 : 0 ≤ m := Real.sInf_nonneg (by rintro _ ⟨s, rfl⟩; exact Real.sqrt_nonneg _)
  obtain ⟨δ, hδ, hδ1, hδm⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ * m < ε := by
    refine ⟨min (1 / 2) (ε / (2 * (m + 1))), by positivity, ?_, ?_⟩
    · exact (min_le_left _ _).trans_lt (by norm_num)
    · have h1 : min (1 / 2) (ε / (2 * (m + 1))) ≤ ε / (2 * (m + 1)) := min_le_right _ _
      have h2 : ε / (2 * (m + 1)) * m < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      exact (mul_le_mul_of_nonneg_right h1 hm0).trans_lt h2
  filter_upwards [eventually_form_comparison Q hQ hhom hpos x₀ δ hδ hδ1] with x hx
  have hlow : ∀ s, Real.sqrt (Q x₀ (c s)) ≤ (1 - δ)⁻¹ * Real.sqrt (Q x (c s)) := by
    intro s
    have h1 : 0 < 1 - δ := by linarith
    rw [inv_mul_eq_div, le_div_iff₀' h1]
    have := Real.sqrt_le_sqrt (hx _ (hc s)).1
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq h1.le] at this
  have hup : ∀ s, Real.sqrt (Q x (c s)) ≤ (1 + δ) * Real.sqrt (Q x₀ (c s)) := by
    intro s
    have h1 : 0 < 1 + δ := by linarith
    have := Real.sqrt_le_sqrt (hx _ (hc s)).2
    rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq h1.le] at this
  have hA := sInf_range_le_mul _ _ (fun s => Real.sqrt_nonneg _) _
    (inv_pos.mpr (by linarith : 0 < 1 - δ)) hlow
  have hB := sInf_range_le_mul _ _ (fun s => Real.sqrt_nonneg _) _ (by linarith : 0 < 1 + δ) hup
  rw [← hm] at hA hB
  set l := sInf (Set.range fun s => Real.sqrt (Q x (c s))) with hl
  have hA' : (1 - δ) * m ≤ l := by
    have h1 : 0 < 1 - δ := by linarith
    rw [inv_mul_eq_div, le_div_iff₀' h1] at hA
    exact hA
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem linearIndependent_periods (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) :
    LinearIndependent ℝ fun i => R.P (b i) := by
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => R.P (b i)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    rw [← b.sum_repr v, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine linearIndependent_of_top_le_span_of_card_eq_finrank htop ?_
  have h1 : Fintype.card ι = 2 * g := by
    rw [← R.rank, Module.finrank_eq_card_basis b]
  have h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  rw [h1, h2]

def comb (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : ι → Λ) (a : ι → ℝ) : Fin g → ℂ :=
  ∑ i, ((a i : ℝ) : ℂ) • R.P (b i)

theorem comb_repr (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) (v : Λ) :
    comb R b (fun i => ((b.repr v i : ℤ) : ℝ)) = R.P v := by
  conv_rhs => rw [← b.sum_repr v, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
  simp

theorem comb_ne_zero (R : RiemLat E g Λ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Λ) (a : ι → ℝ)
    (ha : a ≠ 0) : comb R b a ≠ 0 := by
  intro h0
  apply ha
  have hli := linearIndependent_periods R b
  have h1 : ∑ i, a i • R.P (b i) = 0 := by
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext j
    simp
  funext i
  exact Fintype.linearIndependent_iff.mp hli a h1 i

end GlobalTheory.CompanionTheory.Ar.Cusp.FirstMin

open GlobalTheory.CompanionTheory.Ar.Cusp.FirstMin in

theorem GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ), (∀ v, Continuous fun x => (R x).P v) → (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).lam1 := by
  intro E _ _ _ g Λ _ _ X _ R hP hH
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact continuous_of_const fun x => hX.elim x
  haveI := (R x₀).free
  haveI := (R x₀).fin
  let b := Module.Free.chooseBasis ℤ Λ
  let Q : X → (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) → ℝ := fun x a =>
    ((R x).ip (comb (R x) b a) (comb (R x) b a)).re
  have hL : Continuous fun p : X × (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) => comb (R p.1) b p.2 := by
    unfold comb
    refine continuous_finset_sum _ fun i _ => ?_
    exact (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_snd)).smul
      ((hP (b i)).comp continuous_fst)
  have hQ : Continuous fun p : X × (Module.Free.ChooseBasisIndex ℤ Λ → ℝ) => Q p.1 p.2 := by
    refine Complex.continuous_re.comp ?_
    exact hL.dotProduct ((hH.comp continuous_fst).matrix_mulVec hL.star)
  have hhom : ∀ x (r : ℝ) a, Q x (r • a) = r ^ 2 * Q x a := by
    intro x r a
    have hc : comb (R x) b (r • a) = (r : ℂ) • comb (R x) b a := by
      unfold comb
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      simp
    simp only [Q, RiemLat.ip, hc, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp [pow_two, mul_assoc]
  have hpos : ∀ x a, a ≠ 0 → 0 < Q x a := fun x a ha => (R x).pos _ (comb_ne_zero (R x) b a ha)
  have hmain := continuous_sInf_sqrt_form Q hQ hhom hpos
    (fun (s : {v : Λ // v ≠ 0}) i => ((b.repr s.1 i : ℤ) : ℝ)) (by
      intro s h0
      apply s.2
      apply b.repr.injective
      ext i
      have := congrFun h0 i
      simpa using this)
  convert hmain using 2 with x
  unfold RiemLat.lam1
  congr 1
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨v, hv⟩, ?_⟩
    simp only [Q, comb_repr, RiemLat.normSq]
  · rintro ⟨⟨v, hv⟩, rfl⟩
    refine ⟨v, hv, ?_⟩
    simp only [Q, comb_repr, RiemLat.normSq]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentPolynomialInAction
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula

variable {E : Type} [Field E] [NumberField E]

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s :=
  (RingHom.injective_iff_ker_eq_bot _).2
    (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))

def extend (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (K := E) (emb_injective s)

theorem extend_comp (s : 𝓞 E →+* ℂ) : (extend s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext fun x => by rw [RingHom.comp_apply, extend, IsFractionRing.lift_algebraMap]

def chr (t : E →+* ℂ) : 𝓞 E →* ℂ := ((t.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ) : 𝓞 E →* ℂ)

theorem chr_injective : Function.Injective (chr (E := E)) := fun t t' h =>
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => DFunLike.congr_fun h x)

theorem span_eq_top :
    Submodule.span ℂ (Set.range fun (a : 𝓞 E) (t : E →+* ℂ) => t (algebraMap (𝓞 E) E a)) = ⊤ := by
  classical
  by_contra h
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
  apply hφ0
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp (chr (E := E)) chr_injective
  have hc := Fintype.linearIndependent_iff.1 li
    (fun t => φ fun j => if t = j then 1 else 0) (by
      funext a
      have h0 : φ (fun t : E →+* ℂ => t (algebraMap (𝓞 E) E a)) = 0 :=
        hφ (Submodule.subset_span ⟨a, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ φ] at h0
      simpa [chr, Finset.sum_apply, mul_comm] using h0)
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.pi_apply_eq_sum_univ φ w]
  simp only [hc, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

open Classical in

theorem exists_coeffs (s : 𝓞 E →+* ℂ) : ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ),
    ∀ t : E →+* ℂ, ∑ i, c i * t (algebraMap (𝓞 E) E (a i)) = if t = extend s then 1 else 0 := by
  have hmem : (fun t : E →+* ℂ => if t = extend s then (1 : ℂ) else 0) ∈
      Submodule.span ℂ (Set.range fun (a : 𝓞 E) (t : E →+* ℂ) => t (algebraMap (𝓞 E) E a)) := by
    rw [span_eq_top]; trivial
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨f.support.card, fun i => (f.support.equivFin.symm i).1,
    fun i => f (f.support.equivFin.symm i).1, fun t => ?_⟩
  have ht := congrFun hf t
  rw [Finsupp.sum, Finset.sum_apply] at ht
  rw [← ht]
  refine (Equiv.sum_comp f.support.equivFin.symm
    (fun x : f.support => f x.1 * t (algebraMap (𝓞 E) E x.1))).trans ?_
  exact Finset.sum_coe_sort f.support (fun x => f x * t (algebraMap (𝓞 E) E x))

theorem eigComp_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : 𝓞 E →+* ℂ),
    ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ), ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ]
      (R : RiemLat E g Λ) (z : Fin g → ℂ), eigComp R.B s z = ∑ i, c i • R.B (a i) z := by
  classical
  intro E _ _ _ s
  obtain ⟨N, a, c, h⟩ := exists_coeffs s
  refine ⟨N, a, c, ?_⟩
  intro g Λ _ _ R z
  obtain ⟨-, -, hs, hsum, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have hB : ∀ (b : 𝓞 E) (t : E →+* ℂ), R.B b (eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z) =
      t (algebraMap (𝓞 E) E b) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
    intro b t
    have hm := (hs (t.comp (algebraMap (𝓞 E) E))).1 z
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker] at hm
    have := hm b
    simpa [sub_eq_zero] using this
  have hz : ∀ b : 𝓞 E, R.B b z = ∑ t : E →+* ℂ,
      t (algebraMap (𝓞 E) E b) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
    intro b
    conv_lhs => rw [← hsum z]
    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => hB b t
  calc eigComp R.B s z
      = ∑ t : E →+* ℂ, (if t = extend s then (1 : ℂ) else 0) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp [extend_comp]
    _ = ∑ t : E →+* ℂ, (∑ i, c i * t (algebraMap (𝓞 E) E (a i))) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp only [h]
    _ = ∑ i, c i • ∑ t : E →+* ℂ, t (algebraMap (𝓞 E) E (a i)) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
        exact Finset.sum_comm
    _ = ∑ i, c i • R.B (a i) z := by simp only [hz]

end GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryFactorCommutation
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection

theorem exists_conj : ∀ (L : Type) [Field L] (N j : ℕ) (ca cb : Fin N) (U : Matrix (Fin N) (Fin N) L) (X' s : L), (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → U ca ca + s * U ca cb ≠ 0 → X' * (U ca ca + s * U ca cb) = s * U cb cb → ∃ V : Matrix (Fin N) (Fin N) L, IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c, c ≠ cb → V c c ≠ 0) ∧ (1 + Matrix.single cb ca X') * V = U * (1 + Matrix.single cb ca s) := by
  intro L _ N j ca cb U X' s hcb hblk hU hT hd hne hX
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hne' : cb ≠ ca := hlt.ne'
  have hR : ∀ (M : Matrix (Fin N) (Fin N) L) (t : L) (r c : Fin N),
      (M * Matrix.single cb ca t) r c = if c = ca then M r cb * t else 0 := by
    intro M t r c
    by_cases h : c = ca
    · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, h, Ne.symm h]
  have hL : ∀ (M : Matrix (Fin N) (Fin N) L) (t : L) (r c : Fin N),
      (Matrix.single cb ca t * M) r c = if r = cb then t * M ca c else 0 := by
    intro M t r c
    by_cases h : r = cb
    · subst h; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, h, Ne.symm h]
  have hW : ∀ r c : Fin N, ((1 + Matrix.single cb ca (-X')) * U) r c
      = U r c + if r = cb then -X' * U ca c else 0 := by
    intro r c
    rw [add_mul, one_mul, Matrix.add_apply, hL]
  have hV : ∀ r c : Fin N,
      ((1 + Matrix.single cb ca (-X')) * U * (1 + Matrix.single cb ca s)) r c
      = U r c + (if r = cb then -X' * U ca c else 0)
        + if c = ca then (U r cb + if r = cb then -X' * U ca cb else 0) * s else 0 := by
    intro r c
    rw [mul_add, mul_one, Matrix.add_apply, hR, hW, hW]
  have hTv : ∀ t : L, IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) L) := by
    intro t a b h
    have hab : a ≠ b := by
      rintro rfl
      exact h Iff.rfl
    rw [Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply, zero_add]
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact h hblk.symm
  refine ⟨(1 + Matrix.single cb ca (-X')) * U * (1 + Matrix.single cb ca s),
    ((hTv _).mul hU).mul (hTv _), ?_, ?_, ?_⟩
  · intro r c hrc
    have hrc' : c < r := hrc
    rw [hV]
    by_cases hc : c = ca
    · subst hc
      by_cases hr : r = cb
      · subst hr
        have h0 : U r c = 0 := hT hrc
        simp only [if_true, h0]
        linear_combination -hX
      · have hcr : cb < r := by
          rw [Fin.lt_def] at hrc' ⊢
          have : (r : ℕ) ≠ cb := fun h => hr (Fin.ext h)
          omega
        have h0 : U r c = 0 := hT hrc
        have h1 : U r cb = 0 := hT hcr
        simp [hr, h0, h1]
    · by_cases hr : r = cb
      · subst hr
        have hcca : c < ca := by
          rw [Fin.lt_def] at hrc' ⊢
          have : (c : ℕ) ≠ ca := fun h => hc (Fin.ext h)
          omega
        have h0 : U r c = 0 := hT hrc
        have h1 : U ca c = 0 := hT hcca
        simp [hc, h0, h1]
      · have h0 : U r c = 0 := hT hrc
        simp [hc, hr, h0]
  · intro c hc
    rw [hV]
    by_cases hca : c = ca
    · subst hca
      simp only [if_true, if_neg hc, add_zero]
      intro h
      apply hne
      linear_combination h
    · simpa [hc, hca] using hd c
  · have hinv : (1 + Matrix.single cb ca X') * (1 + Matrix.single cb ca (-X'))
        = (1 : Matrix (Fin N) (Fin N) L) := by
      have h0 : Matrix.single cb ca X' * Matrix.single cb ca (-X')
          = (0 : Matrix (Fin N) (Fin N) L) := by
        ext r c
        rw [hL, Matrix.single_apply]
        simp [hne']
      rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, h0, add_zero, add_assoc,
        ← Matrix.single_add]
      simp
    rw [← mul_assoc, ← mul_assoc, hinv, one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.MoveTransvection
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPosDefFormOnQuotient
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.QuotUniv

theorem hermitian_transport_along_orthogonal_complement :
    ∀ (g g' : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ (S : Submodule ℂ (Fin g → ℂ)) (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), Function.Surjective q → LinearMap.ker q = S → (∀ z : Fin g → ℂ, ∃ s ∈ S, ∀ v ∈ S, (z - s) ⬝ᵥ Hm *ᵥ star v = 0) → ∃ Hm' : Matrix (Fin g') (Fin g') ℂ, Hm'.IsHermitian ∧ (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm' *ᵥ star z).re) ∧ ∀ x y : Fin g → ℂ, (∀ v ∈ S, x ⬝ᵥ Hm *ᵥ star v = 0) → q y ⬝ᵥ Hm' *ᵥ star (q x) = y ⬝ᵥ Hm *ᵥ star x := by
  intro g g' Hm hHm hpos S q hq hker hproj
  have hconj : ∀ x y : Fin g → ℂ, star (x ⬝ᵥ Hm *ᵥ star y) = y ⬝ᵥ Hm *ᵥ star x := by
    intro x y
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hHm.eq,
      ← Matrix.dotProduct_mulVec]
  have hmemS : ∀ z, q z = 0 → z ∈ S := fun z hz => by
    rw [← hker]
    exact LinearMap.mem_ker.2 hz
  choose z hz using fun i : Fin g' => hq (Pi.single i 1)
  choose s hsS hs using fun i => hproj (z i)
  let A : Matrix (Fin g') (Fin g) ℂ := Matrix.of fun i => z i - s i
  have hAq : ∀ i, q (z i - s i) = Pi.single i 1 := by
    intro i
    have hs0 : q (s i) = 0 := by
      have : s i ∈ LinearMap.ker q := by rw [hker]; exact hsS i
      exact LinearMap.mem_ker.1 this
    rw [map_sub, hz i, hs0, sub_zero]
  have hT : ∀ u : Fin g' → ℂ, Matrix.vecMul u A = ∑ i, u i • (z i - s i) := by
    intro u
    ext a
    simp [A, Matrix.vecMul, dotProduct, Finset.sum_apply]
  have hTq : ∀ u, q (Matrix.vecMul u A) = u := by
    intro u
    rw [hT, map_sum]
    simp_rw [map_smul, hAq]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hTorth : ∀ u, ∀ v ∈ S, Matrix.vecMul u A ⬝ᵥ Hm *ᵥ star v = 0 := by
    intro u v hv
    rw [hT, sum_dotProduct]
    exact Finset.sum_eq_zero fun i _ => by rw [smul_dotProduct, hs i v hv, smul_zero]
  have hkey : ∀ u u' : Fin g' → ℂ, u ⬝ᵥ (A * Hm * A.conjTranspose) *ᵥ star u' =
      Matrix.vecMul u A ⬝ᵥ Hm *ᵥ star (Matrix.vecMul u' A) := by
    intro u u'
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u A,
      Matrix.star_vecMul]
  have hlift : ∀ x : Fin g → ℂ, (∀ v ∈ S, x ⬝ᵥ Hm *ᵥ star v = 0) →
      Matrix.vecMul (q x) A = x := by
    intro x hx
    have hdS : Matrix.vecMul (q x) A - x ∈ S := hmemS _ (by rw [map_sub, hTq, sub_self])
    have hd0 : (Matrix.vecMul (q x) A - x) ⬝ᵥ Hm *ᵥ star (Matrix.vecMul (q x) A - x) = 0 := by
      rw [sub_dotProduct, hTorth _ _ hdS, hx _ hdS, sub_zero]
    by_contra hne
    have := hpos _ (sub_ne_zero.2 hne)
    rw [hd0, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨A * Hm * A.conjTranspose, Matrix.isHermitian_mul_mul_conjTranspose A hHm, ?_, ?_⟩
  · intro u hu
    rw [hkey]
    apply hpos
    intro h0
    apply hu
    rw [← hTq u, h0, map_zero]
  · intro x y hx
    rw [hkey, hlift x hx, ← sub_eq_zero, ← sub_dotProduct, ← hconj,
      hx (Matrix.vecMul (q y) A - y) (hmemS _ (by rw [map_sub, hTq, sub_self])), star_zero]

end GlobalTheory.CompanionTheory.Ar.QuotUniv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRealOrthogonalProjectionOfRealGram
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.ProjReal

theorem orthogonal_projection_real_coefficients :
    ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) →
      ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℂ u →
      (∀ z : Fin g → ℂ, ∃ c : Fin k → ℂ, ∀ j, (z - ∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0) →
      (∀ i j, (u i ⬝ᵥ Hm *ᵥ star (u j)).im = 0) →
      ∀ z : Fin g → ℂ, (∀ j, (z ⬝ᵥ Hm *ᵥ star (u j)).im = 0) →
      ∃ c : Fin k → ℝ, ∀ j, (z - ∑ i, (c i : ℂ) • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := by
  intro g k Hm _ u _ hproj hu z hz
  obtain ⟨c, hc⟩ := hproj z
  refine ⟨fun i => (c i).re, fun j => ?_⟩
  have h := hc j
  simp only [sub_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul] at h ⊢
  apply Complex.ext
  · have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.re_sum, Complex.mul_re, hu, mul_zero, sub_zero, Complex.zero_re] at h'
    simpa [Complex.sub_re, Complex.re_sum, Complex.mul_re, hu] using h'
  · simp [Complex.sub_im, Complex.im_sum, Complex.mul_im, hu, hz]

end GlobalTheory.CompanionTheory.Ar.ProjReal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecompositionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_potential_block_decomposition : ∀ (N j : ℕ) (i : Fin N) (Pi G h : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsPeriodGram j Pi G → IsBlockDiag j G → G.PosDef → IsBlockDiag j h → h.det ≠ 0 → InFlagDomain N j (Pi * h) ∧ stepPot N j i (Pi * h) = blockPot j i G h + Real.log ‖detFac j i h‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.stepPot_mul_eq_blockPot | exact GlobalTheory.CompanionTheory.Ar.PB.stepPot_mul_eq_blockPot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.stepPot_mul_eq_blockPot <;> assumption)
end

