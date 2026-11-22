import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicKappaPropertiesProof
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.HyperbolicKappaLemmas

open UpperTheory.Esk

theorem nsq (z w : ℂ) : ‖z - conj w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im + w.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

theorem pos_den {z w : ℂ} (h : 0 < z.im * w.im) : 0 < ‖z - conj w‖ ^ 2 := by
  rw [nsq]
  nlinarith [sq_nonneg (z.re - w.re), sq_nonneg z.im, sq_nonneg w.im]

theorem kap_of {z w : P} (h : 0 < z.1.im * w.1.im) :
    kap z w = 4 * (z.1.im * w.1.im) / ‖z.1 - conj w.1‖ ^ 2 := by
  unfold kap
  rw [if_pos h]

theorem kap_of_not {z w : P} (h : ¬ 0 < z.1.im * w.1.im) : kap z w = 0 := by
  unfold kap
  rw [if_neg h]

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (by linarith) (sq_nonneg _)
  · exact le_rfl

theorem key {z w u : ℂ} (h1 : 0 < z.im * w.im) (h2 : 0 < w.im * u.im) :
    w.im ^ 2 * ‖z - conj u‖ ^ 2 ≤ ‖z - conj w‖ ^ 2 * ‖w - conj u‖ ^ 2 := by
  have h13 : 0 < z.im * u.im := by
    by_contra hc
    have hc := not_lt.mp hc
    nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg w.im)]
  have hp : 0 ≤ z.im ^ 2 + 2 * z.im * w.im := by nlinarith [sq_nonneg z.im]
  have hq : 0 ≤ u.im ^ 2 + 2 * w.im * u.im := by nlinarith [sq_nonneg u.im]
  rw [nsq, nsq, nsq]
  nlinarith [sq_nonneg ((z.re - w.re) * (w.re - u.re) - w.im ^ 2),
    mul_nonneg (sq_nonneg (z.re - w.re)) hq, mul_nonneg (sq_nonneg (w.re - u.re)) hp,
    mul_nonneg (sq_nonneg w.im) h1.le, mul_nonneg (sq_nonneg w.im) h2.le,
    mul_nonneg (sq_nonneg w.im) h13.le, mul_nonneg h13.le h1.le, mul_nonneg h13.le h2.le,
    sq_nonneg (z.im * u.im)]

theorem p1 (z w : P) : 0 ≤ kap z w ∧ kap z w ≤ 1 ∧ kap z w = kap w z := by
  refine ⟨kap_nonneg z w, ?_, ?_⟩
  · by_cases h : 0 < z.1.im * w.1.im
    · rw [kap_of h, div_le_iff₀ (pos_den h), nsq]
      nlinarith [sq_nonneg (z.1.re - w.1.re), sq_nonneg (z.1.im - w.1.im)]
    · rw [kap_of_not h]
      norm_num
  · have e2 : ‖w.1 - conj z.1‖ ^ 2 = ‖z.1 - conj w.1‖ ^ 2 := by
      rw [nsq, nsq]
      ring
    unfold kap
    rw [mul_comm w.1.im z.1.im, e2]

theorem p2 (z : P) : kap z z = 1 := by
  have h : 0 < z.1.im * z.1.im := mul_self_pos.mpr z.2
  rw [kap_of h, div_eq_one_iff_eq (pos_den h).ne', nsq]
  ring

theorem p3 (z w u : P) : kap z w * kap w u ≤ 4 * kap z u := by
  by_cases h1 : 0 < z.1.im * w.1.im
  · by_cases h2 : 0 < w.1.im * u.1.im
    · have h13 : 0 < z.1.im * u.1.im := by
        by_contra hc
        have hc := not_lt.mp hc
        nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg w.1.im)]
      have hA := pos_den h1
      have hB := pos_den h2
      have hC := pos_den h13
      have hk := mul_le_mul_of_nonneg_left (key h1 h2) h13.le
      rw [kap_of h1, kap_of h2, kap_of h13, div_mul_div_comm, mul_div_assoc', le_div_iff₀ hC,
        div_mul_eq_mul_div, div_le_iff₀ (mul_pos hA hB)]
      nlinarith [hk]
    · rw [kap_of_not h2, mul_zero]
      exact mul_nonneg (by norm_num) (kap_nonneg z u)
  · rw [kap_of_not h1, zero_mul]
    exact mul_nonneg (by norm_num) (kap_nonneg z u)

theorem p4 (z w : P) : kap z w * |w.1.im| ≤ 4 * |z.1.im| := by
  by_cases h : 0 < z.1.im * w.1.im
  · rw [kap_of h, div_mul_eq_mul_div, div_le_iff₀ (pos_den h), nsq]
    rcases lt_or_gt_of_ne w.2 with hw | hw
    · have hz : z.1.im < 0 := by nlinarith [h, hw]
      rw [abs_of_neg hw, abs_of_neg hz]
      nlinarith [mul_nonneg (neg_nonneg.mpr hz.le) (sq_nonneg (z.1.re - w.1.re)),
        mul_nonneg (neg_nonneg.mpr hz.le) (sq_nonneg z.1.im),
        mul_nonneg (sq_nonneg z.1.im) (neg_nonneg.mpr hw.le)]
    · have hz : 0 < z.1.im := by nlinarith [h, hw]
      rw [abs_of_pos hw, abs_of_pos hz]
      nlinarith [mul_nonneg hz.le (sq_nonneg (z.1.re - w.1.re)), mul_nonneg hz.le (sq_nonneg z.1.im),
        mul_nonneg (sq_nonneg z.1.im) hw.le]
  · rw [kap_of_not h, zero_mul]
    positivity

theorem p5 : Continuous (fun p : P × P => kap p.1 p.2) := by
  have hv1 : Continuous (fun p : P × P => p.1.1) := continuous_subtype_val.comp continuous_fst
  have hv2 : Continuous (fun p : P × P => p.2.1) := continuous_subtype_val.comp continuous_snd
  have hc : Continuous (fun p : P × P => p.1.1.im * p.2.1.im) :=
    (Complex.continuous_im.comp hv1).mul (Complex.continuous_im.comp hv2)
  have hd : Continuous (fun p : P × P => ‖p.1.1 - conj p.2.1‖ ^ 2) :=
    ((hv1.sub (Complex.continuous_conj.comp hv2)).norm).pow 2
  have hopen : IsOpen {p : P × P | 0 < p.1.1.im * p.2.1.im} := isOpen_lt continuous_const hc
  have hclosed : IsClosed {p : P × P | 0 < p.1.1.im * p.2.1.im} := by
    have e : {p : P × P | 0 < p.1.1.im * p.2.1.im} = {p : P × P | 0 ≤ p.1.1.im * p.2.1.im} := by
      ext p
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => le_of_lt h, fun h => lt_of_le_of_ne h (Ne.symm (mul_ne_zero p.1.2 p.2.2))⟩
    rw [e]
    exact isClosed_le continuous_const hc
  have hfr : frontier {p : P × P | 0 < p.1.1.im * p.2.1.im} = ∅ := by
    rw [frontier, hclosed.closure_eq, hopen.interior_eq, Set.sdiff_self]
  show Continuous (fun p : P × P => if 0 < p.1.1.im * p.2.1.im then
    4 * (p.1.1.im * p.2.1.im) / ‖p.1.1 - conj p.2.1‖ ^ 2 else 0)
  apply continuous_if
  · intro a ha
    simp [hfr] at ha
  · rw [hclosed.closure_eq]
    exact ((continuous_const.mul hc).continuousOn).div hd.continuousOn
      (fun p hp => (pos_den (z := p.1.1) (w := p.2.1) hp).ne')
  · exact continuousOn_const

theorem p6 (z : P) : ∃ g : GL (Fin 2) ℝ, g 1 0 = 0 ∧ g 1 1 = 1 ∧ g • iP = z := by
  have hdet : (!![z.1.im, z.1.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simpa using z.2
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl, rfl, Subtype.ext ?_⟩
  rw [coe_smul]
  show num (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) Complex.I /
    den (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) Complex.I = z.1
  have h00 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 0 0 = z.1.im := rfl
  have h01 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 0 1 = z.1.re := rfl
  have h10 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 1 0 = 0 := rfl
  have h11 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 1 1 = 1 := rfl
  rw [num, den, h00, h01, h10, h11]
  apply Complex.ext <;> simp

end UpperTheory.Esk.HyperbolicKappaLemmas

namespace UpperTheory.Esk

theorem hyperbolic_kappa_properties_proof : B1c := by
  unfold B1c
  exact ⟨HyperbolicKappaLemmas.p1, HyperbolicKappaLemmas.p2, HyperbolicKappaLemmas.p3, HyperbolicKappaLemmas.p4, HyperbolicKappaLemmas.p5, HyperbolicKappaLemmas.p6⟩

end UpperTheory.Esk
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfLinTr
section
noncomputable section

open MeasureTheory

namespace UpperTheory.Esk.LinearTraceLemmas

variable {A Y : Type} [MeasurableSpace Y] (ν : Measure Y) (V : Submodule ℂ (A → ℂ))

def evl (a : A) : Module.Dual ℂ V := (LinearMap.proj a : (A → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype

theorem evl_apply (a : A) (f : V) : evl V a f = f.1 a := rfl

theorem span_evl [FiniteDimensional ℂ V] : Submodule.span ℂ (Set.range (evl V)) = ⊤ := by
  by_contra h
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)
  obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ V).surjective f
  have hv : v = 0 := by
    apply Subtype.ext
    funext a
    have h1 : (Module.evalEquiv ℂ V v) (evl V a) = 0 :=
      LinearMap.mem_ker.mp (hfk (Submodule.subset_span ⟨a, rfl⟩))
    have h2 : (Module.evalEquiv ℂ V v) (evl V a) = v.1 a := by
      rfl
    have h3 : v.1 a = 0 := h2.symm.trans h1
    simpa using h3
  exact hf0 (by rw [hv, map_zero])

omit [MeasurableSpace Y] in
theorem bound_mul {g h : Y → ℂ} {n : Y → ℝ} (hn : ∀ y, 0 < n y) (C D : ℝ)
    (hC : ∀ y, ‖g y‖ ≤ C * n y) (hD : ∀ y, ‖h y‖ * n y ≤ D) (y : Y) : ‖g y * h y‖ ≤ C * D := by
  have hn' := hn y
  have hC0 : 0 ≤ C := by
    by_contra hneg
    have hlt : C < 0 := not_le.mp hneg
    have : C * n y < 0 := mul_neg_of_neg_of_pos hlt hn'
    linarith [norm_nonneg (g y), hC y]
  rw [norm_mul]
  calc ‖g y‖ * ‖h y‖ ≤ (C * n y) * ‖h y‖ := mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)
    _ = C * (‖h y‖ * n y) := by ring
    _ ≤ C * D := mul_le_mul_of_nonneg_left (hD y) hC0

theorem integrable_mul [IsFiniteMeasure ν] {g h : Y → ℂ} {n : Y → ℝ} (hn : ∀ y, 0 < n y)
    (hg : Measurable g) (hh : Measurable h) (C D : ℝ) (hC : ∀ y, ‖g y‖ ≤ C * n y)
    (hD : ∀ y, ‖h y‖ * n y ≤ D) : Integrable (fun y => g y * h y) ν := by
  exact (integrable_const (C * D)).mono' (hg.mul hh).aestronglyMeasurable
    (ae_of_all _ fun y => bound_mul hn C D hC hD y)

def Good (K : Y → V) (ev : Y → A) (n : Y → ℝ) (φ : Module.Dual ℂ V) : Prop :=
  Measurable (fun y => φ (K y)) ∧ (∃ C, ∀ y, ‖φ (K y)‖ ≤ C * n y) ∧
    ∀ f : V, ∫ y, φ (K y) * f.1 (ev y) ∂ν = φ f

theorem good_all [IsFiniteMeasure ν] [FiniteDimensional ℂ V] (K : Y → V) (ev : Y → A) (n : Y → ℝ)
    (hn : ∀ y, 0 < n y) (hK : ∀ a, Measurable fun y => (K y).1 a)
    (hev : ∀ f : V, Measurable fun y => f.1 (ev y)) (hKb : ∀ a, ∃ C, ∀ y, ‖(K y).1 a‖ ≤ C * n y)
    (hevb : ∀ f : V, ∃ C, ∀ y, ‖f.1 (ev y)‖ * n y ≤ C)
    (hrep : ∀ (f : V) a, ∫ y, (K y).1 a * f.1 (ev y) ∂ν = f.1 a) (φ : Module.Dual ℂ V) :
    Good ν V K ev n φ := by
  have hint : ∀ ψ : Module.Dual ℂ V, Good ν V K ev n ψ → ∀ f : V,
      Integrable (fun y => ψ (K y) * f.1 (ev y)) ν := by
    intro ψ hψ f
    obtain ⟨C, hC⟩ := hψ.2.1
    obtain ⟨D, hD⟩ := hevb f
    exact integrable_mul ν hn hψ.1 (hev f) C D hC hD
  have hadd : ∀ φ₁ φ₂, Good ν V K ev n φ₁ → Good ν V K ev n φ₂ → Good ν V K ev n (φ₁ + φ₂) := by
    intro φ₁ φ₂ h₁ h₂
    obtain ⟨C₁, hC₁⟩ := h₁.2.1
    obtain ⟨C₂, hC₂⟩ := h₂.2.1
    refine ⟨h₁.1.add h₂.1, ⟨C₁ + C₂, fun y => ?_⟩, fun f => ?_⟩
    · rw [LinearMap.add_apply, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hC₁ y) (hC₂ y))
    · simp only [LinearMap.add_apply, add_mul]
      rw [integral_add (hint φ₁ h₁ f) (hint φ₂ h₂ f), h₁.2.2 f, h₂.2.2 f]
  have hzero : Good ν V K ev n 0 := by
    refine ⟨?_, ⟨0, fun y => ?_⟩, fun f => ?_⟩
    · simp
    · simp
    · simp
  have hsmul : ∀ (c : ℂ) φ, Good ν V K ev n φ → Good ν V K ev n (c • φ) := by
    intro c φ h
    obtain ⟨C, hC⟩ := h.2.1
    refine ⟨h.1.const_mul c, ⟨‖c‖ * C, fun y => ?_⟩, fun f => ?_⟩
    · rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)
    · simp only [LinearMap.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, h.2.2 f]
  obtain ⟨Sg, hSg⟩ : ∃ Sg : Submodule ℂ (Module.Dual ℂ V), ∀ ψ, ψ ∈ Sg ↔ Good ν V K ev n ψ :=
    ⟨{ carrier := {ψ | Good ν V K ev n ψ}
       add_mem' := fun {a b} ha hb => hadd a b ha hb
       zero_mem' := hzero
       smul_mem' := fun c ψ h => hsmul c ψ h }, fun _ => Iff.rfl⟩
  have hev' : ∀ a, Good ν V K ev n (evl V a) := by
    intro a
    refine ⟨?_, ?_, fun f => ?_⟩
    · simpa only [evl_apply] using hK a
    · simpa only [evl_apply] using hKb a
    · simpa only [evl_apply] using hrep f a
  have htop : Sg = ⊤ := by
    rw [eq_top_iff, ← span_evl V, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact (hSg _).mpr (hev' a)
  exact (hSg φ).mp (by rw [htop]; exact Submodule.mem_top)

theorem main : UpperTheory.Esk.LinTr := by
  intro A Y _ ν _ V _ T K ev n _ hn hK hev hKb hevb hrep
  have hgood : ∀ φ : Module.Dual ℂ V, Good ν V K ev n φ :=
    good_all ν V K ev n hn hK hev hKb hevb hrep
  let b := Module.finBasis ℂ V
  have hexp : ∀ y, (T (K y)).1 (ev y) = ∑ i, b.coord i (K y) * (T (b i)).1 (ev y) := by
    intro y
    have e : T (K y) = ∑ i, b.repr (K y) i • T (b i) := by
      conv_lhs => rw [← b.sum_repr (K y)]
      rw [map_sum]
      simp only [map_smul]
    rw [e]
    simp [Module.Basis.coord_apply]
  have hmeas : Measurable fun y => (T (K y)).1 (ev y) := by
    simp_rw [hexp]
    exact Finset.measurable_sum _ fun i _ => (hgood (b.coord i)).1.mul (hev (T (b i)))
  have hbd : ∃ C, ∀ y, ‖(T (K y)).1 (ev y)‖ ≤ C := by
    choose Cs hCs using fun i => (hgood (b.coord i)).2.1
    choose Ds hDs using fun i => hevb (T (b i))
    refine ⟨∑ i, Cs i * Ds i, fun y => ?_⟩
    rw [hexp]
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i _ => bound_mul hn (Cs i) (Ds i) (hCs i) (hDs i) y)
  have hintg : ∀ i, Integrable (fun y => b.coord i (K y) * (T (b i)).1 (ev y)) ν := by
    intro i
    obtain ⟨C, hC⟩ := (hgood (b.coord i)).2.1
    obtain ⟨D, hD⟩ := hevb (T (b i))
    exact integrable_mul ν hn (hgood (b.coord i)).1 (hev (T (b i))) C D hC hD
  refine ⟨hmeas, hbd, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ b T, Matrix.trace]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => hintg i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hgood (b.coord i)).2.2 (T (b i))]
  simp [LinearMap.toMatrix_apply, Module.Basis.coord_apply]

end UpperTheory.Esk.LinearTraceLemmas

theorem UpperTheory.Esk.pf_LinTr : UpperTheory.Esk.LinTr := by
  exact UpperTheory.Esk.LinearTraceLemmas.main
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.RSubPowApply
section
namespace UpperTheory.Esk.CommutingOperatorTraces

open Module Module.End

variable {J V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

noncomputable def E (T : J → Module.End ℂ V) (s : J → ℂ) : Submodule ℂ V :=
  ⨅ j, (T j).maxGenEigenspace (s j)

lemma mapsTo_E (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (i : J) : Set.MapsTo (T i) (E T s) (E T s) := by
  intro x hx
  simp only [E, SetLike.mem_coe, Submodule.mem_iInf] at hx ⊢
  intro j
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (hT j i) (s j) (hx j)

lemma mapsTo_prod (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) : Set.MapsTo (W.map T).prod (E T s) (E T s) := by
  induction W with
  | nil => intro x hx; simpa using hx
  | cons a W ih =>
    intro x hx
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact mapsTo_E T hT s a (ih hx)

noncomputable def R (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (j : J) : Module.End ℂ (E T s) :=
  (T j).restrict (mapsTo_E T hT s j)

lemma R_apply (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (j : J) (x : E T s) : ((R T hT s j x : E T s) : V) = T j x := rfl

lemma R_comm (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (i j : J) : Commute (R T hT s i) (R T hT s j) := by
  show R T hT s i * R T hT s j = R T hT s j * R T hT s i
  refine LinearMap.ext fun x => Subtype.ext ?_
  simp only [Module.End.mul_apply, R_apply]
  exact LinearMap.congr_fun (hT i j) x

lemma R_prod_apply (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) (x : E T s) : (((W.map (R T hT s)).prod x : E T s) : V) = (W.map T).prod x := by
  induction W with
  | nil => simp
  | cons a W ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, R_apply, ih]

lemma R_sub_pow_apply (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i)
    (s : J → ℂ) (j : J) (n : ℕ) (x : E T s) :
    ((((R T hT s j - algebraMap ℂ _ (s j)) ^ n) x : E T s) : V) = ((T j - s j • 1) ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    rw [← ih]
    simp [R_apply, Algebra.algebraMap_eq_smul_one]

lemma R_nil (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ) (j : J) :
    IsNilpotent (R T hT s j - algebraMap ℂ _ (s j)) := by
  rw [Module.End.isNilpotent_iff_of_finite]
  intro x
  have hx := x.2
  simp only [E] at hx
  obtain ⟨k, hk⟩ := (Module.End.mem_iInf_maxGenEigenspace_iff T s (x : V)).mp hx j
  refine ⟨k, Subtype.ext ?_⟩
  rw [R_sub_pow_apply, hk]
  rfl

lemma trace_R_prod (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) : LinearMap.trace ℂ (E T s) (W.map (R T hT s)).prod =
      (Module.finrank ℂ (E T s) : ℂ) * (W.map s).prod := by
  induction W with
  | nil => simp [LinearMap.trace_one]
  | cons a W ih =>
    have hc : Commute (W.map (R T hT s)).prod (R T hT s a) := by
      apply Commute.list_prod_left
      intro y hy
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy
      exact R_comm T hT s b a
    simp only [List.map_cons, List.prod_cons]
    rw [← hc.eq, Module.End.mul_eq_comp,
      LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent (s a) hc (R_nil T hT s a), ih]
    ring

lemma trace_restrict (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (W : List J) (h : Set.MapsTo (W.map T).prod (E T s) (E T s)) :
    LinearMap.trace ℂ (E T s) ((W.map T).prod.restrict h) =
      (Module.finrank ℂ (E T s) : ℂ) * (W.map s).prod := by
  have : (W.map T).prod.restrict h = (W.map (R T hT s)).prod := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [R_prod_apply]
    rfl
  rw [this, trace_R_prod]

lemma exists_eigvec (T : J → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i) (s : J → ℂ)
    (hs : E T s ≠ ⊥) : ∃ f : V, f ≠ 0 ∧ ∀ j, T j f = s j • f := by
  classical
  let P : Set (Submodule ℂ V) :=
    {U | U ≠ ⊥ ∧ U ≤ E T s ∧ ∀ j, ∀ x ∈ U, T j x ∈ U}
  have hP : (E T s) ∈ P := ⟨hs, le_rfl, fun j x hx => mapsTo_E T hT s j hx⟩
  obtain ⟨U, ⟨hU0, hUE, hUT⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ V)).has_min P ⟨_, hP⟩
  obtain ⟨x, hxU, hx0⟩ := (Submodule.ne_bot_iff U).mp hU0
  refine ⟨x, hx0, fun j => ?_⟩

  have hsub : ∀ n : ℕ, ∀ y ∈ U, ((T j - s j • 1) ^ n) y ∈ U := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      have h1 := ih y hy
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact U.sub_mem (hUT j _ h1) (U.smul_mem _ h1)
  let U' : Submodule ℂ V := U ⊓ (T j).eigenspace (s j)
  have hU'P : U' ∈ P := by
    refine ⟨?_, inf_le_left.trans hUE, ?_⟩
    · have hxE : x ∈ E T s := hUE hxU
      simp only [E] at hxE
      have hex := (Module.End.mem_iInf_maxGenEigenspace_iff T s x).mp hxE j
      let k := Nat.find hex
      have hk : ((T j - s j • 1) ^ k) x = 0 := Nat.find_spec hex
      have hk0 : k ≠ 0 := by
        intro h0
        rw [h0, pow_zero, Module.End.one_apply] at hk
        exact hx0 hk
      obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hne : ((T j - s j • 1) ^ k') x ≠ 0 := by
        have := Nat.find_min hex (show k' < k by omega)
        exact this
      rw [Submodule.ne_bot_iff]
      refine ⟨((T j - s j • 1) ^ k') x, ⟨hsub k' x hxU, ?_⟩, hne⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have h2 : ((T j - s j • 1) ^ k) x = 0 := hk
      rw [hk', pow_succ', Module.End.mul_apply] at h2
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h2
      exact sub_eq_zero.mp h2
    · intro i y hy
      refine ⟨hUT i y hy.1, ?_⟩
      have hy2 : T j y = s j • y := (Module.End.mem_eigenspace_iff).mp hy.2
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have := LinearMap.congr_fun (hT j i) y
      simp only [Module.End.mul_apply] at this
      rw [this, hy2, map_smul]
  have hle : U' ≤ U := inf_le_left
  have hUU : U' = U := by
    by_contra hne
    exact hmin U' hU'P (lt_of_le_of_ne hle hne)
  have hxU' : x ∈ U' := hUU ▸ hxU
  exact (Module.End.mem_eigenspace_iff).mp hxU'.2

end UpperTheory.Esk.CommutingOperatorTraces

open UpperTheory.Esk.CommutingOperatorTraces in
theorem UpperTheory.Esk.pf_Sys : UpperTheory.Esk.Sys := by
  intro J V _ _ _ T hT
  classical
  have hind : iSupIndep (E T) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
      (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hT j i) φ)
  have htop : ⨆ s, E T s = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T
      (fun i j _ => hT i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (T i))
  have hfin : {s | E T s ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have htr : ∀ W : List J, LinearMap.trace ℂ V (W.map T).prod =
      ∑ s ∈ hfin.toFinset, (Module.finrank ℂ (E T s) : ℂ) * (W.map s).prod := by
    intro W
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin (mapsTo_prod T hT · W)]
    exact Finset.sum_congr rfl fun s _ => trace_restrict T hT s W _
  refine ⟨hfin.toFinset, fun s => Module.finrank ℂ (E T s), ?_, ?_, ?_, htr⟩
  · intro s
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · exact exists_eigvec T hT s
    · rintro ⟨f, hf0, hf⟩ hbot
      have hfE : f ∈ E T s := by
        simp only [E, Submodule.mem_iInf]
        intro j
        apply Module.End.eigenspace_le_maxGenEigenspace
        exact (Module.End.mem_eigenspace_iff).mpr (hf j)
      rw [hbot, Submodule.mem_bot] at hfE
      exact hf0 hfE
  · intro s hs
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hs
    exact Submodule.one_le_finrank_iff.mpr hs
  · have h0 := htr []
    simp only [List.map_nil, List.prod_nil, LinearMap.trace_one, mul_one] at h0
    exact_mod_cast h0.symm
end

