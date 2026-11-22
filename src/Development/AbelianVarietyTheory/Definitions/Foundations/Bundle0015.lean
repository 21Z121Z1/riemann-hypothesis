import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
section
noncomputable section

namespace GlobalTheory.Eis

open scoped NNReal
open Filter Topology Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

section Sums

variable {G : Type} [Group G] (P Γ : Subgroup G)

abbrev Cosets : Type := Quot (P.subgroupOf Γ)

def term {X : Type} (Φ : G → X) (g : G) (q : Cosets P Γ) : X := Φ ((q.out : Γ) * g)

def cosetSum (Φ : G → ℂ) (g : G) : ℂ := ∑' q, term P Γ Φ g q

def CosetConv (Φ : G → ℂ) (g : G) : Prop := Summable fun q => ‖term P Γ Φ g q‖

def rmulEquiv (γ : Γ) : Cosets P Γ ≃ Cosets P Γ :=
  ⟨rmul _ γ, rmul _ γ⁻¹, fun q => by rw [← rmul_mul, mul_inv_cancel, rmul_one],
    fun q => by rw [← rmul_mul, inv_mul_cancel, rmul_one]⟩

variable {P Γ} {X : Type} {Φ Ψ : G → ℂ} {g : G}

theorem term_mk {Φ : G → X} (h : LeftInv (P ⊓ Γ) Φ) (g : G) (γ : Γ) : term P Γ Φ g (mk _ γ) = Φ (γ * g) :=
  LeftInv.descend_mk (Γ := P.subgroupOf Γ) (φ := fun x : Γ => Φ (x * g))
    (fun δ hδ x => (congrArg Φ (mul_assoc _ _ _)).trans (h δ ⟨hδ, δ.2⟩ _)) γ

theorem term_mul_left {Φ : G → X} (h : LeftInv (P ⊓ Γ) Φ) (γ : Γ) (g : G) (q : Cosets P Γ) :
    term P Γ Φ (γ * g) q = term P Γ Φ g (rmulEquiv P Γ γ q) :=
  Quotient.inductionOn q fun x => (term_mk h _ x).trans (((term_mk h g (x * γ)).trans (by simp [mul_assoc])).symm)

theorem leftInv_cosetSum (h : LeftInv (P ⊓ Γ) Φ) : LeftInv Γ (cosetSum P Γ Φ) := fun γ hγ g =>
  (tsum_congr (term_mul_left h ⟨γ, hγ⟩ g)).trans ((rmulEquiv P Γ ⟨γ, hγ⟩).tsum_eq _)

theorem cosetConv_mul_left (h : LeftInv (P ⊓ Γ) Φ) {γ : G} (hγ : γ ∈ Γ) : CosetConv P Γ Φ (γ * g) ↔ CosetConv P Γ Φ g := by
  rw [CosetConv, CosetConv, ← (rmulEquiv P Γ ⟨γ, hγ⟩).summable_iff (f := fun q => ‖term P Γ Φ g q‖)]
  exact summable_congr fun q => congrArg norm (term_mul_left h ⟨γ, hγ⟩ g q)

theorem cosetSum_mul_right (Φ : G → ℂ) (k g : G) : cosetSum P Γ (fun x => Φ (x * k)) g = cosetSum P Γ Φ (g * k) := by
  simp only [cosetSum, term, mul_assoc]

theorem cosetConv_mul_right (Φ : G → ℂ) (k g : G) : CosetConv P Γ (fun x => Φ (x * k)) g ↔ CosetConv P Γ Φ (g * k) := by
  simp only [CosetConv, term, mul_assoc]

theorem cosetSum_eq_tsum (h : LeftInv (P ⊓ Γ) Φ) {ι : Type} {r : ι → Γ}
    (hr : Function.Bijective fun i => mk (P.subgroupOf Γ) (r i)) (g : G) : cosetSum P Γ Φ g = ∑' i, Φ (r i * g) :=
  ((Equiv.ofBijective _ hr).tsum_eq _).symm.trans (tsum_congr fun i => term_mk h g (r i))

theorem cosetConv_iff (h : LeftInv (P ⊓ Γ) Φ) {ι : Type} {r : ι → Γ}
    (hr : Function.Bijective fun i => mk (P.subgroupOf Γ) (r i)) : CosetConv P Γ Φ g ↔ Summable fun i => ‖Φ (r i * g)‖ :=
  (Equiv.ofBijective _ hr).summable_iff.symm.trans (summable_congr fun i => congrArg norm (term_mk h g (r i)))

theorem CosetConv.hasSum (h : CosetConv P Γ Φ g) : HasSum (term P Γ Φ g) (cosetSum P Γ Φ g) := h.of_norm.hasSum

theorem CosetConv.of_norm_le (h : CosetConv P Γ Ψ g) {C : ℝ} (e : ∀ x, ‖Φ x‖ ≤ C * ‖Ψ x‖) : CosetConv P Γ Φ g :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => e _) (h.mul_left C)

theorem CosetConv.add (h : CosetConv P Γ Φ g) (h' : CosetConv P Γ Ψ g) : CosetConv P Γ (Φ + Ψ) g :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_add_le _ _) (Summable.add h h')

theorem CosetConv.smul (h : CosetConv P Γ Φ g) (c : ℂ) : CosetConv P Γ (c • Φ) g :=
  h.of_norm_le fun x => (norm_smul c (Φ x)).le

theorem cosetSum_add (h : CosetConv P Γ Φ g) (h' : CosetConv P Γ Ψ g) :
    cosetSum P Γ (Φ + Ψ) g = cosetSum P Γ Φ g + cosetSum P Γ Ψ g := (h.hasSum.add h'.hasSum).tsum_eq

theorem cosetSum_smul (c : ℂ) (Φ : G → ℂ) (g : G) : cosetSum P Γ (c • Φ) g = c * cosetSum P Γ Φ g := tsum_mul_left

theorem cosetSum_of_le (e : Γ ≤ P) (h : LeftInv (P ⊓ Γ) Φ) (g : G) : CosetConv P Γ Φ g ∧ cosetSum P Γ Φ g = Φ g := by
  have hr : Function.Bijective fun _ : Unit => mk (P.subgroupOf Γ) 1 := ⟨fun _ _ _ => rfl, fun q =>
    Quotient.inductionOn q fun x => ⟨(), mk_eq_iff.2 ⟨⟨x, e x.2⟩, mul_one _⟩⟩⟩
  exact ⟨(cosetConv_iff h hr).2 .of_finite, by simpa using cosetSum_eq_tsum h hr g⟩

theorem cosetSum_indicator (g : G) : LeftInv (P ⊓ Γ) (indicator ((P ⊓ Γ : Subgroup G) : Set G) (1 : G → ℂ)) ∧
    CosetConv P Γ (indicator ((P ⊓ Γ : Subgroup G) : Set G) 1) g ∧
    cosetSum P Γ (indicator ((P ⊓ Γ : Subgroup G) : Set G) 1) g = indicator (Γ : Set G) 1 g := by
  have h : LeftInv (P ⊓ Γ) (indicator ((P ⊓ Γ : Subgroup G) : Set G) (1 : G → ℂ)) := fun γ hγ x => by
    classical simp only [indicator, SetLike.mem_coe, Subgroup.mul_mem_cancel_left _ hγ, Pi.one_apply]
  by_cases hg : g ∈ Γ
  · have h0 : ∀ q ≠ mk (P.subgroupOf Γ) 1, term P Γ (indicator ((P ⊓ Γ : Subgroup G) : Set G) (1 : G → ℂ)) 1 q = 0 :=
      fun q => Quotient.inductionOn q fun x hx => (term_mk h 1 x).trans (indicator_of_notMem
        (fun e => hx (mk_eq_iff.2 ⟨⟨x, Subgroup.mem_subgroupOf.2 (by simpa using e.1)⟩, mul_one _⟩).symm) _)
    rw [← mul_one g, cosetConv_mul_left h hg, leftInv_cosetSum h g hg, mul_one, indicator_of_mem hg]
    refine ⟨h, summable_of_ne_finset_zero (s := {mk _ 1}) fun q hq => by rw [h0 q (by simpa using hq), norm_zero], ?_⟩
    rw [cosetSum, tsum_eq_single _ h0, term_mk h]
    exact indicator_of_mem (by simp) _
  · have h0 : term P Γ (indicator ((P ⊓ Γ : Subgroup G) : Set G) (1 : G → ℂ)) g = 0 := funext fun q =>
      indicator_of_notMem (fun e => hg ((Γ.mul_mem_cancel_left q.out.2).1 e.2)) _
    rw [CosetConv, cosetSum, h0, indicator_of_notMem hg]
    exact ⟨h, by simpa using summable_zero, tsum_zero⟩

example (Φ : G → ℂ) (g : G) : cosetSum ⊥ Γ Φ g = orbitSum Γ Φ g :=
  cosetSum_eq_tsum (fun γ hγ x => by rw [Subgroup.mem_bot.1 hγ.1, one_mul]) (r := id)
    ⟨fun x y e => by
      obtain ⟨γ, rfl⟩ := mk_eq_iff.1 e
      rw [show (γ : Γ) = 1 from Subtype.ext γ.2, one_mul, id], fun q => ⟨q.out, q.out_eq⟩⟩ g

end Sums

theorem rpow_le_add {x a b t : ℝ} (hx : 0 < x) (h1 : a ≤ t) (h2 : t ≤ b) : x ^ t ≤ x ^ a + x ^ b := by
  rcases le_total x 1 with h | h
  · exact (Real.rpow_le_rpow_of_exponent_ge hx h h1).trans (le_add_of_nonneg_right (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_le h h2).trans (le_add_of_nonneg_left (by positivity))

theorem differentiable_npow {r : ℝ≥0} (hr : 0 < r) : Differentiable ℂ (npow r) := by
  rw [funext (npow_eq_exp hr)]; fun_prop

theorem analyticOnNhd_tsum_npow {ι : Type} {f : ι → ℂ} {a : ι → ℝ≥0} (ha : ∀ i, 0 < a i) {σ : ℝ} {s₀ : ℂ}
    (h : ∀ s : ℂ, σ < s.re → Summable fun i => ‖f i * npow (a i) (s - s₀)‖) :
    AnalyticOnNhd ℂ (fun s => ∑' i, f i * npow (a i) (s - s₀)) (rightOf σ) := fun s hs => by
  obtain ⟨τ, h1, h2⟩ := exists_between (mem_rightOf.1 hs)
  have ho : IsOpen {z : ℂ | τ < z.re ∧ z.re < s.re + 1} :=
    (isOpen_rightOf τ).inter (isOpen_lt Complex.continuous_re continuous_const)
  refine (Complex.differentiableOn_tsum_of_summable_norm ((h τ h1).add (h (s.re + 1 : ℝ) (by simp; linarith)))
    (fun i => ?_) ho fun i z hz => ?_).analyticAt (ho.mem_nhds ⟨h2, lt_add_one _⟩)
  · exact (((differentiable_npow (ha i)).comp (differentiable_id.sub_const s₀)).const_mul _).differentiableOn
  · simp only [norm_mul, norm_npow (ha i), ← mul_add, Complex.sub_re, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_left (rpow_le_add (ha i) (by linarith [hz.1]) (by linarith [hz.2])) (norm_nonneg _)

section Family

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {P Γ K : Subgroup G} {δ : P →* ℝ≥0}
  {χ : P →* Circle} {ρ σ : ℝ} {Φ : ℂ → G → ℂ} (hI : IsIwasawa δ K) (hK : IsCompact (K : Set G))
  (hc : ContinuousOn (fun x : ℂ × G => Φ x.1 x.2) (rightOf σ ×ˢ univ)) (hl : ∀ s ∈ rightOf σ, IndLaw δ χ (s + ρ) (Φ s))
  (hs : ∀ τ, σ < τ → Summable fun q => ((term P Γ (iwAbs δ K) 1 q : ℝ≥0) : ℝ) ^ (τ + ρ))
include hI hK hc hl hs

theorem exists_majorant {S : Set ℂ} {C : Set G} (hS : IsCompact S) (hσ : S ⊆ rightOf σ) (hC : IsCompact C) :
    ∃ u : Cosets P Γ → ℝ, Summable u ∧ ∀ q, ∀ s ∈ S, ∀ g ∈ C, ‖term P Γ (Φ s) g q‖ ≤ u q := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, summable_zero, fun _ _ h => h.elim⟩
  obtain ⟨a, ha, h1⟩ := hS.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨b, hb, h2⟩ := hS.exists_isMaxOn hne Complex.continuous_re.continuousOn
  obtain ⟨M, hM⟩ := (hS.prod (hK.mul hC)).exists_bound_of_continuousOn (hc.mono (prod_mono hσ (subset_univ _)))
  refine ⟨_, ((hs _ (hσ ha)).add (hs _ (hσ hb))).mul_right M, fun q s h g hg => ?_⟩
  obtain ⟨p, k, hk, e⟩ := hI.1 (q.out : Γ)
  have h3 := hM (s, k * g) ⟨h, mul_mem_mul hk hg⟩
  simp only [term, e, mul_one, hI.iwAbs_mul p hk]
  rw [mul_assoc, hl s (hσ h), norm_mul, norm_mul, Circle.norm_coe, one_mul, norm_npow (hom_pos δ p), Complex.add_re,
    Complex.ofReal_re]
  exact mul_le_mul (rpow_le_add (hom_pos δ p) (add_le_add_left (h1 h) _) (add_le_add_left (h2 h) _)) h3 (norm_nonneg _)
    (by positivity)

theorem cosetConv_of_spherical {s : ℂ} (h : σ < s.re) (g : G) : CosetConv P Γ (Φ s) g :=
  let ⟨_, hu, e⟩ := exists_majorant hI hK hc hl hs isCompact_singleton (singleton_subset_iff.2 h) (isCompact_singleton (x := g))
  .of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => e q s rfl g rfl) hu

theorem continuousOn_cosetSum [WeaklyLocallyCompactSpace G] :
    ContinuousOn (fun x : ℂ × G => cosetSum P Γ (Φ x.1) x.2) (rightOf σ ×ˢ univ) := fun x hx => by
  obtain ⟨S, hS, h1, h2⟩ := local_compact_nhds ((isOpen_rightOf σ).mem_nhds hx.1)
  obtain ⟨C, hC, h3⟩ := exists_compact_mem_nhds x.2
  obtain ⟨u, hu, e⟩ := exists_majorant hI hK hc hl hs h2 h1 hC
  refine ((continuousOn_tsum (s := S ×ˢ C) (fun q => ?_) hu fun q y hy => e q _ hy.1 _ hy.2).continuousAt
    (prod_mem_nhds hS h3)).continuousWithinAt
  exact hc.comp (f := fun y : ℂ × G => (y.1, ((q.out : Γ) : G) * y.2)) (by fun_prop) fun y hy => ⟨h1 hy.1, trivial⟩

theorem analyticOnNhd_cosetSum (hd : ∀ g, DifferentiableOn ℂ (Φ · g) (rightOf σ)) (g : G) :
    AnalyticOnNhd ℂ (fun s => cosetSum P Γ (Φ s) g) (rightOf σ) := fun s h => by
  obtain ⟨S, hS, h1, h2⟩ := local_compact_nhds ((isOpen_rightOf σ).mem_nhds h)
  obtain ⟨u, hu, e⟩ := exists_majorant hI hK hc hl hs h2 h1 (isCompact_singleton (x := g))
  exact (Complex.differentiableOn_tsum_of_summable_norm hu (fun q => (hd _).mono (interior_subset.trans h1)) isOpen_interior
    fun q z hz => e q z (interior_subset hz) g rfl).analyticAt (interior_mem_nhds.2 hS)

end Family

end GlobalTheory.Eis

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.NotHasParamOfSubsingleton
section
noncomputable section

namespace GlobalTheory.LFun.Model

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

def constMap (G : Type) : ℂ →ₗ[ℂ] (G → ℂ) := LinearMap.pi fun _ => LinearMap.id

theorem constMap_injective (G : Type) [Group G] : Function.Injective (constMap G) := fun _ _ h => congrFun h 1

section Linear

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)

def rhoGL (i : Fin n) : ℂˣ := npowU w (((n : ℂ) - 1) / 2 - (i : ℕ))

theorem chiDelta_rhoGL (b : GL (Fin n) (w.adicCompletion E)) : chiDelta E w (fun i => (rhoGL w n i : ℂ)) b = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have hq : ((qV E w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast qV_ne_zero w
  change (((qV E w : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2 - (i : ℕ))) ^ _ * _ = 1
  rw [← Complex.cpow_mul_int, ← Complex.cpow_add _ _ hq]
  convert Complex.cpow_zero _ using 2
  ring

theorem hasSatGL_trivial : HasSatGL w (Representation.trivial ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (seg w 1 n) := by
  have e : seg w 1 n = Finset.univ.val.map (rhoGL w n) := by
    rw [seg, Finset.range_val, ← Multiset.coe_range, ← List.map_coe_finRange_eq_range, Multiset.map_coe, List.map_map]
    simp only [one_mul]
    rfl
  rw [e]
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl, one_ne_zero⟩, fun x _ h0 => ?_⟩
  refine IsSatVecGL.of_map (constMap _) (fun _ _ => rfl) (constMap_injective _)
    (isSatVecGL_of_isSpherical (fun b g k _ _ => ?_) fun h => h0 (congrFun h 1))
  rw [chiDelta_rhoGL, one_mul]; rfl

theorem not_hasSatGL_trivial_one :
    ¬ HasSatGL w (Representation.trivial ℂ (GL (Fin 2) (w.adicCompletion E)) ℂ) {1, 1} := fun h => by
  have e := (hasSatGL_trivial w 2).unique h
  have h1 : (1 : ℂˣ) * npowU w ((((2 : ℕ) : ℂ) - 1) / 2 - (0 : ℕ)) ∈ seg w 1 2 :=
    Multiset.mem_map.2 ⟨0, by simp, rfl⟩
  rw [e] at h1
  have h2 : npow w ((((2 : ℕ) : ℂ) - 1) / 2 - (0 : ℕ)) = 1 := by
    have : npowU w ((((2 : ℕ) : ℂ) - 1) / 2 - (0 : ℕ)) = 1 := by simpa using h1
    exact congrArg Units.val this
  have h3 := congrArg norm h2
  rw [norm_npow, norm_one] at h3
  refine (Real.one_lt_rpow (by exact_mod_cast one_lt_absNorm w) ?_).ne' h3
  norm_num

theorem psFunGL_one_apply (a : ℂˣ) (t : GL (Fin 1) (w.adicCompletion E)) (ht : IsUnifV E w (t.1 0 0))
    (φ : psSpaceGL w (fun _ : Fin 1 => a)) :
    HasSatGL w (psFunGL w fun _ : Fin 1 => a) {a} ∧ psFunGL w (fun _ : Fin 1 => a) t φ = (a : ℂ) • φ := by
  refine ⟨hasSatGL_psFunGL _, Subtype.ext (funext fun g => ?_)⟩
  change φ.1 (g * t) = a * φ.1 g
  have hc : g * t = t * g := Units.ext (by ext i j; simp [Matrix.mul_apply, mul_comm, Subsingleton.elim i 0, Subsingleton.elim j 0])
  have ho : ordV E w (t.1 0 0) = 1 := by
    have h0 : Valued.v (t.1 0 0) ≠ 0 := by rw [ht]; exact WithZero.coe_ne_zero
    have h1 : WithZero.unzero h0 = Multiplicative.ofAdd (-1 : ℤ) :=
      WithZero.coe_injective ((WithZero.coe_unzero h0).trans ht)
    rw [ordV, dif_neg h0, h1]; rfl
  rw [hc, φ.2 t g fun i j h => absurd h (by simp [Subsingleton.elim i j])]
  simp [chiDelta, ho]

end Linear

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {σ : L →+* L} {ϖ : L} {q : ℕ}

def rhoU {q : ℕ} (hq : q ≠ 0) (n : ℕ) (i : Fin (n / 2)) : ℂˣ :=
  Units.mk0 (q : ℂ) (by exact_mod_cast hq) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ))

theorem hasSatU_trivial (hU : IsUnramInv ϖ σ q) (hq : q ≠ 0) (n : ℕ) :
    HasSatU ϖ q (Representation.trivial ℂ (GU σ n) ℂ) (rhoU hq n) := by
  refine ⟨(Submodule.ne_bot_iff _).2 ⟨1, GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl, one_ne_zero⟩, fun x _ h0 => ?_⟩
  refine IsSatVecU.of_map hU (constMap _) (fun _ _ => rfl) (constMap_injective _)
    (isSatVecU_of_isSphericalU hU (fun b g k _ _ => ?_) fun h => h0 (congrFun h 1))
  have : chiDeltaU q (fun i => (rhoU hq n i : ℂ)) b = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    split_ifs
    · simp only [rhoU, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [← zpow_mul, ← zpow_add₀ hq']
      convert zpow_zero _ using 2
      ring
    · rfl
  rw [this, one_mul]; rfl

end U

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}

theorem paramOf_trivial_split (hv : IsSplit (E := E) v) {e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E)}
    (he : IsSplitChart σ J L h e) : paramOf σ J L h (Representation.trivial ℂ _ ℂ) = seg w 1 n :=
  HasParam.paramOf_eq_of_isSplit hv (Or.inl ⟨hv, e, he, hasSatGL_trivial w n⟩)

theorem hasParam_trivial_inert (hw : IsInertAt F E v w) {c : w.adicCompletion E →+* w.adicCompletion E}
    {ϖ : w.adicCompletion E} (hU : IsUnramInv ϖ c (qV F v)) {e : GLoc σ J v ≃* GU c n}
    (he : IsInertChart σ J L h c e) :
    HasParam σ J L h (Representation.trivial ℂ _ ℂ) (bcParam n (rhoU (qV_ne_zero v) n)) :=
  Or.inr ⟨hw, c, ϖ, e, _, hU, he, hasSatU_trivial hU _ n, rfl⟩

open scoped TensorProduct in

theorem toCompl_surjective (h : w.under (𝓞 F) = v) : Function.Surjective (toCompl h) := fun x => by
  classical
  obtain ⟨y, hy⟩ := (finAdEquiv F E).surjective ⟨Pi.single w x, by
    filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with u hu
    rw [Pi.single_eq_of_ne (by simpa using hu)]
    exact zero_mem _⟩
  exact ⟨_, (finAdEquiv_apply h y).symm.trans (by rw [hy]; exact Pi.single_eq_same w x)⟩

theorem isConjAt_unique {c c' : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c)
    (hc' : IsConjAt σ h c') : c = c' := RingHom.ext fun x => by
  obtain ⟨y, rfl⟩ := toCompl_surjective h x
  rw [hc, hc']

theorem not_hasParam_id (hw : IsInertAt F E v w) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GLoc (AlgHom.id F E) J v) V) (B : Multiset ℂˣ) :
    ¬ HasParam (AlgHom.id F E) J L h ρ B := by
  rintro (⟨hv, -⟩ | ⟨-, c, ϖ, e, α, hU, he, -⟩)
  · exact not_isSplit_of_isInertAt hw hv
  · have hc : c = RingHom.id _ := isConjAt_unique he.1 fun y => by
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ (AlgHom.id F E) y = y := by simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
      rw [this]; rfl
    obtain ⟨x, -, hx⟩ := hU.2.2.2.2.1
    simp [hc] at hx

theorem not_hasParam_of_subsingleton {V : Type} [AddCommGroup V] [Module ℂ V] [Subsingleton V]
    (ρ : Representation ℂ (GLoc σ J v) V) (B : Multiset ℂˣ) : ¬ HasParam σ J L h ρ B := fun hρ => by
  obtain ⟨x, hx⟩ := hρ.exists_vec
  exact hx.ne_zero (Subsingleton.elim _ _)

theorem not_isFrameAt_bot (a : GL (Fin (n + 1)) (w.adicCompletion E)) : ¬ IsFrameAt w ⊥ a := fun ha => by
  have h1 := (ha (fun _ => 1)).1 fun _ => one_mem _
  have h2 : latAt w (⊥ : Submodule (𝓞 E) (Fin (n + 1) → E)) = ⊥ := by
    rw [latAt, Submodule.span_eq_bot]
    rintro _ ⟨x, hx, rfl⟩
    rw [(Submodule.mem_bot _).1 hx]
    funext i; simp
  rw [h2, Submodule.mem_bot] at h1
  have h3 := congrArg (fun y => (a⁻¹).1.mulVec y) h1
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h3
  exact one_ne_zero (congrFun h3 0)

theorem locL_trivial (s : ℂ) : locL (segFam (fun _ : HeightOneSpectrum (𝓞 E) => 1) n) w s =
    ∏ i ∈ Finset.range n, (1 - npow w (-(s - ((n : ℂ) - 1) / 2 + i)))⁻¹ := by
  rw [locL_segFam]; simp [locL]

end Global

example : ((bcParam 3 (rhoU (q := 3) (by norm_num) 3)).map fun b : ℂˣ => (b : ℂ)) = {9, 9⁻¹, 1} := by
  change ({((rhoU (q := 3) _ 3 0 : ℂˣ) : ℂ), (((rhoU (q := 3) _ 3 0)⁻¹ : ℂˣ) : ℂ), ((1 : ℂˣ) : ℂ)} : Multiset ℂ) = _
  simp [rhoU]; norm_num

end GlobalTheory.LFun.Model

end
end

