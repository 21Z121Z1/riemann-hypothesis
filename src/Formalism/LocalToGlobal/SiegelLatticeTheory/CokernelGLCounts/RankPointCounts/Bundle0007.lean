import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StrongApproximation.Bundle0001

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolOneEqOne
section
noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

def lawX {ι P : Type} (BX : P → (P → ℂ) → (P → ℂ) → ℂ) (γ x : ι → P → ℂ) : ι → P → ℂ :=
  fun v p => γ v p + x v p + BX p (γ v) (x v)

theorem pi_measure_eq_prod_absNorm_mul_sqrt_discr (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (P : Type) [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBm : ∀ p, Measurable (fun z : (P → ℂ) × (P → ℂ) => BX p z.1 z.2))
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (hB0 : ∀ p (x : P → ℂ), BX p x 0 = 0)
    (c : ℝ) (hc : 0 ≤ c) (I : P → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : P → AddSubgroup K)
    (hΛ : ∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : P → ℕ)
    (hk : ∀ p, (Λ p).relIndex
      (((I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k p)
    (hk0 : ∀ p, k p ≠ 0) (s : P → ℂ) (hs : ∀ p, s p ≠ 0)
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (hinv : ∀ γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) → ∃ γ' : ι → P → ℂ,
      (∀ p, (fun v => γ' v p) - τ p γ' ∈ (Λ p).map (embS φ (s p))) ∧
        ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x)
    (Kset : Set (ι → P → ℂ)) (hK : MeasurableSet Kset)
    (hKd : ∀ x, ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) ∧
      lawX BX γ x ∈ Kset) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : P => ENNReal.ofReal c • (volume : Measure ℂ)) Kset =
      ∏ p, ENNReal.ofReal (c ^ Fintype.card ι * k p *
        (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
        2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s p‖ ^ (2 * Fintype.card ι)) := by
  have hsf : SigmaFinite (ENNReal.ofReal c • (volume : Measure ℂ)) :=
    (inferInstance : SigmaFinite (c.toNNReal • (volume : Measure ℂ)))
  let sw : (ι → P → ℂ) → (P → ι → ℂ) := fun x p v => x v p
  let usw : (P → ι → ℂ) → (ι → P → ℂ) := fun y v p => y p v
  have h1 : ∀ x, usw (sw x) = x := fun x => rfl
  have h2 : ∀ y, sw (usw y) = y := fun y => rfl
  have hsw : MeasurePreserving sw _ _ := swap_mp (ι := ι) (P := P) (ENNReal.ofReal c • (volume : Measure ℂ))
  have husw : Measurable usw :=
    measurable_pi_lambda _ fun v => measurable_pi_lambda _ fun p =>
      (measurable_pi_apply v).comp (measurable_pi_apply p)
  let B : ∀ _ : P, (P → ι → ℂ) → (P → ι → ℂ) → (ι → ℂ) := fun p y y' v => BX p (fun q => y q v) (fun q => y' q v)
  let τT : ∀ _ : P, (P → ι → ℂ) → (ι → ℂ) := fun p y => τ p (usw y)
  have hlaw : ∀ γ x, mlaw B (sw γ) (sw x) = sw (lawX BX γ x) := fun γ x => rfl
  have hmemT : ∀ γ : ι → P → ℂ, (∀ p, sw γ p - τT p (sw γ) ∈ (Λ p).map (embS φ (s p))) ↔
      (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) := fun γ => Iff.rfl
  have hpre : Kset = sw ⁻¹' (usw ⁻¹' Kset) := by ext x; simp [h1]
  have hKT : MeasurableSet (usw ⁻¹' Kset) := husw hK
  rw [hpre, hsw.measure_preimage hKT.nullMeasurableSet]
  refine covol_oneT K ι φ σ hφ P h B ?_ ?_ ?_ c hc I Λ hΛ k hk hk0 s hs τT ?_ ?_ (usw ⁻¹' Kset) hKT ?_
  · intro p
    refine measurable_pi_lambda _ fun v => ?_
    have hf : Measurable (fun z : (P → ι → ℂ) × (P → ι → ℂ) => ((fun q => z.1 q v), (fun q => z.2 q v))) :=
      (measurable_pi_lambda _ fun q => (measurable_pi_apply v).comp ((measurable_pi_apply q).comp measurable_fst)).prodMk
        (measurable_pi_lambda _ fun q => (measurable_pi_apply v).comp ((measurable_pi_apply q).comp measurable_snd))
    exact (hBm p).comp hf
  · intro p x x' y y' hxy
    funext v
    exact hBd p _ _ _ _ fun q hq => ⟨congrFun (hxy q hq).1 v, congrFun (hxy q hq).2 v⟩
  · intro p x
    funext v
    exact hB0 p _
  · intro p x x' hxx
    exact hτ p _ _ fun q hq v => congrFun (hxx q hq) v
  · intro γT hγT
    obtain ⟨γ', hγ', hinv'⟩ := hinv (usw γT) ((hmemT (usw γT)).1 (by rw [h2]; exact hγT))
    refine ⟨sw γ', (hmemT γ').2 hγ', fun g => ⟨?_, ?_⟩⟩
    · have := (hinv' (usw g)).1
      calc mlaw B (sw γ') (mlaw B γT g) = mlaw B (sw γ') (mlaw B (sw (usw γT)) (sw (usw g))) := by rw [h2, h2]
        _ = sw (lawX BX γ' (lawX BX (usw γT) (usw g))) := by rw [hlaw, hlaw]
        _ = g := by rw [this, h2]
    · have := (hinv' (usw g)).2
      calc mlaw B γT (mlaw B (sw γ') g) = mlaw B (sw (usw γT)) (mlaw B (sw γ') (sw (usw g))) := by rw [h2, h2]
        _ = sw (lawX BX (usw γT) (lawX BX γ' (usw g))) := by rw [hlaw, hlaw]
        _ = g := by rw [this, h2]
  · intro g
    obtain ⟨γ, ⟨hγΓ, hγK⟩, hγu⟩ := hKd (usw g)
    refine ⟨sw γ, ⟨(hmemT γ).2 hγΓ, ?_⟩, ?_⟩
    · show usw (mlaw B (sw γ) g) ∈ Kset
      rw [show g = sw (usw g) from (h2 g).symm, hlaw, h1]; exact hγK
    · rintro γT ⟨hΓT, hKT'⟩
      have e := hγu (usw γT) ⟨(hmemT (usw γT)).1 (by rw [h2]; exact hΓT), by
        have : usw (mlaw B γT g) ∈ Kset := hKT'
        rw [show γT = sw (usw γT) from (h2 γT).symm, show g = sw (usw g) from (h2 g).symm, hlaw, h1] at this
        exact this⟩
      rw [← e, h2]

theorem covol_one_eq_one (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (P : Type) [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBm : ∀ p, Measurable (fun z : (P → ℂ) × (P → ℂ) => BX p z.1 z.2))
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (hB0 : ∀ p (x : P → ℂ), BX p x 0 = 0)
    (c : ℝ) (hc : 0 ≤ c) (I : P → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : P → AddSubgroup K)
    (hΛ : ∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : P → ℕ)
    (hk : ∀ p, (Λ p).relIndex
      (((I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k p)
    (hk0 : ∀ p, k p ≠ 0) (s : P → ℂ) (hs : ∀ p, s p ≠ 0)
    (hconst : ∏ p, (c ^ Fintype.card ι * k p *
        (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
        2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s p‖ ^ (2 * Fintype.card ι)) = 1)
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (hinv : ∀ γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) → ∃ γ' : ι → P → ℂ,
      (∀ p, (fun v => γ' v p) - τ p γ' ∈ (Λ p).map (embS φ (s p))) ∧
        ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x)
    (Kset : Set (ι → P → ℂ)) (hK : MeasurableSet Kset)
    (hKd : ∀ x, ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) ∧
      lawX BX γ x ∈ Kset) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : P => ENNReal.ofReal c • (volume : Measure ℂ)) Kset = 1 := by
  rw [pi_measure_eq_prod_absNorm_mul_sqrt_discr K ι φ σ hφ P h BX hBm hBd hB0 c hc I Λ hΛ k hk hk0 s hs τ hτ hinv Kset hK hKd,
    ← ENNReal.ofReal_prod_of_nonneg, hconst, ENNReal.ofReal_one]
  intro p _
  have hN := FractionalIdeal.absNorm_nonneg (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  have hN' : (0 : ℝ) ≤ (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) := by
    exact_mod_cast hN
  positivity

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAd
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Ball

variable {K : Type*} [Field K] [ValuativeRel K]

def InBall (c x : K) : Prop := ValuativeRel.valuation K x ≤ ValuativeRel.valuation K c

def ballS (c : K) : AddSubgroup K where
  carrier := {x | InBall c x}
  zero_mem' := by simp [InBall]
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_setOf_eq, InBall] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  neg_mem' := fun {x} hx => by
    simp only [Set.mem_setOf_eq, InBall] at hx ⊢
    simpa [Valuation.map_neg] using hx

theorem mem_ballS {c x : K} : x ∈ ballS c ↔ valuation K x ≤ valuation K c := by
  show InBall c x ↔ _
  rfl

theorem ballS_isOpen [TopologicalSpace K] [IsValuativeTopology K] {c : K} (hc : c ≠ 0) :
    IsOpen (ballS c : Set K) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hv : valuation K c ≠ 0 := by simpa using hc
  refine IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ hv, fun y hy => ?_⟩
  have hy' : valuation K (y - x) < valuation K c := by simpa using hy
  rw [SetLike.mem_coe, mem_ballS]
  have e : y = (y - x) + x := by ring
  rw [e]
  exact Valuation.map_add_le _ hy'.le hx

theorem ballS_mul {c x : K} (hc : c ≠ 0) (hx : x ∈ ballS c) : ∃ β ∈ 𝒪[K], x = c * β := by
  refine ⟨x / c, ?_, by field_simp⟩
  rw [Valuation.mem_integer_iff, map_div₀]
  exact div_le_one_of_le₀ (mem_ballS.1 hx) zero_le'

end Ball

section Ad

open Formalism.MainNotions.S.Loc PI.StrongApproxE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p)

theorem sa_lat (T : Finset (HeightOneSpectrum (𝓞 F))) (x : ∀ p, (L p).Ep) (c : ∀ p, (L p).Fp)
    (hc : ∀ p ∈ T, c p ≠ 0) :
    ∃ t : E, (∀ p ∈ T, ∃ y ∈ (L p).O, (L p).ιE t - x p = algebraMap (L p).Fp (L p).Ep (c p) * y) ∧
      ∀ p, p ∉ T → (L p).ιE t ∈ (L p).O := by
  classical
  obtain ⟨n, b, hbint, hbspan⟩ := intSpan' F E
  choose α hα using fun p => local_span_holds F E sig p (L p) n b hbspan (x p)
  set c' : ∀ p, (L p).Fp := fun p => if p ∈ T then c p else 1 with hc'
  have hc'0 : ∀ p, c' p ≠ 0 := by
    intro p
    by_cases hp : p ∈ T
    · simp only [hc', if_pos hp]; exact hc p hp
    · simp only [hc', if_neg hp]; exact one_ne_zero
  have hVo : ∀ p, IsOpen (ballS (c' p) : Set (L p).Fp) := by
    intro p
    have := (L p).lf
    exact ballS_isOpen (hc'0 p)
  choose a ha using fun p (i : Fin n) => local_dense_embedding F E sig p (L p) (ballS (c' p)) (hVo p) (α p i)
  choose d hd0 hd using fun p => local_neighbourhood_small F E sig p (L p) (ballS (c' p)) (hVo p)
  choose t ht1 ht2 using fun i : Fin n => strong_approximation_finite_places F T (fun p => a p i) d (fun p _ => hd0 p)
  refine ⟨∑ i, t i • b i, fun p hp => ?_, fun p hp => ?_⟩
  · have hιE : (L p).ιE (∑ i, t i • b i) = ∑ i, (L p).ιF (t i) • (L p).ιE (b i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => existsLatticeAutomorphismApprox F E sig p (L p) (t i) (b i)
    have h1 : (L p).ιE (∑ i, t i • b i) - x p = ∑ i, ((L p).ιF (t i) - α p i) • (L p).ιE (b i) := by
      rw [hιE]
      conv_lhs => rw [hα p]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    have hmem : ∀ i, (L p).ιF (t i) - α p i ∈ ballS (c' p) := by
      intro i
      have h2 : (L p).ιF (t i) - α p i = (L p).ιF (t i - a p i) + ((L p).ιF (a p i) - α p i) := by
        rw [map_sub]; ring
      rw [h2]
      exact (ballS (c' p)).add_mem (hd p _ (ht1 i p hp)) (ha p i)
    have hcp : c' p = c p := by simp only [hc', if_pos hp]
    choose β hβO hβ using fun i => ballS_mul (hc'0 p) (hmem i)
    have hbO : ∀ i, (L p).ιE (b i) ∈ (L p).O := by
      intro i
      have := local_integral_of_substitution F E sig p (L p) 1 (b i) (by simp) (hbint i)
      simpa using this
    have hβE : ∀ i, algebraMap (L p).Fp (L p).Ep (β i) * (L p).ιE (b i) ∈ (L p).O := by
      intro i
      have := (L p).lf
      have hA : IsIntegral 𝒪[(L p).Fp] (algebraMap (L p).Fp (L p).Ep (β i)) :=
        isIntegral_algebraMap (R := 𝒪[(L p).Fp]) (A := (L p).Ep) (x := ⟨β i, hβO i⟩)
      exact (L p).O.mul_mem (((L p).O_def _).mpr hA) (hbO i)
    refine ⟨∑ i, algebraMap (L p).Fp (L p).Ep (β i) * (L p).ιE (b i), (L p).O.sum_mem fun i _ => hβE i, ?_⟩
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hβ i, ← hcp, Algebra.smul_def, map_mul, mul_assoc]
  · rw [map_sum]
    refine (L p).O.sum_mem fun i _ => ?_
    rw [existsLatticeAutomorphismApprox F E sig p (L p) (t i) (b i)]
    exact local_integral_of_substitution F E sig p (L p) (t i) (b i) (ht2 i p hp) (hbint i)

end Ad

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxGen
section
noncomputable section

open IsDedekindDomain

namespace Formalism.L2.SG.Pf.ProdEApprox

section DedekindLFunctions

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {n : ℕ}

end DedekindLFunctions

section Ent

variable {A : Type*} [CommRing A] {n : ℕ}

def EntIn (J : AddSubgroup A) (X : Matrix (Fin n) (Fin n) A) : Prop := ∀ i j, X i j ∈ J

theorem entIn_mul {J1 J2 J3 : AddSubgroup A} (h : ∀ x ∈ J1, ∀ y ∈ J2, x * y ∈ J3)
    {X Y : Matrix (Fin n) (Fin n) A} (hX : EntIn J1 X) (hY : EntIn J2 Y) : EntIn J3 (X * Y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => h _ (hX i k) _ (hY k j)

theorem entIn_add {J : AddSubgroup A} {X Y : Matrix (Fin n) (Fin n) A} (hX : EntIn J X) (hY : EntIn J Y) :
    EntIn J (X + Y) :=
  fun i j => J.add_mem (hX i j) (hY i j)

theorem entIn_neg {J : AddSubgroup A} {X : Matrix (Fin n) (Fin n) A} (hX : EntIn J X) : EntIn J (-X) :=
  fun i j => J.neg_mem (hX i j)

theorem pow_apply_eq_zero (f : Fin n → ℕ) {X : Matrix (Fin n) (Fin n) A} (hX : ∀ i j, f i ≤ f j → X i j = 0)
    (m : ℕ) : ∀ i j, f i < f j + m → (X ^ m) i j = 0 := by
  induction m with
  | zero =>
    intro i j h
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl
    omega
  | succ m ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : f i < f k + m
    · rw [ih i k hk, zero_mul]
    · rw [hX k j (by omega), mul_zero]

theorem pow_eq_zero_of (f : Fin n → ℕ) (hf : ∀ i, f i < n) {X : Matrix (Fin n) (Fin n) A}
    (hX : ∀ i j, f i ≤ f j → X i j = 0) : X ^ n = 0 := by
  ext i j
  have := hf i
  exact pow_apply_eq_zero f hX n i j (by omega)

theorem entIn_negpow {J : AddSubgroup A} (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J) {X : Matrix (Fin n) (Fin n) A}
    (hX : EntIn J X) (m : ℕ) : EntIn J ((-X) ^ (m + 1)) := by
  induction m with
  | zero => rw [zero_add, pow_one]; exact entIn_neg hX
  | succ m ih => rw [pow_succ]; exact entIn_mul hJ ih (entIn_neg hX)

theorem inv_sub_one (f : Fin n → ℕ) (hf : ∀ i, f i < n) {J : AddSubgroup A} (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J)
    (x : GL (Fin n) A) (hlow : ∀ i j, f i ≤ f j → ((x : Matrix (Fin n) (Fin n) A) - 1) i j = 0)
    (hx : EntIn J ((x : Matrix (Fin n) (Fin n) A) - 1)) :
    EntIn J (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1) ∧
      ∀ i j, f i ≤ f j → (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1) i j = 0 := by
  set X := (x : Matrix (Fin n) (Fin n) A) - 1 with hXdef
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hnX : ∀ i j, f i ≤ f j → (-X) i j = 0 := fun i j h => by rw [Matrix.neg_apply, hlow i j h, neg_zero]
  have hpow : (-X) ^ n = 0 := pow_eq_zero_of f hf hnX

  have hxS : (x : Matrix (Fin n) (Fin n) A) * ∑ i ∈ Finset.range n, (-X) ^ i = 1 := by
    have e : (x : Matrix (Fin n) (Fin n) A) = 1 - (-X) := by rw [sub_neg_eq_add, hXdef, add_sub_cancel]
    rw [e, mul_neg_geom_sum, hpow, sub_zero]
  have hinv : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = ∑ i ∈ Finset.range n, (-X) ^ i := by
    calc ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
        = ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *
          ((x : Matrix (Fin n) (Fin n) A) * ∑ i ∈ Finset.range n, (-X) ^ i) := by rw [hxS, mul_one]
      _ = ∑ i ∈ Finset.range n, (-X) ^ i := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hY : ((x⁻¹ : GL (Fin (k + 1)) A) : Matrix (Fin (k + 1)) (Fin (k + 1)) A) - 1 =
      ∑ i ∈ Finset.range k, (-X) ^ (i + 1) := by
    rw [hinv, Finset.sum_range_succ', pow_zero, add_sub_cancel_right]
  rw [hY]
  refine ⟨fun i j => ?_, fun i j h => ?_⟩
  · rw [Matrix.sum_apply]
    exact sum_mem fun m _ => entIn_negpow hJ hx m i j
  · rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun m _ => pow_apply_eq_zero f hnX (m + 1) i j (by omega)

end Ent

end Formalism.L2.SG.Pf.ProdEApprox
end
end

