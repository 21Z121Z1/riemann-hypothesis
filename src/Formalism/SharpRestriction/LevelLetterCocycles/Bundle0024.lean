import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UniformizerMemDeltaInvariants
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0001
import Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0004

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LengthCokerLe
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

def π0N (T : LocLat G Qp LL O) (i : ZMod n) : Submodule O ↥(NDl W T i) :=
  ((NDl W T i).map (W.π₀ • (LinearMap.id : W.DD T →ₗ[O] W.DD T))).comap (NDl W T i).subtype

def IsRed (T : LocLat G Qp LL O) (i : ZMod n) {r : ℕ} (red : ↥(NDl W T i) →ₗ[O] (Fin r → O)) : Prop :=
  Function.Surjective red ∧ LinearMap.ker red = π0N W T i

def DetRed : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (r : ℕ) (red : ↥(NDl W T₂ i) →ₗ[O] (Fin r → O)), IsRed W T₂ i red

def DetCols : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d, ∀ (r : ℕ) (red : ↥(NDl W T₂ i) →ₗ[O] (Fin r → O)),
      IsRed W T₂ i red →
      ∃ (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → W.DD T₂) (_ : ∀ j, g j ∈ NDl W T₂ i)
        (cols : Fin r → ↥(NDl W T₂ i)),
        (∀ k, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) ∈ QhP W T₂ i (b i + S) ∨
          ∃ j, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) = g j) ∧
        ∃ V : ℕ, V ≤ finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m ∧
          (Matrix.of fun l k => red (cols k) l).det ∣ ((PD.p : ℕ) : O) ^ V

theorem length_coker_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r : ℕ}
    (QQ : Matrix (Fin r) (Fin r) O) (l : O) (hl : l ≠ 0) (V : ℕ) (hd : QQ.det ∣ l ^ V) :
    Module.length O ((Fin r → O) ⧸ LinearMap.range (Matrix.toLin' QQ)) ≤
      (V : ℕ∞) * Module.length O (O ⧸ Ideal.span {l}) := by
  classical
  have hdet0 : QQ.det ≠ 0 := by
    intro h0
    rw [h0, zero_dvd_iff] at hd
    exact pow_ne_zero V hl hd
  have hL := Formalism.KernelCokernelLengths.length_theorems_all_hold.1 O (Fin r → O) (Matrix.toLin' QQ) (by rwa [LinearMap.det_toLin'])
  rw [hL, LinearMap.det_toLin', ← Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.len_pow l hl V]
  have hle : Ideal.span {l ^ V} ≤ Ideal.span {QQ.det} := Ideal.span_singleton_le_span_singleton.2 hd
  first
    | exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    | exact Module.length_le_of_surjective (Ideal.Quotient.factorₐ O hle).toLinearMap
        (Ideal.Quotient.factor_surjective hle)

theorem lemmaDN_core {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}
    (hS : SetCS W d T₁ T₂ F b S η m) (i : ZMod n) {r : ℕ} (red : ↥(NDl W T₂ i) →ₗ[O] (Fin r → O))
    (hsurj : Function.Surjective red) (hker : LinearMap.ker red = π0N W T₂ i) {m' : ℕ} (hm' : m' ≤ m)
    (g : Fin m' → W.DD T₂) (hgN : ∀ j, g j ∈ NDl W T₂ i) (cols : Fin r → ↥(NDl W T₂ i))
    (hcols : ∀ k, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) ∈ QhP W T₂ i (b i + S) ∨
      ∃ j, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) = g j)
    (V : ℕ) (hV : V ≤ finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m)
    (hdet : (Matrix.of fun l k => red (cols k) l).det ∣ ((PD.p : ℕ) : O) ^ V) :
    ∃ s : Finset (W.DD T₂), s.card ≤ m ∧ (↑s : Set (W.DD T₂)) ⊆ NDl W T₂ i ∧
      ∃ L kO : ℕ, Module.length O (↥(NDl W T₂ i) ⧸
          ((NDl W T₂ i).map (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            (PhiPullΔ W T₂ i).map
              ((Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S)) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            Submodule.span O (↑s : Set (W.DD T₂))).comap (NDl W T₂ i).subtype) ≤ (L : ℕ∞) ∧
        lenOl PD (O := O) = kO ∧
        (L : ℝ) ≤ lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S * kO := by
  classical
  obtain ⟨hdom, hdvr, -⟩ := hS.2.2.2.1
  haveI := hdom
  haveI := hdvr
  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  haveI : NeZero PD.p := ⟨by omega⟩
  have hpL : ((PD.p : ℕ) : LL) ≠ 0 := (hζ.neZero').out
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    apply hpL
    have := congrArg (algebraMap O LL) h
    rwa [map_natCast, map_zero] at this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := by
    first
      | exact hϖ.maximalIdeal_eq
      | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hlen1 : Module.length O (O ⧸ Ideal.span {ϖ}) = 1 := by
    rw [← hm]
    first
      | exact Module.length_eq_one_iff.2
          (isSimpleModule_iff_isCoatom.2 (IsLocalRing.maximalIdeal.isMaximal O).out)
      | exact Module.length_eq_one_iff.2
          (isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal O)))
  have hlenp : Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) = (k : ℕ∞) := by
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit,
      Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.len_pow ϖ hϖ.ne_zero k, hlen1, mul_one]
  let s : Finset (W.DD T₂) := Finset.univ.image g
  refine ⟨s, ?_, ?_, V * k, k, ?_, ?_, ?_⟩
  · exact Finset.card_image_le.trans (by simpa using hm')
  · intro x hx
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨j, rfl⟩ := hx
    exact hgN j
  · set X := (((NDl W T₂ i).map (W.π₀ • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            (PhiPullΔ W T₂ i).map
              ((Formalism.MainNotions.LiftingTheory.qp W ^ (b i + S)) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂)) ⊔
            Submodule.span O (↑s : Set (W.DD T₂))).comap (NDl W T₂ i).subtype) with hX
    have hkerX : LinearMap.ker red ≤ X := by
      rw [hker]
      exact Submodule.comap_mono (le_sup_left.trans le_sup_left)
    have hcolX : ∀ k', cols k' ∈ X := by
      intro k'
      rw [hX, Submodule.mem_comap, Submodule.coe_subtype]
      rcases hcols k' with h | ⟨j, hj⟩
      · exact Submodule.mem_sup_left (Submodule.mem_sup_right h)
      · rw [hj]
        exact Submodule.mem_sup_right (Submodule.subset_span (by simp [s]))
    let QQ : Matrix (Fin r) (Fin r) O := Matrix.of fun l k' => red (cols k') l
    let e := LinearMap.quotKerEquivOfSurjective red hsurj
    let f : (Fin r → O) →ₗ[O] (↥(NDl W T₂ i) ⧸ X) := (Submodule.factor hkerX) ∘ₗ e.symm.toLinearMap
    have hf : Function.Surjective f := (Submodule.factor_surjective hkerX).comp e.symm.surjective
    have hrange : LinearMap.range (Matrix.toLin' QQ) ≤ LinearMap.ker f := by
      rintro _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker]
      have hv : Matrix.toLin' QQ v = red (∑ k', v k' • cols k') := by
        ext l'
        simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum, map_smul, QQ, mul_comm]
      have he : e.symm (red (∑ k', v k' • cols k')) =
          Submodule.Quotient.mk (∑ k', v k' • cols k') := by
        rw [LinearEquiv.symm_apply_eq]
        first
          | rfl
          | exact (LinearMap.quotKerEquivOfSurjective_apply_mk red hsurj _).symm
      simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hv, he,
        Submodule.factor_mk, Submodule.Quotient.mk_eq_zero]
      first
        | rw [Submodule.factor_mk, Submodule.Quotient.mk_eq_zero]
        | (change Submodule.Quotient.mk (p := X) (∑ k', v k' • cols k') = 0
           rw [Submodule.Quotient.mk_eq_zero])
      exact Submodule.sum_mem _ fun k' _ => Submodule.smul_mem _ _ (hcolX k')
    let g' := (LinearMap.range (Matrix.toLin' QQ)).liftQ f hrange
    have hg' : Function.Surjective g' := by
      intro z
      obtain ⟨y, rfl⟩ := hf z
      exact ⟨Submodule.Quotient.mk y, rfl⟩
    calc Module.length O (↥(NDl W T₂ i) ⧸ X)
        ≤ Module.length O ((Fin r → O) ⧸ LinearMap.range (Matrix.toLin' QQ)) :=
          Module.length_le_of_surjective g' hg'
      _ ≤ (V : ℕ∞) * Module.length O (O ⧸ Ideal.span {((PD.p : ℕ) : O)}) :=
          length_coker_le QQ _ hp0 V hdet
      _ = ((V * k : ℕ) : ℕ∞) := by rw [hlenp, Nat.cast_mul]
  · unfold Formalism.WeaklyAdmissibleFiltrations.lenOl
    exact hlenp
  · have hp1 : (1 : ℝ) < (PD.p : ℝ) := by exact_mod_cast (by omega : 1 < PD.p)
    have hcD : 0 ≤ Formalism.MainNotions.RamifiedCoefficientChains.cD PD.p (hpar n b S + η) := by
      unfold Formalism.MainNotions.RamifiedCoefficientChains.cD
      have h1 : 0 < (PD.p : ℝ) - 1 := by linarith
      have h2 : 0 ≤ ((hpar n b S + η : ℕ) : ℝ) + 1 := by positivity
      have := div_nonneg h2 h1.le
      linarith
    have hfl := Nat.floor_le hcD
    have hV' : (V : ℝ) ≤ (finrank LL T₂.V : ℝ) * S + 2 * m * Formalism.MainNotions.RamifiedCoefficientChains.cD PD.p (hpar n b S + η) := by
      have h := (Nat.cast_le (α := ℝ)).2 hV
      push_cast at h
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [h, hfl, hm0]
    unfold Formalism.MainNotions.RamifiedCoefficientChains.S9.lenC
    push_cast
    exact mul_le_mul_of_nonneg_right hV' (Nat.cast_nonneg k)

theorem lemmaDN_of_det (h0 : DetRed W) (h1 : DetCols W) :
    LemmaDN W := by
  intro d T₁ T₂ F b S η m hS i hi
  obtain ⟨r, red, hred⟩ := h0 d T₁ T₂ F b S η m hS i hi
  obtain ⟨m', hm', g, hgN, cols, hcols, V, hV, hdet⟩ := h1 d T₁ T₂ F b S η m hS i hi r red hred
  obtain ⟨hsurj, hker⟩ := hred
  exact lemmaDN_core W hS i red hsurj hker hm' g hgN cols hcols V hV hdet

def DetColsE : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (r : ℕ) (red : ↥(NDl W T₂ i) →ₗ[O] (Fin r → O)) (_ : IsRed W T₂ i red)
        (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → W.DD T₂) (_ : ∀ j, g j ∈ NDl W T₂ i)
        (cols : Fin r → ↥(NDl W T₂ i)),
        (∀ k, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) ∈ QhP W T₂ i (b i + S) ∨
          ∃ j, ((cols k : ↥(NDl W T₂ i)) : W.DD T₂) = g j) ∧
        ∃ V : ℕ, V ≤ finrank LL T₂.V * S + 2 * ⌊cD PD.p (hpar n b S + η)⌋₊ * m ∧
          (Matrix.of fun l k => red (cols k) l).det ∣ ((PD.p : ℕ) : O) ^ V

theorem lemmaDN_of_detE (h : DetColsE W) : LemmaDN W := by
  intro d T₁ T₂ F b S η m hS i hi
  obtain ⟨r, red, hred, m', hm', g, hgN, cols, hcols, V, hV, hdet⟩ := h d T₁ T₂ F b S η m hS i hi
  obtain ⟨hsurj, hker⟩ := hred
  exact lemmaDN_core W hS i red hsurj hker hm' g hgN cols hcols V hV hdet

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.WachQuotientCyclicDecomposition
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD
  Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

def DRFree : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      Module.Free O (RR W T₂ i (b i + S)) ∧ Module.Finite O (RR W T₂ i (b i + S))

def DRQEta : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d, ∀ x ∈ NDl W T₂ i,
      Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ PhiPullΔ W T₂ i

def DRLat (hπ : W.π₀ ∈ W.AΔ) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → ↥(NDl W T₂ i)) (k : Fin m' → ℕ),
        (∃ e : ↥(RRp W T₂ hπ i (b i + S) g) ≃ₗ[O] ((j : Fin m') → Aq O (k j)),
          ∀ (x : ↥(RRp W T₂ hπ i (b i + S) g)) (j : Fin m'),
            e ⟨qR W T₂ hπ i (b i + S) x, RRp_stable W T₂ hπ i (b i + S) g x x.2⟩ j =
              Ideal.Quotient.mk _ PowerSeries.X * e x j) ∧
        (∀ (z : RR W T₂ i (b i + S)) (t : ℕ), ((PD.p : ℕ) : O) ^ t • z ∈ RRp W T₂ hπ i (b i + S) g →
          ((PD.p : ℕ) : O) ^ (2 * ⌊cD PD.p (hpar n b S + η)⌋₊) • z ∈ RRp W T₂ hπ i (b i + S) g) ∧
        finrank O (RR W T₂ i (b i + S) ⧸ satL ((PD.p : ℕ) : O) (RRp W T₂ hπ i (b i + S) g)) ≤
          finrank LL T₂.V * S

theorem qR_nil_of (hπ : W.π₀ ∈ W.AΔ) (T : LocLat G Qp LL O) (i : ZMod n) (h η : ℕ)
    (hq : ∀ x ∈ NDl W T i, Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ PhiPullΔ W T i) :
    IsNilpotent (qR W T hπ i h) := by
  have hq1 : ∀ y : ↥(NDl W T i),
      ((qN W T hπ i y : ↥(NDl W T i)) : W.DD T) = Formalism.MainNotions.LiftingTheory.qp W • (y : W.DD T) := fun y => rfl
  have hpow : ∀ (k : ℕ) (y : ↥(NDl W T i)),
      (((qN W T hπ i ^ k) y : ↥(NDl W T i)) : W.DD T) = Formalism.MainNotions.LiftingTheory.qp W ^ k • (y : W.DD T) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [pow_succ', Module.End.mul_apply, hq1, ih, pow_succ', mul_smul]
  refine ⟨h + η, ?_⟩
  unfold qR
  rw [← Submodule.mapQ_pow]
  ext x
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.zero_comp,
    LinearMap.zero_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  show (((qN W T hπ i ^ (h + η)) x : ↥(NDl W T i)) : W.DD T) ∈ QhP W T i h
  rw [hpow, pow_add, mul_smul]
  unfold QhP
  exact Submodule.mem_map.2 ⟨_, hq x x.2, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩

theorem drData_of (hπ : W.π₀ ∈ W.AΔ) (h1 : DRFree W) (h2 : DRQEta W) (h3 : DRLat W hπ) :
    ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
      SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
        DRData W T₂ hπ i (b i + S) m (2 * ⌊cD PD.p (hpar n b S + η)⌋₊) (finrank LL T₂.V * S) := by
  intro d T₁ T₂ F b S η m hS i hi
  obtain ⟨hfree, hfin⟩ := h1 d T₁ T₂ F b S η m hS i hi
  obtain ⟨m', hm', g, k, he, htor, hrk⟩ := h3 d T₁ T₂ F b S η m hS i hi
  unfold DRData
  exact ⟨m', hm', g, k, hfree, hfin,
    qR_nil_of W hπ T₂ i (b i + S) η (h2 d T₁ T₂ F b S η m hS i hi), he, htor, hrk⟩

theorem lemmaDN_of_pieces (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (h1 : DRFree W) (h2 : DRQEta W)
    (h3 : DRLat W (uniformizer_mem_delta_invariants W)) : LemmaDN W :=
  LD.lemmaDN_of W (uniformizer_mem_delta_invariants W) hpu (drData_of W (uniformizer_mem_delta_invariants W) h1 h2 h3)

theorem lemmaDN0_of_piece (h0 : NinQbP W) : Formalism.MainNotions.N.Pv.LocalLengthBound.LemmaDN0 W := by
  intro d T₁ T₂ F b S η m hS hm i hi x hx
  obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.1 (h0 d T₁ T₂ F b S η m hS hm i hi x hx)
  rw [LinearMap.smul_apply, LinearMap.id_apply] at hxy
  have hπ := uniformizer_mem_delta_invariants W
  have hqp := qp_mem W hπ
  obtain ⟨X, hX⟩ : ∃ X : LetA O n, X = Formalism.MainNotions.LiftingTheory.qp W - W.π₀ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : LetA O n,
      c = ∑ k ∈ Finset.range S, X ^ k * Formalism.MainNotions.LiftingTheory.qp W ^ (S - 1 - k) := ⟨_, rfl⟩
  have hXeq : X = ((PD.p : ℕ) : LetA O n) := by
    rw [hX]
    unfold Formalism.MainNotions.LiftingTheory.qp
    ring
  have hgeom : c * (X - Formalism.MainNotions.LiftingTheory.qp W) = X ^ S - Formalism.MainNotions.LiftingTheory.qp W ^ S := by
    rw [hc]
    exact geom_sum₂_mul X (Formalism.MainNotions.LiftingTheory.qp W) S
  have hXmem : X ∈ W.AΔ := by
    rw [hX]
    exact Subalgebra.sub_mem _ hqp hπ
  have hcmem : c ∈ W.AΔ := by
    rw [hc]
    exact Subalgebra.sum_mem _ fun k _ =>
      Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hXmem _) (Subalgebra.pow_mem _ hqp _)
  have hXq : X - Formalism.MainNotions.LiftingTheory.qp W = -W.π₀ := by
    rw [hX]
    ring
  rw [hXq] at hgeom
  have hX' : X ^ S = W.π₀ * (-c) + Formalism.MainNotions.LiftingTheory.qp W ^ S := by
    linear_combination -hgeom
  have hscal : ((PD.p : O) ^ S) • x = (X ^ S) • x := by
    rw [hXeq, ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [hscal, hX', add_smul, mul_smul]
  refine Submodule.add_mem_sup ?_ ?_
  · exact Submodule.mem_map.2 ⟨(-c) • x, ndl_smul W T₂ i (Subalgebra.neg_mem _ hcmem) hx,
      by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩
  · refine Submodule.mem_map.2 ⟨y, hy, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, ← hxy, ← mul_smul, ← pow_add, add_comm]

def lowSum (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) (h η : ℕ) : ℤ :=
  ∑ u ∈ Finset.Icc (-(η : ℤ)) η, multV PD T.ρ τ u * ((h : ℤ) + u)

def DRRank (hπ : W.π₀ ∈ W.AΔ) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d, ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∀ (m' : ℕ) (g : Fin m' → ↥(NDl W T₂ i)) (k : Fin m' → ℕ)
        (_ : ↥(RRp W T₂ hπ i (b i + S) g) ≃ₗ[O] ((j : Fin m') → Aq O (k j))),
        lowSum (PD := PD) T₂ τ (b i + S) η ≤ ∑ j, (k j : ℤ) →
        finrank O (RR W T₂ i (b i + S) ⧸ satL ((PD.p : ℕ) : O) (RRp W T₂ hπ i (b i + S) g)) ≤
          finrank LL T₂.V * S

def WachQuotientCyclicDecomposition (hπ : W.π₀ ∈ W.AΔ) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i ∈ evens n d,
      ∃ (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → ↥(NDl W T₂ i)) (k : Fin m' → ℕ),
        (∃ e : ↥(RRp W T₂ hπ i (b i + S) g) ≃ₗ[O] ((j : Fin m') → Aq O (k j)),
          ∀ (x : ↥(RRp W T₂ hπ i (b i + S) g)) (j : Fin m'),
            e ⟨qR W T₂ hπ i (b i + S) x, RRp_stable W T₂ hπ i (b i + S) g x x.2⟩ j =
              Ideal.Quotient.mk _ PowerSeries.X * e x j) ∧
        (∀ (z : RR W T₂ i (b i + S)) (t : ℕ), ((PD.p : ℕ) : O) ^ t • z ∈ RRp W T₂ hπ i (b i + S) g →
          ((PD.p : ℕ) : O) ^ (2 * ⌊cD PD.p (hpar n b S + η)⌋₊) • z ∈ RRp W T₂ hπ i (b i + S) g) ∧
        ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i → lowSum (PD := PD) T₂ τ (b i + S) η ≤ ∑ j, (k j : ℤ)

theorem drLat_of (hπ : W.π₀ ∈ W.AΔ) (ha : DRRank W hπ) (hb : WachQuotientCyclicDecomposition W hπ) : DRLat W hπ := by
  intro d T₁ T₂ F b S η m hS i hi
  obtain ⟨m', hm', g, k, ⟨e, he⟩, htor, hlow⟩ := hb d T₁ T₂ F b S η m hS i hi
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := by
    unfold Formalism.MainNotions.RamifiedCoefficientChains.SetCS at hS
    exact hS.1

  let eK : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hA.1
  have hov : Formalism.MainNotions.LiftingTheory.Over W ((W.emb i).comp eK.symm.toAlgHom) i := by
    unfold Formalism.MainNotions.LiftingTheory.Over
    ext x
    show W.emb i (eK.symm (IsScalarTower.toAlgHom Qp K₀ K x)) = W.emb i x
    have hx : IsScalarTower.toAlgHom Qp K₀ K x = eK x := rfl
    rw [hx, AlgEquiv.symm_apply_apply]
  exact ⟨m', hm', g, k, ⟨e, he⟩, htor,
    ha d T₁ T₂ F b S η m hS i hi _ hov m' g k e (hlow _ hov)⟩

theorem lemmaDN_of_pieces4 (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (h1 : DRFree W) (h2 : DRQEta W)
    (h3a : DRRank W (uniformizer_mem_delta_invariants W)) (h3b : WachQuotientCyclicDecomposition W (uniformizer_mem_delta_invariants W)) : LemmaDN W :=
  lemmaDN_of_pieces W hpu h1 h2 (drLat_of W (uniformizer_mem_delta_invariants W) h3a h3b)

end Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut
end
end

