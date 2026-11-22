import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem LatticePacking.intersectionNumber_baseChange : LatticePacking.Statement := by
  intro Λ _ _ _ nrm B hB0 htri hhom hsep
  set R := Module.finrank ℤ Λ
  let b := Module.finBasis ℤ Λ
  set m : ℕ := ⌊2 * Real.exp B⌋₊ + 1 with hm
  have hm0 : m ≠ 0 := Nat.succ_ne_zero _
  have : NeZero m := ⟨hm0⟩
  have hmgt : 2 * Real.exp B < m := by
    rw [hm]; push_cast; exact Nat.lt_floor_add_one _
  have hexp1 : 1 ≤ Real.exp B := Real.one_le_exp hB0
  have hmle : (m : ℝ) ≤ 5 * Real.exp B := by
    rw [hm]; push_cast
    have := Nat.floor_le (show 0 ≤ 2 * Real.exp B by positivity)
    linarith
  have hneg : ∀ y, nrm (-y) = nrm y := fun y ↦ by
    have := hhom (-1) y; simpa using this

  let f : Λ → (Fin R → ZMod m) := fun x i ↦ ((b.repr x i : ℤ) : ZMod m)
  have hinj : Set.InjOn f {x | nrm x ≤ 1} := by
    intro x hx y hy hxy
    by_contra hne
    have hdvd : ∀ i, (m : ℤ) ∣ b.repr (x - y) i := fun i ↦ by
      have h := congrFun hxy i
      simp only [f] at h
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
      rw [map_sub, Finsupp.sub_apply]
      have h' := dvd_neg.mpr h
      rwa [neg_sub] at h'
    let z : Λ := ∑ i, (b.repr (x - y) i / m) • b i
    have hz : (m : ℤ) • z = x - y := by
      conv_rhs => rw [← b.sum_repr (x - y)]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_smul, Int.mul_ediv_cancel' (hdvd i)]
    have hz0 : z ≠ 0 := by
      rintro h0
      rw [h0, smul_zero] at hz
      exact hne (sub_eq_zero.mp hz.symm)
    have h1 : nrm (x - y) ≤ 2 := by
      have := htri x (-y)
      rw [hneg, ← sub_eq_add_neg] at this
      have hx' : nrm x ≤ 1 := hx
      have hy' : nrm y ≤ 1 := hy
      linarith
    have h2 : nrm (x - y) = m * nrm z := by
      rw [← hz, hhom]; push_cast; rw [abs_of_nonneg (by positivity)]
    have h3 := hsep z hz0
    have h4 : 2 < (m : ℝ) * Real.exp (-B) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos B)]
      exact hmgt
    have : (m : ℝ) * Real.exp (-B) ≤ m * nrm z :=
      mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg m)
    linarith
  have hfin : {x | nrm x ≤ 1}.Finite :=
    Set.Finite.of_finite_image (Set.toFinite _) hinj
  refine ⟨hfin, ?_⟩
  have hcard : {x | nrm x ≤ 1}.ncard ≤ m ^ R := by
    have := Set.ncard_le_ncard_of_injOn f (t := Set.univ) (fun _ _ ↦ Set.mem_univ _) hinj
      (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_fin] at this
    exact this
  calc (({x | nrm x ≤ 1}.ncard : ℕ) : ℝ) ≤ ((m ^ R : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (m : ℝ) ^ R := by push_cast; rfl
    _ ≤ (Real.exp B * 5) ^ R := pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith) R
    _ = Real.exp (R * (B + Real.log 5)) := by
      rw [Real.exp_nat_mul, Real.exp_add, Real.exp_log (by norm_num)]

theorem LatticePacking.equiv :
    GroundTheory.Heights₂.Heights.LatticePacking.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LatticePacking.Statement := by
  refine ⟨fun _ ↦ LatticePacking.intersectionNumber_baseChange, fun hB ↦ ?_⟩
  intro V _ _ L hL B hB0 hsep
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hL
  have : Module.IsTorsionFree ℤ V := Module.IsTorsionFree.trans_faithfulSMul ℤ ℝ V
  have : Module.Free ℤ L := inferInstance
  obtain ⟨hfin, hcard⟩ := hB L (fun x ↦ ‖(x : V)‖) B hB0 (fun x y ↦ norm_add_le _ _)
    (fun k x ↦ by
      change ‖((k • x : L) : V)‖ = _
      rw [Submodule.coe_smul, norm_zsmul ℝ k (x : V), Real.norm_eq_abs])
    (fun x hx ↦ hsep x x.2 fun h ↦ hx (Subtype.ext h))
  have himg : {x : V | x ∈ L ∧ ‖x‖ ≤ 1} = Subtype.val '' {x : L | ‖(x : V)‖ ≤ 1} := by
    ext x
    constructor
    · rintro ⟨hx, hn⟩; exact ⟨⟨x, hx⟩, hn, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
  rw [himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  exact ⟨hfin.image _, hcard⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsArithVarOfRingKrullDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem ArithVariety.isArithVar_of_ringKrullDim {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {n : ι → ℕ} (P : ArithVariety n) {D : ℕ}
    (hdim : ringKrullDim P.CoordRing = ((D + 1 + Fintype.card ι : ℕ) : WithBot ℕ∞)) :
    Geo.IsArithVar (ι := blockIdx n) P.ideal (D + 1) :=
  ⟨inferInstance, P.isMultiProjPrime, P.isHorizontal, hdim⟩

theorem FibrePoints.proof (hG : GeometricArithmeticNumbers.Statement) : FibrePoints.Statement := by
  intro hDeg ι _ _ _ n P D hdim L hL
  have hP : Geo.IsArithVar (ι := blockIdx n) P.ideal (D + 1) := P.isArithVar_of_ringKrullDim hdim
  have hfin := Geo.divSupp_finite (ι := blockIdx n) P.ideal (C ((2 : ℕ) : ℤ))
  rw [hDeg ι (blockIdx n) P.ideal D L 2 hP hL Nat.prime_two,
    hG ι n P D hdim (fun j ↦ (L j).a) 2]
  have hcast := (Int.castAddHom ℝ).map_finsum_mem
    (fun V ↦ (Geo.multAt (ι := blockIdx n) (P.ideal ⊔ Ideal.span {C ((2 : ℕ) : ℤ)}) V : ℤ) *
      Geo.geoNum (ι := blockIdx n) D V (fun j ↦ (L j).a)) hfin
  simp only [Int.coe_castAddHom, Int.cast_mul, Int.cast_natCast] at hcast
  exact hcast.symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LineDegreeBundleStatement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder

noncomputable section

def LineDegreeBundle.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (F : HermLattice K n),
    F.lattice = (HermLattice.standard K n).lattice →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (E : HermitianBundle.{0} K')
      (φ : E.carrier ≃ₗ[𝓞 K'] (Fin n → 𝓞 K')),
      (∀ (σ' : K' →+* ℂ) (x y : E.carrier),
        (E.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 K'] x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 K'] y) =
          star (fun j ↦ σ' (φ x j : K')) ⬝ᵥ
            (F.metric (σ'.comp (algebraMap K K')) *ᵥ fun j ↦ σ' (φ y j : K'))) →
      ∀ v : Fin n → 𝓞 K', v ≠ 0 →
        HermitianBundle.normDegree E ((satLine v).comap φ.toLinearMap) =
          F.lineDegree K' fun j ↦ (v j : K')

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LinearIndependentOfMemSpan
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

namespace HadamardGramBound

theorem linearIndependent_of_mem_span {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℕ} (v b : Fin r → E) (hv : LinearIndependent ℝ v)
    (hb : ∀ i, v i ∈ Submodule.span ℤ (Set.range b)) : LinearIndependent ℝ b := by
  have hle : Submodule.span ℝ (Set.range v) ≤ Submodule.span ℝ (Set.range b) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.span_le_restrictScalars ℤ ℝ (Set.range b) (hb i)
  have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) = r := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  have hfin : FiniteDimensional ℝ (Submodule.span ℝ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  have h2 : r ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range b)) := by
    have := Submodule.finrank_mono hle
    omega
  have h3 : Module.finrank ℝ (Submodule.span ℝ (Set.range b)) ≤ r := by
    simpa [Set.finrank] using finrank_range_le_card (R := ℝ) b
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank]
  omega

theorem equiv : GroundTheory.Heights₂.Heights.HadamardGramBound.Statement ↔
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.HadamardGramBound.Statement := by
  constructor
  · intro hA E _ _ r v hv hn
    have key : ∀ b : Fin r → E, (∀ i, v i ∈ Submodule.span ℤ (Set.range b)) →
        0 ≤ -Real.log (Real.sqrt (gram b)) := by
      intro b hb
      obtain ⟨_, h1⟩ := hA E r v b hv hn hb
      rw [neg_nonneg]
      have h1' : gram b ≤ 1 := h1
      refine Real.log_nonpos (Real.sqrt_nonneg _) ?_
      simpa using Real.sqrt_le_sqrt h1'
    refine ⟨key v fun i ↦ Submodule.subset_span ⟨i, rfl⟩, fun b _ hb ↦ key b fun i ↦ ?_⟩
    have h := hb i
    rwa [← Submodule.span_int_eq_addSubgroupClosure] at h
  · intro hB V _ _ r v b hv hn hb
    have hbli := linearIndependent_of_mem_span v b hv hb
    have hpos : 0 < gram b := (Matrix.posDef_gram_of_linearIndependent hbli).det_pos
    have h := (hB V r v hv hn).2 b hbli fun i ↦ by
      rw [← Submodule.span_int_eq_addSubgroupClosure]
      exact hb i
    rw [neg_nonneg, Real.log_nonpos_iff (Real.sqrt_nonneg _),
      Real.sqrt_le_left zero_le_one, one_pow] at h
    exact ⟨hpos, h⟩

end HadamardGramBound

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MapCompExtMap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}

theorem map_comp_extMap (D : Heights.AddBlockData P) :
    (MvPolynomial.map (funFieldEquiv P : P.FunField →+* FunField P)).comp D.extMap =
      (mConeMap (AddBlockData.ofObjects D).yPlus).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    refine Eq.trans ?_ (map_intCast (mConeMap (AddBlockData.ofObjects D).yPlus) r).symm
    simp [Heights.AddBlockData.extMap]
  · intro v
    refine Eq.trans ?_ (MvPolynomial.aeval_X (R := ℤ)
      (fun p : Coord D.extSizes ↦ C ((AddBlockData.ofObjects D).yPlus p) * X p.1) v).symm
    rcases v with ⟨_ | k, i⟩
    · simp [Heights.AddBlockData.extMap, Heights.AddBlockData.extVal, AddBlockData.yPlus,
        AddBlockData.ofObjects]
    · simp [Heights.AddBlockData.extMap, Heights.AddBlockData.extVal, AddBlockData.yPlus,
        funFieldEquiv_mkF_X]

theorem ext_ofObjects (D : Heights.AddBlockData P) :
    (AddBlockData.ofObjects D).ext = D.extIdeal := by
  ext f
  show mConeMap (AddBlockData.ofObjects D).yPlus f = 0 ↔ D.extMap f = 0
  have h : MvPolynomial.map (funFieldEquiv P : P.FunField →+* FunField P) (D.extMap f) =
      mConeMap (AddBlockData.ofObjects D).yPlus f :=
    RingHom.congr_fun (map_comp_extMap D) f
  constructor
  · intro h0
    apply MvPolynomial.map_injective _ (funFieldEquiv P).injective
    rw [map_zero]
    exact h.trans h0
  · intro h0
    exact h.symm.trans (by rw [h0, map_zero])

theorem ExtensionDimension.equiv :
    GroundTheory.Heights₂.Heights.ExtensionDimension.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ExtensionDimension.Statement := by
  constructor
  · intro h ι _ _ n P D
    obtain ⟨E, rfl⟩ : ∃ E, AddBlockData.ofObjects E = D :=
      ⟨AddBlockData.toObjects D, AddBlockData.ofObjects_toObjects D⟩
    rw [ext_ofObjects]
    exact h ι n P E
  · intro h ι _ _ n P D
    have := h ι n P (AddBlockData.ofObjects D)
    rw [ext_ofObjects] at this
    exact this

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MemConePointsProjIdealIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [Fintype ι] in

theorem mem_conePoints_projIdeal_iff (P : ArithVariety n) (k₀ : ι)
    (w : Cone (fun _ : Unit ↦ n k₀) ℂ) :
    w ∈ GroundTheory.Heights₂.Heights.conePoints (P.projIdeal k₀) ℂ ↔ w () ∈ oneBlockPoints P k₀ := by
  have hw0 : BlockNonzero w ↔ w () ≠ 0 := ⟨fun h ↦ h (), fun h u ↦ by cases u; exact h⟩
  let σ : Fin (n k₀ + 1) → Coord (fun _ : Unit ↦ n k₀) := fun i ↦ ⟨(), i⟩
  let τ : Coord (fun _ : Unit ↦ n k₀) → Fin (n k₀ + 1) := fun v ↦ v.2
  have hev : ∀ f, eval₂ (Int.castRingHom ℂ) (w ()) f = evalCone w (rename σ f) := by
    intro f
    rw [evalCone, eval₂_rename]
    rfl
  have hev' : ∀ f, evalCone w f = eval₂ (Int.castRingHom ℂ) (w ()) (rename τ f) := by
    intro f
    rw [evalCone, eval₂_rename]
    congr 1
  simp only [GroundTheory.Heights₂.Heights.conePoints, oneBlockPoints, Set.mem_ofPred_eq]
  rw [hw0]
  refine and_congr_right fun _ ↦ ⟨fun h f hf ↦ ?_, fun h f hf ↦ ?_⟩
  · rw [hev]
    apply h
    rw [ArithVariety.projIdeal, Ideal.mem_comap, rename_rename]
    exact Ideal.mem_comap.1 hf
  · rw [hev']
    apply h
    rw [oneBlockIdeal, Ideal.mem_comap, rename_rename]
    exact Ideal.mem_comap.1 hf

theorem BlockSurjectivity.equiv :
    GroundTheory.Heights₂.Heights.BlockSurjectivity.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.BlockSurjectivity.Statement := by
  constructor
  · intro h ι _ _ n P k₀
    have hA := h ι n P k₀
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : projBlock k₀ z ∈ GroundTheory.Heights₂.Heights.conePoints (P.projIdeal k₀) ℂ :=
        hA ▸ ⟨z, hz, rfl⟩
      exact (mem_conePoints_projIdeal_iff P k₀ _).1 hz'
    · intro hv
      have hv' : (fun _ : Unit ↦ v) ∈ GroundTheory.Heights₂.Heights.conePoints (P.projIdeal k₀) ℂ :=
        (mem_conePoints_projIdeal_iff P k₀ _).2 hv
      rw [← hA] at hv'
      obtain ⟨z, hz, hzv⟩ := hv'
      exact ⟨z, hz, congrFun hzv ()⟩
  · intro h ι _ _ n P k₀
    have hB := h ι n P k₀
    ext w
    rw [mem_conePoints_projIdeal_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hB ▸ ⟨z, hz, rfl⟩
    · intro hw
      rw [← hB] at hw
      obtain ⟨z, hz, hzw⟩ := hw
      exact ⟨z, hz, funext fun u ↦ by cases u; exact hzw⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MemPointsOfGeneratorsVanish
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open scoped ContDiff

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

theorem contDiff_evalCone (f : MvPolynomial (Coord n) ℤ) :
    ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ evalCone z f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa only [evalCone, eval₂_C] using contDiff_const
  | add p q hp hq => simpa only [evalCone, eval₂_add] using hp.add hq
  | mul_X p v hp =>
    simpa only [evalCone, eval₂_mul, eval₂_X] using
      hp.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id v.1) v.2)

theorem ContDiffOn.zpow_of_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {s : Set E} (hf : ContDiffOn ℝ ∞ f s) (h0 : ∀ x ∈ s, f x ≠ 0) (m : ℤ) :
    ContDiffOn ℝ ∞ (fun x ↦ f x ^ m) s := by
  cases m with
  | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv fun x hx ↦ pow_ne_zero _ (h0 x hx)

omit [Fintype ι] in

theorem ArithVariety.mem_points_of_generators_vanish (P : ArithVariety n) {r : ℕ}
    {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ} (hG : P.IsHomogGenerators G δ)
    {z : Cone n ℂ} (hz : BlockNonzero z) (h0 : ∀ i, evalCone z (G i) = 0) : z ∈ P.points ℂ := by
  refine ⟨hz, fun f hf ↦ ?_⟩
  rw [← hG.span_eq] at hf
  have hle : Ideal.span (Set.range G) ≤
      RingHom.ker (eval₂Hom (Int.castRingHom ℂ) fun v : Coord n ↦ z v.1 v.2) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact h0 i
  exact hle hf

theorem ChartDenominatorAlt.proof (hV : ChartVanishing.Statement) : ChartDenominatorAlt.Statement := by
  intro ι _ _ n P D d g hg r G δ hG
  refine ⟨fun z hz ↦ ?_, ?_⟩
  · have hB : 0 ≤ ∑ i, ‖evalCone z (G i)‖ ^ 2 *
        ∏ k, l2Norm (z k) ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) :=
      Finset.sum_nonneg fun i _ ↦ mul_nonneg (sq_nonneg _)
        (Finset.prod_nonneg fun k _ ↦ zpow_nonneg (Real.sqrt_nonneg _) _)
    have hA : 0 ≤ ∑ c, ∑ j, ‖evalCone z (g c j)‖ ^ 2 :=
      Finset.sum_nonneg fun c _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
    unfold AddBlockData.den
    by_cases hGz : ∃ i, evalCone z (G i) ≠ 0
    · obtain ⟨i, hi⟩ := hGz
      refine add_pos_of_nonneg_of_pos hA (Finset.sum_pos' (fun i _ ↦ ?_) ⟨i, Finset.mem_univ i, ?_⟩)
      · exact mul_nonneg (sq_nonneg _)
          (Finset.prod_nonneg fun k _ ↦ zpow_nonneg (Real.sqrt_nonneg _) _)
      · exact mul_pos (pow_pos (norm_pos_iff.mpr hi) 2)
          (Finset.prod_pos fun k _ ↦ zpow_pos (vectorL2Norm_pos (hz k)) _)
    · push Not at hGz
      have hzP := P.mem_points_of_generators_vanish hG hz hGz
      have hc : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz k)
      choose c hc using hc
      have hm : evalCone z (chartMonomial c d) ≠ 0 := by
        rw [evalCone_chartMonomial]
        exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
      have hj : ∃ j, evalCone z (g c j) ≠ 0 := by
        by_contra hne
        push Not at hne
        exact hm ((hV ι n P D d g hg z hzP c).mp hne)
      obtain ⟨j, hj⟩ := hj
      refine add_pos_of_pos_of_nonneg (Finset.sum_pos' (fun c _ ↦ ?_) ⟨c, Finset.mem_univ c, ?_⟩) hB
      · exact Finset.sum_nonneg fun j _ ↦ sq_nonneg _
      · exact Finset.sum_pos' (fun j _ ↦ sq_nonneg _)
          ⟨j, Finset.mem_univ j, pow_pos (norm_pos_iff.mpr hj) 2⟩
  · have hsq : ∀ f : MvPolynomial (Coord n) ℤ,
        ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ ‖evalCone z f‖ ^ 2) :=
      fun f ↦ (contDiff_norm_sq ℝ).comp (contDiff_evalCone f)
    unfold AddBlockData.den
    refine ContDiffOn.add ?_ ?_
    · exact (ContDiff.sum fun c _ ↦ ContDiff.sum fun j _ ↦ hsq (g c j)).contDiffOn
    · refine ContDiffOn.sum fun i _ ↦ (hsq (G i)).contDiffOn.mul ?_
      refine contDiffOn_prod fun k _ ↦ ?_
      exact ContDiffOn.zpow_of_ne_zero (contDiffOn_l2Norm_block k)
        (fun z hz ↦ (vectorL2Norm_pos (hz k)).ne') _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusArithVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem YPlusArithVar.proof (hPrime : ChartPrimality.Statement) (hDim : ExtensionDimension.Statement) :
    YPlusArithVar.Statement := by
  intro ι _ _ n P D Ω _ y x' E hR hA
  obtain ⟨Q, hQ⟩ := hPrime ι n P D
  obtain ⟨_, _, _, hd⟩ := hA
  rw [← hR.ext_eq]
  refine ⟨inferInstance, hQ ▸ Q.isMultiProjPrime, hQ ▸ Q.isHorizontal, ?_⟩
  rw [← hR.ideal_eq] at hd
  change ringKrullDim (MvPolynomial (Coord D.extSizes) ℤ ⧸ D.extIdeal) = _
  rw [hDim ι n P D]
  change ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) + 1 = _
  change ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) = _ at hd
  rw [hd, Fintype.card_option]
  norm_cast

end GroundTheory.Heights₂.Heights
end

