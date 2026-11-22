import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPoints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralEqFiniteSumOverNumberField

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsN1LocalHomMemOpen
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.VolBridge.NormOneIdeleAutomorphisms

variable {E : Type} [Field E] {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}

def autOf (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) : (Fin (M + c') → E) ≃ₗ[E] (Fin (M + c') → E) :=
  LinearEquiv.ofLinear (Matrix.toLin' (g.val.submatrix e.symm e.symm)) (Matrix.toLin' ((g⁻¹).val.submatrix e.symm e.symm))
    (by rw [← Matrix.toLin'_mul, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv, Matrix.toLin'_one])

theorem autOf_apply (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) (v : Fin (M + c') → E) :
    autOf e g v = (g.val.submatrix e.symm e.symm).mulVec v := rfl

theorem autOf_inv_apply (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) (v : Fin (M + c') → E) :
    (autOf e g)⁻¹ v = ((g⁻¹).val.submatrix e.symm e.symm).mulVec v := rfl

theorem lev_symm (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)
    (l : Fin (M + c')) : lev (n := A) (c := c) 1 (e.symm l) = if l.val < M then 1 else l.val - M + 1 := by
  rcases hm : e.symm l with a | i
  · have h1 : l = e (Sum.inl a) := by rw [← hm]; simp
    have := eX_lt e hcc he a
    rw [← h1] at this
    simp [lev, this]
  · have h1 : l = e (Sum.inr i) := by rw [← hm]; simp
    have := he i
    rw [← h1] at this
    simp [lev, this]

theorem mulVec_fix (e : A ⊕ Fin c ≃ Fin (M + c')) (m : Matrix (A ⊕ Fin c) (A ⊕ Fin c) E)
    (hm : ∀ r s, lev 1 s ≤ lev 1 r → m r s = (1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) E) r s) (v : Fin (M + c') → E)
    (l : Fin (M + c')) (hv : ∀ j, v j ≠ 0 → lev (n := A) (c := c) 1 (e.symm j) ≤ lev 1 (e.symm l)) :
    (m.submatrix e.symm e.symm).mulVec v l = v l := by
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  rw [Finset.sum_eq_single l]
  · rw [hm _ _ le_rfl, Matrix.one_apply_eq, one_mul]
  · intro j _ hj
    by_cases h0 : v j = 0
    · rw [h0, mul_zero]
    · rw [hm _ _ (hv j h0), Matrix.one_apply_ne (fun h => hj (e.symm.injective h).symm), zero_mul]
  · simp

theorem mem_normOneIdeles (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)
    (g : GL (A ⊕ Fin c) E) (hg : g ∈ N E A c 1) : autOf e g ∈ Loc.N1 E M c' := by
  have hL := lev_symm e hcc he
  have key : ∀ g : GL (A ⊕ Fin c) E, g ∈ N E A c 1 → ∀ (v : Fin (M + c') → E) (l : Fin (M + c')),
      (∀ j, v j ≠ 0 → lev (n := A) (c := c) 1 (e.symm j) ≤ lev 1 (e.symm l)) →
      (g.val.submatrix e.symm e.symm).mulVec v l = v l := fun g hg v l hv =>
    mulVec_fix e g.val (Model.mem_N_iff.1 hg) v l hv
  have hR : ∀ g : GL (A ⊕ Fin c) E, g ∈ N E A c 1 → ∀ r : (Fin (M + c') → E) ≃ₗ[E] (Fin (M + c') → E),
      (∀ v, r v = (g.val.submatrix e.symm e.symm).mulVec v) → Loc.R1cond E M c' r := by
    intro g hg r hr
    refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
    · intro l hl
      simp only [Set.mem_setOf_eq, not_lt] at hl
      rw [hr, key g hg v l ?_]
      · exact hv l (by simpa using hl)
      · intro j hj
        have : j.val < M + i := by
          by_contra h
          exact hj (hv j (by simpa using h))
        rw [hL, hL]; split_ifs <;> omega
    · funext l
      rw [hr, key g hg _ l]
      intro j hj
      have : j.val = M := by
        by_contra h; exact hj (by simp [Loc.eN, h])
      rw [hL, hL]; split_ifs <;> omega
    · intro l hl
      simp only [Set.mem_setOf_eq, not_lt] at hl
      rw [Pi.sub_apply, hr, key g hg _ l, sub_self]
      intro j hj
      have : j.val = M + i := by
        by_contra h; exact hj (by simp [Loc.eN, h])
      rw [hL, hL]; split_ifs <;> omega
  refine ⟨⟨hR g hg _ (autOf_apply e g), hR g⁻¹ (inv_mem hg) _ (autOf_inv_apply e g)⟩, fun x => ?_⟩
  funext l
  rw [autOf_apply, key g hg _ l]
  intro j hj
  have : j.val < M := by
    by_contra h
    exact hj (by simp [Loc.inX, h])
  rw [hL, hL]; split_ifs <;> omega

theorem locHom_autOf {k : Type} [Field k] (ι : E →+* k) (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) :
    (locHom ι e (autOf e g)).val = g.val.map ι := by
  rw [locHom_val]
  ext i j
  simp [GlobalTheory.SymBridge.toLoc, autOf_apply, Matrix.mulVec_single_one]

end GlobalTheory.VolBridge.NormOneIdeleAutomorphisms

namespace GlobalTheory.VolBridge
open NormOneIdeleAutomorphisms

theorem exists_N1_local_hom_mem_open : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V := by
  intro E k _ _ _ _ _ ι hι A _ _ M c c' e hcc he u hu V hV huV
  let f : (VolN.Ix A c 1 → k) → GL (A ⊕ Fin c) k := fun a => ((Model.mkNel 1 a : N k A c 1) : GL (A ⊕ Fin c) k)
  have hf : Continuous f := continuous_subtype_val.comp (VolN.continuous_mkNel 1)
  have hW : IsOpen (f ⁻¹' V) := hV.preimage hf
  have h0 : VolN.co 1 ⟨u, hu⟩ ∈ f ⁻¹' V := by
    show ((Model.mkNel 1 (VolN.co 1 ⟨u, hu⟩) : N k A c 1) : GL (A ⊕ Fin c) k) ∈ V
    rw [VolN.mkNel_co]; exact huV
  have hD : DenseRange (Pi.map fun (_ : VolN.Ix A c 1) => (ι : E → k)) := DenseRange.piMap fun _ => hι
  obtain ⟨b, hb⟩ := hD.exists_mem_open hW ⟨_, h0⟩
  refine ⟨autOf e ((Model.mkNel 1 b : N E A c 1) : GL (A ⊕ Fin c) E), mem_normOneIdeles e hcc he _ (Model.mkNel 1 b).2, ?_⟩
  have : locHom ι e (autOf e ((Model.mkNel 1 b : N E A c 1) : GL (A ⊕ Fin c) E)) = f (Pi.map (fun _ => (ι : E → k)) b) := by
    apply Units.ext
    rw [locHom_autOf]
    show _ = ((Model.mkNel 1 _ : N k A c 1) : GL (A ⊕ Fin c) k).val
    rw [VolN.val_mkNel, VolN.val_mkNel]
    ext r s
    simp only [Matrix.map_apply, Matrix.add_apply, map_add, VolN.ext0, Matrix.of_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [this]; exact hb

end GlobalTheory.VolBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarVolumeRatioCompactEqRelIndexRatio
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
open scoped Pointwise ENNReal

namespace GlobalTheory.VolRatio

theorem relIndex_mul_measure_sub {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by
  obtain ⟨s, hs, -⟩ := (H.subgroupOf L).exists_isComplement_left 1
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hU : (⋃ a : s, (a.val : L) • (H : Set G)) = (L : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_smul_set, SetLike.mem_coe]
    constructor
    · rintro ⟨a, h, hh, rfl⟩
      exact L.mul_mem a.val.2 (hHL hh)
    · intro hx
      obtain ⟨⟨b, h⟩, hbh, -⟩ := hs.existsUnique ⟨x, hx⟩
      refine ⟨b, (h.val : G), Subgroup.mem_subgroupOf.mp h.2, ?_⟩
      have := congrArg Subtype.val hbh
      exact this
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => (a.val : L) • (H : Set G)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨h1, hh1, rfl⟩ ⟨h2, hh2, he⟩
    apply hab
    have hh1' : (⟨h1, hHL hh1⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh1
    have hh2' : (⟨h2, hHL hh2⟩ : L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh2
    have e : (a.val : L) * ⟨h1, hHL hh1⟩ = (b.val : L) * ⟨h2, hHL hh2⟩ := Subtype.ext he.symm
    have := (hs.existsUnique ((a.val : L) * ⟨h1, hHL hh1⟩)).unique
      (y₁ := (a, ⟨_, hh1'⟩)) (y₂ := (b, ⟨_, hh2'⟩)) rfl e.symm
    exact congrArg Prod.fst this
  calc (H.relIndex L : ENNReal) * μ H = ∑' a : s, μ ((a.val : L) • (H : Set G)) := by
        simp [measure_smul, hs.encard_left, Subgroup.relIndex]
    _ = μ (⋃ a : s, (a.val : L) • (H : Set G)) :=
        (measure_iUnion hdisj fun a => hH.const_smul _).symm
    _ = μ L := by rw [hU]

theorem vol_ratio : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (A B : Subgroup G), IsOpen ((A ⊓ B : Subgroup G) : Set G) → IsCompact (A : Set G) → IsCompact (B : Set G) → (μ (A : Set G)).toReal / (μ (B : Set G)).toReal = (B.relIndex A : ℝ) / (A.relIndex B : ℝ) := by
  intro G _ _ _ _ _ μ _ A B hC hA hB
  have hCA : A ⊓ B ≤ A := inf_le_left
  have hCB : A ⊓ B ≤ B := inf_le_right
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  haveI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  haveI : ((A ⊓ B).subgroupOf A).FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen ((A ⊓ B).subgroupOf A)
      (hC.preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  haveI : ((A ⊓ B).subgroupOf B).FiniteIndex := by
    haveI := Subgroup.quotient_finite_of_isOpen ((A ⊓ B).subgroupOf B)
      (hC.preimage continuous_subtype_val)
    exact Subgroup.finiteIndex_of_finite_quotient
  have hCm : MeasurableSet ((A ⊓ B : Subgroup G) : Set G) := hC.measurableSet
  have h1 := relIndex_mul_measure_sub (A ⊓ B) A hCA hCm μ
  have h2 := relIndex_mul_measure_sub (A ⊓ B) B hCB hCm μ
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right] at h2
  have hpos : 0 < μ ((A ⊓ B : Subgroup G) : Set G) := hC.measure_pos μ ⟨1, (A ⊓ B).one_mem⟩
  have hfin : μ ((A ⊓ B : Subgroup G) : Set G) < ⊤ :=
    lt_of_le_of_lt (measure_mono hCA) hA.measure_lt_top
  have hr : 0 < (μ ((A ⊓ B : Subgroup G) : Set G)).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  rw [← h1, ← h2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, mul_div_mul_right _ _ hr.ne']

end GlobalTheory.VolRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LcvNonnegOfIntegralFull
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem lcv_nonneg_of_integral_full :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (j : ℕ) (Γ : Matrix (Fin j) (Fin j) K) (Y : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ) (L : Submodule (𝓞 K) (Fin j → K)), (∀ v, IsUnit (Y v).det) → Submodule.IsLattice K L → Γ.det ≠ 0 → Formalism.HermitianLatticesTheory.IsIntegralLat (R := 𝓞 K) (hform Γ) L → (∏ v : InfinitePlace K, ‖v.embedding Γ.det‖ ≤ ∏ v : InfinitePlace K, (gram Y v (fun i => (Pi.single i 1 : Fin j → K))).det.re) → 0 ≤ lcv Y L := by
  intro K _ _ _ _ j Γ Y L hY hL hΓ hint hle
  have h := GlobalTheory.TestLat.neg_log_le_lcv_of_integral_form K j Y hY Γ 1 one_pos hΓ hle L hL (by
    intro x hx y hy
    have h1 := hint x hx y hy
    rw [RationalHermitianForm.hform_eq_dot] at h1
    simpa using h1)
  simpa using h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLIffIsUnitDetAtPrimeStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralGL_iff_isUnit_det_at_prime : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l τ j : ℕ) (M : ℕ → ℕ → E), (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = Matrix.of fun a b => ι (M (zPos a) (zPos b))) ↔ (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) ∧ IsUnit (redP P (Matrix.det (Matrix.of fun s s' : Fin (κ + l + j * τ) => M s.1 s'.1))) := by
  first | exact @GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det | exact GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det | (intros; apply GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMirabolicProjectionIffColSpaceAutToLocalGL
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.VolBridge

section PrXIff
variable {E : Type} [Field E] {M c' : ℕ}

theorem inX_castAdd (v : Sp E M) (i : Fin M) : Loc.inX E M c' v (Fin.castAdd c' i) = v i := by
  simp [Loc.inX]

theorem inX_natAdd (v : Sp E M) (i : Fin c') : Loc.inX E M c' v (Fin.natAdd M i) = 0 := by
  simp [Loc.inX]

theorem extX_inX (y : Sp E M ≃ₗ[E] Sp E M) (v : Sp E M) :
    extX c' y (Loc.inX E M c' v) = Loc.inX E M c' (y v) := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [extX_castAdd, inX_castAdd]
    have h : (fun j => Loc.inX E M c' v (Fin.castAdd c' j)) = v := funext fun j => inX_castAdd v j
    rw [h]
  · rw [extX_natAdd, inX_natAdd, inX_natAdd]

variable {A : Type} {c : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c)
  (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

include he in
theorem e_inl (a : A) : e (Sum.inl a) = Fin.castAdd c' (eX e hcc he a) := Fin.ext (by simp [eX_val])

include he in
theorem e_inr (i : Fin c) : e (Sum.inr i) = Fin.natAdd M (⟨i.val, hcc ▸ i.isLt⟩ : Fin c') := Fin.ext (by simp [he])

theorem single_inl (a : A) :
    (Pi.single (e (Sum.inl a)) 1 : Sp E (M + c')) = Loc.inX E M c' (Pi.single (eX e hcc he a) 1) := by
  rw [e_inl e hcc he]
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [inX_castAdd]
    by_cases h : i = eX e hcc he a
    · subst h; simp
    · rw [Pi.single_eq_of_ne (fun h' => h (Fin.castAdd_injective _ _ h')), Pi.single_eq_of_ne h]
  · rw [inX_natAdd, Pi.single_eq_of_ne]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

end PrXIff

section Blocks
variable {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}
  (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

theorem locHom_inl_inl (r : Sp E (M + c') ≃ₗ[E] Sp E (M + c')) (y : Sp E M ≃ₗ[E] Sp E M)
    (hr : ∀ v, r (Loc.inX E M c' v) = Loc.inX E M c' (y v)) (a b : A) :
    (locHom ι e r).val (Sum.inl a) (Sum.inl b) = (locHom ι (eX e hcc he) y).val a b := by
  show ι (r (Pi.single (e (Sum.inl b)) 1) (e (Sum.inl a))) = ι (y (Pi.single (eX e hcc he b) 1) (eX e hcc he a))
  rw [single_inl e hcc he, hr, e_inl e hcc he, inX_castAdd]

theorem locHom_extX (y : Sp E M ≃ₗ[E] Sp E M) :
    locHom ι e (extX c' y) = embX c (locHom ι (eX e hcc he) y) := by
  ext i j
  rw [GlobalTheory.RootEx.VolN.val_embX]
  show ι (extX c' y (Pi.single (e j) 1) (e i)) = _
  rcases i with a | s
  · rw [e_inl e hcc he, extX_castAdd]
    rcases j with b | t
    · rw [single_inl e hcc he]
      have h : (fun l => Loc.inX E M c' (Pi.single (eX e hcc he b) (1 : E)) (Fin.castAdd c' l)) = Pi.single (eX e hcc he b) 1 :=
        funext fun l => inX_castAdd _ l
      rw [h]
      rfl
    · have h : (fun l => (Pi.single (e (Sum.inr t)) (1 : E) : Sp E (M + c')) (Fin.castAdd c' l)) = 0 := by
        funext l
        rw [Pi.single_eq_of_ne]
        · rfl
        intro h'
        have := congrArg Fin.val h'
        simp [he] at this
        omega
      rw [h, map_zero]
      simp
  · rw [e_inr e hcc he, extX_natAdd]
    rcases j with b | t
    · rw [Pi.single_eq_of_ne]
      · simp
      intro h'
      have := congrArg Fin.val h'
      simp [eX_val] at this
      have := eX_lt e hcc he b
      omega
    · rw [e_inr e hcc he]
      by_cases h : s = t
      · subst h; simp
      · rw [Pi.single_eq_of_ne]
        · simp [Matrix.one_apply, h]
        intro h'
        have := congrArg Fin.val h'
        simp at this
        exact h (Fin.ext this)

end Blocks

theorem prX_iff_locHom : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val), (∀ x, x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1) → (∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V) → ∀ (CE : Subgroup (Sp E (M + c') ≃ₗ[E] Sp E (M + c'))) (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (∀ z ∈ R k A c 1, z ∈ Ck ↔ z ∈ O) → Ck ≤ R k A c 1 → (∀ x, x ∈ CE ↔ locHom ι e x ∈ Ck) → ∀ y, y ∈ Loc.prX CE ↔ locHom ι (eX e hcc he) y ∈ prX Ck := by
  intro E k _ _ _ _ _ ι A _ _ M c c' e hcc he hN hdense CE Ck O hO hCkO hCkR hCE y
  constructor
  · rintro ⟨r, hr, hry⟩
    have hg : locHom ι e r ∈ Ck := (hCE r).1 hr
    obtain ⟨x', u, hu, hxu⟩ := GlobalTheory.RootEx.VolN.exists_of_mem_R (hCkR hg)
    have hu' := GlobalTheory.RootEx.Model.mem_N_iff.1 hu
    have hx' : x' = locHom ι (eX e hcc he) y := by
      ext a b
      rw [← locHom_inl_inl ι e hcc he r y hry a b, hxu, Units.val_mul, GlobalTheory.RootEx.VolN.val_embX, Matrix.mul_apply,
        Fintype.sum_sum_type]
      have h1 : ∀ a', u.val (Sum.inl a') (Sum.inl b) = if a' = b then 1 else 0 := fun a' => by
        rw [hu' (Sum.inl a') (Sum.inl b) le_rfl]
        simp [Matrix.one_apply]
      simp [h1]
    refine ⟨embX c x' * u * (embX c x')⁻¹, ?_, ?_⟩
    · have := GlobalTheory.RootEx.Model.conj_mem hu x'⁻¹
      simpa [map_inv, inv_inv] using this
    · rw [← hx']
      simpa [mul_assoc, ← hxu] using hg
  · rintro ⟨u, hu, huC⟩
    set x := locHom ι (eX e hcc he) y with hx
    have huO : u * embX c x ∈ O := (hCkO _ (hCkR huC)).1 huC
    have hV : IsOpen {v : GL (A ⊕ Fin c) k | v * embX c x ∈ O} := hO.preimage (continuous_mul_const _)
    obtain ⟨x₀, hx₀, hx₀V⟩ := hdense u hu _ hV huO
    refine ⟨x₀ * extX c' y, ?_, fun v => ?_⟩
    · rw [hCE, map_mul, locHom_extX ι e hcc he]
      have hR : locHom ι e x₀ * embX c x ∈ R k A c 1 :=
        mul_mem (Subgroup.mem_sup_right ((hN x₀).1 hx₀)) (Subgroup.mem_sup_left ⟨x, rfl⟩)
      exact (hCkO _ hR).2 hx₀V
    · show x₀ (extX c' y (Loc.inX E M c' v)) = _
      rw [extX_inX]
      exact (Subgroup.mem_inf.1 hx₀).2 (y v)

end GlobalTheory.VolBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLocalizedStdLatticeIffIntegralGL
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.VolBridge.StabRead

variable {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k]
  {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}

theorem mem_stdAt_iff_int (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (v : Sp E M) :
    v ∈ stdAt E M P ↔ ∀ i, ι (v i) ∈ 𝒪[k] := by
  rw [GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.mem_stdAt]
  exact forall_congr' fun i => (hι _).symm

theorem single_mem_stdAt (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (m : Fin M) :
    (Pi.single m 1 : Sp E M) ∈ stdAt E M P := by
  rw [mem_stdAt_iff_int hι]
  intro i
  rw [Pi.single_apply]
  split_ifs
  · rw [map_one]; exact Subring.one_mem _
  · rw [map_zero]; exact Subring.zero_mem _

theorem map_mem_stdAt (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (y : Sp E M ≃ₗ[E] Sp E M)
    (hy : ∀ i m, ι (y (Pi.single m 1) i) ∈ 𝒪[k]) {v : Sp E M} (hv : v ∈ stdAt E M P) : y v ∈ stdAt E M P := by
  rw [mem_stdAt_iff_int hι] at hv ⊢
  intro i
  have e : y v = LinearMap.toMatrix' (y : Sp E M →ₗ[E] Sp E M) *ᵥ v := (LinearMap.toMatrix'_mulVec _ v).symm
  rw [e]
  simp only [Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply, map_sum, map_mul]
  exact Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hy i m) (hv m)

end GlobalTheory.VolBridge.StabRead

open GlobalTheory.VolBridge.StabRead in

theorem GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k)
    (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M)
    (x : Sp E M ≃ₗ[E] Sp E M) : x ∈ stabL E M (stdAt E M P) ↔ locHom ι e x ∈ KO k A := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  constructor
  · intro hx
    have hx' : x⁻¹ ∈ stabL E M (stdAt E M P) := inv_mem hx
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · change ι (x (Pi.single (e b) 1) (e a)) ∈ 𝒪[k]
      exact (mem_stdAt_iff_int hι _).1 ((hx _).2 (single_mem_stdAt hι _)) _
    · change ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single (e b) 1) (e a)) ∈ 𝒪[k]
      exact (mem_stdAt_iff_int hι _).1 ((hx' _).2 (single_mem_stdAt hι _)) _
  · rintro ⟨h1, h2⟩
    have i1 : ∀ i m, ι (x (Pi.single m 1) i) ∈ 𝒪[k] := fun i m => by
      have h := h1 (e.symm i) (e.symm m)
      change ι (x (Pi.single (e (e.symm m)) 1) (e (e.symm i))) ∈ 𝒪[k] at h
      simpa only [Equiv.apply_symm_apply] using h
    have i2 : ∀ i m, ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single m 1) i) ∈ 𝒪[k] := fun i m => by
      have h := h2 (e.symm i) (e.symm m)
      change ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single (e (e.symm m)) 1) (e (e.symm i))) ∈ 𝒪[k] at h
      simpa only [Equiv.apply_symm_apply] using h
    intro v
    constructor
    · intro hv
      have h := map_mem_stdAt hι _ i2 hv
      have ev : (x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (x v) = v := x.symm_apply_apply v
      rwa [ev] at h
    · exact map_mem_stdAt hι x i1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymChainPatternIffPlaceConditionsStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symChainPattern_iff_place_conditions : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l ρ τ j : ℕ) (M : ℕ → ℕ → E), (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) → ((∀ a b : Ix (Fin κ ⊕ Fin l) (Fin τ) j, ¬ FreeIx ρ a b → valuation k (ι (M (zPos a) (zPos b)) - (1 : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k) a b) < 1) ↔ ((∀ p', p' < κ + l → redP P (M p' p') = 1 ∧ ∀ p, p < κ + l + j * τ → p ≠ p' → (κ + l ≤ p ∨ symIdx κ ρ p' < symIdx κ ρ p ∨ (p' = κ + ρ ∧ p < κ)) → redP P (M p p') = 0) ∧ (∀ p p', κ + l ≤ p' → p' < κ + l + j * τ → p < κ + l + j * τ → (p' - (κ + l)) / τ < (p - (κ + l)) / τ → redP P (M p p') = 0))) := by
  first | exact @GlobalTheory.PatResidue.pattern_iff_places | exact GlobalTheory.PatResidue.pattern_iff_places | (intros; apply GlobalTheory.PatResidue.pattern_iff_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPointsStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symLevelTestFunctions_agree_rationalPoints : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → PhiAgree P q ι σ₀ ψ₀ χ S := by
  first | exact @GlobalTheory.SymBridge.PhiAgreeProof.phiAgree | exact GlobalTheory.SymBridge.PhiAgreeProof.phiAgree | (intros; apply GlobalTheory.SymBridge.PhiAgreeProof.phiAgree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelCharacterAtRationalPointStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLevel_character_at_rational_point : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ), Comparison₂ P q ι σ₀ ψ₀ χ S → ∀ (M : ℕ → ℕ → E), (∀ p p', p < κ + (s + 1) → p' < κ + (s + 1) → IntAt P (M p p')) → ∀ g : S.P.J, (g : GL (Fin κ ⊕ Fin (s + 1)) k).val = Matrix.of (fun a b => ι (M (Sum.elim (fun i => i.val) (fun i => κ + i.val) a) (Sum.elim (fun i => i.val) (fun i => κ + i.val) b))) → (S.P.lam g : ℂ) = σ₀ (ψ₀ (redP P (∑ i ∈ Finset.range (κ - 1), M i (i + 1) + ∑ i ∈ Finset.range (κ + s + 1 - κ - 1), M (κ + i) (κ + i + 1)))) := by
  first | exact @GlobalTheory.symLevel_lam_residue_elim | exact GlobalTheory.symLevel_lam_residue_elim | (intros; apply GlobalTheory.symLevel_lam_residue_elim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralEqFiniteSumOverNumberFieldStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingIntegral_eq_finiteSum_overNumberField : SumAgree := by
  first | exact @GlobalTheory.UnfoldSum.sumAgree | exact GlobalTheory.UnfoldSum.sumAgree | (intros; apply GlobalTheory.UnfoldSum.sumAgree <;> assumption)
end

