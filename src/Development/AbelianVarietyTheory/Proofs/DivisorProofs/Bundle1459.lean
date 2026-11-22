import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
import GroundTheory.GlobalFields.TateThesis.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPointsIntegralAlmostAll
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocRatPt

open scoped ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem map_mem_UL (hU : Unr E) (w : Pl E) (γ : UE E n) :
    GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ UL n w := by
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  · have hc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hs).1
    have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 *
        (γ.1 : Matrix (Fin n) (Fin n) E) = 1 := γ.2
    change cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) * 1 *
      (γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) = 1
    have key : cT (cj w) ((γ.1 : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E))) =
        (cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E)).map
          (algebraMap E (w.adicCompletion E)) := by
      exact Matrix.ext fun i j => hc _
    rw [key, Matrix.mul_one, ← Matrix.map_mul]
    rw [Matrix.mul_one] at hγ
    rw [hγ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem locPt_val (hU : Unr E) (w : Pl E) (γ : UE E n) :
    (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  rw [locPt, toSub, dif_pos (map_mem_UL hU w γ)]

theorem eventually_valuation_le_one (x : E) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), w.valuation E x ≤ 1 := by
  rw [Filter.eventually_cofinite]
  refine (HeightOneSpectrum.Support.finite (𝓞 E) x).subset fun w hw => ?_
  exact lt_of_not_ge hw

theorem algebraMap_mem_Ov {w : Pl E} {x : E} (h : w.valuation E x ≤ 1) :
    algebraMap E (w.adicCompletion E) x ∈ Ov E w := by
  rw [ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [show Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x from
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x]
  exact h

theorem mem_GLint_of_entries {K : Type} [Field K] {O : Subring K} {x : GL (Fin n) K} (h1 : ∀ i j, x.1 i j ∈ O)
    (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ GLint (Fin n) O := by
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, ?_, ?_⟩, rfl⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem eventually_mem_KL (hU : Unr E) (γ : UE E n) :
    ∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w := by
  have h1 : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ i j, w.valuation E ((γ.1 : GL (Fin n) E).1 i j) ≤ 1 ∧
      w.valuation E (((γ.1 : GL (Fin n) E)⁻¹).1 i j) ≤ 1 := by
    simp only [Filter.eventually_all]
    intro i j
    exact (eventually_valuation_le_one _).and (eventually_valuation_le_one _)
  filter_upwards [h1] with w hw
  rw [KL, Subgroup.mem_subgroupOf, locPt_val hU]
  refine mem_GLint_of_entries (fun i j => algebraMap_mem_Ov (hw i j).1) (fun i j => ?_)
  rw [← map_inv]
  exact algebraMap_mem_Ov (hw i j).2

theorem norm_eq_one_of_root (γ : UE E n) (τ : E →+* ℂ) (z : ℂ)
    (hz : z ∈ ((γ.1 : GL (Fin n) E).val.charpoly.map τ).roots) : ‖z‖ = 1 := by
  first
  | (rename_i h_1 h_2 h_3; revert E h_1 h_2 h_3 n γ τ z hz; exact @_root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly)
  | exact @_root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly
  | exact _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly
  | (apply _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitaryCharpolyRootNorm.norm_root_charpoly ..)

theorem charpoly_mem_Ell (γ : UE E n) (hs : (γ.1 : GL (Fin n) E).val.charpoly.Separable) :
    (γ.1 : GL (Fin n) E).val.charpoly ∈ Ell E n :=
  ⟨Matrix.charpoly_monic _, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], hs,
    fun τ z hz => norm_eq_one_of_root γ τ z hz⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : UE E n), (∀ w : Pl E, (locPt w γ).1 = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1) ∧ (∀ᶠ w in (cofinite : Filter (Pl E)), locPt w γ ∈ KL n w) ∧ (γ.1.val.charpoly.Separable → γ.1.val.charpoly ∈ Ell E n) := by
  intro E _ _ _ hU n γ
  exact ⟨fun w => locPt_val hU w γ, eventually_mem_KL hU γ, charpoly_mem_Ell γ⟩

end GlobalTheory.LocRatPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
section
noncomputable section

namespace GlobalTheory.CtTyp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def ctf {d d₁ : ℕ} {W : Spc F E d} (H' : Plane E d d₁) (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H'))
    (f : UA σ W.J → ℂ) (g : UA σ W.J) : ℂ :=
  ∫ u in 𝓕, f (u.1 * g) ∂μ

theorem absE_pos (t : (AE F E)ˣ) : 0 < (absE F E t : ℝ) := by
  have h : absE F E t * absE F E t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h0 : absE F E t ≠ 0 := left_ne_zero_of_mul_eq_one h
  exact_mod_cast pos_iff_ne_zero.2 h0

def twAbs (χ : Chr F E) (s : ℝ) : (AE F E)ˣ →* ℂˣ where
  toFun t := Units.mk0 ((χ t : ℂ) * (((absE F E t : ℝ) ^ s : ℝ) : ℂ))
    (mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (absE_pos t) s).ne'))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Circle.coe_mul, NNReal.coe_mul, Units.val_mul, Units.val_mk0]
    rw [Real.mul_rpow (absE_pos x).le (absE_pos y).le]
    push_cast
    ring

@[simp] theorem coe_twAbs (χ : Chr F E) (s : ℝ) (t : (AE F E)ˣ) :
    ((twAbs χ s t : ℂˣ) : ℂ) = (χ t : ℂ) * (((absE F E t : ℝ) ^ s : ℝ) : ℂ) := rfl

example : twAbs (1 : Chr F E) 0 = 1 := by ext t; simp

theorem norm_twAbs (χ : Chr F E) (s : ℝ) (t : (AE F E)ˣ) : ‖((twAbs χ s t : ℂˣ) : ℂ)‖ = (absE F E t : ℝ) ^ s := by
  rw [coe_twAbs, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (absE_pos t) s)]

theorem log_absE_mul (x y : (AE F E)ˣ) :
    Real.log (absE F E (x * y) : ℝ) = Real.log (absE F E x : ℝ) + Real.log (absE F E y : ℝ) := by
  rw [map_mul, NNReal.coe_mul, Real.log_mul (absE_pos x).ne' (absE_pos y).ne']

theorem log_absE_eq_zero {t : (AE F E)ˣ} : Real.log (absE F E t : ℝ) = 0 ↔ absE F E t = 1 := by
  constructor
  · intro h
    have := Real.exp_log (absE_pos t)
    rw [h, Real.exp_zero] at this
    exact_mod_cast this.symm
  · intro h; rw [h]; simp

end GlobalTheory.CtTyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKUConjOfComp
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.IntRead

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def thAt (u : Pl E) : GLw n (cPl E u) →* GLw n u :=
  (MulAut.conj (PhiU n (u.adicCompletion E))).toMonoidHom.comp
    ((invT n (u.adicCompletion E)).comp (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv u)))

theorem thAt_apply (u : Pl E) (h : GLw n (cPl E u)) (i j : Fin n) :
    (thAt u h).val i j =
      (-1) ^ ((i : ℕ) + j) * conjLoc (IsCMField.complexConj E).toRingEquiv u ((h⁻¹).val j.rev i.rev) :=
  GlobalTheory.ThetaPull.phi_mul_apply _ i j

theorem map_thF (u : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    GeneralLinearGroup.map (pLoc E u) (thF E n g) = thAt u (GeneralLinearGroup.map (pLoc E (cPl E u)) g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := GlobalTheory.ThetaPull.thetaGL_apply (a := n) (conjFin (IsCMField.complexConj E).toRingEquiv) g i j
  change pLoc E u ((thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j) = _
  rw [h, thAt_apply, map_mul, map_pow, map_neg, map_one, pLoc_conjFin]
  rfl

theorem mem_KGL_of_thAt (u : Pl E) (k : GLw n (cPl E u)) (hk : thAt u k ∈ GlobalTheory.LFun.KGL u n) :
    k ∈ GlobalTheory.LFun.KGL (cPl E u) n := by
  have hv : ∀ (h : GLw n (cPl E u)) (i j : Fin n),
      Valued.v ((thAt u h).val i j) = Valued.v ((h⁻¹).val j.rev i.rev) := by
    intro h i j
    rw [thAt_apply, Valuation.map_mul, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow, one_mul]
    exact (conjLoc_spec (IsCMField.complexConj E).toRingEquiv u).2.2 _
  rw [GlobLev.mem_KGL_iff_val] at hk ⊢
  obtain ⟨h1, h2⟩ := hk
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have := h2 j.rev i.rev
    rw [← map_inv, hv, inv_inv, Fin.rev_rev, Fin.rev_rev] at this
    exact this
  · have := h1 j.rev i.rev
    rwa [hv, Fin.rev_rev, Fin.rev_rev] at this

end GlobalTheory.EulerTw.IntRead

namespace GlobalTheory.EulerTw.IntRead

open GlobalTheory.EulerTw

end GlobalTheory.EulerTw.IntRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorLatticeAtPlaceIffFrameCoordinatesIntegrStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_tensorLatticeAtPlace_iff_frame_coordinates_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ AE F E),
      Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L), (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PV : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) → (∀ x : Fin d → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PW : Matrix (Fin d) (Fin d) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z, z ∈ latAtV X W v ↔ ∃ u : Matrix (Fin d) (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
        GlobalTheory.InertLocFrame.xm ι PV PW u = z := by
  first | exact @GlobalTheory.InertLocFrame.mem_latAtV_iff_xm | exact GlobalTheory.InertLocFrame.mem_latAtV_iff_xm | (intros; apply GlobalTheory.InertLocFrame.mem_latAtV_iff_xm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ModuAdele

open scoped Pointwise

theorem distribHaarChar_adeleRing (K : Type) [Field K] [NumberField K] (a : (AdeleRing (𝓞 K) K)ˣ) :
    (distribHaarChar (AdeleRing (𝓞 K) K) a : ℝ) = (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) := by
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := GroundTheory.Global.measurableSpace_adeleRing K
  obtain ⟨s, hsc, hs0⟩ : ∃ s : Set (AdeleRing (𝓞 K) K), IsCompact s ∧ s ∈ nhds (0 : AdeleRing (𝓞 K) K) :=
    exists_compact_mem_nhds 0
  have hpos : 0 ≤ (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) := (GroundTheory.Global.IdeleGroup.ideleModule K a).2.le
  set r : NNReal := ⟨_, hpos⟩ with hr
  set μ := GroundTheory.Global.adeleMeasure K with hμ
  set ν : Measure (AdeleRing (𝓞 K) K) := Measure.addHaar with hν
  have e1 := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν hsc.closure
  have e2 := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure μ ν (hsc.smul a).closure
  have hm := GroundTheory.Global.adeleMeasure_smul a s
  set c := μ.addHaarScalarFactor ν
  have hμs : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hs0).ne'
  have hνs : ν s ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hs0).ne'
  have hνs' : ν s ≠ ⊤ := hsc.measure_lt_top.ne
  have hc : (c : ENNReal) ≠ 0 := by
    intro h0
    apply hμs
    rw [e1, ENNReal.smul_def, smul_eq_mul, h0, zero_mul]
  have h := distribHaarChar_eq_of_measure_smul_eq_mul (g := a) (μ := ν) (s := s) hνs hνs'
    (r := r) (by
      rw [e1, e2, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
        ENNReal.ofReal_eq_coe_nnreal hpos] at hm
      have hm' : (c : ENNReal) * ν (a • s) = (c : ENNReal) * ((r : ENNReal) * ν s) := by
        calc (c : ENNReal) * ν (a • s) = (r : ENNReal) * ((c : ENNReal) * ν s) := hm
          _ = (c : ENNReal) * ((r : ENNReal) * ν s) := by ring
      exact (ENNReal.mul_right_inj hc ENNReal.coe_ne_top).1 hm')
  rw [h]
  rfl

end GlobalTheory.ModuAdele

theorem GlobalTheory.ModuAdele.modu_norm_eq_absE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (x : (AE F E)ˣ),
    (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) = absE F E x := by
  intro F E _ _ _ _ _ x
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖evFin F v (Algebra.norm (AF F) x.1)‖₊).Finite := by
    simpa only [GlobalTheory.Doubling.absEv_unitFin] using GlobalTheory.Doubling.finite_mulSupport_absEv x
  apply NNReal.eq
  change (distribHaarChar (AdeleRing (𝓞 F) F) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) : ℝ) = _
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply]
  simp only [GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf]
  rw [NNReal.coe_mul, NNReal.coe_prod]
  congr 1
  rw [show ((∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖evFin F v (Algebra.norm (AF F) x.1)‖₊ : ℝ≥0) : ℝ) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((‖evFin F v (Algebra.norm (AF F) x.1)‖₊ : ℝ≥0) : ℝ) from
      NNReal.toRealHom.toMonoidHom.map_finprod hf]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def hat {κ : Type} (w : (κ → F) × (κ → F)) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (w.1 i), fun i => algebraMap F (AF F) (w.2 i))

theorem hat_add {κ : Type} (a b : (κ → F) × (κ → F)) : hat (a + b) = hat a + hat b := by
  simp only [hat, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]; rfl

theorem hat_smul {κ : Type} (c : F) (a : (κ → F) × (κ → F)) : hat (c • a) = algebraMap F (AF F) c • hat a := by
  simp only [hat, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul]; rfl

theorem hat_zero {κ : Type} : hat (0 : (κ → F) × (κ → F)) = 0 := by
  simp only [hat, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, map_zero]; rfl

theorem schr_comp {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add,
    add_assoc, add_dotProduct, dotProduct_add]
  congr 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

def IsMixed (M₁ : Model σ X W₁) (H' : Plane E d d₁) (m : Matrix (Fin n) (Fin d) (AE F E)) : Prop :=
  ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
    (M₁.co.e z).1 = 0 ∧ m = u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ

theorem isMixed_zero (M₁ : Model σ X W₁) (H' : Plane E d d₁) : IsMixed M₁ H' 0 :=
  ⟨0, ⟨0, by ext i j; simp [Matrix.vecMulVec_apply]⟩, 0, by simp, by simp⟩

theorem IsMixed.add {M₁ : Model σ X W₁} {H' : Plane E d d₁} {m m' : Matrix (Fin n) (Fin d) (AE F E)}
    (h : IsMixed M₁ H' m) (h' : IsMixed M₁ H' m') : IsMixed M₁ H' (m + m') := by
  obtain ⟨u, ⟨y, rfl⟩, z, hz, rfl⟩ := h
  obtain ⟨u', ⟨y', rfl⟩, z', hz', rfl⟩ := h'
  refine ⟨Matrix.vecMulVec (y + y') (incV F H'.x), ⟨y + y', rfl⟩, z + z', by simp [hz, hz'], ?_⟩
  rw [Matrix.add_vecMulVec, Matrix.mul_add, Matrix.add_mul]
  abel

theorem IsMixed.smul {M₁ : Model σ X W₁} {H' : Plane E d d₁} {m : Matrix (Fin n) (Fin d) (AE F E)}
    (h : IsMixed M₁ H' m) (t : AF F) : IsMixed M₁ H' (t • m) := by
  obtain ⟨u, ⟨y, rfl⟩, z, hz, rfl⟩ := h
  refine ⟨Matrix.vecMulVec (t • y) (incV F H'.x), ⟨t • y, rfl⟩, t • z, by simp [hz], ?_⟩
  rw [smul_add, Matrix.smul_vecMulVec, Matrix.mul_smul, Matrix.smul_mul]

def lagr (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) :
    Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) where
  carrier := {w | IsMixed M₁ H' (M.co.e.symm (hat w))}
  zero_mem' := by simpa [hat_zero] using isMixed_zero M₁ H'
  add_mem' := fun ha hb => by simpa [Set.mem_setOf_eq, hat_add, map_add] using ha.add hb
  smul_mem' := fun c a ha => by
    show IsMixed M₁ H' (M.co.e.symm (hat (c • a)))
    rw [hat_smul, LinearEquiv.map_smul]
    exact ha.smul _

theorem mem_lagr {M : Model σ X W} {M₁ : Model σ X W₁} {H' : Plane E d d₁} {w} :
    w ∈ lagr M M₁ H' ↔ IsMixed M₁ H' (M.co.e.symm (hat w)) := Iff.rfl

theorem mul_transpose_injective : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n d d₁ : ℕ)
    (JW : Matrix (Fin d) (Fin d) E) (JW₁ : Matrix (Fin d₁) (Fin d₁) E) (ι : Matrix (Fin d) (Fin d₁) E),
    ιᵀ * JW * ι.map σ = JW₁ → JW₁.det ≠ 0 → Function.Injective fun z : Matrix (Fin n) (Fin d₁) E => z * ιᵀ := by
  intro F E _ _ _ σ n d d₁ JW JW₁ ι hg hdet z z' h
  simp only at h
  have h0 : (z - z') * JW₁ = 0 := by
    rw [← hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.sub_mul, h, sub_self, Matrix.zero_mul, Matrix.zero_mul]
  have h1 : z - z' = 0 := by
    have := congrArg (· * JW₁⁻¹) h0
    simp only [Matrix.zero_mul] at this
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one] at this
  exact sub_eq_zero.mp h1

end GlobalTheory.MixedLagr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastNotMemCubePrimeAdjoinJInvariantSqrtNegStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCast_notMem_cube_prime_adjoin_jInvariant_sqrtNeg : ∀ (p : ℕ) (L₀ : PeriodPair) [NumberField ℚ⟮(latticeCurve L₀).j⟯] (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)), p.Prime → IsIntegersLattice p L₀ → (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  first | exact @GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j | exact GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j | (intros; apply GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatMulVec
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.UnipMass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) : AE F E :=
  v ⬝ᵥ (incM F J *ᵥ fun i => cA σ (w i))

def nmat (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → AE F E) (c : AE F E) :
    Matrix (Fin n) (Fin n) (AE F E) :=
  1 - Matrix.vecMulVec (u + c • x) (incM F J *ᵥ fun i => cA σ (x i)) -
    Matrix.vecMulVec x (incM F J *ᵥ fun i => cA σ (u i))

theorem nmat_mulVec (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x u : Fin n → AE F E) (c : AE F E)
    (v : Fin n → AE F E) : nmat σ J x u c *ᵥ v = v - hA σ J v x • (u + c • x) - hA σ J v u • x := by
  ext i
  simp only [nmat, hA, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Matrix.vecMulVec_mulVec, Pi.smul_apply,
    smul_eq_mul, op_smul_eq_mul]
  rw [dotProduct_comm v, dotProduct_comm v]
  ring

end GlobalTheory.UnipMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCommutingTwistedConjCompactMemTwistedCentralStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normCommuting_twistedConj_compact_mem_twistedCentralizer_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ z : GLw n w, z * nrmL n w y = nrmL n w y * z → z⁻¹ * y * thL n w z ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, z = t * d := by
  first | exact @GlobalTheory.NormOneProper.main | exact GlobalTheory.NormOneProper.main | (intros; apply GlobalTheory.NormOneProper.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSubLeOfLieDerivativeUnipotentSegmentStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sub_le_of_lieDerivative_unipotentSegment : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ψ : Sm E a) (g : GA E a) (n : Matrix (Fin a) (Fin a) (Cinf E)) (u : ℝ → GL (Fin a) (Cinf E)) (M : ℝ), n * n = 0 → (∀ τ : ℝ, (u τ).val = 1 + τ • n) → (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖lieD (toL n) ψ.1 (g * infGL E a (u τ))‖ ≤ M) → ‖ψ.1 (g * infGL E a (u 1)) - ψ.1 g‖ ≤ M := by
  first | exact @GlobalTheory.CuspRapid.norm_sub_le_of_lieD_unipotent_segment | exact GlobalTheory.CuspRapid.norm_sub_le_of_lieD_unipotent_segment | (intros; apply GlobalTheory.CuspRapid.norm_sub_le_of_lieD_unipotent_segment <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealActs

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def DerOn (N : Submodule ℂ (SInf F κ)) (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) : Prop :=
  ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ N, D f ∈ N) ∧ ∀ f ∈ N, ∀ f₁ : SInf F κ, ActsD (evI F) T f f₁ ↔ f₁ = D f

def OpOn (N : Submodule ℂ (SInf F κ)) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) : Prop :=
  ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ N, D f ∈ N) ∧ ∀ f ∈ N, ∀ f₁ : SInf F κ, Acts (evI F) T f f₁ ↔ f₁ = D f

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def PolActs (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) : Prop :=
  (∀ γ ∈ Lines σ X, DerOn (M.Pol B.ψ B.emb) (fun t => om (γ (Multiplicative.ofAdd t), 1))) ∧
  (∀ k ∈ KInf σ X B.emb, OpOn (M.Pol B.ψ B.emb) (om (k, 1))) ∧
  (∀ γ ∈ Lines σ W, DerOn (M.Pol B.ψ B.emb) (fun t => om (1, γ (Multiplicative.ofAdd t)))) ∧
  ∀ k ∈ KInf σ W B.emb, OpOn (M.Pol B.ψ B.emb) (om (1, k))

def KerStab (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) {P : Type}
    [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Prop :=
  (∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f = 0 → p f₁ = 0) ∧
  ∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    Acts (evI F) (om (1, k)) f f₁ → p f = 0 → p f₁ = 0

def Irred (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) {P : Type}
    [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Prop :=
  ∀ N : Submodule ℂ P,
    (∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    (∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f ∈ N → p f₁ ∈ N) → N = ⊥ ∨ N = ⊤

end GlobalTheory.RealActs

end
end

