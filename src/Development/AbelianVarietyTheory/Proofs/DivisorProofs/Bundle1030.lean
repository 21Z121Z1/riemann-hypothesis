import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0993
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0173

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseDifferentMaxValuation
section
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem invDifferent_exists_max_valuation :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)), ∃ e : E, e ≠ 0 ∧
      (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) ∧
      ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
        w.valuation E f ≤ w.valuation E e := by
  intro E _ _ w
  classical

  have hint : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
      IsIntegral ℤ ((NumberField.discr E : E) * f) := by
    intro f hf
    have hmem : f ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨y, rfl⟩ := Submodule.mem_one.mp ha
      have h := hf y
      rw [IsIntegrallyClosed.isIntegral_iff] at h
      obtain ⟨k, hk⟩ := h
      refine ⟨k, ?_⟩
      rw [Algebra.traceForm_apply, hk, mul_comm]
    have hb : ∀ i, IsIntegral ℤ (integralBasis E i) := fun i => by
      rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
    have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    have := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
      (1 : Submodule (𝓞 E) E) hb h1 hmem
    rw [← coe_discr, Algebra.smul_def, mul_one] at this
    simpa using this
  have hle : ∀ f : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) →
      w.valuation E ((NumberField.discr E : E) * f) ≤ 1 := by
    intro f hf
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hint f hf)
    rw [← hy]
    exact w.valuation_le_one y
  have hd0 : (NumberField.discr E : E) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have hvd : w.valuation E (NumberField.discr E : E) ≠ 0 := by simpa using hd0
  have hP1 : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * 1)) := fun o => by
    rw [mul_one]; exact Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe o)
  let S : ℤ → Prop := fun k => ∃ f : E, f ≠ 0 ∧
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * f))) ∧
      WithZero.log (w.valuation E f) = k
  have hbdd : ∃ b, ∀ z, S z → z ≤ b := by
    refine ⟨-WithZero.log (w.valuation E (NumberField.discr E : E)), ?_⟩
    rintro z ⟨f, hf0, hf, rfl⟩
    have hvf : w.valuation E f ≠ 0 := by simpa using hf0
    have h := hle f hf
    rw [map_mul, ← WithZero.exp_log hvd, ← WithZero.exp_log hvf, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    omega
  have hne : ∃ z, S z := ⟨_, 1, one_ne_zero, hP1, rfl⟩
  obtain ⟨k, ⟨e, he0, he, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨e, he0, he, fun f hf => ?_⟩
  by_cases hf0 : f = 0
  · subst hf0; simp
  have hvf : w.valuation E f ≠ 0 := by simpa using hf0
  have hve : w.valuation E e ≠ 0 := by simpa using he0
  have h := hmax _ ⟨f, hf0, hf, rfl⟩
  rw [← WithZero.exp_log hvf, ← WithZero.exp_log hve, WithZero.exp_le_exp]
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
section
namespace GlobalTheory.EtaConjExist

section General

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L]

theorem fin_supp {M : Type} [CommGroup M] (c : HeightOneSpectrum (𝓞 L) → M) {n : HeightOneSpectrum (𝓞 L) → ℤ}
    (h : {v | n v ≠ 0}.Finite) : (Function.mulSupport fun v => c v ^ n v).Finite :=
  h.subset fun v hv h0 => hv (by simp only [h0, zpow_zero])

noncomputable def idealChar (c : HeightOneSpectrum (𝓞 L) → ℂˣ) : Ideles L →* ℂˣ :=
  MonoidHom.mk' (fun a => ∏ᶠ v, c v ^ GlobalTheory.Idele.ord_vw (GlobalTheory.HeckeProduct.finPart L a) v) fun a b => by
    rw [← finprod_mul_distrib (fin_supp c (Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero _)))
      (fin_supp c (Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero _)))]
    refine finprod_congr fun v => ?_
    rw [map_mul, GlobalTheory.Idele.ord_vw_mul, zpow_add]

theorem idealChar_apply (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (a : Ideles L) :
    idealChar c a = ∏ᶠ v, c v ^ (-WithZero.log (Valued.v ((a : AdeleRing (𝓞 L) L).2 v))) := rfl

theorem idealChar_unit (c : HeightOneSpectrum (𝓞 L) → ℂˣ) {a : Ideles L} (ha : a ∈ unitIdl L) : idealChar c a = 1 := by
  rw [idealChar_apply]
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  rw [ha v, WithZero.log_one, neg_zero, zpow_zero]

theorem idealChar_local (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    idealChar c (localIdele L v x) = c v ^ (-WithZero.log (Valued.v (x : v.adicCompletion L))) := by
  rw [idealChar_apply, finprod_eq_single _ v, GlobalTheory.HeckeProduct.localIdele_snd_self]
  intro w hw
  rw [GlobalTheory.HeckeProduct.localIdele_snd_ne L v w hw, map_one, WithZero.log_one, neg_zero, zpow_zero]

theorem exists_classChar (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (h : ∀ k : Lˣ, ∏ᶠ v, c v ^ ordF v k = 1) :
    ∃ ξ : HChar L, ξ.IsUnitary ∧ (∀ v, ξ.UnrAt v) ∧ ∀ v, ξ.val v = c v := by
  have hd : ∀ k : Lˣ, idealChar c (diagUnits L k) = 1 := fun k => by
    rw [idealChar_apply, ← h k]
    refine finprod_congr fun v => ?_
    have hk : Valued.v ((diagUnits L k : AdeleRing (𝓞 L) L).2 v) = v.valuation L (k : L) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : L)
    rw [hk, ordF]
  have hc : Continuous (idealChar c) := by
    refine continuous_of_continuousAt_one _ ?_
    refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.mem_nhds (unitIdl L).one_mem] with a ha
    exact (idealChar_unit c ha).symm
  refine ⟨⟨idealChar c, hc, hd⟩, fun x => ?_, fun v x hx => ?_, fun v => ?_⟩
  · have := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
    obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((unitIdl L ⊔ (diagUnits L).range).pow_index_mem x)
    have e1 := congrArg (fun z => ((idealChar c z : ℂˣ) : ℂ)) e
    simp only [map_mul, map_pow, idealChar_unit c hu, hd, one_mul, Units.val_one, Units.val_pow_eq_pow_val] at e1
    exact Complex.norm_eq_one_of_pow_eq_one e1.symm this.index_ne_zero
  · refine (idealChar_local c v x).trans ?_
    rw [show Valued.v (x : v.adicCompletion L) = 1 from hx, WithZero.log_one, neg_zero, zpow_zero]
  · refine (idealChar_local c v _).trans ?_
    rw [show Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = _ from unif_spec v,
      WithZero.log_exp, neg_neg, zpow_one]

theorem finprod_sqrt [IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (k : Lˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 L), ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ ordF v k) *
      ∏ i, ‖φ i (k : L)‖ = 1 := by
  have h1 := prod_abs_eq_one k.ne_zero
  rw [← hφ.prod_comp, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at h1
  have h2 : ∀ i, (InfinitePlace.mk (φ i)) (k : L) ^ (InfinitePlace.mk (φ i)).mult = ‖φ i (k : L)‖ * ‖φ i (k : L)‖ := by
    intro i
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq, sq]
  have h3 : ∀ v : HeightOneSpectrum (𝓞 L), FinitePlace.equivHeightOneSpectrum.symm v (k : L) =
      ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ ordF v k *
        ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ ordF v k := fun v => by
    have h0 : v.valuation L (k : L) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
    rw [← mul_zpow, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _), inv_zpow',
      FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding, HeightOneSpectrum.adicAbv_def,
      WithZeroMulInt.toNNReal_neg_apply _ h0, ordF, neg_neg]
    push_cast
    congr 1
    exact WithZero.toAdd_unzero_eq_log h0
  have h4 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) =>
      ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ ordF v k).Finite :=
    (GlobalTheory.HeckeProduct.finite_ordF k).subset fun v hv h0 => hv (by simp only [h0, zpow_zero])
  simp only [h2, h3] at h1
  rw [finprod_mul_distrib h4 h4, Finset.prod_mul_distrib] at h1
  refine (mul_self_eq_one_iff.1 (by linear_combination h1)).resolve_right fun h => ?_
  have : (0 : ℝ) ≤ -1 := h ▸ mul_nonneg (finprod_nonneg fun v => by positivity) (by positivity)
  linarith

theorem finprod_alg [IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (hu : ∀ v, χ.UnrAt v)
    (hi : χ.HasInf φ fun _ => 1) (w : HeightOneSpectrum (𝓞 L) → ℂˣ)
    (hw : ∀ v, (w v : ℂ) = χ.val v * (((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) : ℂ)) (k : Lˣ) :
    ((∏ᶠ v, w v ^ ordF v k : ℂˣ) : ℂ) * ∏ i, φ i (k : L) = 1 := by
  have e5 := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hu v) k
  simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at e5
  have e6 := finprod_sqrt φ hφ k
  have hs : ∀ {M : Type} [CommGroupWithZero M] (f : HeightOneSpectrum (𝓞 L) → M), ∏ᶠ v, f v ^ ordF v k =
      ∏ v ∈ (GlobalTheory.HeckeProduct.finite_ordF k).toFinset, f v ^ ordF v k := fun f =>
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset]
      exact fun h0 => hv (by simp only [h0, zpow_zero])
  have hs' : ∀ (f : HeightOneSpectrum (𝓞 L) → ℂˣ), ((∏ᶠ v, f v ^ ordF v k : ℂˣ) : ℂ) =
      ∏ v ∈ (GlobalTheory.HeckeProduct.finite_ordF k).toFinset, (f v : ℂ) ^ ordF v k := fun f => by
    rw [finprod_eq_prod_of_mulSupport_subset (s := (GlobalTheory.HeckeProduct.finite_ordF k).toFinset) _ fun v hv => by
      simp only [Set.Finite.coe_toFinset]
      exact fun h0 => hv (by simp only [h0, zpow_zero])]
    simp
  have e7 := congrArg Units.val e5
  have e8 := congrArg Complex.ofReal e6
  rw [Units.val_mul, hs', hi k, Units.val_one] at e7
  rw [hs] at e8
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_zpow, Complex.ofReal_one] at e8
  simp only [zpow_one, Finset.prod_div_distrib] at e7
  have h0 : ∏ i, ((‖φ i (k : L)‖ : ℝ) : ℂ) ≠ 0 := right_ne_zero_of_mul_eq_one e8
  rw [hs']
  simp only [hw, mul_zpow, Finset.prod_mul_distrib]
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq h0] at e7
  rw [mul_right_comm, mul_comm _ (∏ i, φ i (k : L)), e7, mul_comm, e8]

theorem finprod_quot {M : Type} [Field M] (e σ : M →+* ℂ) (y : HeightOneSpectrum (𝓞 L) → Mˣ) (k : Lˣ) (n : M)
    (h : ((∏ᶠ v, Units.map e.toMonoidHom (y v) ^ ordF v k : ℂˣ) : ℂ) * e n = 1) (hn : σ n = e n) :
    ∏ᶠ v, (Units.map σ.toMonoidHom (y v) / Units.map e.toMonoidHom (y v)) ^ ordF v k = 1 := by
  have hf := GlobalTheory.HeckeProduct.finite_ordF k
  have hm : ∀ f : M →+* ℂ, ∏ᶠ v, Units.map f.toMonoidHom (y v) ^ ordF v k =
      Units.map f.toMonoidHom (∏ᶠ v, y v ^ ordF v k) := fun f => by
    rw [MonoidHom.map_finprod _ (fin_supp y hf)]
    simp only [map_zpow]
  simp only [div_zpow]
  rw [finprod_div_distrib (fin_supp _ hf) (fin_supp _ hf), hm, hm, div_eq_one]
  rw [hm] at h
  have h1 : ((∏ᶠ v, y v ^ ordF v k : Mˣ) : M) * n = 1 := e.injective (by rw [map_mul, map_one]; exact h)
  have h2 := congrArg σ h1
  rw [map_mul, map_one, hn, ← h] at h2
  exact Units.ext (mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h) h2)

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unram_of_chrEq {D : D7} {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ)
    (hu : ∀ P, χ.UnrAt P) : UnramEverywhere D c := by
  intro x hx h4 h5
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  apply Circle.ext
  rw [GlobalTheory.Mem.EtaTilde.val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc hu x hx, Circle.coe_one,
    Units.val_eq_one]
  refine finprod_eq_one_of_forall_eq_one fun P => ?_
  have e := GlobalTheory.Mem.EtaTilde.val_mul_inv (RingHom.id _) P (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := e
  have e1 : Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    refine le_antisymm ((h2 _).1 h4 P) ?_
    rw [← e']
    exact mul_le_of_le_one_right' ((h2 _).1 h5 P)
  rw [e1, WithZero.log_one, neg_zero, zpow_zero]

theorem exists_norm (D : D7) (k : D.host.E) :
    ∃ n ∈ D.host.K, D.what₂.embLL (D.embE n) = ∏ g, Formalism.L2.Host.embPsi D.host g k := by
  have hE := D.host.hostE_isGalois
  have h := Algebra.norm_eq_prod_automorphisms D.host.K k
  refine ⟨_, (Algebra.norm D.host.K k).2, (DFunLike.congr_fun D.embE_φ₀ _).trans ?_⟩
  change D.host.φ₀ (algebraMap D.host.K D.host.E _) = _
  rw [h, map_prod]
  exact (Fintype.prod_bijective _ (GlobalTheory.InducedType.galK_bijective D.host) _ _ fun _ => rfl).symm

theorem exists_conj {D : D7} (η : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq η χ)
    (hχ : Formalism.L2.Host.IsEtaT D.host χ)
    (hy : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ y : D.what₂.LL,
      D.what₂.embLL y = χ.val P * (((Real.sqrt (Ideal.absNorm P.asIdeal : ℕ))⁻¹ : ℝ) : ℂ))
    (σ : D.what₂.LL →+* ℂ) (hσ : OverK σ) : ∃ η', IsEtaConj σ η η' := by
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨_, -, hd, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  choose y hy using hy
  have hy0 : ∀ P, D.what₂.embLL (y P) ≠ 0 := fun P => by
    have : (0 : ℝ) < (Ideal.absNorm P.asIdeal : ℕ) :=
      Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
    rw [hy]
    exact mul_ne_zero (Units.ne_zero _) (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 this).ne'))
  let u : HeightOneSpectrum (𝓞 D.host.E) → D.what₂.LLˣ := fun P => Units.mk0 (y P) ((map_ne_zero _).1 (hy0 P))
  obtain ⟨ξ, x1, x2, x3⟩ := exists_classChar
    (fun P => Units.map σ.toMonoidHom (u P) / Units.map D.what₂.embLL.toMonoidHom (u P)) fun k => by
      obtain ⟨n, hn, hn'⟩ := exists_norm D k
      refine finprod_quot _ _ u k (D.embE n) ?_ (hσ n hn)
      rw [hn']
      exact finprod_alg _ hd.bij χ hχ.unr hχ.inf _ hy k
  obtain ⟨c, hc'⟩ := GlobalTheory.CharTransport.exists_chrEq D (χ * ξ) fun x => by
    change ‖((χ.1 x * ξ.1 x : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, hχ.unitary x, x1 x, one_mul]
  refine ⟨c, hc'.1, unram_of_chrEq hc' fun P x hx => ?_, fun P e he x hx => ⟨y P, ?_, ?_⟩⟩
  · rw [Formalism.L2.Host.HChar.loc_mul, hχ.unr P x hx, x2 P x hx, one_mul]
  · rw [hc.2 P e he _ x hx]
    exact hy P
  · have h1 : ((c x : Circle) : ℂ) = ((χ.val P * ξ.val P : ℂˣ) : ℂ) := hc'.2 P e he _ x hx
    rw [h1, x3, Units.val_mul, mul_right_comm, Units.val_div_eq_div_val]
    have h2 := hy P
    refine Eq.trans ?_ (congrArg (· * (σ (y P) / D.what₂.embLL (y P))) h2)
    exact (mul_div_cancel₀ _ (hy0 P)).symm

end GlobalTheory.EtaConjExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsMultIPOfModel
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLower

theorem IsMultIP₂ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (H : HMod (MMap M)) {N : ℂ} (h : ∀ x y, inner ℂ x y = N * ipM M μ 𝓕 (H.e x) (H.e y)) (x y : H.H) :
    ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c := by
  have h1 : ∀ x y : H.H, inner ℂ x y ≠ 0 → ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c := fun x y hxy => by
    by_contra hc
    apply hxy
    rw [h, ipM, dif_neg hc, mul_zero]
  by_cases hx : x = 0
  · subst hx
    exact ⟨0, fun v v' => by simp⟩
  by_cases hxy : inner ℂ x y = 0
  · obtain ⟨c, hc⟩ := h1 x (x + y) (by rw [inner_add_right, hxy, add_zero]; exact inner_self_ne_zero.2 hx)
    obtain ⟨c', hc'⟩ := h1 x x (inner_self_ne_zero.2 hx)
    refine ⟨c - c', fun v v' => ?_⟩
    have e : (fun g => star (H.e x v g) * H.e y v' g) =
        fun g => star (H.e x v g) * H.e (x + y) v' g - star (H.e x v g) * H.e x v' g := by
      funext g; simp [mul_add]
    rw [e]
    exact ⟨(hc v v').1.sub (hc' v v').1, by rw [integral_sub (hc v v').1 (hc' v v').1, (hc v v').2, (hc' v v').2, sub_mul]⟩
  · exact h1 x y hxy

theorem schurMult_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R h i σ _ _ _ T hT T' hT'
  obtain ⟨-, hr, hip⟩ := h i σ
  have hT1 : T ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hT
  have hT2 : T' ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hT'
  obtain ⟨x, rfl⟩ := hT1
  obtain ⟨y, rfl⟩ := hT2
  exact IsMultIP₂ (R.HW i σ) hip x y

end GlobalTheory.LiftLower

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaPForms
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace Topology ComplexOrder
open GlobalTheory.GalLift

namespace GlobalTheory.ConjThetaIntegral

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem conjVal_one {D : D7} {σ : D.what₂.LL →+* ℂ} {a b : ℂ} (h : ConjVal σ a b) (ha : a = 1) : b = 1 := by
  obtain ⟨y, h1, h2⟩ := h
  have : y = 1 := D.what₂.embLL.injective (by rw [h1, ha, map_one])
  rw [← h2, this, map_one]

theorem ext_continuous {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (χ' : (levEnv V β L).J →* ℂˣ) (hχ : ∀ k, (levEnv V β L).χ k = 1 → χ' k = 1)
    {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J χ') : Continuous (c.ext f) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact GlobalTheory.ThetaIntegrand.form_continuous (finHom V).rangeRestrict (GQ V) c.ρ hc.2.2.1
    ((GlobalTheory.ThetaIntegrand.eventually_level V β L).mono fun _ h => h.elim fun hk h1 => ⟨hk, hχ _ h1⟩) hf

theorem IsThetaP₂ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank)
    (χ' : (levEnv S β L).J →* ℂˣ) (hχ : ∀ k, (levEnv S β L).χ k = 1 → χ' k = 1)
    {X : Type} [AddCommGroup X] [Module ℂ X] (e : X →ₗ[ℂ] (Bridge.Gf S → c.W))
    (he : ∀ x, e x ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J χ')
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    {TK : Type} [AddCommGroup TK] [Module ℂ TK]
    (io : TK →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank) {K : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {μ : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hμ : IsMeasDef S K μ 𝓕) :
    ∃ thP, Lift.IsThetaP μ 𝓕 (fun g h φ => thetaKO om h g φ) (fun P => pt P) io (LinearMap.range (c.ext ∘ₗ e)) thP := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  refine GlobalTheory.ThetaIntegralLinear.exists_isThetaP_of_integrable μ 𝓕
    (fun g h => LinearMap.proj (R := ℂ) (φ := fun _ : WO S T => ℂ) 0 ∘ₗ om (h, g)) pt io _ ?_
  rintro ⟨_, x, rfl⟩ v g
  exact GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hom.std S T χS χT om hom hpos c.W (pt ∘ₗ io v)
    (fun w => hpt _) _ (ext_continuous c hc β L χ' hχ (he x)) (GlobalTheory.ThetaIntegrand.ext_invariant c (he x)) μ 𝓕 hμ.1.1 hμ.2 g

theorem exists_isThetaP_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), ∀ (σ : D.what₂.LL →+* ℂ) (μ' η' : (AE D)ˣ →* Circle) (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ c₀ c c₁ H j → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω → VecData R i σ f₀ f B → ∃ thP, Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ H.e)) thP := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i σ μ' η' c₀ c c₁ H j hj ω f₀ f B io hω hv
  have hm := hj.model
  obtain ⟨χ', hχ, hH⟩ := hm
  exact IsThetaP₂ hω (D.sp.V_sig _) (hR.models.vpos i) c hj.coef (R.βV i) (R.datVt i A.μ0) χ'
    (fun k hk => Units.ext (conjVal_one (hχ k) (congrArg Units.val hk))) H.e
    (fun x => hH.2.1.le (LinearMap.mem_range_self _ x))
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f) hv.theta io (hR.models.νV i A.μ0)

end GlobalTheory.ConjThetaIntegral

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKFiniteModuleIrreducibleUnitaryStatement
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kFiniteModule_irreducible_unitary : CompanionTheory.D.LK.KModExists := by
  first | exact @GlobalTheory.CompanionTheory.KModExistsStep.kModExists_holds | exact GlobalTheory.CompanionTheory.KModExistsStep.kModExists_holds | (intros; apply GlobalTheory.CompanionTheory.KModExistsStep.kModExists_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeBasisHermitianSpaceStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_basis_hermitian_space : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r), ∃ β : GL (Fin r) (EAf D), LatticeBasisLifts.IsLatBasis V hr β := by
  first | exact @GlobalTheory.LatAdelicBasis.exists_isLatBasis | exact GlobalTheory.LatAdelicBasis.exists_isLatBasis | (intros; apply GlobalTheory.LatAdelicBasis.exists_isLatBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelActionCuspFormRepresentationStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_action_cusp_form_representation : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → (∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c lev g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) → ∃ ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i), ∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.LevelRep.exists_cusp_rep | exact GlobalTheory.LevelRep.exists_cusp_rep | (intros; apply GlobalTheory.LevelRep.exists_cusp_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixAdjoinTensorUnramifiedOfCommuteSepar
section
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolyTensorCommutant

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)

def algK : Algebra K (KQ p K r) := inferInstanceAs (Algebra K (K ⊗[ℚ_[p]] Qr p r))

attribute [local instance] algK

theorem inclK_mul (a : K) (x : KQ p K r) : inclK p K r a * x = a • x := by
  rw [Algebra.smul_def]; rfl

def bQ : Module.Basis (Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r)) K (KQ p K r) :=
  Algebra.TensorProduct.basis K (Module.Basis.ofVectorSpace ℚ_[p] (Qr p r))

theorem bQ_apply (i) : bQ p K r i = inclQ p K r (Module.Basis.ofVectorSpace ℚ_[p] (Qr p r) i) :=
  Algebra.TensorProduct.basis_apply _ _

theorem mul_algebraMap_apply (n : ℕ) (M : Matrix (Fin n) (Fin n) (KQ p K r)) (c : KQ p K r) (i j : Fin n) :
    (M * algebraMap (KQ p K r) (Matrix (Fin n) (Fin n) (KQ p K r)) c) i j = M i j * c := by
  rw [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply,
    Matrix.mul_diagonal]

theorem exists_phi_eq : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ)
    (γ : Matrix (Fin n) (Fin n) K), 0 < r → γ.charpoly.Separable → ∀ X : Matrix (Fin n) (Fin n) (KQ p K r),
    Commute X (γ.map (inclK p K r)) → ∃ x, GlobalTheory.PolyTensor.phi p K n γ r x = X := by
  intro p _ K n r γ _ hsep X hX
  classical
  let Xc : Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r) → Matrix (Fin n) (Fin n) K :=
    fun i => X.map (fun x => (bQ p K r).coord i x)
  have hcomm : ∀ i, Commute (Xc i) γ := by
    intro i
    refine Matrix.ext fun a c => ?_
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) (KQ p K r) => (bQ p K r).coord i (M a c)) hX.eq
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, Xc] at h ⊢
    simp only [mul_comm (X _ _) (inclK p K r _), inclK_mul, map_smul, smul_eq_mul] at h
    simpa [mul_comm] using h
  have hmem : ∀ i, Xc i ∈ GlobalTheory.PolyTensor.polySub p K n γ := by
    intro i
    obtain ⟨q, hq⟩ := GlobalTheory.CentralizerSeparable.matrix_eq_aeval_of_commute n γ (Xc i) hsep (hcomm i)
    rw [GlobalTheory.PolyTensor.mem_polySub, hq]
    exact Polynomial.aeval_mem_adjoin_singleton K γ
  let y : Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r) → GlobalTheory.PolyTensor.PolyAlg p K n γ := fun i => ⟨Xc i, hmem i⟩
  let e := Module.Basis.ofVectorSpace ℚ_[p] (Qr p r)
  let s : Finset (Module.Basis.ofVectorSpaceIndex ℚ_[p] (Qr p r)) :=
    Finset.univ.biUnion (fun ac : Fin n × Fin n => ((bQ p K r).repr (X ac.1 ac.2)).support)
  refine ⟨∑ i ∈ s, y i ⊗ₜ e i, ?_⟩
  rw [map_sum]
  refine Matrix.ext fun a c => ?_
  simp only [GlobalTheory.PolyTensor.phi_tmul, Matrix.sum_apply, mul_algebraMap_apply, Matrix.map_apply]
  have hv : ∀ i, GlobalTheory.PolyTensor.val p K n γ (y i) = Xc i := fun i => rfl
  simp only [hv, Xc, Matrix.map_apply, inclK_mul, ← bQ_apply]
  simp only [e, ← bQ_apply, Module.Basis.coord_apply]
  have hsub : ((bQ p K r).repr (X a c)).support ⊆ s := fun i hi =>
    Finset.mem_biUnion.2 ⟨(a, c), Finset.mem_univ _, hi⟩
  rw [← Finsupp.sum_of_support_subset _ hsub (fun i k => k • bQ p K r i) (fun i _ => zero_smul _ _),
    ← Finsupp.linearCombination_apply, Module.Basis.linearCombination_repr]

end GlobalTheory.PolyTensorCommutant
end
end

