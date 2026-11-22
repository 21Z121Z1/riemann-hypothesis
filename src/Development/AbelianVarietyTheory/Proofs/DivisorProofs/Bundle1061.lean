import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIdealMulSpanMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisIffExistsIntegralMultiple
section
open Matrix NumberField IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem rat_mem_adicInt_iff (v : HeightOneSpectrum ℤ) (q : ℚ) :
    algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ ↔ v.valuation ℚ q ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q
  rw [← this]
  rfl

theorem valuation_int_eq_one (v : HeightOneSpectrum ℤ) {s : ℤ} (hs : s ∉ v.asIdeal) :
    v.valuation ℚ (s : ℚ) = 1 := by
  have e : ((s : ℚ)) = algebraMap ℤ ℚ s := rfl
  rw [e]
  refine le_antisymm (v.valuation_le_one s) (not_lt.1 fun h => hs ?_)
  exact (Ideal.dvd_span_singleton).1 ((v.valuation_lt_one_iff_dvd s).1 h)

theorem den_not_mem (v : HeightOneSpectrum ℤ) (q : ℚ) (hq : v.valuation ℚ q ≤ 1) :
    ((q.den : ℤ)) ∉ v.asIdeal := by
  intro hd
  have hlt : v.valuation ℚ ((q.den : ℤ) : ℚ) < 1 := by
    have e : (((q.den : ℤ)) : ℚ) = algebraMap ℤ ℚ (q.den : ℤ) := rfl
    rw [e]; exact (v.valuation_lt_one_iff_dvd _).2 (Ideal.dvd_span_singleton.2 hd)
  have hn : v.valuation ℚ ((q.num : ℤ) : ℚ) < 1 := by
    have e : ((q.num : ℤ) : ℚ) = q * ((q.den : ℤ) : ℚ) := by
      rw [Int.cast_natCast, Rat.mul_den_eq_num]
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hq) hlt
  have hnm : q.num ∈ v.asIdeal := by
    have e : ((q.num : ℤ) : ℚ) = algebraMap ℤ ℚ q.num := rfl
    rw [e] at hn
    exact Ideal.dvd_span_singleton.1 ((v.valuation_lt_one_iff_dvd _).1 hn)
  have hc : IsCoprime q.num (q.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using q.reduced
  obtain ⟨u, w, h⟩ := hc
  have h1 : (1 : ℤ) ∈ v.asIdeal := h ▸ add_mem (Ideal.mul_mem_left _ _ hnm) (Ideal.mul_mem_left _ _ hd)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem repr_via {K M ι κ : Type} [Field K] [AddCommGroup M] [Module K M] [Fintype ι] (c : Module.Basis κ K M)
    (d : Module.Basis ι K M) (z : M) (i : κ) :
    c.repr z i = ∑ j, d.repr z j * c.repr (d j) i := by
  conv_lhs => rw [← d.sum_repr z]
  rw [map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem isIntB_one_tmul_iff (v : HeightOneSpectrum ℤ) {L κ : Type} [Field L] [Algebra ℚ L]
    (ℓ : Module.Basis κ ℚ L) (z : L) :
    IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] z) ↔ ∀ i, v.valuation ℚ (ℓ.repr z i) ≤ 1 := by
  unfold IsIntB
  simp only [repr_tmul_apply, one_mul, rat_mem_adicInt_iff]

theorem isIntB_one_tmul_iff_exists_isIntegral : ∀ (L : Type) [Field L] [NumberField L] (κ : Type)
    (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ z : L,
      IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] z) ↔ ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * z) := by
  intro L _ _ κ ℓ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex ℓ
  set b := integralBasis L
  have h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × Module.Free.ChooseBasisIndex ℤ (𝓞 L),
      algebraMap ℚ (v.adicCompletion ℚ) (ℓ.repr (b t.2) t.1) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have h2 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : Module.Free.ChooseBasisIndex ℤ (𝓞 L) × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (ℓ t.2) t.1) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (h1.and h2)
  refine ⟨hfin.toFinset, fun v hv z => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨h1v, h2v⟩ := hv
  simp only [rat_mem_adicInt_iff] at h1v h2v
  rw [isIntB_one_tmul_iff]
  constructor
  · intro hz
    have hb : ∀ j, v.valuation ℚ (b.repr z j) ≤ 1 := fun j => by
      rw [repr_via b ℓ z j]
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [map_mul]
      exact mul_le_one' (hz i) (h2v (j, i))
    refine ⟨∏ j, ((b.repr z j).den : ℤ), ?_, ?_⟩
    · intro hd
      obtain ⟨j, _, hj⟩ := (Ideal.IsPrime.prod_mem_iff (hp := v.isPrime)).1 hd
      exact den_not_mem v _ (hb j) hj
    · set d : ℤ := ∏ j, ((b.repr z j).den : ℤ) with hd
      have hdv : ∀ j, ((b.repr z j).den : ℤ) ∣ d := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
      have hmem : (d : L) * z ∈ Submodule.span ℤ (Set.range b) := by
        rw [Submodule.mem_span_range_iff_exists_fun]
        refine ⟨fun j => d / ((b.repr z j).den : ℤ) * (b.repr z j).num, ?_⟩
        conv_rhs => rw [← b.sum_repr z]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hc : (((d / ((b.repr z j).den : ℤ) * (b.repr z j).num : ℤ)) : ℚ) = (d : ℚ) * b.repr z j := by
          have e1 := Int.ediv_mul_cancel (hdv j)
          conv_rhs => rw [← e1]
          rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, mul_assoc, mul_comm ((b.repr z j).den : ℚ),
            Rat.mul_den_eq_num]
        rw [← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, hc, mul_smul]
      obtain ⟨y, hy⟩ := (mem_span_integralBasis L).1 hmem
      rw [← hy]
      exact RingOfIntegers.isIntegral_coe y
  · rintro ⟨s, hs, hint⟩ i
    have hmem : (s : L) * z ∈ Submodule.span ℤ (Set.range b) := (mem_span_integralBasis L).2 ⟨⟨_, hint⟩, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
    have hsz : ℓ.repr ((s : L) * z) i = (s : ℚ) * ℓ.repr z i := by
      rw [← zsmul_eq_mul, map_zsmul, Finsupp.smul_apply, zsmul_eq_mul]
    have hval : v.valuation ℚ (ℓ.repr ((s : L) * z) i) ≤ 1 := by
      rw [← hc, map_sum, Finsupp.finset_sum_apply]
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_zsmul, Finsupp.smul_apply, zsmul_eq_mul, map_mul]
      have e : ((c j : ℤ) : ℚ) = algebraMap ℤ ℚ (c j) := rfl
      rw [e]
      exact mul_le_one' (v.valuation_le_one (c j)) (h1v (i, j))
    rwa [hsz, map_mul, valuation_int_eq_one v hs, one_mul] at hval

end GlobalTheory.AdicSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyIdeleMapInfIdeleNegOne
section
open NumberField IsDedekindDomain

noncomputable section

open Formalism.L2.Host GlobalTheory.UnitaryBC GlobalTheory.CuspRep ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem continuous_infAdeleMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap K L) :=
  continuous_fst.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp
    (Continuous.prodMk_left (0 : FiniteAdeleRing (𝓞 K) K)))

omit [IsCMField E] in
theorem continuous_finAdeleMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L) :=
  continuous_snd.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp
    (Continuous.prodMk_right (0 : InfiniteAdeleRing K)))

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in
theorem pInf_ideleMap_infIdele (v : InfinitePlace (maximalRealSubfield E)) (w : InfinitePlace E) :
    pInf E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) : Ad E) w =
      if w.comap (algebraMap (maximalRealSubfield E) E) = v then -1 else 1 := by
  show (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
    (NumberField.LiesOver.completionMap (v := w.comap (algebraMap (maximalRealSubfield E) E)) (w := w)
      (Pi.mulSingle v ((-1 : (v.Completion)ˣ) : v.Completion) (w.comap (algebraMap (maximalRealSubfield E) E)))) = _
  split_ifs with h
  · subst h
    rw [Pi.mulSingle_eq_same]
    simp
  · rw [Pi.mulSingle_eq_of_ne h]
    simp

theorem pFin_ideleMap_infIdele (v : InfinitePlace (maximalRealSubfield E)) :
    pFin E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) : Ad E) = 1 :=
  map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in

def iAt (v : InfinitePlace (maximalRealSubfield E)) : (Cinf E)ˣ where
  val w := if w.comap (algebraMap (maximalRealSubfield E) E) = v then Complex.I else 1
  inv w := if w.comap (algebraMap (maximalRealSubfield E) E) = v then -Complex.I else 1
  val_inv := by
    funext w
    simp only [Pi.mul_apply, Pi.one_apply]
    split_ifs <;> simp
  inv_val := by
    funext w
    simp only [Pi.mul_apply, Pi.one_apply]
    split_ifs <;> simp

theorem apply_ideleMap_infIdele_neg_one (χ : HChar E)
    (hc : ∀ x : (AdeleRing (𝓞 E) E)ˣ, χ.1 (Units.map (conjAd E).toMonoidHom x) = χ.1 x)
    (v : InfinitePlace (maximalRealSubfield E)) :
    χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))) = 1 := by
  classical
  have h1 : pInf E (infId E (iAt v)).val = (iAt v).val := by
    change (infEq E).symm (1 - infEq E 1 + infEq E (iAt v).val) = _
    simp
  have h2 : pFin E (infId E (iAt v)).val = 1 := by
    change (1 : Af E) - 0 + 0 = 1
    simp
  have key : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) =
      infId E (iAt v) * (Units.map (conjAd E).toMonoidHom (infId E (iAt v)))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    refine Units.ext (ad_ext ?_ ?_)
    · funext w
      change pInf E ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))).val *
        conjAd E (infId E (iAt v)).val) w = pInf E (infId E (iAt v)).val w
      rw [map_mul, Pi.mul_apply, GlobalTheory.ThetaPull.pInf_conjAd, h1, pInf_ideleMap_infIdele]
      change _ * starRingEnd ℂ ((iAt v).val w) = (iAt v).val w
      simp only [iAt]
      split_ifs <;> simp
    · change pFin E ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))).val *
        conjAd E (infId E (iAt v)).val) = pFin E (infId E (iAt v)).val
      rw [map_mul, GlobalTheory.ThetaPull.pFin_conjAd, h2,
        pFin_ideleMap_infIdele, map_one, one_mul]
  rw [key, map_mul, map_inv, hc, mul_inv_cancel]

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem apply_conjAd_of_isAbsPow {χ : HChar E} {u : ℝ} (h : χ.IsAbsPow u) (x : (AdeleRing (𝓞 E) E)ˣ) :
    χ.1 (Units.map (conjAd E).toMonoidHom x) = χ.1 x := by
  have e : χ * GlobalTheory.ThetaPull.thetaChar χ = 1 := GlobalTheory.HeckeUnrTrivial.eq_one_of_val_eq_one _ fun v _ => by
    have h2 := (GlobalTheory.ThetaPull.isAbsPow_thetaChar h).2.1 v
    have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    refine Units.ext ?_
    rw [HChar.val_mul, Units.val_mul, h.2.1 v, h2, Units.val_one, ← Complex.cpow_add _ _ h0]
    simp
  have h3 := congrArg (fun c : HChar E => c.1 x) e
  change χ.1 x * (χ.1 (Units.map (conjAd E).toMonoidHom x))⁻¹ = 1 at h3
  exact (mul_inv_eq_one.1 h3).symm

theorem adeleMap_conj_eq (x : AdeleRing (𝓞 E) E) :
    @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap E E _ _ _ _
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra x = conjAd E x := by
  letI : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  have key : ∀ k : E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap E E (algebraMap E (AdeleRing (𝓞 E) E) k) =
      conjAd E (algebraMap E (AdeleRing (𝓞 E) E) k) := by
    intro k
    rw [conjAd_algebraMap]
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap E E k
  have hsymm : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  refine Prod.ext ?_ ?_
  · exact congrFun ((InfiniteAdeleRing.denseRange_algebraMap E).equalizer (continuous_infAdeleMap E E)
      ((continuous_infEq E).comp (continuous_star.comp hsymm))
      (funext fun k => congrArg Prod.fst (key k))) x.1
  · exact congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := E)).equalizer
      (continuous_finAdeleMap E E) (continuous_conjFin _)
      (funext fun k => congrArg Prod.snd (key k))) x.2

theorem ideleConj_eq (x : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E x = Units.map (conjAd E).toMonoidHom x :=
  Units.ext (adeleMap_conj_eq x.val)

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def resReal (χ : HChar E) : HChar (maximalRealSubfield E) :=
  ⟨χ.1.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E),
    χ.2.1.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap _ E), fun k =>
      (congrArg χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele _ E k)).trans (χ.2.2 _)⟩

theorem resReal_apply (χ : HChar E) (x : (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))ˣ) :
    (resReal χ).1 x = χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) := rfl

theorem resReal_locInf_neg_one {χ : HChar E} {u : ℝ} (h : χ.IsAbsPow u) (v : InfinitePlace (maximalRealSubfield E)) :
    (resReal χ).locInf v (-1) = 1 :=
  apply_ideleMap_infIdele_neg_one χ (apply_conjAd_of_isAbsPow h) v

end GlobalTheory.PolChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicExpansionInDictionary
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.Descent

theorem lact_mul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ γ' : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) := by
  funext τ
  show ((γ * γ' : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ =
    (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ' : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem lact_rmul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) =
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) * mat b τ
  rw [Matrix.mul_assoc]

theorem archM_mul {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (a b : GA D V) :
    archM V θ (a * b) = archM V θ a * archM V θ b := by
  simp only [archM, map_mul, Units.val_mul, Matrix.map_mul]

theorem isUnit_of_negFirst {D : D7} {V : HSp D} {q : ℕ} {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : NegFirst V q x) (ρ : D.what₂.Tau) : IsUnit (x ρ) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  have h1 := congrArg Matrix.det (h ρ)
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at h1
  refine (Finset.prod_ne_zero_iff.2 fun c _ => ?_) h1.symm
  split_ifs <;> simp

theorem archM_eq_of_frIs {D : D7} {θ : InfFam D} {V : HSp D} {r : ℕ} {hr : V.rank = r} {X : Data D.host.E r}
    {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hM : ModelOf V hr X) (hx : NegFirst V X.p0 x)
    {u u' : GA D V} {y : Frame X.Ψ r} (h : FrIs θ V hr X x u y) (h' : FrIs θ V hr X x u' y) (ρ : D.what₂.Tau) :
    archM V (θ ρ) u = archM V (θ ρ) u' := by
  have e := (h ρ ⟨tauE D ρ, (hM.1 _).2 ⟨ρ, rfl⟩⟩ rfl).symm.trans (h' ρ ⟨tauE D ρ, (hM.1 _).2 ⟨ρ, rfl⟩⟩ rfl)
  exact (isUnit_of_negFirst hx ρ).mul_right_cancel ((Matrix.reindex _ _).injective e)

theorem descent : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → Data D.host.E r) (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V)) (x₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (ψ : GA D V → ℂ), IsInfFam θ → BaseDict θ V hr X dict Kf x₀ → (∀ k, ∀ γ ∈ (X k).Γ, (X k).χ (la k) γ = 1) → (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) → (∀ k ∈ Kf, ∀ g, ψ (g * k) = ψ g) → (∀ (k : Comp) (g : GA D V), ∃ Q : Frame (X k).Ψ r → ℂ, DifferentiableOn ℂ Q (X k).dom ∧ (∀ y ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, Q (rmul y b) = bchar (la k) b * Q y) ∧ ∀ u ∈ GinfC V, ∀ y, FrIs θ V hr (X k) x₀ u y → Q y = ψ (g * u)) → ∃ P : FDSec X, (∀ k, (X k).IsSec (la k) (P k)) ∧ (∀ g, ψ g = P (dict g).1 (dict g).2) ∧ ∀ C : ℝ, (∀ g, ‖ψ g‖ ≤ C) → ∀ k, ∀ y ∈ (X k).dom, (X k).pnorm (la k) (P k) y ≤ C := by
  intro D θ V r hr Comp X dict Kf x₀ la ψ hθ hB hχ hL hR hQ
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hF : ∀ (k : Comp) (h h' : GA D V) (z : Frame (X k).Ψ r), ∀ γ ∈ (X k).Γ,
      dict h = ⟨k, z⟩ → dict h' = ⟨k, lact γ z⟩ → ψ h' = ψ h := by
    intro k h h' z γ hγ e e'
    have key : ∀ p : Σ k, Frame (X k).Ψ r, p = ⟨k, z⟩ →
        ∃ γ' ∈ (X p.1).Γ, dict h' = ⟨p.1, lact γ' p.2⟩ := by
      rintro p rfl
      exact ⟨γ, hγ, e'⟩
    obtain ⟨δ, hδ, κ, hκ, rfl⟩ := hB3 h h' (key _ e)
    rw [hR κ hκ, hL δ hδ]
  have hK : ∀ k : Comp, ∃ Q : Frame (X k).Ψ r → ℂ, DifferentiableOn ℂ Q (X k).dom ∧
      (∀ y ∈ (X k).dom, ∀ b ∈ Bor (X k).Ψ r, Q (rmul y b) = bchar (la k) b * Q y) ∧
      ∀ y, IsUnitFr (X k) y → ∃ h, ∃ γ ∈ (X k).Γ, dict h = ⟨k, lact γ y⟩ ∧ Q y = ψ h := by
    intro k
    obtain ⟨hM, hN, g, rfl⟩ := hB1 k
    obtain ⟨U1, U2, -, U4, -⟩ := GlobalTheory.T.frame_unit_correspondence D θ V r hr (X (dict g).1) x₀ hθ hM hN
    obtain ⟨γ, hγ, hfr, hu⟩ := hB2 g
    obtain ⟨a, ha, hfa⟩ := U2 _ (U1 _ _ hfr)
    have ea := archM_eq_of_frIs hM hN hfr hfa
    obtain ⟨Q, hQ1, hQ2, hQ3⟩ := hQ (dict g).1 (γ * g * a⁻¹)
    refine ⟨Q, hQ1, hQ2, fun y hy => ?_⟩
    obtain ⟨v, hv, hfv⟩ := U2 y hy
    obtain ⟨γ', hγ', y', hd, hfy'⟩ := hu (a⁻¹ * v) (mul_mem (inv_mem ha) hv)
    have hfy : FrIs θ V hr (X (dict g).1) x₀ v y' := by
      intro ρ τ hτ
      rw [hfy' ρ τ hτ, archM_mul V _ (γ * g), ea ρ, ← archM_mul, mul_inv_cancel_left]
    obtain rfl : y' = y := U4 v _ _ hfy hfv
    refine ⟨_, γ', hγ', hd, ?_⟩
    rw [hQ3 v hv _ hfv, ← hL γ hγ (g * (a⁻¹ * v))]
    simp only [mul_assoc]
  choose P hP1 hP2 hP3 using hK
  refine ⟨P, fun k => ⟨hP1 k, hP2 k, fun γ hγ x hx => ?_⟩, fun g => ?_, fun C hC k x hx => ?_⟩
  · obtain ⟨G1, G2, -, -, G5, -⟩ := GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames D.host.E r (X k)
    obtain ⟨y, hy, b, hb, rfl⟩ := G2 x hx
    have hy' := G5 y hy γ hγ
    obtain ⟨h, γ₁, hγ₁, hd, he⟩ := hP3 k y hy
    obtain ⟨h', γ₂, hγ₂, hd', he'⟩ := hP3 k _ hy'
    have e : ψ h' = ψ h := by
      refine hF k h h' _ (γ₂ * γ * γ₁⁻¹) (mul_mem (mul_mem hγ₂ hγ) (inv_mem hγ₁)) hd ?_
      rw [hd', ← lact_mul, ← lact_mul, inv_mul_cancel_right]
    rw [hχ k γ hγ, one_mul, lact_rmul, hP2 k _ (G1 _ hy') b hb, hP2 k _ (G1 _ hy) b hb, he, he', e]
  · obtain ⟨hM, hN, -⟩ := hB1 (dict g).1
    obtain ⟨U1, -⟩ := GlobalTheory.T.frame_unit_correspondence D θ V r hr (X (dict g).1) x₀ hθ hM hN
    obtain ⟨γ, -, hfr, -⟩ := hB2 g
    obtain ⟨h, γ₁, hγ₁, hd, he⟩ := hP3 _ _ (U1 _ _ hfr)
    rw [he]
    exact (hF _ g h _ γ₁ hγ₁ rfl hd).symm
  · obtain ⟨G1, G2, -, -, -, -, G7⟩ := GlobalTheory.T.gramSchmidt_flagDomain_orthonormalFrames D.host.E r (X k)
    obtain ⟨y, hy, b, hb, rfl⟩ := G2 x hx
    rw [G7 (la k) (P k) y hy b hb (hP2 k y (G1 y hy) b hb)]
    obtain ⟨h, -, -, -, he⟩ := hP3 k y hy
    rw [he]
    exact hC h

end GlobalTheory.HolRead.Descent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaTwistedInvolutionEqComplexConjOfMarked
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

theorem iM_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ (τ : FM P →+* ℂ) (a : FM P), τ (iM P a) = (starRingEnd ℂ) (τ a) := by
  intro p _ G P μ ha hM τ a
  set φ : G.F →+* ℂ := τ.comp (algebraMap G.F (FM P)) with hφ
  have hroot : P.pol.eval₂ φ (τ (AdjoinRoot.root P.pol)) = 0 := by
    rw [hφ, ← Polynomial.hom_eval₂]
    have : P.pol.eval₂ (algebraMap G.F (FM P)) (AdjoinRoot.root P.pol) = 0 := AdjoinRoot.eval₂_root P.pol
    rw [this, map_zero]
  have hn := GlobalTheory.LKMid.MarkEll.mark_ell p G P μ ha hM φ _ hroot
  set z := τ (AdjoinRoot.root P.pol) with hz
  have hc0 : ((P.c : ℚ) : ℂ) ≠ 0 := by exact_mod_cast (P.c.ne_zero)
  have hzc : (starRingEnd ℂ) z * z = ((P.c : ℚ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; exact_mod_cast hn
  have hz0 : z ≠ 0 := by
    rintro h; rw [h, mul_zero] at hzc; exact hc0 hzc.symm
  have hiz : τ (iM P (AdjoinRoot.root P.pol)) * z = ((P.c : ℚ) : ℂ) := by
    rw [hz, ← map_mul, iM_root_mul]
    exact eq_ratCast (τ.comp (algebraMap ℚ (FM P))) _
  have h1 : τ (iM P (AdjoinRoot.root P.pol)) = (starRingEnd ℂ) z :=
    mul_right_cancel₀ hz0 (hiz.trans hzc.symm)
  have hext : τ.comp (iM P).toRingHom = (starRingEnd ℂ).comp τ := by
    apply AdjoinRoot.ringHom_ext
    · ext x
      simp only [RingHom.comp_apply]
      change τ (iM P (algebraMap G.F (FM P) x)) = (starRingEnd ℂ) (τ (algebraMap G.F (FM P) x))
      rw [iM_algF]
      exact IsCMField.complexEmbedding_complexConj G.F φ x
    · simpa using h1
  exact congrArg (fun f => f a) hext

end GlobalTheory.StabFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedCoordinatesPPowerDenominator
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_coordinates_p_power_denominator : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : ℝ), ∃ e : ℕ, ∀ c : G.C, (∀ (w : Fin G.m) (a b : Fin G.n), ‖((G.rho w c a b : G.Fw w) : PadicAlgCl p)‖ ≤ B ∧ ‖((G.rho w (sh G c) a b : G.Fw w) : PadicAlgCl p)‖ ≤ B) → ∀ i, ∃ (k : ℤ) (m : ℕ), ¬ p ∣ m ∧ (Module.finBasis ℚ G.C).repr c i * (p : ℚ) ^ e = k / m := by
  first | (exact @GlobalTheory.CoordP.coord_bound) | (exact GlobalTheory.CoordP.coord_bound) | (intros; apply GlobalTheory.CoordP.coord_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorIntegralPower
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_denominator_integral_power : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (B : ℝ), ∃ m₀ : ℕ, ∀ (c : K) (D : ℕ), (∃ m : ℕ, IsIntegral ℤ ((p : K) ^ m * D * c)) → (∀ φ : K →+* PadicAlgCl p, ‖φ c‖ ≤ B) → IsIntegral ℤ ((p : K) ^ m₀ * D * c) := by
  first | (exact @GlobalTheory.IntAwayP.exists_pow_mul_isIntegral) | (exact GlobalTheory.IntAwayP.exists_pow_mul_isIntegral) | (intros; apply GlobalTheory.IntAwayP.exists_pow_mul_isIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardPowLeEncardSeminormBallDigitSums
section
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr.DigitSums

theorem mono {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (hB : IsBallFam Λ B) {r r' : ℝ} (h : r ≤ r') {x : G} (hx : x ∈ B r) : x ∈ B r' := by
  have h0 := hB.zero_mem (r' - r) (by linarith)
  have := hB.sub_mem r (r' - r) x 0 hx h0
  simpa using this

end GlobalTheory.VolBr.DigitSums

namespace GlobalTheory.VolBr

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerScalarPadicBounded
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_scalar_padic_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r) (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) → ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom → ‖(((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])‖ ≤ 1 := by
  first | (exact @GlobalTheory.StabFin.sim_norm_le_one) | (exact GlobalTheory.StabFin.sim_norm_le_one) | (intros; apply GlobalTheory.StabFin.sim_norm_le_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactNormalSubgroupDescentInvariantsStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_normal_subgroup_descent_invariants : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ N N' : Subgroup G) [DiscreteTopology Γ]
    [LocallyCompactSpace N] [LocallyCompactSpace N'], N' ≤ N → (∀ p ∈ N, ∀ m ∈ N', p * m * p⁻¹ ∈ N') →
    GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' →
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
      [MeasurableSpace V] [BorelSpace V] (Λ : AddSubgroup V) (s : V → G) (π : N → V),
      Continuous s → (∀ v w, s (v + w) = s v * s w) → (∀ v, s v ∈ N) → Continuous π →
      (∀ a b : N, π (a * b) = π a + π b) → (∀ (a : N) (v : V), (a : G) = s v → π a = v) →
      (∀ a : N, π a = 0 ↔ (a : G) ∈ N') → (∀ v ∈ Λ, s v ∈ Γ) → (∀ a : N, (a : G) ∈ Γ → π a ∈ Λ) →
      ∀ φ : G → ℂ, GlobalTheory.AutomorphicL2Unitary.LeftInv Γ φ → Continuous φ → (∀ m ∈ N', ∀ g, φ (m * g) = φ g) →
      ∀ (μ : MeasureTheory.Measure V) (𝓕 : Set V), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Λ 𝓕 μ →
        ∀ x : G, ∫ v in 𝓕, φ (s v * x) ∂μ = μ.real 𝓕 • GlobalTheory.Cusp.constTermOn Γ N φ x := by
  first | exact @GlobalTheory.Cusp.Shear.integral_section_eq_constTermOn | exact GlobalTheory.Cusp.Shear.integral_section_eq_constTermOn | (intros; apply GlobalTheory.Cusp.Shear.integral_section_eq_constTermOn <;> assumption)
end

