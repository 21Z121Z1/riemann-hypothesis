import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleFibre
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

set_option linter.unusedSectionVars false

namespace NefAmpleFibreAlt

section Reduction

variable {K : Type} {ι : K → Type} (p : ℕ)

abbrev red : MRing ι →+* MRingOver (ZMod p) ι := MvPolynomial.map (Int.castRingHom (ZMod p))

theorem red_surjective : Function.Surjective (red (ι := ι) p) :=
  MvPolynomial.map_surjective _ (fun x => ZMod.intCast_surjective x)

theorem ker_red_le {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    RingHom.ker (red (ι := ι) p) ≤ J := by
  rw [MvPolynomial.ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton, Ideal.span_le,
    Set.singleton_subset_iff]
  simpa using hp

theorem mem_map_red_iff {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (g : MRing ι) :
    red p g ∈ J.map (red p) ↔ g ∈ J := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ (red_surjective p), sup_eq_left.mpr]
  rw [← RingHom.ker_eq_comap_bot]
  exact ker_red_le p hp

theorem ringKrullDim_red {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) :
    ringKrullDim (MRingOver (ZMod p) ι ⧸ J.map (red p)) = ringKrullDim (MRing ι ⧸ J) := by
  have e : J = RingHom.ker ((Ideal.Quotient.mk (J.map (red p))).comp (red p)) := by
    ext g
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, mem_map_red_iff p hp]
  exact (ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq e).trans
    (RingHom.quotientKerEquivOfSurjective (Ideal.Quotient.mk_surjective.comp (red_surjective p))))).symm

end Reduction

section Homog

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {R S : Type} [CommRing R] [CommRing S]

theorem map_weightedHomogeneousComponent (f : R →+* S) (w : (Σ k, ι k) → K → ℕ) (b : K → ℕ)
    (g : MRingOver R ι) :
    weightedHomogeneousComponent w b (MvPolynomial.map f g) =
      MvPolynomial.map f (weightedHomogeneousComponent w b g) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_map, coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem isMultiHomogIdeal_map (f : R →+* S) {V : Ideal (MRingOver R ι)} (hV : IsMultiHomogIdeal V) :
    IsMultiHomogIdeal (V.map (MvPolynomial.map f)) := by
  obtain ⟨T, hT, rfl⟩ := hV
  refine ⟨MvPolynomial.map f '' T, ?_, by rw [Ideal.map_span]⟩
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨a, ha⟩ := hT g hg
  exact ⟨a, fun m hm => ha m (support_map_subset _ _ hm)⟩

theorem isMultiHomogIdeal_comap (f : R →+* S) {W : Ideal (MRingOver S ι)} (hW : IsMultiHomogIdeal W) :
    IsMultiHomogIdeal (W.comap (MvPolynomial.map f)) := by
  classical
  have hW' := (Bridge.isMultiHomogIdeal_iff (R := S) W).mpr hW
  refine (Bridge.isMultiHomogIdeal_iff (R := R) _).mp fun g hg b => ?_
  rw [Ideal.mem_comap, ← map_weightedHomogeneousComponent]
  exact hW' _ hg b

end Homog

section Nef

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem nefOnF_map_red (ℓ : ℕ) [Fact ℓ.Prime] (hGeo : GeoNumStatement ι) {I : IFamily (ZMod ℓ) ι}
    (hI : IsFieldIntersection I) {P : Ideal (MRing ι)} {α : K → ℤ} (hN : NefOnFibres P α) :
    KH.NefOnF I (P.map (red ℓ)) α := by
  intro W' hW' hle
  obtain ⟨⟨hW'p, hW'h, hW'r⟩, hW'd⟩ := hW'
  set W := W'.comap (red ℓ) with hWdef
  have hmap : W.map (red ℓ) = W' := Ideal.map_comap_of_surjective _ (red_surjective ℓ) W'
  have hpW : ((ℓ : ℕ) : MRing ι) ∈ W := by
    have h0 : ((ℓ : ℕ) : MRingOver (ZMod ℓ) ι) = 0 := by
      rw [← map_natCast (C : ZMod ℓ →+* MRingOver (ZMod ℓ) ι), ZMod.natCast_self, map_zero]
    rw [hWdef, Ideal.mem_comap, map_natCast, h0]
    exact W'.zero_mem
  have hWm : IsMultiProjPrime W := by
    refine ⟨Ideal.comap_isPrime _ W', isMultiHomogIdeal_comap _ hW'h, fun k => ?_⟩
    obtain ⟨i, hi⟩ := hW'r k
    refine ⟨i, ?_⟩
    rw [hWdef, Ideal.mem_comap, map_X]
    exact hi
  have hPW : P ≤ W := Ideal.map_le_iff_le_comap.mp hle
  have hdim : ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← ringKrullDim_red ℓ hpW, hmap, hW'd]
  have hchar : charOf W ≠ 0 := by
    intro h0
    have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0 := Int.natAbs_eq_zero.mp h0
    have hmem : ((ℓ : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, map_natCast]
      exact hpW
    rw [← Submodule.IsPrincipal.span_singleton_generator (W.comap (C : ℤ →+* MRing ι)), hg,
      Ideal.mem_span_singleton, zero_dvd_iff] at hmem
    exact (Fact.out : ℓ.Prime).ne_zero (by exact_mod_cast hmem)
  have hWp : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))) 1 := by
    show IsProjVarF (W.map (red ℓ)) 1
    rw [hmap]
    exact ⟨⟨hW'p, hW'h, hW'r⟩, hW'd⟩
  have h := hN W hWm hPW hchar hdim
  rw [hGeo ℓ I hI W 1 _ hWm hpW hWp] at h
  change 0 ≤ I (W.map (red ℓ)) 1 (fun _ => α) at h
  rw [hmap] at h
  convert h using 2
  funext j
  fin_cases j
  rfl

end Nef

end NefAmpleFibreAlt

open NefAmpleFibreAlt in

theorem NefAmpleFibre.proof (hK : KleimanScheme.Statement)
    (hGeo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], GeoNumStatement ι)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι) :
    NefAmpleFibre.Statement := by
  intro K _ _ ι _ _ Ω _ y D α b a ℓ hP hN hb ha hℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨I, hI, -⟩ := hR4 (ZMod ℓ) K ι
  have e : ((b : ℤ) • α + fun _ => (a : ℤ)) = (b • α + fun _ => (a : ℤ)) := by
    rw [natCast_zsmul]
  rw [e]
  exact hK (ZMod ℓ) K ι I (fibreIdeal ℓ y) α b a hI (isMultiHomogIdeal_map _ hP.2.1.2.1)
    (nefOnF_map_red ℓ (hGeo K ι) hI hN) hb ha

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ κ, Fintype (ι κ)] {Ω : Type} [Field Ω]

noncomputable def expo (d : K → ℕ) : K →₀ ℕ := Finsupp.equivFunOnFinite.symm d

@[simp] theorem coe_expo (d : K → ℕ) : ⇑(expo d) = d := Finsupp.coe_equivFunOnFinite_symm d

theorem mapDomain_fst_apply (μ : (Σ κ, ι κ) →₀ ℕ) (κ : K) :
    μ.mapDomain Sigma.fst κ = ∑ i, μ ⟨κ, i⟩ := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_sigma]
  simp [Finsupp.single_apply]

omit [Fintype K] [∀ κ, Fintype (ι κ)] in

theorem mConeMap_monomial (y : (Σ κ, ι κ) → Ω) (μ : (Σ κ, ι κ) →₀ ℕ) (r : ℤ) :
    mConeMap y (monomial μ r) = monomial (μ.mapDomain Sigma.fst) (aeval y (monomial μ r)) := by
  rw [mConeMap, aeval_monomial, aeval_monomial, monomial_eq,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mConeMap_of_homog (y : (Σ κ, ι κ) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = monomial (expo d) (aeval y g) := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [mConeMap_monomial]
  have hμd : μ.mapDomain Sigma.fst = expo d := by
    ext κ
    rw [mapDomain_fst_apply, coe_expo, hg μ hμ κ]
  rw [hμd]

def formRing (y : (Σ κ, ι κ) → Ω) : Subalgebra ℤ (MvPolynomial K Ω) where
  carrier := {F | ∀ m : K →₀ ℕ, coeff m F ∈ secM y ⇑m}
  mul_mem' := by
    classical
    intro F G hF hG m
    rw [coeff_mul]
    refine sum_mem fun x hx => ?_
    have hm : ⇑x.1 + ⇑x.2 = ⇑m := by rw [← Finsupp.coe_add, (Finset.HasAntidiagonal.mem_antidiagonal.mp hx)]
    rw [← hm]
    exact secM_mul_mem y (hF x.1) (hG x.2)
  add_mem' := by
    intro F G hF hG m
    rw [coeff_add]
    exact add_mem (hF m) (hG m)
  algebraMap_mem' := by
    classical
    intro n m
    rw [MvPolynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      have h1 : (1 : Ω) ∈ secM y ⇑(0 : K →₀ ℕ) :=
        Submodule.subset_span ⟨1, ProjLine.isMultiHomog_one, map_one _⟩
      have := zsmul_mem h1 n
      simpa using this
    · exact zero_mem _

theorem mConeMap_mem_formRing (y : (Σ κ, ι κ) → Ω) (f : MRing ι) : mConeMap y f ∈ formRing y := by
  classical
  induction f using MvPolynomial.induction_on with
  | C n =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ n
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hp fun m => ?_
    rw [mConeMap, aeval_X, coeff_C_mul, coeff_X]
    split_ifs with h
    · subst h
      refine Submodule.subset_span ⟨X q, ?_, by simp⟩
      convert ProjLine.isMultiHomog_X (ι := ι) q using 1
      funext κ
      simp [Finsupp.single_apply, eq_comm]
    · simp

theorem monomial_mem_range (y : (Σ κ, ι κ) → Ω) {d : K → ℕ} {v : Ω} (hv : v ∈ secM y d) :
    monomial (expo d) v ∈ (mConeMap y).range := by
  change v ∈ Submodule.span ℤ _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g, mConeMap_of_homog y hg⟩
  | zero => simp
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul n x _ hx => rw [map_zsmul]; exact zsmul_mem hx n

theorem proof (h : KH.CondStatement) : NmSectionsFinite.Statement := by
  unfold NmSectionsFinite.Statement
  intro K _ ι _ Ω _ y a ha hy hbir τ₂
  classical
  obtain ⟨k, c, -, hc0, hc⟩ := h K ι Ω y a ha hy hbir
  set R := (mConeMap y).range
  have : IsNoetherianRing R :=
    isNoetherianRing_of_surjective (MRing ι) R (mConeMap y).rangeRestrict.toRingHom
      (mConeMap y).rangeRestrict_surjective

  set G : Set (MvPolynomial K Ω) := {F | ∃ τ, τ₂ ≤ τ ∧ ∃ s ∈ chartLatNm y (fun κ => (a κ : ℤ)) τ,
    F = monomial (expo fun κ => τ * a κ) s}
  set u : MvPolynomial K Ω := monomial (expo fun κ => k * a κ) (aeval y c)
  have hinj : Function.Injective (LinearMap.mulLeft R u) := by
    intro F F' hF
    simp only [LinearMap.mulLeft_apply] at hF
    exact mul_left_cancel₀ (by simpa [u] using hc0) hF
  have hmap : (Submodule.span R G).map (LinearMap.mulLeft R u) ≤ Submodule.span R {1} := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨F, ⟨τ, -, s, hs, rfl⟩, rfl⟩
    rw [LinearMap.mulLeft_apply, monomial_mul]
    have hdeg : expo (fun κ => k * a κ) + expo (fun κ => τ * a κ) = expo fun κ => (τ + k) * a κ := by
      ext κ; simp; ring
    rw [hdeg]
    obtain ⟨g, hg⟩ := monomial_mem_range y (hc τ s hs)
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨⟨_, g, rfl⟩, by rw [Subalgebra.smul_def, smul_eq_mul, mul_one]; exact hg⟩
  have hfg : (Submodule.span R G).FG := by
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have := isNoetherian_of_fg_of_noetherian (Submodule.span R {(1 : MvPolynomial K Ω)})
      (Submodule.fg_span_singleton 1)
    have := isNoetherian_of_le hmap
    exact Module.Finite.iff_fg.mp inferInstance
  obtain ⟨t, htG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
  choose d hd e he hte using fun j : t => htG j.2
  refine ⟨t, inferInstance, d, e, max τ₂ (Finset.univ.sup d), fun j => ⟨hd j,
    le_max_of_le_right (Finset.le_sup (Finset.mem_univ j)), he j⟩, ?_⟩
  intro τ hτ s hs
  have hdτ : ∀ j, d j ≤ τ := fun j =>
    le_trans (le_max_of_le_right (Finset.le_sup (Finset.mem_univ j))) hτ
  have hmem : monomial (expo fun κ => τ * a κ) s ∈ Submodule.span R (t : Set (MvPolynomial K Ω)) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨τ, le_trans (le_max_left _ _) hτ, s, hs, rfl⟩
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hmem
  have hR : ∀ F, ((f F : R) : MvPolynomial K Ω) ∈ formRing y := by
    intro F
    obtain ⟨g, hg⟩ := (f F).2
    rw [← hg]
    exact mConeMap_mem_formRing y g
  refine ⟨fun j => coeff (expo fun κ => (τ - d j) * a κ) ((f j : R) : MvPolynomial K Ω), fun j => ?_, ?_⟩
  · simpa using hR j (expo fun κ => (τ - d j) * a κ)
  · have hc' := congrArg (coeff (expo fun κ => τ * a κ)) hf
    rw [coeff_monomial, if_pos rfl] at hc'
    rw [← hc', coeff_sum, ← Finset.sum_coe_sort t]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul]
    set p := ((f j : R) : MvPolynomial K Ω)
    rw [hte j]
    rw [coeff_mul_monomial', if_pos]
    · congr 2
      ext κ
      simp [Nat.sub_mul]
    · intro κ
      simpa using Nat.mul_le_mul_right (a κ) (hdτ j)

end NmSectionsFinite

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRankBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsRankBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ κ, Fintype (ι κ)] {Ω : Type} [Field Ω]

omit [∀ κ, Fintype (ι κ)] in

theorem shift_mem (y : (Σ κ, ι κ) → Ω) (c : ∀ κ, ι κ) (a a' : K → ℤ) (τ τ' : ℕ) (e : K → ℕ)
    (he : ∀ κ, (τ : ℤ) * a κ + e κ = τ' * a' κ) {s : Ω} (hs : s ∈ chartLatNm y a τ) :
    (∏ κ, y ⟨κ, c κ⟩ ^ e κ) * s ∈ chartLatNm y a' τ' := by
  intro c' hc'
  have hmem : ∀ κ, y ⟨κ, c κ⟩ / y ⟨κ, c' κ⟩ ∈ chartRingZ y c' := fun κ =>
    Algebra.subset_adjoin ⟨⟨κ, c κ⟩, rfl⟩
  have hk : ∀ κ, y ⟨κ, c' κ⟩ ^ (-((τ' : ℤ) * a' κ)) =
      y ⟨κ, c' κ⟩ ^ (-((τ : ℤ) * a κ)) * (y ⟨κ, c' κ⟩ ^ e κ)⁻¹ := by
    intro κ
    rw [← he κ, neg_add, zpow_add₀ (hc' κ), zpow_neg (y ⟨κ, c' κ⟩) (e κ : ℤ), zpow_natCast]
  have heq : (∏ κ, y ⟨κ, c κ⟩ ^ e κ) * s * ∏ κ, y ⟨κ, c' κ⟩ ^ (-((τ' : ℤ) * a' κ)) =
      (s * ∏ κ, y ⟨κ, c' κ⟩ ^ (-((τ : ℤ) * a κ))) * ∏ κ, (y ⟨κ, c κ⟩ / y ⟨κ, c' κ⟩) ^ e κ := by
    simp only [hk, div_pow, Finset.prod_mul_distrib, Finset.prod_div_distrib, Finset.prod_inv_distrib]
    ring
  rw [heq]
  refine Subalgebra.mul_mem _ (hs c' hc') (Subalgebra.prod_mem _ fun κ _ => Subalgebra.pow_mem _ ?_ _)
  exact (integralClosure (chartRingZ y c') Ω).algebraMap_mem ⟨_, hmem κ⟩

theorem proof (h₁ : NmSectionsFinite.Statement) (h₂ : SecMRankBound.Statement) :
    NmSectionsRankBound.Statement := by
  intro K _ ι _ Ω _ y D a hvar hbir
  classical

  have hy : ∀ κ, ∃ i, y ⟨κ, i⟩ ≠ 0 := by
    intro κ
    obtain ⟨i, hi⟩ := hvar.2.1.2.2 κ
    refine ⟨i, fun h0 => hi ?_⟩
    simp [mCoordIdeal, RingHom.mem_ker, mConeMap, h0]

  have hchar : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      simp [mCoordIdeal, RingHom.mem_ker, mConeMap]
      rw [← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    rw [hvar.2.2.1, Ideal.mem_bot] at hmem
    exact_mod_cast hmem
  choose c hc using hy
  set b : K → ℕ := fun κ => (a κ).toNat + 1 with hb
  have hb1 : ∀ κ, 1 ≤ b κ := fun κ => Nat.le_add_left 1 _
  have hab : ∀ κ, a κ ≤ (b κ : ℤ) := fun κ => by simp only [hb]; push_cast; omega
  obtain ⟨J, _, d, e, τ₁, -, hgen⟩ := h₁ K ι Ω y b hb1 (fun κ => ⟨c κ, hc κ⟩) hbir 0
  obtain ⟨hfin, C, hC0, hC⟩ := h₂ K ι Ω y D b hvar hb1

  have hbig : ∀ τ, τ₁ ≤ τ → Module.Finite ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) ∧
      (Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) : ℝ) ≤
        Fintype.card J * C * ((τ : ℝ) + 1) ^ D := by
    intro τ hτ
    let M : J → AddSubgroup Ω := fun j => secM y (fun κ => (τ - d j) * b κ)
    let Φ : (∀ j, M j) →ₗ[ℤ] Ω :=
      ∑ j, (LinearMap.mulRight ℤ (e j)).comp ((M j).subtype.toIntLinearMap.comp (LinearMap.proj j))
    have hle : ∀ s ∈ chartLatNm y (fun κ => (b κ : ℤ)) τ, s ∈ LinearMap.range Φ := by
      intro s hs
      obtain ⟨r, hr, rfl⟩ := hgen τ hτ s hs
      exact ⟨fun j => ⟨r j, hr j⟩, by simp [Φ, M]⟩
    let f : chartLatNm y (fun κ => (b κ : ℤ)) τ →ₗ[ℤ] LinearMap.range Φ :=
      LinearMap.codRestrict _ (chartLatNm y (fun κ => (b κ : ℤ)) τ).subtype.toIntLinearMap
        (fun x => hle x x.2)
    have hinj : Function.Injective f := fun x x' hxx => by
      have h := congrArg Subtype.val hxx
      exact Subtype.ext h
    have : ∀ j, Module.Finite ℤ (M j) := fun j => hfin (τ - d j)
    have : ∀ j, Module.IsTorsionFree ℤ (M j) := fun j =>
      Function.Injective.moduleIsTorsionFree (M j).subtype Subtype.val_injective (fun _ _ => rfl)
    refine ⟨Module.Finite.of_injective f hinj, ?_⟩
    have h1 : Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) ≤ ∑ j, Module.finrank ℤ (M j) :=
      (LinearMap.finrank_le_finrank_of_injective hinj).trans
        ((LinearMap.finrank_range_le Φ).trans_eq (Module.finrank_pi_fintype ℤ))
    calc (Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) τ) : ℝ)
        ≤ ∑ j, (Module.finrank ℤ (M j) : ℝ) := by exact_mod_cast h1
      _ ≤ ∑ _j : J, C * ((τ : ℝ) + 1) ^ D := by
          refine Finset.sum_le_sum fun j _ => (hC (τ - d j)).trans ?_
          gcongr
          exact_mod_cast Nat.sub_le τ (d j)
      _ = Fintype.card J * C * ((τ : ℝ) + 1) ^ D := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

  have hmap : ∀ τ, ∃ f : chartLatNm y a τ →ₗ[ℤ] chartLatNm y (fun κ => (b κ : ℤ)) (max τ τ₁),
      Function.Injective f := by
    intro τ
    set τ' := max τ τ₁
    set ex : K → ℕ := fun κ => ((τ' : ℤ) * b κ - τ * a κ).toNat
    have hex : ∀ κ, (τ : ℤ) * a κ + ex κ = τ' * (b κ : ℤ) := by
      intro κ
      have h0 : (τ : ℤ) * a κ ≤ τ' * b κ :=
        calc (τ : ℤ) * a κ ≤ τ * b κ := mul_le_mul_of_nonneg_left (hab κ) (by positivity)
          _ ≤ τ' * b κ := mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left τ τ₁) (by positivity)
      simp only [ex]
      rw [Int.toNat_of_nonneg (by linarith)]
      ring
    set u : Ω := ∏ κ, y ⟨κ, c κ⟩ ^ ex κ
    have hu : u ≠ 0 := Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hc κ)
    let F : chartLatNm y a τ →+ chartLatNm y (fun κ => (b κ : ℤ)) τ' :=
      ((AddMonoidHom.mulLeft u).comp (chartLatNm y a τ).subtype).codRestrict _
        (fun x => shift_mem y c a _ τ τ' ex hex x.2)
    refine ⟨F.toIntLinearMap, fun x x' hxx => ?_⟩
    have h : u * (x : Ω) = u * x' := congrArg Subtype.val hxx
    exact Subtype.ext (mul_left_cancel₀ hu h)
  refine ⟨fun τ => ?_, Fintype.card J * C * ((τ₁ : ℝ) + 1) ^ D, by positivity, fun τ => ?_⟩
  · obtain ⟨f, hf⟩ := hmap τ
    have := (hbig (max τ τ₁) (le_max_right _ _)).1
    exact Module.Finite.of_injective f hf
  · obtain ⟨f, hf⟩ := hmap τ
    obtain ⟨hF, hR⟩ := hbig (max τ τ₁) (le_max_right _ _)
    have h1 : (Module.finrank ℤ (chartLatNm y a τ) : ℝ) ≤
        Module.finrank ℤ (chartLatNm y (fun κ => (b κ : ℤ)) (max τ τ₁)) := by
      exact_mod_cast LinearMap.finrank_le_finrank_of_injective hf
    have h2 : ((max τ τ₁ : ℕ) : ℝ) + 1 ≤ ((τ₁ : ℝ) + 1) * ((τ : ℝ) + 1) := by
      rcases le_total τ τ₁ with h | h
      · rw [max_eq_right h]; nlinarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ), (Nat.cast_nonneg τ₁ : (0 : ℝ) ≤ τ₁)]
      · rw [max_eq_left h]; nlinarith [(Nat.cast_nonneg τ : (0 : ℝ) ≤ τ), (Nat.cast_nonneg τ₁ : (0 : ℝ) ≤ τ₁)]
    calc (Module.finrank ℤ (chartLatNm y a τ) : ℝ)
        ≤ Fintype.card J * C * (((max τ τ₁ : ℕ) : ℝ) + 1) ^ D := h1.trans hR
      _ ≤ Fintype.card J * C * ((((τ₁ : ℝ) + 1) * ((τ : ℝ) + 1)) ^ D) := by
          gcongr
      _ = Fintype.card J * C * ((τ₁ : ℝ) + 1) ^ D * ((τ : ℝ) + 1) ^ D := by rw [mul_pow]; ring

end NmSectionsRankBound

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockGraphDeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockGraphDeg.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) →
    IsBlockImage y k₀ M N x →
    ∃ (G : GenFibre (inrV (ι := ι) (ι₂ := GlobalTheory κ)) (graphIdeal (mCoordIdeal y) (blockForms k₀ M)))
      (J : IFamily G.Φ (fibreIdx (Sum.elim ι (GlobalTheory κ)) (Sum.inr : Unit → K ⊕ Unit))),
      IsFieldIntersection J ∧ J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = 1

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartLatRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartLatRank.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Module.finrank ℤ (AddSubgroup.toIntSubmodule (chartLat y a n)) = Module.finrank ℚ (chartLatQ y a n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

