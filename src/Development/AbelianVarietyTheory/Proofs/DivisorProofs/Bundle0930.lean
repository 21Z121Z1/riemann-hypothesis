import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0614
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0520
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0523
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0906
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatioConjOfToricRatioConjugates
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.HeckeGal GlobalTheory.ToricDenom
open Cardinal

namespace GlobalTheory.ToricRatioBridge

abbrev algC : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield

theorem mem_algC {z : ℂ} : z ∈ algC ↔ IsAlgebraic ℚ z := mem_algebraicClosure_iff

theorem isAlgebraic_finPart {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {m : I → ℤ}
    {χ : HChar E} (hm : HasInf χ φ m) {c : Ideal (OF E)} [Finite (PicO c)] (hu : ∀ y ∈ hatOUnits c, finPart χ y = 1)
    (y : (Af E)ˣ) : IsAlgebraic ℚ (finPart χ y : ℂ) := by
  let M : Subfield ℂ := algC
  let H : Subgroup (Af E)ˣ := M.toSubmonoid.units.comap (finPart χ)
  have hH : ∀ y, y ∈ H ↔ (finPart χ y : ℂ) ∈ M := fun y =>
    ⟨fun h => h.1, fun h => (Submonoid.mem_units_iff _ _).2 ⟨h, by rw [Units.val_inv_eq_inv_val]; exact M.inv_mem h⟩⟩
  have hE : ∀ (σ : E →+* ℂ) (x : E), σ x ∈ M := fun σ x =>
    mem_algC.2 ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom).isAlgebraic
  have hle : princ ⊔ hatOUnits c ≤ H := by
    refine sup_le ?_ fun u h => (hH u).2 (by rw [hu u h]; exact one_mem M)
    rintro _ ⟨k, rfl⟩
    rw [hH, eq_inv_of_mul_eq_one_left (finPart_mul_inf χ k), Units.val_inv_eq_inv_val, (hasInfRatio_iff χ φ m).1 hm k]
    exact inv_mem (prod_mem fun i _ => zpow_mem (div_mem (hE _ _) (hE ((starRingEnd ℂ).comp (φ i)) _)) _)
  let p : PicO c →* (Af E)ˣ ⧸ H := QuotientGroup.map _ _ (MonoidHom.id _) hle
  have : Finite ((Af E)ˣ ⧸ H) := Finite.of_surjective p fun q => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hn := pow_card_eq_one' (G := (Af E)ˣ ⧸ H) (x := (QuotientGroup.mk y))
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hH, map_pow, Units.val_pow_eq_pow_val] at hn
  exact IsAlgebraic.of_pow Nat.card_pos (mem_algC.1 hn)

theorem exists_eq_of_isAlgebraic {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* ℂ) {z : ℂ} (hz : IsAlgebraic ℚ z) :
    ∃ x : Ω, j x = z := by
  let _ : Algebra Ω ℂ := j.toAlgebra
  have : CharZero Ω := RingHom.charZero j
  have : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun q => (map_ratCast j q).symm
  have hi : IsIntegral Ω z := (hz.isIntegral).tower_top
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one Ω z
    (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hi))
  exact ⟨x, hx⟩

theorem comp_eq_of_sqrt {R : Ranks} (H : Host R) (f g : H.E →+* ℂ) (h : f H.sqrtMinusD = g H.sqrtMinusD) :
    f.comp (algebraMap H.K H.E) = g.comp (algebraMap H.K H.E) := by
  refine RingHom.ext fun x => ?_
  have hx : (x : H.E) ∈ Algebra.adjoin ℚ {H.sqrtMinusD} := by
    have h1 : IsIntegral ℚ H.sqrtMinusD := Algebra.IsIntegral.isIntegral _
    have : (x : H.E) ∈ IntermediateField.adjoin ℚ {H.sqrtMinusD} := x.2
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic h1.isAlgebraic] at this
    exact this
  have hle : Algebra.adjoin ℚ {H.sqrtMinusD} ≤ AlgHom.equalizer f.toRatAlgHom g.toRatAlgHom :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 h)
  show f (x : H.E) = g (x : H.E)
  exact hle hx

theorem upIdele_eq (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele K E t = Units.map (GlobalTheory.AdeleBaseChange.adMap K E).toMonoidHom t :=
  Units.ext (FiniteAdeleRing.ext _ fun P => (GlobalTheory.CharTransport.locMap_eq K E P _).symm)

theorem countable_of_isAlgClosure (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    Countable Ω := by
  have hK : #K ≤ ℵ₀ := by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  rw [← Cardinal.mk_le_aleph0_iff]
  exact (Algebra.IsAlgebraic.cardinalMk_le_max K Ω).trans (max_le hK le_rfl)

end GlobalTheory.ToricRatioBridge

namespace GlobalTheory.ToricRatioBridge

open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (ToricRatioConjugates IsSymbol classOf conjChar)

theorem ratioConj_of_toricRatioConjugates (hG : ToricRatioConjugates) : GlobalTheory.ToricRational.RatioConj := by
  intro R H I _ φ s κ 𝔣 χ hD Ω _ _ _ j τ₀ hj art ha T₀ hT₀ h0 Q hQ hfin T hT
  have : IsCMField H.E := H.isCMField_hostE
  have hU : UnramFin H.E := GlobalTheory.ToricDenomBridge.host_unramFin H
  let ι : H.K →+* ℂ := (φ τ₀).comp (algebraMap H.K H.E)
  have hι : ∀ i, (φ i).comp (algebraMap H.K H.E) = ι := fun i => comp_eq_of_sqrt H _ _ (hD.2.1 i τ₀)
  let δ : H.K := ⟨H.sqrtMinusD, H.sqd_mem_K⟩
  have hδ : δ ^ 2 = -(H.d : H.K) := Subtype.ext (by push_cast; exact H.sqrtMinusD_sq)
  have hK2 : Module.finrank ℚ H.K = 2 := H.finrank_K
  obtain ⟨T₀', Tw, hT₀', -, hTw, halg, hconj⟩ := hG H.E H.K H.d δ ι I φ s κ 𝔣 Q χ hU hK2 H.hyp.2.1.pos hδ hD.1 hι
    hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2.1 hQ hD.2.2.2.2.2
  have h𝔣 : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  have hT₀'' : IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀' := by rw [h𝔣]; exact hT₀'
  have e0 : T₀' = T₀ := hT₀''.unique hT₀
  subst e0
  let up : (PicO (condQ 𝔣 Q) →* Ωˣ) → (PicO (condQ 𝔣 Q) →* ℂˣ) := fun ψ => (Units.map j.toMonoidHom).comp ψ
  have hsum : ∀ ψ', Tw ψ' = ∑ᶠ q, ((ψ' q : ℂˣ) : ℂ)⁻¹ * T q := fun ψ' => by
    obtain ⟨_, S, hS, e⟩ := hTw ψ'
    rw [e]
    refine finsum_congr fun q => ?_
    obtain ⟨S', hS', e'⟩ := hT q
    rw [e', mul_assoc, (hS q).unique hS']
    rfl
  have hΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed H.K
  choose ρ hρ using fun ψ => exists_eq_of_isAlgebraic j (halg (up ψ))
  refine ⟨ρ, fun ψ => by rw [hρ, hsum]; rfl, fun g hgE hgl t ht ψ => ?_⟩
  have : Countable Ω := countable_of_isAlgClosure H.K Ω
  obtain ⟨g', hg'⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq j (j.comp g.toRingEquiv.toRingHom)
  have hfix : ∀ z : ℂ, IsAlgebraic ℚ z → (∀ x, j x = z → g x = x) → g' z = z := fun z hz hx => by
    obtain ⟨x, rfl⟩ := exists_eq_of_isAlgebraic j hz
    rw [hg']
    exact congrArg j (hx x rfl)
  have hφ : ∀ i (x : H.E), IsAlgebraic ℚ (φ i x) := fun i x =>
    ((Algebra.IsIntegral.isIntegral (R := ℚ) x).map (φ i).toRatAlgHom).isAlgebraic
  have : Finite (PicO (condQ 𝔣 ∅)) := hT₀.1
  have hl : ∀ y, IsAlgebraic ℚ (GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF χ s y) := fun y => by
    have h1 := isAlgebraic_finPart hD.2.2.2.2.2.2.2.1 (c := condQ 𝔣 ∅)
      (OrderUnits.finPart_eq_one H.E I φ hD.1 s κ 𝔣 ∅ χ hU hD.2.2.2.2.1 (fun _ h => absurd h (Finset.notMem_empty _))
        hD.2.2.2.2.2) y
    refine mem_algC.1 (mul_mem (mem_algC.2 h1) ?_)
    rw [Complex.ofReal_pow]
    exact pow_mem (GlobalTheory.ToricRational.modF_mem _ y) s
  have hσ : ∀ x, j (g x) = g' (j x) := fun x => (hg' x).symm
  have hsym : IsSymbol art t g := by rw [IsSymbol, ht, map_inv, inv_inv]
  obtain ⟨e, -⟩ := hconj Ω j art (RingHom.ext hj) ha g' g t (fun i x => hfix _ (hφ i x) fun x' hx' => hgE x' i x hx')
    (fun y => hfix _ (hl y) fun x' hx' => hgl x' y hx') hσ hsym (up ψ)
  have hc : conjChar g' (up ψ) = up ((Units.map g.toRingEquiv.toMonoidHom).comp ψ) :=
    MonoidHom.ext fun q => Units.ext (hg' _)
  have hcls : classOf H.K (condQ 𝔣 Q) t = QuotientGroup.mk (GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.upIdele H.K H.E t) := by
    rw [classOf, upIdele_eq]
  apply j.injective
  rw [hσ, hρ, e, hc, hcls, map_mul, map_inv₀, hρ]
  rfl

end GlobalTheory.ToricRatioBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealUnitaryCovolumeSum
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section
namespace GlobalTheory.SUVolBound
theorem countable_numberField (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

theorem countable_inReal {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Ψ : Finset (E →+* ℂ))
    (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)) : Countable (inReal Ψ G Γ) := by
  haveI := countable_numberField E
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) := Function.Injective.countable (f := fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) (fun a b h => Units.ext h)
  have hsub : ∀ y : inReal Ψ G Γ, ∃ γ : GL (Fin r) E, embGL Ψ r γ = (y : realSU Ψ G).1 := by
    rintro ⟨y, hy⟩
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
    exact ⟨γ, hγ⟩
  choose f hf using hsub
  refine Function.Injective.countable (f := f) fun a b hab => ?_
  apply Subtype.ext; apply Subtype.ext
  rw [← hf a, ← hf b, hab]

theorem tangentHaar_smul {ι : Type} [Fintype ι] {r : ℕ} (H : Subgroup (ι → GL (Fin r) ℂ)) [LocallyCompactSpace H]
    [MeasurableSpace H] [BorelSpace H] (c : ℝ≥0∞) (hc : c ≠ ⊤) (ν : Measure (ι → Fin r → Fin r → ℂ)) :
    tangentHaar H (c • ν) = c • tangentHaar H ν := by
  unfold tangentHaar
  rw [smul_smul]
  congr 1
  simp only [Measure.smul_apply, smul_eq_mul, mul_div_assoc]
  exact ENNReal.limsup_const_mul_of_ne_top hc

theorem covolume_smul {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
    [MeasurableConstSMul G α] (ν : Measure α) [SMulInvariantMeasure G α ν] (c : ℝ≥0∞) (hc : c ≠ 0) :
    covolume G α (c • ν) = c * covolume G α ν := by
  by_cases h : HasFundamentalDomain G α ν
  · obtain ⟨s, hs⟩ := h.ExistsIsFundamentalDomain
    have hs' : IsFundamentalDomain G s (c • ν) := hs.mono (Measure.smul_absolutelyContinuous)
    rw [hs'.covolume_eq_volume, hs.covolume_eq_volume, Measure.smul_apply, smul_eq_mul]
  · have h' : ¬ HasFundamentalDomain G α (c • ν) := by
      rintro ⟨⟨s, hs⟩⟩
      exact h ⟨⟨s, hs.mono (Measure.absolutelyContinuous_smul hc)⟩⟩
    simp [covolume, h, h']

theorem abs_discr_real_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) :
    |(discr (maximalRealSubfield E) : ℝ)| = rdE E ^ fdeg E := by
  have hdiff : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ :=
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top _ E).1 (by
      haveI : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hU; infer_instance)
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield E)
    (𝓞 (maximalRealSubfield E)) E (𝓞 E)
  rw [hdiff, Algebra.IsQuadraticExtension.finrank_eq_two] at h
  simp only [Ideal.absNorm_top, one_mul] at h
  have hd : dE E = |(discr (maximalRealSubfield E) : ℝ)| ^ 2 := by
    unfold dE
    rw [← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.abs_eq_natAbs, h]
    push_cast; ring
  have hf : 1 ≤ (fdeg E : ℝ) := one_le_field_half_degree
  rw [rootDiscriminant_eq_rpow, hd, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
    ← Real.rpow_mul (abs_nonneg _)]
  have : (((2 : ℕ) : ℝ) * (1 / (2 * (fdeg E : ℝ))) * (fdeg E : ℝ)) = 1 := by
    field_simp; norm_num
  rw [this, Real.rpow_one]

theorem exists_lie_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : SelfDualLat G Λ) :
    ∃ e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E,
      (∀ i, e i ∈ lieLat G Λ) ∧ LinearIndependent (maximalRealSubfield E) e := by
  obtain ⟨e, he, hli⟩ := GlobalTheory.T.exists_unitary_lie_basis G hΛ.1 hΛ.2.1
  choose N hN hmem using fun i => GlobalTheory.T.integral_multiple_in_lie_lattice G Λ hΛ.2.2.1 hΛ.2.2.2.1 (e i) (he i).1 (he i).2
  refine ⟨fun i => (N i : E) • e i, hmem, ?_⟩
  let w : Fin (r ^ 2 - 1) → (maximalRealSubfield E)ˣ :=
    fun i => Units.mk0 (N i : maximalRealSubfield E) (by exact_mod_cast (hN i).ne')
  have hw : (fun i => (N i : E) • e i) = w • e := by
    funext i
    ext a b
    simp [w, Algebra.smul_def]
  rw [hw]
  exact hli.units_smul w

theorem sum_covolume_le : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → Unr E → SelfDualLat X.Gm Λ → IsOrth X x → IsSReps X.Gm (Λ : Set (Fin r → E)) 1 s → ∑' j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x) ≤ ENNReal.ofReal (rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  intro hP E _ _ _ r X Λ x _ _ J s hr hU hΛ hx hs
  obtain ⟨e, he, hli⟩ := exists_lie_basis X.Gm Λ hΛ
  obtain ⟨hmult, hP1⟩ := hP E r X.Gm Λ X.Ψ e J s hr hU hΛ X.cmType he hli hs
  have hlie := GlobalTheory.T.riemannian_lie_volume_formula E r X Λ x e hr hU hΛ hx he hli
  obtain ⟨hPpos, hPinv⟩ := GlobalTheory.T.local_factor_product_bound E r hr hmult
  set m : ℝ := ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex
    (lieLat X.Gm Λ) : ℝ) with hm
  set P : ℝ := ∏' v, locFactor E r v with hPdef
  set D : ℝ := |(discr (maximalRealSubfield E) : ℝ)| with hD
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZ
  set n : ℝ := (r : ℝ) ^ 2 - 1 with hn
  set μ := tangentHaar (realSU X.Ψ X.Gm) (formLie X.Ψ e) with hμ
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt r ^ fdeg E * m) with hc
  have hDpos : 0 < D := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hmpos : 0 < m := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero, zero_mul, ENNReal.ofReal_zero, mul_zero] at hP1
      exact zero_ne_one hP1
  have hr0 : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r))
  have hcpos : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hriem : riemHaar X.Ψ X.Gm x = c • μ := by
    unfold riemHaar
    rw [hlie, tangentHaar_smul _ _ ENNReal.ofReal_ne_top]
  have hcov : ∀ j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm)
      (riemHaar X.Ψ X.Gm x) = c * covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j)))
      (realSU X.Ψ X.Gm) μ := by
    intro j
    haveI := countable_inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))
    rw [hriem, covolume_smul _ _ hcpos]
  simp_rw [hcov]
  rw [ENNReal.tsum_mul_left]
  set S := ∑' j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) μ
    with hS
  have ha : 0 < D ^ (-n / 2) * m * P := by positivity
  have hS1 : S = ENNReal.ofReal ((D ^ (-n / 2) * m * P)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos ha]
    exact (ENNReal.eq_inv_of_mul_eq_one_left hP1)
  rw [hS1, hc, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hDr : D = rdE E ^ fdeg E := abs_discr_real_eq hU
  have hrd0 : 0 ≤ rdE E := by
    unfold rdE; exact Real.rpow_nonneg (abs_nonneg _) _
  have hDn : D ^ (n / 2) = rdE E ^ ((fdeg E : ℝ) * n / 2) := by
    rw [hDr, ← Real.rpow_natCast, ← Real.rpow_mul hrd0, mul_div_assoc]
  have key : Real.sqrt r ^ fdeg E * m * (D ^ (-n / 2) * m * P)⁻¹ = D ^ (n / 2) * Real.sqrt r ^ fdeg E * P⁻¹ := by
    rw [neg_div, Real.rpow_neg hDpos.le]
    have : D ^ (n / 2) ≠ 0 := (Real.rpow_pos_of_pos hDpos _).ne'
    field_simp
  rw [key, hDn, mul_pow, mul_assoc]
  gcongr

end GlobalTheory.SUVolBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section Hom

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem subst_sum_smul {σ τ ι : Type} [Fintype ι] {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (m : ι → C)
    (f : ι → MvPowerSeries σ C) : subst a (∑ i, m i • f i) = ∑ i, m i • (subst a (f i) : MvPowerSeries τ C) := by
  rw [← substAlgHom_apply ha, map_sum]
  simp only [map_smul, substAlgHom_apply]

theorem isIntHom_comp {d d' d'' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'} {G'' : LogFGL v d''}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {ψ : Fin d'' → MvPowerSeries (Fin d') C}
    {M : Matrix (Fin d') (Fin d) C} {N : Matrix (Fin d'') (Fin d') C}
    (hφ : IsIntHom G G' φ M) (hψ : IsIntHom G' G'' ψ N) :
    IsIntHom G G'' (fun b => subst φ (ψ b)) (N * M) := by
  obtain ⟨hφ0, hφi, hφl⟩ := hφ
  obtain ⟨hψ0, hψi, hψl⟩ := hψ
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ0
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  refine ⟨fun b => constantCoeff_subst_eq_zero hφs hφ0 (hψ0 b), fun b => ?_, fun c => ?_⟩
  · exact ptIntSer_subst hφs (fun s => hφi s) (hψi b)
  · rw [← subst_comp_subst_apply hψs hφs, hψl c, subst_sum_smul hφs]
    simp_rw [hφl, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm

end Hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

section Labels

variable {c : Coeff l} {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def embO (σ : E →+* ℂ) : 𝓞 E →+* X.O where
  toFun a := (X.ints.exists_of_le_one (v_embX_le_one io X σ a)).choose
  map_one' := X.ints.hom_inj (by rw [(X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_one, map_one])
  map_zero' := X.ints.hom_inj (by
    rw [(X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_zero, map_zero])
  map_mul' a b := X.ints.hom_inj (by
    rw [map_mul (algebraMap X.O X.C), (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_mul])
  map_add' a b := X.ints.hom_inj (by
    rw [map_add (algebraMap X.O X.C), (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec,
      (X.ints.exists_of_le_one (v_embX_le_one io X σ _)).choose_spec, map_add])

theorem algebraMap_embO (σ : E →+* ℂ) (a : 𝓞 E) : algebraMap X.O X.C (embO io X σ a) = embX io X σ a :=
  (X.ints.exists_of_le_one (v_embX_le_one io X σ a)).choose_spec

def red (σ : E →+* ℂ) : 𝓞 E →+* ResidueField X.O := (residue X.O).comp (embO io X σ)

theorem residue_eq_zero_iff_v (x : X.O) : residue X.O x = 0 ↔ X.v (algebraMap X.O X.C x) < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, X.ints.isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (X.ints.map_le_one x) h, fun h => h.ne⟩

theorem residue_eq_iff_v (x y : X.O) :
    residue X.O x = residue X.O y ↔ X.v (algebraMap X.O X.C x - algebraMap X.O X.C y) < 1 := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_v, map_sub]

theorem primeBelow_eq_ker (σ : E →+* ℂ) : primeBelow io X σ = RingHom.ker (red io X σ) := by
  ext a
  rw [RingHom.mem_ker]
  show X.v (embX io X σ a) < 1 ↔ residue X.O (embO io X σ a) = 0
  rw [residue_eq_zero_iff_v, algebraMap_embO]

theorem red_eq_pow_iff (σ σ' : E →+* ℂ) (a : 𝓞 E) (n : ℕ) :
    red io X σ' a = red io X σ a ^ n ↔ X.v (embX io X σ' a - embX io X σ a ^ n) < 1 := by
  show residue X.O (embO io X σ' a) = residue X.O (embO io X σ a) ^ n ↔ _
  rw [← map_pow, residue_eq_iff_v, map_pow, algebraMap_embO, algebraMap_embO]

theorem charP_residueField_of_irreducible : CharP (ResidueField X.O) p := by
  have h : ((p : ℕ) : ResidueField X.O) = 0 := by
    rw [← map_natCast (residue X.O), residue_eq_zero_iff]
    exact X.nonunit.out
  exact (CharP.charP_iff_prime_eq_zero Fact.out).2 h

theorem vX_vp_pos_iff (x : X.C) : 0 < vX_vp X x ↔ X.v x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hpO : ¬ IsUnit (p : X.O) := X.nonunit.out
  have hp1 : X.v (p : X.C) < 1 := by
    have h := X.ints.map_le_one (p : X.O)
    rw [map_natCast] at h
    refine lt_of_le_of_ne h fun h1 => hpO ?_
    apply X.ints.isUnit_of_one'
    rw [map_natCast]
    exact h1
  have hp0 : (0 : NNReal) < X.v (p : X.C) := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx0 : (0 : NNReal) < X.v x := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact hx
  have hlp : Real.log (X.v (p : X.C) : ℝ) < 0 :=
    Real.log_neg (by exact_mod_cast hp0) (by exact_mod_cast hp1)
  have hi : (Real.log (X.v (p : X.C) : ℝ))⁻¹ < 0 := inv_lt_zero.mpr hlp
  rw [vX_vp_apply X hx, show (0 : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) from rfl, WithTop.coe_lt_coe,
    mul_pos_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact absurd h1 (not_lt.mpr hi.le)
    · have h3 := (Real.log_neg_iff (by exact_mod_cast hx0)).mp h2
      exact_mod_cast h3
  · intro h
    right
    exact ⟨hi, Real.log_neg (by exact_mod_cast hx0) (by exact_mod_cast h)⟩

end Labels

variable {Dw : Datum H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr}
  {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def tanX (a : 𝓞 E) : Matrix (Fin (chD Ch.ch)) (Fin (chD Ch.ch)) X.C :=
  Matrix.of fun i j => jX X (coeff (Finsupp.single ((0 : Fin 1), j) 1) (Ch.actT a i))

end GlobalTheory.PrimePart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOfIntegersJointEigenspaceDisjointBiSup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section
namespace GlobalTheory.UPel.HT.LieType

theorem eigSp_disjoint_biSup : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (s : Finset (F →+* ℂ)) (τ : F →+* ℂ), τ ∉ s → Disjoint (eigSp φ τ) (⨆ τ' ∈ s, eigSp φ τ') := by
  intro F _ _ g φ s τ hτ
  let ρ : 𝓞 F →+* Module.End ℂ (Fin g → ℂ) := (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)).toRingEquiv.toRingHom.comp φ
  have hcomm : ∀ a b : 𝓞 F, Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun a : 𝓞 F => ρ a)
    (fun i j m => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) m)
  let χ : (F →+* ℂ) → (𝓞 F → ℂ) := fun σ c => σ (c : F)
  have hχ : Function.Injective χ := by
    intro σ₁ σ₂ he
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F))
    ext c
    exact congrFun he c
  have hle : ∀ σ : F →+* ℂ, eigSp φ σ ≤ ⨅ c : 𝓞 F, (ρ c).maxGenEigenspace (χ σ c) := by
    intro σ u hu
    rw [Submodule.mem_iInf]
    intro c
    apply (Module.End.genEigenspace (ρ c) (χ σ c)).mono le_top
    rw [Module.End.mem_eigenspace_iff]
    have := hu c
    simpa [ρ, χ, Matrix.toLin'_apply] using this
  have hnot : χ τ ∉ (χ '' (s : Set (F →+* ℂ))) := by
    rintro ⟨σ, hσ, he⟩
    exact hτ (hχ he ▸ hσ)
  have hd := h.disjoint_biSup hnot
  refine (hd.mono_left (hle τ)).mono_right ?_
  refine iSup₂_le fun σ hσ => (hle σ).trans ?_
  exact le_iSup₂_of_le (f := fun (x : 𝓞 F → ℂ) (_ : x ∈ χ '' (s : Set (F →+* ℂ))) => ⨅ c : 𝓞 F, (ρ c).maxGenEigenspace (x c)) (χ σ) ⟨σ, hσ, rfl⟩ le_rfl

end GlobalTheory.UPel.HT.LieType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveDegreeTwoClassDiesOnPrincipalOpStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localization_away_pull_eq_zero_Ht_two : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ (i : ℤ) (x : Ht q (sp B) 2 i), ∃ f : B, f ≠ 0 ∧ pull _ (spMap (algebraMap B (Localization.Away f))) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen) | (exact GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen) | (intros; apply GlobalTheory.EtC.smoothAffineCurve_degreeTwo_class_dies_on_principalOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionTensorObjDualStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Serre
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_tensorObj_dual_finrank_mul : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (g : ℕ), SmoothOfRelativeDimension g B.hom → SmoothOfRelativeDimension (Module.finrank O X * g) (tensorObj (Module.Dual O X) a).hom := by
  first | exact @GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual | exact GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual | (intros; apply GlobalTheory.TensorDualDim.smoothOfRelativeDimension_tensorObj_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalFunctionDualLabelStatement
section
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_function_dual_label : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (α : Fin n → ℂ) (φ : GL (Fin n) (P.adicCompletion E) → ℂ), (∀ i, α i ≠ 0) → IsSpherical E P α φ → ∃ φ' : GL (Fin n) (P.adicCompletion E) → ℂ, IsSpherical E P (fun i => (α i.rev)⁻¹) φ' ∧ φ' 1 = φ 1 ∧ ∀ d : List ℤ, d.length = n → hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) (dualLab d)) φ' 1 = hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) d) φ 1 := by
  first | exact @GlobalTheory.InvTranspose.exists_spherical_dual | exact GlobalTheory.InvTranspose.exists_spherical_dual | (intros; apply GlobalTheory.InvTranspose.exists_spherical_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharFiniteSuperDiagonalSumIntegralStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAdelicCharFinite_superDiagonalSum_integral_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (u : GL (Fin n) (Af E)), u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) → u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1 := by
  first | exact @GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral | exact GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral | (intros; apply GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral <;> assumption)
end

