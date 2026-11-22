import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0123
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackPtC
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDiscreteValuationRingIntO
section
open IsLocalRing Cardinal
open Formalism.MainNotions.DIV.Cons (SCF intO BigT)

namespace GlobalTheory.LocM.Cht.CompletedClosure

theorem isDiscreteValuationRing_intO {K : Type} [NormedField K] [IsUltrametricDist K] (π : K) (h0 : π ≠ 0)
    (h1 : ‖π‖ < 1) (h : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n) : IsDiscreteValuationRing ↥(intO K) := by
  have hpos : 0 < ‖π‖ := norm_pos_iff.2 h0
  have hunit : ∀ x : ↥(intO K), IsUnit x ↔ ‖(x : K)‖ = 1 := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hx.exists_right_inv
      have e : ‖(x : K)‖ * ‖(y : K)‖ = 1 := by
        rw [← norm_mul, ← Subring.coe_mul, hy, Subring.coe_one, norm_one]
      have hx1 : ‖(x : K)‖ ≤ 1 := x.2
      have hy1 : ‖(y : K)‖ ≤ 1 := y.2
      nlinarith [norm_nonneg (x : K), norm_nonneg (y : K)]
    · intro hx
      have hx0 : (x : K) ≠ 0 := fun h' => by simp [h'] at hx
      refine IsUnit.of_mul_eq_one (⟨(x : K)⁻¹, show ‖(x : K)⁻¹‖ ≤ 1 by simp [hx]⟩ : ↥(intO K)) (Subtype.ext ?_)
      exact mul_inv_cancel₀ hx0
  have hnat : ∀ x : ↥(intO K), x ≠ 0 → ∃ n : ℕ, ‖(x : K)‖ = ‖π‖ ^ n := by
    intro x hx
    obtain ⟨n, hn⟩ := h x (fun h' => hx (Subtype.ext h'))
    have hx1 : ‖(x : K)‖ ≤ 1 := x.2
    have hn0 : 0 ≤ n := by
      rw [hn] at hx1
      exact (zpow_le_one_iff_right_of_lt_one₀ hpos h1).1 hx1
    lift n to ℕ using hn0
    exact ⟨n, by rw [hn, zpow_natCast]⟩
  let ϖ : ↥(intO K) := ⟨π, h1.le⟩
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖ, ⟨?_, ?_⟩, ?_⟩
  · rw [hunit]; exact h1.ne
  · intro a b hab
    have e : π = (a : K) * b := congrArg Subtype.val hab
    have ha : a ≠ 0 := fun h' => h0 (by rw [e, h']; simp)
    have hb : b ≠ 0 := fun h' => h0 (by rw [e, h']; simp)
    obtain ⟨m, hm⟩ := hnat a ha
    obtain ⟨n, hn⟩ := hnat b hb
    have e2 : ‖π‖ ^ 1 = ‖π‖ ^ (m + n) := by
      rw [pow_add, ← hm, ← hn, ← norm_mul, ← e, pow_one]
    have e3 : 1 = m + n := (pow_right_strictAnti₀ hpos h1).injective e2
    rw [hunit, hunit, hm, hn]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · left; simp
    · right
      have : n = 0 := by omega
      simp [this]
  · intro x hx
    obtain ⟨n, hn⟩ := hnat x hx
    have hnorm : ‖(x : K) / π ^ n‖ = 1 := by
      rw [norm_div, norm_pow, hn, div_self (pow_pos hpos n).ne']
    let u : ↥(intO K) := ⟨(x : K) / π ^ n, hnorm.le⟩
    have hu : IsUnit u := (hunit u).2 hnorm
    refine ⟨n, hu.unit, Subtype.ext ?_⟩
    change π ^ n * ((x : K) / π ^ n) = x
    exact mul_div_cancel₀ _ (pow_ne_zero n h0)

theorem exists_scf_equiv {p : ℕ} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [IsAlgClosed C] [CharZero C] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹) (hC : #C ≤ 𝔠) :
    ∃ (D : SCF p) (e : C →+* ↥D.S), (∀ x, ‖e x‖ = ‖x‖) ∧ Function.Surjective e := by
  have hle : #C ≤ #BigT := by
    refine hC.trans ?_
    rw [mk_set, mk_set, mk_real]
    exact (cantor _).le.trans (cantor _).le
  obtain ⟨j⟩ := (Cardinal.le_def _ _).1 hle
  let S : Set BigT := Set.range j
  let e : S ≃ C := (Equiv.ofInjective j j.injective).symm
  letI : Field S := e.field
  let r : S ≃+* C := e.ringEquiv
  letI : NormedField S := NormedField.induced S C r r.injective
  have hn : ∀ x : S, ‖x‖ = ‖r x‖ := fun _ => rfl
  have hn' : ∀ x : C, ‖r.symm x‖ = ‖x‖ := fun x => by rw [hn, r.apply_symm_apply]
  letI : NontriviallyNormedField S :=
    { (inferInstance : NormedField S) with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := C)
        exact ⟨r.symm x, (hn' x).symm ▸ hx⟩ }
  haveI : IsUltrametricDist S :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hn, hn, hn, map_add]; exact IsUltrametricDist.norm_add_le_max _ _
  haveI : IsAlgClosed S := IsAlgClosed.of_ringEquiv C S r.symm
  have hiso : Isometry r := AddMonoidHomClass.isometry_of_norm r fun x => (hn x).symm
  haveI : CompleteSpace S :=
    (hiso.isUniformInducing.completeSpace_congr r.surjective).2 inferInstance
  haveI : CharZero S := charZero_of_injective_ringHom (f := r.symm.toRingHom) r.symm.injective
  exact ⟨{ S := S, norm_p := by rw [hn, map_natCast, hp] }, r.symm.toRingHom, hn', r.symm.surjective⟩

theorem exists_scf_dense {p : ℕ} {F C : Type} [Field F] [CharZero F] [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra F C] (hF : #F ≤ 𝔠)
    (hp : ‖(p : C)‖ = (p : ℝ)⁻¹) {x : F} (hx : 1 < ‖algebraMap F C x‖) :
    ∃ (D : SCF p) (i : F →+* ↥D.S), (∀ y, ‖i y‖ = ‖algebraMap F C y‖) ∧
      Dense {z : ↥D.S | ∃ q : Polynomial F, q ≠ 0 ∧ q.eval₂ i z = 0} := by
  let A := algebraicClosure F C
  let L : Subfield C := A.toSubfield.topologicalClosure
  have hAL : A.toSubfield ≤ L := A.toSubfield.le_topologicalClosure
  have hKL : ∀ y : F, algebraMap F C y ∈ L := fun y => hAL (A.algebraMap_mem y)
  have hcl : IsClosed (L : Set C) := A.toSubfield.isClosed_topologicalClosure
  letI : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL x⟩, hx⟩ }
  haveI : CompleteSpace L := hcl.completeSpace_coe
  letI : Algebra A L := (Subfield.inclusion hAL : A.toSubfield →+* L).toAlgebra
  have hd : DenseRange (algebraMap A L) :=
    (denseRange_inclusion_iff (s := (A.toSubfield : Set C)) (t := (L : Set C)) hAL).2 subset_rfl
  haveI : IsAlgClosed A := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosed L := isAlgClosed_of_denseRange hd
  have hL : #L ≤ 𝔠 := by
    refine (GlobalTheory.SmallClosedField.mk_le_of_denseRange _ hd).trans ?_
    have hA : #A ≤ 𝔠 :=
      (Algebra.IsAlgebraic.cardinalMk_le_max F A).trans (max_le hF aleph0_le_continuum)
    exact (power_le_power_right hA).trans continuum_power_aleph0.le
  let i : F →+* L := (algebraMap F C).codRestrict L hKL
  have hi : ∀ y, ‖i y‖ = ‖algebraMap F C y‖ := fun _ => rfl
  haveI : CharZero L := charZero_of_injective_ringHom i.injective
  have hLp : ‖(p : L)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast i, hi, map_natCast, hp]
  obtain ⟨D, e, he, hs⟩ := exists_scf_equiv hLp hL
  refine ⟨D, e.comp i, fun y => by rw [RingHom.comp_apply, he, hi], ?_⟩
  have hc : Continuous e := (AddMonoidHomClass.isometry_of_norm e he).continuous
  refine Dense.mono ?_ (hs.denseRange.comp hd hc)
  rintro _ ⟨a, rfl⟩
  obtain ⟨q, hq, hqa⟩ : IsAlgebraic F (a : C) := mem_algebraicClosure_iff.1 a.2
  refine ⟨q, hq, ?_⟩
  have h2 : q.eval₂ i (algebraMap A L a) = 0 := by
    apply L.subtype.injective
    rw [Polynomial.hom_eval₂, map_zero]
    exact hqa
  rw [Function.comp_apply, ← Polynomial.hom_eval₂, h2, map_zero]

theorem fieldSt : GlobalTheory.LocM.Cht.FieldSt := by
  intro p R _ _ _ _ _ hp hpm
  let F := FractionRing R
  have hp0 : (p : R) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    exists_complete_isAlgClosed_of_isDiscreteValuationRing R F hp0 hpm
      (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
  have hF : #F ≤ 𝔠 :=
    (IsLocalization.cardinalMk_le (nonZeroDivisors R)).trans (mk_le_aleph0.trans aleph0_le_continuum)
  have hx : 1 < ‖algebraMap F C (algebraMap R F p)⁻¹‖ := by
    rw [map_inv₀, norm_inv, hCp, inv_inv]; exact h1
  haveI : CharZero F := charZero_of_injective_ringHom (IsFractionRing.injective R F)
  obtain ⟨D, i, hi, hd⟩ := exists_scf_dense hF (by rw [← hCp, map_natCast, map_natCast]) hx
  let g : R →+* ↥D.S := i.comp (algebraMap R F)
  have hginj : Function.Injective g := i.injective.comp (IsFractionRing.injective R F)
  have hle : ∀ a : R, ‖g a‖ ≤ 1 := fun a => by
    rw [RingHom.comp_apply, hi]; exact (hC _).2 ⟨a, rfl⟩
  have hlt : ∀ a ∈ maximalIdeal R, ‖g a‖ < 1 := fun a ha => by
    refine GlobalTheory.SmallClosedField.norm_lt_one_of_mem_maximalIdeal g hle hp0 ?_ ha
    rw [map_natCast, D.norm_p]
    exact inv_lt_one_of_one_lt₀ h1
  have hone : ∀ a b : R, a * b = 1 → ‖g a‖ = 1 := fun a b hab => by
    have e : ‖g a‖ * ‖g b‖ = 1 := by rw [← norm_mul, ← map_mul, hab, map_one, norm_one]
    nlinarith [norm_nonneg (g a), norm_nonneg (g b), hle a, hle b]
  let f : R →+* ↥(intO ↥D.S) := g.codRestrict (intO ↥D.S) hle
  let K₀ : Subfield ↥D.S := Subfield.closure (Set.range fun a => ((f a : ↥(intO ↥D.S)) : ↥D.S))
  have hK₀ : K₀ = i.fieldRange := by
    refine le_antisymm (Subfield.closure_le.2 ?_) ?_
    · rintro _ ⟨a, rfl⟩
      exact ⟨algebraMap R F a, rfl⟩
    · rintro _ ⟨y, rfl⟩
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) y
      rw [map_div₀]
      exact div_mem (Subfield.subset_closure ⟨a, rfl⟩) (Subfield.subset_closure ⟨b, rfl⟩)
  have hmem : ∀ y : F, i y ∈ K₀.topologicalClosure := fun y =>
    K₀.le_topologicalClosure (hK₀ ▸ ⟨y, rfl⟩)
  refine ⟨D, f, K₀.topologicalClosure, fun a b h => hginj (congrArg Subtype.val h), ⟨fun a ha => ?_⟩, rfl, ?_, ?_⟩
  · by_contra hna
    obtain ⟨y, hy⟩ := ha.exists_right_inv
    have e : ‖g a‖ * ‖(y : ↥D.S)‖ = 1 := by
      rw [← norm_mul, ← norm_one (α := ↥D.S)]
      exact congrArg (fun t : ↥(intO ↥D.S) => ‖(t : ↥D.S)‖) hy
    have hy1 : ‖(y : ↥D.S)‖ ≤ 1 := y.2
    nlinarith [norm_nonneg (g a), norm_nonneg (y : ↥D.S), hlt a hna]
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hπ0 : g π ≠ 0 := (map_ne_zero_iff g hginj).2 hπ.ne_zero
    have hR : ∀ a : R, a ≠ 0 → ∃ n : ℕ, ‖g a‖ = ‖g π‖ ^ n := fun a ha => by
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
      exact ⟨n, by rw [map_mul, norm_mul, hone _ _ u.mul_inv, one_mul, map_pow, norm_pow]⟩
    refine isDiscreteValuationRing_intO (K := ↥K₀.topologicalClosure) ⟨g π, hmem _⟩
      (fun h => hπ0 (congrArg Subtype.val h)) (hlt π hπ.not_isUnit) fun x hx0 => ?_
    have hx1 : (x : ↥D.S) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hxc : (x : ↥D.S) ∈ closure (K₀ : Set ↥D.S) := x.2
    obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hxc ‖(x : ↥D.S)‖ (norm_pos_iff.2 hx1)
    rw [dist_eq_norm] at hxz
    have hzn : ‖z‖ = ‖(x : ↥D.S)‖ := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (x : ↥D.S)) (y := -((x : ↥D.S) - z))
        (by rw [norm_neg]; exact hxz.ne')
      rw [norm_neg, max_eq_left hxz.le] at this
      rw [← this]; congr 1; ring
    rw [hK₀] at hz
    obtain ⟨y, rfl⟩ := hz
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) y
    have ha : a ≠ 0 := by
      rintro rfl
      exact hx1 (norm_eq_zero.1 (by rw [← hzn]; simp))
    obtain ⟨m, hm⟩ := hR a ha
    obtain ⟨n, hn⟩ := hR b (nonZeroDivisors.ne_zero hb)
    refine ⟨(m : ℤ) - n, ?_⟩
    change ‖(x : ↥D.S)‖ = ‖g π‖ ^ ((m : ℤ) - n)
    rw [zpow_sub₀ (norm_ne_zero_iff.2 hπ0), zpow_natCast, zpow_natCast, ← hm, ← hn, ← hzn, map_div₀, norm_div]
    rfl
  · refine hd.mono ?_
    rintro z ⟨q, hq, hqz⟩
    let j : F →+* ↥K₀.topologicalClosure := i.codRestrict _ hmem
    refine ⟨q.map j, (Polynomial.map_ne_zero_iff j.injective).2 hq, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    exact hqz

end GlobalTheory.LocM.Cht.CompletedClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDominantSpMapOfInjective
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.LatDRCrd

theorem isDominant_spMap_of_injective {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (h : Function.Injective φ) : IsDominant (spMap φ) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot φ).1 h]; exact bot_le)⟩

theorem dualMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    (dualMap ψ).comp (dualMap φ) = dualMap (ψ.comp φ) := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

theorem mem_latDR_iff_crd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [X.IsSeparated] (t : SAB H X) (L : FinLB X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd t L M), IsLieEmb t L aff crd → ∀ (i : Fin L.n) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (φ : Γ(X, L.U i) →+* ↥(intO C)) (x : Sp C ⟶ X) (w : Tn t C), spMap ((intO C).subtype.comp φ) ≫ (aff i).fromSpec = x → IsTanAtG t x w → (w ∈ latDR t x ↔ ∀ r, ‖crd i C ((intO C).subtype.comp φ) w r‖ ≤ 1) := by
  intro E _ _ _ H X _ t L aff M crd h i C _ _ φ x w hx hw
  have hx' : spMap (intO C).subtype ≫ (spMap φ ≫ (aff i).fromSpec) = x := by
    rw [← Category.assoc, spMap_comp', hx]
  constructor
  · rintro ⟨xO, hxO, vO, hv, rfl⟩ r
    have := isDominant_spMap_of_injective (intO C).subtype Subtype.val_injective
    obtain rfl : xO = spMap φ ≫ (aff i).fromSpec :=
      ext_of_isDominant (spMap (intO C).subtype) (hxO.trans hx'.symm)
    rw [h.nat i _ C φ (intO C).subtype vO hv]
    exact (crd i _ φ vO r).2
  · intro hr
    subst hx
    obtain ⟨n, v, D, ⟨hv, hb⟩, hD⟩ := h.split i
    obtain ⟨a, ha, -⟩ := hb C _ w hw
    have hvC := fun j => isTanAtG_map t ((intO C).subtype.comp φ) (hv j)
    have hvO := fun j => isTanAtG_map t φ (hv j)
    have h1 : spMap (RingHom.id Γ(X, L.U i)) = 𝟙 _ := Spec.map_id _
    have hc := h.comb i C _ n _ a w hvC ha
    have hn : ∀ j, crd i C ((intO C).subtype.comp φ) (spMap (dualMap ((intO C).subtype.comp φ)) ≫ v j) =
        ((intO C).subtype.comp φ) ∘ crd i _ (RingHom.id _) (v j) := fun j =>
      h.nat i _ C (RingHom.id _) ((intO C).subtype.comp φ) (v j) (by rw [h1, Category.id_comp]; exact hv j)
    have hD' := hD.map ((intO C).subtype.comp φ)
    have hmem : ∀ j, a j ∈ intO C := fun j => by
      have e : a j = ∑ r, ((intO C).subtype.comp φ) (D j r) * crd i C ((intO C).subtype.comp φ) w r := by
        rw [hc]
        simp only [hn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        have : ∀ j', ∑ r, ((intO C).subtype.comp φ) (D j r) *
            (a j' * (((intO C).subtype.comp φ) ∘ crd i _ (RingHom.id _) (v j')) r) =
            if j = j' then a j' else 0 := fun j' => by
          have e := hD' j j'
          simp only [mul_left_comm _ (a j'), ← Finset.mul_sum]
          refine (congrArg (a j' * ·) e).trans ?_
          split_ifs <;> simp
        simp only [this]
        simp
      rw [e]
      exact Subring.sum_mem _ fun r _ => Subring.mul_mem _ (φ (D j r)).2 (hr r)
    obtain ⟨wO, hwO, hcO⟩ := exists_comb t hvO fun j => (⟨a j, hmem j⟩ : ↥(intO C))
    refine ⟨_, hx', wO, hwO, ?_⟩
    have hb := GlobalTheory.LatDRFree.comb_map t (intO C).subtype hcO
    simp only [← Category.assoc, spMap_comp', dualMap_comp'] at hb
    exact comb_unique t hvC hb ha

end GlobalTheory.LatDRCrd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameComposeRingHomBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrame_compose_ringHom_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) := by
  first | exact @GlobalTheory.ShFam.Pad.isFrame_baseChange | exact GlobalTheory.ShFam.Pad.isFrame_baseChange | (intros; apply GlobalTheory.ShFam.Pad.isFrame_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLBOfChartPull
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.NefFibre

theorem isLB_of_chartPull {Y : Scheme.{0}} {A M : LB Y} (a : ChartPull A M (𝟙 Y)) (hM : M.IsLB)
    (hc : ∀ y : Y, ∃ i, y ∈ A.U i) : A.IsLB := by
  refine GlobalTheory.GenSpread.isLB_of_gm A hc fun y i j k hi hj hk => ?_
  have hi' : y ∈ M.U (a.idx i) := a.le i hi
  have hj' : y ∈ M.U (a.idx j) := a.le j hj
  have hk' : y ∈ M.U (a.idx k) := a.le k hk
  rw [a.g y i j hi hj, a.g y j k hj hk, a.g y i k hi hk]
  exact gm_cocycle hM (𝟙 Y) y hi' hj' hk'

theorem isNef_fibre_pull : ∀ (R : Type) [CommRing R] (Z X : Scheme.{0}) (s : Z ⟶ Sp R) (b : X ⟶ Z), IsProjOver s →
    IsProjOver (b ≫ s) → ∀ (L : LB Z) (P : Ideal R) [P.IsPrime],
    (letI := GlobalTheory.algebraΓOfHom (pullback.snd s (spMap (algebraMap R P.ResidueField)));
      GlobalTheory.IsNef P.ResidueField (L.pull (pullback.fst s (spMap (algebraMap R P.ResidueField))))) →
    (letI := GlobalTheory.algebraΓOfHom (pullback.snd (b ≫ s) (spMap (algebraMap R P.ResidueField)));
      GlobalTheory.IsNef P.ResidueField ((L.pull b).pull (pullback.fst (b ≫ s) (spMap (algebraMap R P.ResidueField))))) := by
  intro R _ Z X s b hs hbs L P _ h
  set κ := P.ResidueField
  set t := spMap (algebraMap R κ)
  let := GlobalTheory.algebraΓOfHom (pullback.snd s t)
  let := GlobalTheory.algebraΓOfHom (pullback.snd (b ≫ s) t)
  let bP : pullback (b ≫ s) t ⟶ pullback s t :=
    pullback.map (b ≫ s) t s t b (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hfst : bP ≫ pullback.fst s t = pullback.fst (b ≫ s) t ≫ b := pullback.lift_fst _ _ _
  have hsnd : bP ≫ pullback.snd s t = pullback.snd (b ≫ s) t :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  obtain ⟨hpZ, A, hA⟩ := (GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1
    (GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap R κ) hs)
  obtain ⟨hpX, A', hA'⟩ := (GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1
    (GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap R κ) hbs)
  have : IsProper (GlobalTheory.strHom κ (pullback s t)) := by
    rwa [GlobalTheory.strHom_eq (f := pullback.snd s t) fun _ => rfl]
  have : IsProper (bP ≫ pullback.snd s t) := by rw [hsnd]; exact hpX
  have : IsProper bP := IsProper.of_comp bP (pullback.snd s t)
  have hN := GlobalTheory.PosBaseChange.isNef_pull (E := κ) h hA hA' bP bP.isClosedMap
  have hM : ((L.pull (pullback.fst s t)).pull bP).IsLB := hN.isLB
  have a : ChartPull ((L.pull b).pull (pullback.fst (b ≫ s) t)) ((L.pull (pullback.fst s t)).pull bP)
      (𝟙 _) :=
    GlobalTheory.chartPullPullLinComb L (fun _ : PUnit => b) (fun _ => 1) (pullback.fst (b ≫ s) t) (pullback.fst s t)
      (fun _ => bP) fun _ => hfst
  have hL : ((L.pull b).pull (pullback.fst (b ≫ s) t)).IsLB := by
    refine isLB_of_chartPull a hM fun y => ?_
    obtain ⟨J, hJ⟩ := exists_chart hM y
    refine ⟨fun _ _ => J PUnit.unit PUnit.unit, ?_⟩
    have h1 : (pullback.fst s t) (bP y) ∈ L.U (J PUnit.unit PUnit.unit) := mem_pull.1 (mem_pull.1 hJ)
    rw [← Scheme.Hom.comp_apply, hfst, Scheme.Hom.comp_apply] at h1
    exact mem_pull.2 (mem_pull.2 h1)
  exact GlobalTheory.IsNef.of_lbIso hN hL (LBIso.chartPull a (chartPullId _) ⟨_, idIso_isGen hM⟩)

end GlobalTheory.NefFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTangentOfUniqueIntegralLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTangent_of_unique_integral_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (mu : SABMap t' t f) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (b : Bool) (xO : Sp ↥(intO C) ⟶ X'), (∀ y : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ xO ≫ f → y = xO ≫ f) → ∀ v, IsTanAtG t' (spMap (intO C).subtype ≫ xO) v → (v ∈ lat t' p (spMap (intO C).subtype ≫ xO) b ↔ v ≫ mu.φ ∈ lat t p (spMap (intO C).subtype ≫ xO ≫ f) b) := by
  first | exact @GlobalTheory.ShFam.LatPush.lat_push | exact GlobalTheory.ShFam.LatPush.lat_push | (intros; apply GlobalTheory.ShFam.LatPush.lat_push <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsometryConjTransvectionScaleStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_conj_transvection_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (G g : Matrix (Fin N) (Fin N) E) (ξ : Fin N → E) (ε : E), IsIsom G g → g.mulVec ξ = ε • ξ → cc ε = ε → ε ≠ 0 → ∀ α : E, g * transvMat G ξ α = transvMat G ξ (ε ^ 2 * α) * g := by
  first | exact @GlobalTheory.UnipKill.mul_transvMat_of_scale | exact GlobalTheory.UnipKill.mul_transvMat_of_scale | (intros; apply GlobalTheory.UnipKill.mul_transvMat_of_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KTrivAndPolAtTensAt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.LocM
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.PolFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {S : Scheme.{0}}
  {t : SAB H S} {K : Type} [Field K] {x : Sp K ⟶ S} {u : SAB H (Sp K)}

theorem exists_to_fibre (m : SABMap u t x) :
    ∃ φ : u.G.left ⟶ ((Over.pullback x).obj t.G).left, IsGrpPullback u.G ((Over.pullback x).obj t.G) (𝟙 _) φ ∧
      LBIso u.PP.L ((t.PP.L.pull (pullback.fst t.G.hom x)).pull φ) := by
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x) (m.cart.congr (Category.id_comp _).symm rfl)
    (isGrpPullback_pullback t.G x) t.PP.isLB hM u.PP.isLB (GlobalTheory.Ex.UnifModel.iso_of_map m)
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩
  exact ⟨φ, hφ, e⟩

theorem exists_of_fibre (m : SABMap u t x) :
    ∃ φ : ((Over.pullback x).obj t.G).left ⟶ u.G.left, IsGrpPullback ((Over.pullback x).obj t.G) u.G (𝟙 _) φ ∧
      LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (u.PP.L.pull φ) := by
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom x)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := 𝟙 _) (f := x)
    ((isGrpPullback_pullback t.G x).congr (Category.id_comp _).symm rfl) m.cart t.PP.isLB u.PP.isLB hM
    ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩ (GlobalTheory.Ex.UnifModel.iso_of_map m)
  exact ⟨φ, hφ, e⟩

theorem ample_kTriv_of_polAt (m : SABMap u t x) (hp : GlobalTheory.LN.PolAt t x) :
    RelAmple u.G u.PP.L ∧ KTriv u.G u.PP.L := by
  obtain ⟨φ, hφ, e⟩ := exists_to_fibre m
  exact amplePt _ _ (𝟙 _) _ _ φ hφ _ _ (pull_isLB t.PP.isLB _) u.PP.isLB e hp.2.1 hp.2.2

theorem polAt_of_map (m : SABMap u t x) (hp : IsProper (pullback.snd t.G.hom x)) (hA : RelAmple u.G u.PP.L)
    (hK : KTriv u.G u.PP.L) : GlobalTheory.LN.PolAt t x := by
  obtain ⟨φ, hφ, e⟩ := exists_of_fibre m
  have h := amplePt _ _ (𝟙 _) _ _ φ hφ _ _ u.PP.isLB (pull_isLB t.PP.isLB _) e hA hK
  exact ⟨hp, h.1, h.2⟩

end GlobalTheory.LocM.PolFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def KeyAtVia {Y : Model Xo c β} (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    (x : KeyIn R) (φ : x.P.A.left ⟶ Y.t.G.left) : Prop :=
  ∃ (he : eSec x.P.A ≫ φ = z ≫ eSec Y.t.G) (w : LB.Iso x.P.L (Y.t.PP.L.pull φ)) (hg : x.P.g = M.n),
    IsGrpPullback x.P.A Y.t.G z φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ z he Y.t.PP.L Y.t.PP.rig) ∧
    (∀ (j : (Y.t.PP.L.pull φ).ι) (i : x.P.L.ι)
      (h : (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U (j PUnit.unit))),
      (φ.appLE _ _ h).hom (M.θ (j PUnit.unit)) =
        (show Γ(x.P.A.left, (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    ∀ i, (x.v i).left ≫ φ = spMap (dualMap (ev z M.U hz)) ≫ M.v₀ (i.cast hg)

def ArcFib (Y : Model Xo c β) (bF : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left) (u : HolUnif x.P.A x.P.L g) : Prop :=
  ∀ z, ∃ ψ : Sp ℂ ⟶ Y.oF.t.G.left, ψ ≫ Y.m0.toSABMap.φ = (Fu.ex i P z).left ∧
    ψ ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF ∧ (u.ex z).left ≫ φ = ψ ≫ Y.m.φ

end GlobalTheory.ArcNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorFlagDensityGlueLowerUnitriangularStatement
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingMinorFlagDensity_glueLowerUnitriangular : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ (A : Matrix (Fin r) (Fin r) ℂ) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)), IsUnit (shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det → dens A (glue e w) = dens (shear (reindex e e A) (toMat w.1)).toBlocks₂₂ w.2.1 * ‖(shear (reindex e e A) (toMat w.1)).toBlocks₂₂.det‖ ^ (-(2 * p : ℤ)) * dens (schur (shear (reindex e e A) (toMat w.1))) w.2.2 := by
  first | exact @GlobalTheory.FlagFibre.dens_glue | exact GlobalTheory.FlagFibre.dens_glue | (intros; apply GlobalTheory.FlagFibre.dens_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyMatrixDotProductNonnegIntegralStatement
section
open GlobalTheory.ShFam.Hor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromy_matrix_dotProduct_nonneg_integral : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → ∀ (k : Fin a) (v : Fin g → ℤ), 0 ≤ dotProduct v ((B k).mulVec v) := by
  first | exact @GlobalTheory.monodromy_dotProduct_nonneg | exact GlobalTheory.monodromy_dotProduct_nonneg | (intros; apply GlobalTheory.monodromy_dotProduct_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAdaptedOfIntStepStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_adapted_of_intStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ), Geo M π → IntStep A σ k → Nonempty (Adapted A σ k) := by
  first | exact @GlobalTheory.DRFlag.AdaptedOfStep.nonempty_adapted | exact GlobalTheory.DRFlag.AdaptedOfStep.nonempty_adapted | (intros; apply GlobalTheory.DRFlag.AdaptedOfStep.nonempty_adapted <;> assumption)
end

