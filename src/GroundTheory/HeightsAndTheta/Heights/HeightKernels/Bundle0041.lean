import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0038
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0039

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopStacked
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField
open scoped ComplexOrder

noncomputable section

namespace TopDualStacked

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def DegForm (F G : HermLattice K i) : Prop :=
  ∀ (T T' : Type) [Fintype T] [DecidableEq T] [Fintype T'] [DecidableEq T']
    (b : Module.Basis T ℤ (dualLattice F)) (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (b' : Module.Basis T' ℤ (dualLattice G))
    (hb' : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b'))) (II : IntersectionSystem),
    1 ≤ i → IsIntersectionSystem II →
    II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine G.withStdMetric b' hb') =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) +
        (F.withStdMetric.degree - G.withStdMetric.degree) *
          geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

theorem DegForm.trans {F G H : HermLattice K i} (h₁ : DegForm F G) (h₂ : DegForm G H) : DegForm F H := by
  intro T T' _ _ _ _ b hb b' hb' II hi hII
  obtain ⟨S, hS, hdS, ⟨c⟩⟩ := DualLatticeBasisExists.proof K i G
  have hc := DualEmbBijective.proof K i G S c
  have e₂ := h₂ S T' c hc b' hb' II hi hII
  have e₁ := h₁ T S b hb c hc II hi hII
  linarith

theorem degForm_self (hBasis : DualTopBasisChange.Statement) (F : HermLattice K i) : DegForm F F := by
  intro T T' _ _ _ _ b hb b' hb' II hi hII
  have e := hBasis K i F.withStdMetric T T' b hb b' hb' II hi hII
  rw [sub_self, zero_mul, add_zero]
  exact e

theorem withStdMetric_eq {F G : HermLattice K i} (h : F.lattice = G.lattice) :
    F.withStdMetric = G.withStdMetric := by
  cases F
  cases G
  cases h
  rfl

theorem degForm_iff (F G : HermLattice K i) : DegForm F G ↔ DegForm F.withStdMetric G.withStdMetric :=
  Iff.rfl

theorem degForm_of_eq (hBasis : DualTopBasisChange.Statement) {F G : HermLattice K i}
    (h : G.lattice = F.lattice) : DegForm F G := by
  rw [degForm_iff, withStdMetric_eq h]
  exact degForm_self hBasis _

theorem degForm_of_cover (hSimple : DualTopSimpleSub.Statement) {F G : HermLattice K i}
    (hlt : G.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), G.lattice ≤ N → N ≤ F.lattice → N = G.lattice ∨ N = F.lattice) :
    DegForm F G :=
  fun T T' _ _ _ _ b hb b' hb' II hi hII => hSimple K i F G T T' b hb b' hb' II hi hII hlt hcov

theorem exists_smul_mem (X : HermLattice K i) (v : Fin i → K) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ c • v ∈ X.lattice :=
  _root_.GroundTheory.Variant₂.N1.exists_smul_mem_hermitianLattice X v

theorem exists_cover {F X : HermLattice K i} (hlt : X.lattice < F.lattice) :
    ∃ w ∈ F.lattice, w ∉ X.lattice ∧ ∀ N : Submodule (𝓞 K) (Fin i → K), X.lattice ≤ N →
      N ≤ X.lattice ⊔ Submodule.span (𝓞 K) {w} → N = X.lattice ∨ N = X.lattice ⊔ Submodule.span (𝓞 K) {w} :=
  _root_.GroundTheory.Variant₂.N1.exists_cover hlt

def addVector (X : HermLattice K i) (w : Fin i → K) : HermLattice K i where
  lattice := X.lattice ⊔ Submodule.span (𝓞 K) {w}
  fg := X.fg.sup (Submodule.fg_span_singleton w)
  span_eq := eq_top_iff.mpr (X.span_eq ▸ Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left))
  metric := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  conj := fun _ => by simp

theorem degForm_of_le (hSimple : DualTopSimpleSub.Statement) (hBasis : DualTopBasisChange.Statement)
    (F G : HermLattice K i) (hle : G.lattice ≤ F.lattice) : DegForm F G := by
  have : IsNoetherian (𝓞 K) F.lattice := isNoetherian_of_fg_of_noetherian _ F.fg
  suffices h : ∀ N : Submodule (𝓞 K) F.lattice, ∀ G : HermLattice K i,
      G.lattice = N.map F.lattice.subtype → DegForm F G by
    refine h (G.lattice.comap F.lattice.subtype) G ?_
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  intro N
  refine WellFoundedGT.induction
    (motive := fun N : Submodule (𝓞 K) F.lattice => ∀ G : HermLattice K i,
      G.lattice = N.map F.lattice.subtype → DegForm F G) N ?_
  intro N IH G hG
  by_cases hGF : G.lattice = F.lattice
  · exact degForm_of_eq hBasis hGF
  have hlt : G.lattice < F.lattice :=
    lt_of_le_of_ne (hG ▸ Submodule.map_subtype_le _ _) hGF
  obtain ⟨w, hwF, hwG, hcov⟩ := exists_cover hlt
  have hG'F : (addVector G w).lattice ≤ F.lattice :=
    sup_le hlt.le ((Submodule.span_singleton_le_iff_mem _ _).mpr hwF)
  have hGG' : G.lattice < (addVector G w).lattice :=
    lt_of_le_of_ne le_sup_left fun h =>
      hwG (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
  have hNG : N = G.lattice.comap F.lattice.subtype := by
    rw [hG, Submodule.comap_map_eq_of_injective F.lattice.injective_subtype]
  have hN : N < (addVector G w).lattice.comap F.lattice.subtype := by
    rw [hNG]
    refine lt_of_le_of_ne (Submodule.comap_mono hGG'.le) fun h => hGG'.ne ?_
    have h2 := congrArg (Submodule.map F.lattice.subtype) h
    rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.mpr hlt.le,
      inf_eq_right.mpr hG'F] at h2
  have h1 : DegForm F (addVector G w) :=
    IH _ hN (addVector G w) (by rw [Submodule.map_comap_subtype, inf_eq_right.mpr hG'F])
  exact h1.trans (degForm_of_cover hSimple hGG' hcov)

end TopDualStacked

open TopDualStacked in

theorem DualTopStacked.proof (hSimple : DualTopSimpleSub.Statement) (hBasis : DualTopBasisChange.Statement)
    (hDeg : DualStackedDegree.Statement) : DualTopStacked.Statement := by
  intro K _ _ i F F' T _ _ b hb b' hb' a II hi hII hle hab
  have e := degForm_of_le hSimple hBasis F F' hle T T b hb b' hb' II hi hII
  rw [hDeg K i F F' T b b' a hle hab] at e
  exact e

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.POneBlockPointDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace OneBlockPointDeg

variable {Φ Φ' : Type} [Field Φ] [Field Φ'] [Algebra Φ Φ'] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {k₀ : K}

theorem isMultiHomog_of_isHomogeneous (hK : ∀ k, k = k₀) {f : MRingOver Φ ι} {n : ℕ}
    (hf : f.IsHomogeneous n) : IsMultiHomog f fun _ => n := by
  intro m hm k
  have h := hf (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma, Fintype.sum_eq_single k
    (fun k' hk' => absurd ((hK k').trans (hK k).symm) hk')] at h
  exact h

theorem aeval_homog (hK : ∀ k, k = k₀) {w : (Σ k, ι k) → Φ'} {c : ∀ k, ι k} (hc : w ⟨k₀, c k₀⟩ ≠ 0)
    {g : MRingOver Φ ι} {n : ℕ} (hg : g.IsHomogeneous n) :
    aeval (fun p => w p / w ⟨k₀, c k₀⟩) g * w ⟨k₀, c k₀⟩ ^ n = aeval w g := by
  classical
  have hz : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by obtain rfl := hK k; exact hc
  have e : (fun p : Σ k, ι k => w p / w ⟨k₀, c k₀⟩) = Inter.ChartRankAdjoin.affCoord w c := by
    funext ⟨k, i⟩; obtain rfl := hK k; rfl
  have h := Inter.ChartRankAdjoin.aeval_mul_of_isMultiHomog hz (isMultiHomog_of_isHomogeneous hK hg)
  rwa [Fintype.prod_eq_single k₀ (fun k hk => absurd (hK k) hk), ← e] at h

theorem ringKrullDim_adjoin_eq_one {σ : Type} (w : σ → Φ') (s : Set Φ') (x : Φ')
    [Module.Finite Φ (Algebra.adjoin Φ s)] (htr : Transcendental (Algebra.adjoin Φ s) x)
    (hx : x ∈ Algebra.adjoin Φ (Set.range w)) (hs : Set.range w ⊆ Algebra.adjoin Φ (s ∪ {x})) :
    ringKrullDim (Algebra.adjoin Φ (Set.range w)) = 1 := by
  have hAB : Algebra.adjoin Φ (Set.range w) ≤ (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ := by
    rw [← Algebra.adjoin_union_eq_adjoin_adjoin]; exact Algebra.adjoin_le hs
  let _ : Algebra (Algebra.adjoin Φ (Set.range w)) ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ) :=
    (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  let f : (Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ →ₐ[Algebra.adjoin Φ (Set.range w)] Φ' :=
    { ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ).val.toRingHom with commutes' := fun _ => rfl }
  have hint : Algebra.IsIntegral (Algebra.adjoin Φ (Set.range w))
      ((Algebra.adjoin (Algebra.adjoin Φ s) {x}).restrictScalars Φ) := ⟨fun b => by
    refine (isIntegral_algHom_iff f Subtype.val_injective).mp ?_
    have hb : (b : Φ') ∈ Algebra.adjoin Φ (s ∪ {x}) := by
      rw [Algebra.adjoin_union_eq_adjoin_adjoin]; exact b.2
    refine (Algebra.adjoin_le (S := (integralClosure (Algebra.adjoin Φ (Set.range w)) Φ').restrictScalars Φ) ?_) hb
    rintro y (hy | hy)
    · exact ((IsIntegral.of_finite Φ (⟨y, Algebra.subset_adjoin hy⟩ : Algebra.adjoin Φ s)).map
        (Algebra.adjoin Φ s).val).tower_top
    · rw [Set.mem_singleton_iff.mp hy]
      exact isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin Φ (Set.range w)))⟩
  have : IsArtinianRing (Algebra.adjoin Φ s) := IsArtinianRing.of_finite Φ _
  have : IsNoetherianRing (Algebra.adjoin Φ s) := IsNoetherianRing.of_finite Φ _
  rw [← GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (Subalgebra.inclusion_injective hAB)]
  change ringKrullDim (Algebra.adjoin (Algebra.adjoin Φ s) {x}) = 1
  rw [← ringKrullDim_eq_of_ringEquiv (Polynomial.algEquivOfTranscendental (s := x) (h := htr)).toRingEquiv,
    Polynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_isField (IsArtinianRing.isField_of_isDomain _)]
  rfl

end OneBlockPointDeg

open OneBlockPointDeg in

theorem OneBlockPointDeg.proof : OneBlockPointDeg.Statement := by
  classical
  intro Φ Φ' _ _ _ K _ ι _ k₀ hK w c hc hfin htr
  set r : (Σ k, ι k) → Φ' := fun p => w p / w ⟨k₀, c k₀⟩ with hr
  set L := Algebra.adjoin Φ (Set.range r) with hL
  have hz : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by obtain rfl := hK k; exact hc
  have hcard : Fintype.card K = 1 := Fintype.card_eq_one_iff.mpr ⟨k₀, hK⟩
  have hrL : ∀ p, r p ∈ L := fun p => Algebra.subset_adjoin ⟨p, rfl⟩

  have hcomp : ∀ f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ'), ∀ n,
      homogeneousComponent n f ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') := by
    intro f hf n
    have hmem : ∀ g : MRingOver Φ ι, aeval r g ∈ L := fun g => by
      rw [hL, ← aeval_range]; exact AlgHom.mem_range_self _ g
    let P : Polynomial L := ∑ i ∈ Finset.range (f.totalDegree + 1),
      Polynomial.monomial i ⟨aeval r (homogeneousComponent i f), hmem _⟩
    have hP : Polynomial.aeval (w ⟨k₀, c k₀⟩) P = 0 := by
      have h0 := RingHom.mem_ker.mp hf
      rw [← sum_homogeneousComponent f, map_sum] at h0
      rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.aeval_monomial, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous i f)]
      rfl
    have hP0 := (transcendental_iff.mp htr) P hP
    rw [RingHom.mem_ker, ← aeval_homog hK hc (homogeneousComponent_isHomogeneous n f)]
    by_cases hn : n < f.totalDegree + 1
    · have h1 := congrArg (fun q : Polynomial L => q.coeff n) hP0
      simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq',
        Finset.mem_range, hn, if_true, Polynomial.coeff_zero] at h1
      rw [show aeval r (homogeneousComponent n f) = ((⟨_, hmem _⟩ : L) : Φ') from rfl, h1]
      simp
    · rw [homogeneousComponent_eq_zero (φ := f) (n := n) (by omega)]; simp
  have hchart : IsChart (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c := fun k => by
    rw [RingHom.mem_ker, aeval_X]; exact hz k

  have hhom : IsMultiHomogIdeal (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) := by
    refine ⟨{g | g ∈ RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ') ∧ ∃ a, IsMultiHomog g a}, fun g hg => hg.2,
      le_antisymm (fun f hf => ?_)
      (Ideal.span_le.mpr fun g hg => hg.1)⟩
    rw [← sum_homogeneousComponent f]
    exact Ideal.sum_mem _ fun i _ => Ideal.subset_span
      ⟨hcomp f hf i, _, isMultiHomog_of_isHomogeneous hK (homogeneousComponent_isHomogeneous i f)⟩
  refine ⟨⟨⟨RingHom.ker_isPrime _, hhom, fun k => ⟨c k, hchart k⟩⟩, ?_⟩, hchart, ?_⟩
  ·
    have hs : Set.range w ⊆ Algebra.adjoin Φ (Set.range r ∪ {w ⟨k₀, c k₀⟩}) := by
      rintro _ ⟨p, rfl⟩
      rw [show w p = r p * w ⟨k₀, c k₀⟩ from (div_mul_cancel₀ _ hc).symm]
      exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inl ⟨p, rfl⟩))
        (Algebra.subset_adjoin (Or.inr rfl))
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')).toRingEquiv,
      aeval_range, ringKrullDim_adjoin_eq_one w (Set.range r) _ htr (Algebra.subset_adjoin ⟨_, rfl⟩) hs, hcard]
    rfl
  ·
    have halg : ∀ x ∈ Set.range r, IsAlgebraic Φ x := by
      rintro _ ⟨p, rfl⟩
      exact (IsAlgebraic.of_finite Φ (⟨r p, hrL p⟩ : L)).algHom L.val
    have e : (fun q : Σ k, ι k => w q / w ⟨q.1, c q.1⟩) = r := by
      funext ⟨k, i⟩; obtain rfl := hK k; rfl
    rw [Inter.ChartRankAdjoin.proof K ι Φ Φ' w c hz hhom, e,
      ← IntermediateField.finrank_eq_finrank_subalgebra,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertRIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial NumberField

noncomputable section

namespace VerticalIndex

variable {T : Type} [Fintype T] {K' : Type} [Field K']

theorem aeval_mem_sectionMod (y : (Σ _ : Unit, T) → K') {s : MRing (fun _ : Unit => T)}
    (hs : IsMultiHomog s (fun _ => 1)) : aeval y s ∈ sectionMod y :=
  HilbertSamuel.NormCountBounded.secM_le_chartLat y 1 (Submodule.subset_span ⟨s, hs, rfl⟩)

omit [Fintype T] in

theorem span_toAddSubgroup (y : (Σ _ : Unit, T) → K') (x : K') :
    (Submodule.span (curveRing y) {x}).toAddSubgroup = curveMul y x := by
  ext z
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, curveMul, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩

omit [Fintype T] in

theorem genIndex_eq_card (y : (Σ _ : Unit, T) → K') {x : K'} (hx : x ∈ sectionMod y) :
    genIndex (chartLat y (fun _ => 1) 1) (curveMul y x) = Nat.card (sectionQuot y x) := by
  have hle : curveMul y x ≤ chartLat y (fun _ => 1) 1 := by
    rw [← span_toAddSubgroup]
    intro z hz
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) hz
  rw [genIndex, AddSubgroup.relIndex_eq_one.mpr hle, Nat.cast_one, div_one, ← span_toAddSubgroup]
  rfl

end VerticalIndex

open IndefiniteRowSideFullHecke.HeightsSet in

theorem VertRIndex.proof (hL : LogCardLength.Statement) (hF : SectionQuotFinite.Statement)
    (hV : VertPointLength.Statement) (hR : VertPointResidue.Statement) : VertRIndex.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  have := hF T K' y s hP hs hsP
  obtain ⟨hbij, hmult⟩ := hV T K' y s hP hs hsP
  rw [VerticalIndex.genIndex_eq_card y (VerticalIndex.aeval_mem_sectionMod y hs),
    hL (curveRing y) (sectionQuot y (aeval y s)), vertR]
  calc _ = ∑ᶠ W ∈ divSupp (mCoordIdeal y) s, (locLen (curvePtIdeal y W) (sectionQuot y (aeval y s)) : ℝ) *
          Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W)) := by
        refine finsum_mem_congr rfl fun W hW => ?_
        rw [if_neg (CurveDivVertical.full Unit (fun _ => T) _ s _ hP hs hsP W hW), hmult W hW,
          ← hR T K' y s hP hs hsP W hW]
        congr 3
    _ = ∑ᶠ m ∈ {m : Ideal (curveRing y) | m.IsMaximal ∧ locLen m (sectionQuot y (aeval y s)) ≠ 0},
          (locLen m (sectionQuot y (aeval y s)) : ℝ) * Real.log (Nat.card (curveRing y ⧸ m)) :=
        finsum_mem_eq_of_bijOn _ hbij fun _ _ => rfl
    _ = _ := by
        refine finsum_mem_inter_support_eq _ _ {m : Ideal (curveRing y) | m.IsMaximal} ?_
        ext m
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, fun h0 => h2 (by simp [h0])⟩, h2⟩⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def stackedDiag {T : Type} [DecidableEq T] (a : T → ℤ) : ∀ _ : Unit, T → T → ℤ :=
  fun _ t s => if t = s then a t else 0

abbrev stackedBlocks (T : Type) : Unit ⊕ Unit → Type := Sum.elim (dualBlocks T) (dualBlocks T)

def stackedGraph {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) : Ideal (MRing (stackedBlocks T)) :=
  graphIdeal (dualIdeal b') (linForm (stackedDiag a))

def graphFirst {T : Type} (t : T) : MRing (stackedBlocks T) := X ⟨Sum.inl (), t⟩

def graphSecond {T : Type} (t : T) : MRing (stackedBlocks T) := X ⟨Sum.inr (), t⟩

def degFirst : Unit ⊕ Unit → ℤ := pullDeg (Sum.inl : Unit → Unit ⊕ Unit) fun _ => 1

def degSecond : Unit ⊕ Unit → ℤ := pullDeg (Sum.inr : Unit → Unit ⊕ Unit) fun _ => 1

def DualStackedGraphImage.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    imageZ inrV (stackedGraph b' a) = dualIdeal b ∧
      ∀ (G : GenFibre inrV (stackedGraph b' a))
        (J : IFamily G.Φ (fibreIdx (stackedBlocks T) (Sum.inr : Unit → Unit ⊕ Unit))),
        IsFieldIntersection J → J (fibreIdeal Sum.inr G) 0 Fin.elim0 = 1

def DualStackedGraphHorizontal.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (t : T) (W : Ideal (MRing (stackedBlocks T))), IsHorizontal W →
      (W ∈ divSupp (stackedGraph b' a) (graphSecond t) ↔
        W ∈ divSupp (stackedGraph b' a) (C (a t) * graphFirst t)) ∧
      (W ∈ divSupp (stackedGraph b' a) (graphSecond t) →
        multAt (stackedGraph b' a ⊔ Ideal.span {graphSecond t}) W =
          multAt (stackedGraph b' a ⊔ Ideal.span {C (a t) * graphFirst t}) W)

def DualStackedGraphFibre.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (t : T) (L : Fin (i - 1) → HermLine (stackedBlocks T)),
      (∀ j, (L j).a = degFirst ∨ (L j).a = degSecond) →
      ((∀ j, (L j).a = degSecond) →
        vertR (stackedGraph b' a) L (graphSecond t) - vertR (stackedGraph b' a) L (C (a t) * graphFirst t) =
          -∑ s, Real.log |(a s : ℝ)|) ∧
      ((∃ j, (L j).a = degFirst) →
        vertR (stackedGraph b' a) L (graphSecond t) - vertR (stackedGraph b' a) L (C (a t) * graphFirst t) = 0)

example {T : Type} : ∀ j : Fin (1 - 1), ((Fin.elim0 j : HermLine (stackedBlocks T))).a = degFirst ∨
    ((Fin.elim0 j : HermLine (stackedBlocks T))).a = degSecond :=
  fun j => j.elim0

theorem degFirst_inr : degFirst (Sum.inr ()) = 0 := by
  rw [degFirst, pullDeg, Function.extend_apply' _ _ _ (by rintro ⟨u, hu⟩; exact Sum.inl_ne_inr hu)]
  rfl

theorem degSecond_inr : degSecond (Sum.inr ()) = 1 := by
  rw [degSecond, pullDeg, Sum.inr_injective.extend_apply]

end

end GroundTheory.Heights₂.Heights
end

