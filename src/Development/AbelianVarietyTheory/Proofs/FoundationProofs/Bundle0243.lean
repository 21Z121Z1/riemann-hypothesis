import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompatibleCoboundaries
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompareIntegral
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions
open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.TwistedSelmerCompare

namespace GlobalTheory.BlochKatoBaseChange

section Gen

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem mem_HfD_iff (L : Lattice (O := O) ρ) (c : G → V ⧸ L.T) :
    c ∈ HfD PD L ↔ ∃ z ∈ finiteCocycles PD ρ, ∃ v : V, ∀ g, c g = Submodule.Quotient.mk (z g + (ρ g v - v)) := by
  constructor
  · intro hc
    obtain ⟨_, ⟨z, hz1, rfl⟩, _, ⟨v, rfl⟩, h⟩ := Submodule.mem_sup.1 hc
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact ⟨z, hz1, v, fun g => (congrFun h g).symm⟩
  · rintro ⟨z, hz, v, h⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨z, hz, rfl⟩, _, ⟨Submodule.Quotient.mk v, rfl⟩, funext fun g => (h g).symm⟩

end Gen

section Coord

variable {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [CommRing O] [IsDomain O]
  {f : O₀ →+* O} {hf : Function.Injective f} (p : FractionRing O →+ FractionRing O₀)
  (hp : ∀ y x, p (fracMap f hf y * x) = y * p x)
  (hi : ∀ c : O, ∃ d : O₀, p (algebraMap O _ c) = algebraMap O₀ _ d)

def coordQ (k : ℕ) : KOG O k →+ KOG O₀ k :=
  QuotientAddGroup.map (stdG O (FractionRing O) k).toAddSubgroup (stdG O₀ (FractionRing O₀) k).toAddSubgroup
    (AddMonoidHom.compLeft p (Fin k)) (by
      rintro _ ⟨u, rfl⟩
      choose d hd using hi
      exact ⟨fun j => d (u j), funext fun j => (hd (u j)).symm⟩)

theorem coordQ_mk {k : ℕ} (x : Fin k → FractionRing O) :
    coordQ p hi k (Submodule.Quotient.mk x) = Submodule.Quotient.mk (fun j => p (x j)) := rfl

include hp in
theorem coordQ_act {Γ : Type} [Group Γ] {k : ℕ} (M₀ : Γ →* Matrix (Fin k) (Fin k) O₀) (g : Γ) (x : KOG O k) :
    coordQ p hi k (WKG (mapM f M₀) g x) = WKG M₀ g (coordQ p hi k x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change coordQ p hi k (Submodule.Quotient.mk
      ((((M₀ g).map f).map (algebraMap O (FractionRing O))).mulVec x)) =
    Submodule.Quotient.mk (((M₀ g).map (algebraMap O₀ (FractionRing O₀))).mulVec fun j => p (x j))
  rw [coordQ_mk]
  congr 1
  funext j
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, ← fracMap_alg f hf, hp]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  [Algebra ℤ_[l] O₀] [TopologicalSpace O₀] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O)

include hp in
theorem exists_coordLL (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) :
    ∃ q : ↥B.LL.1 →ₗ[ℚ_[l]] ↥B₀.LL.1, ∀ x, q (Br.toLLK B x) = Br.toLLK B₀ (p x) := by
  obtain ⟨φ, hφ⟩ := exists_coefMap B₀ B f hf hz
  let e := RingEquiv.ofBijective _ (toLLK_bijective B)
  let q : ↥B.LL.1 →+ ↥B₀.LL.1 := (Br.toLLK B₀).toAddMonoidHom.comp (p.comp e.symm.toAddMonoidHom)
  have hq : ∀ x, q (Br.toLLK B x) = Br.toLLK B₀ (p x) := fun x =>
    congrArg (fun y => Br.toLLK B₀ (p y)) (e.symm_apply_apply x)
  refine ⟨{ q with map_smul' := fun r x => ?_ }, hq⟩
  obtain ⟨x, rfl⟩ := (toLLK_bijective B).2 x
  obtain ⟨y, hy⟩ := (toLLK_bijective B₀).2 (algebraMap ℚ_[l] _ r)
  change q (r • Br.toLLK B x) = r • q (Br.toLLK B x)
  rw [Algebra.smul_def, Algebra.smul_def, ← φ.commutes, ← hy, hφ, ← map_mul, hq, hq, hp, map_mul]

set_option synthInstance.maxHeartbeats 400000 in
theorem phi_coordQ {k : ℕ} (q : ↥B.LL.1 →ₗ[ℚ_[l]] ↥B₀.LL.1)
    (hq : ∀ x, q (Br.toLLK B x) = Br.toLLK B₀ (p x)) (x : KOG O k) (w : Fin k → Br.LLw B)
    (h : Br.phi B k x = Submodule.Quotient.mk w) :
    Br.phi B₀ k (coordQ p hi k x) = Submodule.Quotient.mk (fun j => q (w j)) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : (Submodule.Quotient.mk (fun j => Br.toLLK B (x j)) :
      (Fin k → Br.LLw B) ⧸ stdG (Br.Ow B) (Br.LLw B) k) = Submodule.Quotient.mk w := h
  change (Submodule.Quotient.mk (fun j => Br.toLLK B₀ (p (x j))) :
      (Fin k → Br.LLw B₀) ⧸ stdG (Br.Ow B₀) (Br.LLw B₀) k) = _
  rw [Submodule.Quotient.eq] at h1 ⊢
  obtain ⟨u, hu⟩ := h1
  choose d hd using id hi
  refine ⟨fun j => B₀.eO (d (B.eO.symm (u j))), funext fun j => ?_⟩
  have h2 : algebraMap (Br.Ow B) (Br.LLw B) (u j) = Br.toLLK B (x j) - w j := congrFun hu j
  change algebraMap (Br.Ow B₀) (Br.LLw B₀) _ = Br.toLLK B₀ (p (x j)) - q (w j)
  rw [← Br.toLLK_alg, ← hd, ← hq, ← hq, ← map_sub, ← h2, Br.toLLK_alg, RingEquiv.apply_symm_apply]

include hp in
theorem coordLL_mulVec {k : ℕ} (q : ↥B.LL.1 →ₗ[ℚ_[l]] ↥B₀.LL.1)
    (hq : ∀ x, q (Br.toLLK B x) = Br.toLLK B₀ (p x)) (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀)
    (g : ↥(GK B₀.Kw)) (v : Fin k → Br.LLw B) :
    (fun j => q ((Br.locM B (mapM f M₀) (B.e (B₀.e.symm g))).mulVec v j)) =
      (Br.locM B₀ M₀ g).mulVec fun j => q (v j) := by
  choose x hx using fun j => (toLLK_bijective B).2 (v j)
  funext j
  have h1 : ∀ i, Br.locM B (mapM f M₀) (B.e (B₀.e.symm g)) j i =
      Br.toLLK B (fracMap f hf (algebraMap O₀ _ (M₀ (B₀.e.symm g) j i))) := by
    intro i
    rw [fracMap_alg, Br.toLLK_alg]
    change algebraMap (Br.Ow B) (Br.LLw B) (B.eO (f (M₀ (B.e.symm (B.e (B₀.e.symm g))) j i))) = _
    rw [MulEquiv.symm_apply_apply]
  have h2 : ∀ i, Br.locM B₀ M₀ g j i = Br.toLLK B₀ (algebraMap O₀ _ (M₀ (B₀.e.symm g) j i)) := by
    intro i
    rw [Br.toLLK_alg]
    rfl
  simp only [Matrix.mulVec, dotProduct, map_sum, h1, h2, ← hx, ← map_mul, hq, hp]

include hp in
set_option synthInstance.maxHeartbeats 400000 in
theorem coordQ_mem_HfD (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z)
    (P : LocPrime l) (σ : GQ l)
    (hσ : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹)
    {k : ℕ} (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) (c : ↥Gw → KOG O k)
    (hc : (fun g => Br.phi B k (c (Br.ι B g))) ∈ HfD (P.PD B.Kw) (Br.lat B (mapM f M₀))) :
    (fun g => Br.phi B₀ k (coordQ p hi k (c (Br.ι B₀ g)))) ∈ HfD (P.PD B₀.Kw) (Br.lat B₀ M₀) := by
  obtain ⟨q, hq⟩ := exists_coordLL p hp B₀ B hz
  obtain ⟨z, hz1, v, h⟩ := (mem_HfD_iff _ _ _).1 hc
  let θ : ↥(GK B₀.Kw) →* ↥(GK B.Kw) := B.e.toMonoidHom.comp B₀.e.symm.toMonoidHom
  have hθ : Continuous θ := B.e_cont.comp B₀.e_symm_cont
  have hσ' : ∀ g : ↥(GK B₀.Kw), (g : GQ l) = σ⁻¹ * (θ g : GQ l) * σ⁻¹⁻¹ := by
    intro g
    change _ = σ⁻¹ * (B.e (B₀.e.symm g) : GQ l) * σ⁻¹⁻¹
    rw [hσ, MulEquiv.apply_symm_apply]
    group
  have hm := coordLL_mulVec p hp B₀ B q hq M₀
  have hz2 := crystallineCocycle_transport_conjugation P B.Kw B₀.Kw B.LL B₀.LL θ hθ σ⁻¹ hσ' (Br.locM B (mapM f M₀)) (Br.locM B₀ M₀) q hm z hz1
  refine (mem_HfD_iff _ _ _).2 ⟨_, hz2, fun j => q (v j), fun g => ?_⟩
  have h3 : Br.phi B k (c (Br.ι B₀ g)) = Submodule.Quotient.mk
      (z (θ g) + ((Br.locM B (mapM f M₀) (θ g)).mulVec v - v)) := by
    have h4 : Br.ι B (θ g) = Br.ι B₀ g := B.e.symm_apply_apply _
    rw [← h4]
    exact h (θ g)
  refine (phi_coordQ p hi B₀ B q hq _ _ h3).trans ?_
  change _ = (Submodule.Quotient.mk ((fun j => q (z (θ g) j)) +
    ((Br.locM B₀ M₀ g).mulVec (fun j => q (v j)) - fun j => q (v j))) :
      (Fin k → Br.LLw B₀) ⧸ stdG (Br.Ow B₀) (Br.LLw B₀) k)
  rw [← hm]
  congr 1
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, map_add, map_sub]
  rfl

end Coord

theorem exists_coords {O₀ O : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [CommRing O]
    [IsDomain O] (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O₀] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (f : O₀ →+* O) (hf : Function.Injective f)
    (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → O) (p : ι → FractionRing O →+ FractionRing O₀),
      (∀ a y x, p a (fracMap f hf y * x) = y * p a x) ∧
      (∀ a (c : O), ∃ d : O₀, p a (algebraMap O _ c) = algebraMap O₀ _ d) ∧
      ∀ x, ∑ a, b a • fracMap f hf (p a x) = x := by
  letI := f.toAlgebra
  haveI : IsScalarTower ℤ_[l] O₀ O := IsScalarTower.of_algebraMap_eq fun z => (hz z).symm
  haveI : Module.Finite O₀ O := Module.Finite.of_restrictScalars_finite ℤ_[l] O₀ O
  haveI : FaithfulSMul O₀ O := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  letI := FractionRing.liftAlgebra O₀ (FractionRing O)
  let b := Module.Free.chooseBasis O₀ O
  have he : ∀ y, fracMap f hf y = algebraMap (FractionRing O₀) (FractionRing O) y := by
    intro y
    refine DFunLike.congr_fun (IsFractionRing.ringHom_ext (A := O₀) fun z => ?_ :
      fracMap f hf = algebraMap (FractionRing O₀) (FractionRing O)) y
    rw [fracMap_alg, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O₀ O (FractionRing O)]
    rfl
  refine ⟨_, inferInstance, b, (SelmerLevel.fracComp b).p, fun a y x => ?_, fun a c => ?_, fun x => ?_⟩
  · rw [he, ← Algebra.smul_def]
    exact ((SelmerLevel.fracBasis b).coord a).map_smul y x
  · obtain ⟨d, hd⟩ := (SelmerLevel.frac_compat b _).1 ⟨c, rfl⟩ a
    exact ⟨d, hd.symm⟩
  · simp only [he]
    exact (SelmerLevel.fracComp b).sum_p x

set_option synthInstance.maxHeartbeats 400000 in

theorem bkG_le_extCond (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω]
    (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O₀ O : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [Algebra ℤ_[l] O₀] [Module.Finite ℤ_[l] O₀] [TopologicalSpace O₀] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O]
    (B₀ : LocBridge l E Ω Gw O₀) (B : LocBridge l E Ω Gw O) (σ : GQ l)
    (hσ : ∀ g : ↥Gw, ((B.e g : ↥(GK B.Kw)) : GQ l) = σ * ((B₀.e g : ↥(GK B₀.Kw)) : GQ l) * σ⁻¹)
    (f : O₀ →+* O) (hf : Function.Injective f)
    (hz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O₀ z) = algebraMap ℤ_[l] O z)
    (k : ℕ) (M₀ : ↥Gw →* Matrix (Fin k) (Fin k) O₀) :
    Br.bkG B P (WKG (mapM f M₀)) (mapM f M₀) ≤
      extCond f hf (WKG M₀) (Br.bkG B₀ P (WKG M₀) M₀) (WKG (mapM f M₀)) := by
  obtain ⟨ι, _, b, p, hp, hi, hs⟩ := exists_coords l f hf hz
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨c, ?_, rfl⟩
  have hsum : (c : ↥Gw → KOG O k) =
      ∑ a, b a • fun g => pushKO f hf k (coordQ (p a) (hi a) k ((c : ↥Gw → KOG O k) g)) := by
    funext g
    rw [Finset.sum_apply]
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective _ ((c : ↥Gw → KOG O k) g)
    have : x = ∑ a, b a • fun j => fracMap f hf (p a (x j)) := by
      funext j
      rw [Finset.sum_apply]
      exact (hs (x j)).symm
    simp only [Pi.smul_apply, ← hx]
    conv_lhs => rw [this, map_sum]
    rfl
  change (c : ↥Gw → KOG O k) ∈ Submodule.span O _
  rw [hsum]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  have hZ : (fun g => coordQ (p a) (hi a) k ((c : ↥Gw → KOG O k) g)) ∈ Z1 (WKG M₀) :=
    ⟨(continuous_of_discreteTopology (f := coordQ (p a) (hi a) k)).comp c.2.1, fun g h => by
      beta_reduce
      rw [c.2.2, map_add, coordQ_act (p a) (hp a)]⟩
  exact ⟨⟨_, hZ⟩, ⟨⟨_, hZ⟩, coordQ_mem_HfD (p a) (hp a) (hi a) B₀ B hz P σ hσ M₀ c hc, rfl⟩, rfl⟩

end GlobalTheory.BlochKatoBaseChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanInfPosLogLe
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchMean

theorem sum_comp_algHom (K M : Type) [Field K] [Field M] [Algebra ℚ K] [Algebra ℚ M] [Algebra K M]
    [IsScalarTower ℚ K M] [FiniteDimensional ℚ K] [FiniteDimensional ℚ M]
    (F : (K →ₐ[ℚ] ℂ) → ℝ) :
    ∑ ρ : M →ₐ[ℚ] ℂ, F (ρ.comp (IsScalarTower.toAlgHom ℚ K M)) =
      (Module.finrank K M : ℝ) * ∑ φ : K →ₐ[ℚ] ℂ, F φ := by
  haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  haveI : CharZero K := algebraRat.charZero K
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun ρ : M →ₐ[ℚ] ℂ => ρ.comp (IsScalarTower.toAlgHom ℚ K M)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F φ)
    (fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const, nsmul_eq_mul]
  congr 2
  letI : Algebra K ℂ := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq fun q => (φ.commutes q).symm
  rw [← AlgHom.card K M ℂ, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun ψ _ => ψ.restrictScalars ℚ) ?_ ?_ ?_
  · intro ψ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext a
    exact ψ.commutes a
  · intro a _ b _ h
    exact AlgHom.restrictScalars_injective ℚ h
  · intro ρ hρ
    have h := (Finset.mem_filter.1 hρ).2
    exact ⟨{ ρ.toRingHom with commutes' := fun a => DFunLike.congr_fun h a },
      Finset.mem_univ _, rfl⟩

theorem sum_algHom_eq (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (f : InfinitePlace K → ℝ) :
    ∑ φ : K →ₐ[ℚ] ℂ, f (InfinitePlace.mk φ.toRingHom) = 2 * ∑ v, f v := by
  have h1 : ∑ φ : K →ₐ[ℚ] ℂ, f (InfinitePlace.mk φ.toRingHom)
      = ∑ φ : K →+* ℂ, f (InfinitePlace.mk φ) :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ fun _ => rfl
  rw [h1, ← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun φ : K →+* ℂ => InfinitePlace.mk φ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f v)
    (fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const, nsmul_eq_mul]
  congr 1
  have := InfinitePlace.card_filter_mk_eq v
  rw [IsTotallyComplex.mult_eq] at this
  exact_mod_cast this

theorem posLog_sum_le {ι : Type} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) (a b : ι → ℂ) :
    Real.posLog ‖∑ i, (w i : ℂ) * (a i * b i)‖ ≤
      (Real.posLog (∑ i, (w i : ℝ) * ‖a i‖ ^ 2) + Real.posLog (∑ i, (w i : ℝ) * ‖b i‖ ^ 2)) / 2 := by
  have hw' : ∀ i, (0 : ℝ) ≤ w i := fun i => by exact_mod_cast hw i
  have h1 : ‖∑ i, (w i : ℂ) * (a i * b i)‖ ≤
      ∑ i, (Real.sqrt (w i) * ‖a i‖) * (Real.sqrt (w i) * ‖b i‖) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    have h := Real.mul_self_sqrt (hw' i)
    rw [norm_mul, norm_mul, Complex.norm_ratCast, abs_of_nonneg (hw' i)]
    linear_combination (-(‖a i‖ * ‖b i‖)) * h
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i) * ‖a i‖) (fun i => Real.sqrt (w i) * ‖b i‖)
  simp only [mul_pow, Real.sq_sqrt (hw' _)] at h2
  have h3 : ‖∑ i, (w i : ℂ) * (a i * b i)‖ ^ 2 ≤
      (∑ i, (w i : ℝ) * ‖a i‖ ^ 2) * ∑ i, (w i : ℝ) * ‖b i‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have h4 := (Real.posLog_le_posLog (by positivity) h3).trans Real.posLog_mul
  rw [Real.posLog_pow] at h4
  push_cast at h4
  linarith

theorem meanInf_posLog_le :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ : K →+* ℂ) (x : K) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] [IsGalois ℚ M] (ι : Type) [Fintype ι] (w : ι → ℚ) (z : ι → M), (∀ a, σ a ∈ M) → (∀ i, 0 ≤ w i) → σ x = ∑ i, (w i : ℂ) * ((z i : ℂ) * starRingEnd ℂ (z i : ℂ)) → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.posLog ‖v.embedding x‖) ≤ (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (∑ i, (w i : ℝ) * ‖ρ (z i)‖ ^ 2)) / (Module.finrank ℚ M : ℝ) := by
  intro K _ _ _ σ x M _ _ ι _ w z hσ hw hx
  let σ' : K →+* M := σ.codRestrict M hσ
  letI : Algebra K M := σ'.toAlgebra
  haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let j : M →ₐ[ℚ] ℂ := ((starRingEnd ℂ).toRatAlgHom).comp M.val
  have hj : ∀ y : M, starRingEnd ℂ (y : ℂ) ∈ M := fun y => by
    have : j y ∈ j.fieldRange := ⟨y, rfl⟩
    exact (@AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ M (IsGalois.to_normal (F := ℚ) (E := M)) j).le this
  let c : M →ₐ[ℚ] M := (j.toRingHom.codRestrict M hj).toRatAlgHom
  have hc : ∀ y : M, (c y : ℂ) = starRingEnd ℂ (y : ℂ) := fun _ => rfl
  have hcc : ∀ y, c (c y) = y := fun y => Subtype.ext (by rw [hc, hc, Complex.conj_conj])
  have hxM : algebraMap K M x = ∑ i, (w i : M) * (z i * c (z i)) := by
    apply Subtype.ext
    change σ x = M.val _
    rw [hx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_ratCast]
    rfl
  set A : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => Real.posLog (∑ i, (w i : ℝ) * ‖ρ (z i)‖ ^ 2) with hA
  have hinv : Function.Involutive (fun ρ : M →ₐ[ℚ] ℂ => ρ.comp c) := fun ρ => by
    ext y
    simp [hcc]
  have hsum : ∑ ρ : M →ₐ[ℚ] ℂ, A (ρ.comp c) = ∑ ρ, A ρ :=
    Fintype.sum_equiv hinv.toPerm _ _ fun _ => rfl
  have h1 := sum_comp_algHom K M (fun φ => Real.posLog ‖φ x‖)
  have h2 := sum_algHom_eq K (fun v => Real.posLog ‖v.embedding x‖)
  have h3 : ∑ φ : K →ₐ[ℚ] ℂ, Real.posLog ‖φ x‖ =
      2 * ∑ v : InfinitePlace K, Real.posLog ‖v.embedding x‖ := by
    rw [← h2]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
    rfl
  have h4 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog ‖(ρ.comp (IsScalarTower.toAlgHom ℚ K M)) x‖
      ≤ ∑ ρ, A ρ := by
    calc _ ≤ ∑ ρ : M →ₐ[ℚ] ℂ, (A ρ + A (ρ.comp c)) / 2 := by
          refine Finset.sum_le_sum fun ρ _ => ?_
          have : (ρ.comp (IsScalarTower.toAlgHom ℚ K M)) x
              = ∑ i, (w i : ℂ) * (ρ (z i) * ρ (c (z i))) := by
            change ρ (algebraMap K M x) = _
            rw [hxM, map_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_mul, map_mul, map_ratCast]
          rw [this]
          exact posLog_sum_le w hw _ _
      _ = ∑ ρ, A ρ := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, hsum]; ring
  rw [h1, h3] at h4
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hM : (0 : ℝ) < Module.finrank ℚ M := by exact_mod_cast Module.finrank_pos
  have ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K M
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [le_div_iff₀ hM, ← ht]
  refine le_trans (le_of_eq ?_) h4
  field_simp

end GlobalTheory.ArchMean
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareOrthoProductThetaEqProd
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PullNorm

noncomputable def coordLin (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) : VC D N N' →ₗ[ℂ] ℂ where
  toFun := coordB D T b j
  map_add' := fun x y => by simp [coordB, add_mul, Finset.sum_add_distrib]
  map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc]

theorem coordLin_apply (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (j : Fin r) (z : VC D N N') : coordLin D T b j z = coordB D T b j z := rfl

theorem coordB_sum (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (h1 : ∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) (u : Fin r → ℂ) (k : Fin r) :
    coordB D T b k (∑ j, u j • embV D T (b j)) = u k := by
  rw [← coordLin_apply, map_sum]
  simp [coordLin_apply, h1]

theorem parseval (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (z : VC D N N') (h2 : z = ∑ j, coordB D T b j z • embV D T (b j)) :
    (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (z τ i j)) = ((∑ k, ‖coordB D T b k z‖ ^ 2 : ℝ) : ℂ) := by
  have key : ∀ c : Fin r → ℂ,
      (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) ((∑ k, c k • embV D T (b k)) τ i j))
        = ∑ k, coordB D T b k z * (starRingEnd ℂ) (c k) := by
    intro c
    simp only [coordB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum,
      Finset.sum_mul, embV]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have h := key fun k => coordB D T b k z
  rw [← h2] at h
  rw [h]
  push_cast
  exact Finset.sum_congr rfl fun k _ => Complex.mul_conj' _

theorem gaussianWeight_thetaTranslate_normSq (Λ : AddSubgroup ℂ) (g : ℂ → ℂ) (ω z : ℂ) :
    ‖U1 Λ ω g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)
      = ‖g (ω + z)‖ ^ 2 * Real.exp (-Real.pi * ‖ω + z‖ ^ 2 / area Λ) := by
  unfold U1
  rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, add_comm z ω]
  congr 2
  have h2 : (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.sub_re, Complex.div_ofReal_re, Complex.div_ofReal_re, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im]
  push_cast
  ring

theorem normSq_pullB : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ T.abelian₂ = AddSubgroup.closure {w₁, w₂}) → (∀ i j, coordB D T b i (embV D T (b j)) = if i = j then 1 else 0) → (∀ z : VC D N N', z = ∑ j, coordB D T b j z • embV D T (b j)) → ∀ g : ℂ → ℂ, Continuous g → (∀ ω ∈ T.abelian₂, ∀ z, ‖U1 T.abelian₂ ω g z‖ = ‖g z‖) → normSq D T (LaB D T b) (pullB D T b g) = nrm1Sq T.abelian₂ g ^ r := by
  intro D T N N' r b hΛ h1 h2 g _ hg
  let eC : VC D N N' ≃ₗ[ℂ] (Fin r → ℂ) :=
    { LinearMap.pi (fun j => coordLin D T b j) with
      invFun := fun u => ∑ j, u j • embV D T (b j)
      left_inv := fun z => (h2 z).symm
      right_inv := fun u => funext fun k => coordB_sum D T b h1 u k }
  let e : VC D N N' ≃ₗ[ℝ] (Fin r → ℂ) := eC.restrictScalars ℝ
  have he : ∀ z k, e z k = coordB D T b k z := fun _ _ => rfl
  have hA : ∀ x, x ∈ LaB D T b ↔ ∀ k, e x k ∈ T.abelian₂ := by
    intro x
    constructor
    · intro hx k
      unfold LaB at hx
      induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨w, hw, j, rfl⟩ := hy
        rw [he, ← coordLin_apply, map_smul, coordLin_apply, h1]
        split_ifs
        · simpa using hw
        · simp
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
      | neg y _ hy => rw [map_neg]; exact neg_mem hy
    · intro hx
      rw [h2 x]
      exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨_, hx j, j, rfl⟩
  haveI i1 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI i2 : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI i3 : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have main := GlobalTheory.LatticeMean.mean_prod_eq_pow T.abelian₂ hΛ
    (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area T.abelian₂))
    (fun ω hω z => by rw [← gaussianWeight_thetaTranslate_normSq, hg ω hω]) (VC D N N') MeasureTheory.volume r e (LaB D T b) hA
  unfold normSq nrm1Sq
  simp only []
  rw [← main]
  congr 1
  funext z
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Hf, parseval D T b z (h2 z), Complex.div_ofReal_re,
    Complex.ofReal_re, pullB, norm_prod, ← Finset.prod_pow]
  simp only [he]
  congr 2
  rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc]

end GlobalTheory.PullNorm
end

