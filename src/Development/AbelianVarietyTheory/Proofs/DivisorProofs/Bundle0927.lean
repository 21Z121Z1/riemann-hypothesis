import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0050
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0906
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCutoffsOfRestrictionCutoffs
section
noncomputable section

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

variable {F : Type} [NormedField F]

namespace Red

theorem mul_mem_cell_iff {n : ℕ} {z : GL (Fin n) F} {U : Set (GL (Fin n) F)} {u : GL (Fin n) F}
    (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) : u * g ∈ cell z U ↔ g ∈ cell z U := by
  constructor
  · rintro ⟨v, hv, k, hk, e⟩
    refine ⟨u⁻¹ * v, mul_mem (inv_mem hu) hv, k, hk, ?_⟩
    have : g = u⁻¹ * (u * g) := by group
    rw [this, e]
    simp only [mul_assoc]
  · rintro ⟨v, hv, k, hk, rfl⟩
    exact ⟨u * v, mul_mem hu hv, k, hk, by simp only [mul_assoc]⟩

theorem cell_eq_of_mem {n : ℕ} {z g : GL (Fin n) F} {U : Subgroup (GL (Fin n) F)}
    (hg : g ∈ cell z (U : Set (GL (Fin n) F))) : cell g (U : Set (GL (Fin n) F)) = cell z U := by
  obtain ⟨v, hv, k, hk, rfl⟩ := hg
  ext x
  constructor
  · rintro ⟨u, hu, k', hk', rfl⟩
    exact ⟨u * v, mul_mem hu hv, k * k', mul_mem hk hk', by simp only [mul_assoc]⟩
  · rintro ⟨u, hu, k', hk', rfl⟩
    refine ⟨u * v⁻¹, mul_mem hu (inv_mem hv), k⁻¹ * k', mul_mem (inv_mem hk) hk', ?_⟩
    group

theorem act_mul_left {ψ : AddChar F ℂ} {n : ℕ} (T : GL (Fin n) F →₀ ℂ) {f : GL (Fin n) F → ℂ} (hf : Eqv ψ f)
    {u : GL (Fin n) F} (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) :
    act T f (u * g) = ψ (superDiag u) * act T f g := by
  unfold act Finsupp.sum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only
  rw [mul_assoc u g k, hf u hu, mul_left_comm]

theorem indicator_cell_mul_left {ψ : AddChar F ℂ} {n : ℕ} {z : GL (Fin n) F} {U : Set (GL (Fin n) F)}
    {f : GL (Fin n) F → ℂ} (hf : Eqv ψ f) {u : GL (Fin n) F} (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) :
    (cell z U).indicator f (u * g) = ψ (superDiag u) * (cell z U).indicator f g := by
  classical
  by_cases hg : g ∈ cell z U
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((mul_mem_cell_iff hu g).2 hg), hf u hu]
  · rw [Set.indicator_apply, Set.indicator_apply, if_neg hg, if_neg (fun h => hg ((mul_mem_cell_iff hu g).1 h)),
      mul_zero]

end Red

open Red

theorem cuts_mir_of_res : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h) → ∀ U : Subgroup (GL (Fin (m + 2)) F), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∀ z : GL (Fin (m + 2)) F, GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 2)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 2)) F))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1} := by
  intro F _ _ _ ψ _ _ m H U hUc hUo z
  classical
  by_cases hz : ∃ h₀ : GL (Fin (m + 1)) F, cor h₀ ∈ cell z (U : Set (GL (Fin (m + 2)) F))
  swap
  · refine ⟨0, fun f _ _ p hp => ?_⟩
    rw [act_zero, Set.indicator_apply, if_neg]
    intro hpc
    obtain ⟨h, x, rfl⟩ := exists_mir hp
    rw [mir_eq, mul_mem_cell_iff (mir_mem_iff.2 (one_mem _))] at hpc
    exact hz ⟨h, hpc⟩
  obtain ⟨h₀, hh₀⟩ := hz
  have hzc : cell z (U : Set (GL (Fin (m + 2)) F)) = cell (cor h₀) U := (Red.cell_eq_of_mem hh₀).symm
  obtain ⟨B, hBc, _, hUB, hcell⟩ := GlobalTheory.T.exists_blockGroup_unipotentDoubleCosetCell_blockDiag_iff U hUc hUo
  let B' : Subgroup (GL (Fin (m + 1)) F) := U.comap cor
  have hB'o : IsOpen (B' : Set (GL (Fin (m + 1)) F)) := hUo.preimage continuous_cor
  have hB'B : B' ≤ B := fun b hb => hUB b hb
  have hB'c : IsCompact (B' : Set (GL (Fin (m + 1)) F)) :=
    hBc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hB'o) hB'B
  let L : Set (Fin (m + 1) → F) := {y | mir 1 y ∈ U}
  have hL : L ∈ 𝓝 (0 : Fin (m + 1) → F) := by
    refine (hUo.preimage continuous_col).mem_nhds ?_
    show mir 1 0 ∈ U
    rw [mir_one]
    exact one_mem _
  obtain ⟨s, -, hsU, hsd⟩ := GlobalTheory.T.unipotentDoubleCosetCell_finite_disjoint_iUnion B B' hBc hB'o hB'B h₀
  choose T hT using fun x : GL (Fin (m + 1)) F => H B' hB'c hB'o L hL x
  refine ⟨∑ x ∈ s, T x, fun f hf hfU => ?_⟩
  have hB'f : ∀ b ∈ B', ∀ g, f (g * cor b) = f g := fun b hb g => hfU _ hb g
  have hLf : ∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g := fun y hy g => hfU _ hy g
  have hcor : ∀ h, act (∑ x ∈ s, T x) f (cor h) = (cell z (U : Set (GL (Fin (m + 2)) F))).indicator f (cor h) := by
    intro h
    rw [act_finset_sum]
    rw [Finset.sum_congr rfl fun x _ => hT x f hf hB'f hLf h]
    rw [← Finset.indicator_biUnion_apply s _ hsd, ← hsU, hzc]
    by_cases hh : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hcell h₀ h).2 hh)]
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg hh, if_neg fun h' => hh ((hcell h₀ h).1 h')]
  intro p hp
  obtain ⟨h, x, rfl⟩ := exists_mir hp
  have hu : mir 1 x ∈ unipB F (Fin (m + 2)) := mir_mem_iff.2 (one_mem _)
  rw [mir_eq]
  show act _ f (mir 1 x * cor h) = (cell z (U : Set (GL (Fin (m + 2)) F))).indicator f (mir 1 x * cor h)
  rw [act_mul_left _ hf hu, indicator_cell_mul_left hf hu, hcor]

end GlobalTheory.JSW.Cut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAndIsPreconnected
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.SpecialisationPts

open GlobalTheory.AffinePoints GlobalTheory.CxPts

theorem nonempty_point (B : Type) [CommRing B] [Nontrivial B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : Nonempty (B →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let _ := Ideal.Quotient.field m
  have : Module.Finite ℂ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)⟩

theorem specializes_iff_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x z : X}
    (hz : z ∈ U) : x ⤳ z ↔ ∀ f : Γ(X, U), z ∈ X.basicOpen f → x ∈ X.basicOpen f := by
  refine ⟨fun h f hf => h.mem_open (X.basicOpen f).2 hf, fun h => ?_⟩
  rw [specializes_iff_forall_open]
  intro s hs hzs
  obtain ⟨g, hg, hzg⟩ := hU.exists_basicOpen_le (V := ⟨s, hs⟩) ⟨z, hzs⟩ hz
  exact hg (h g hzg)

theorem mem_basicOpen_iff_notMem {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) (f : Γ(X, U)) :
    x ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x ∈ X.basicOpen f := by
    change hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ _
    rw [hU.fromSpec_primeIdealOf]
  rw [← h, hU.fromSpec_preimage_basicOpen]
  rfl

theorem specializes_iff_ev {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) {y : GlobalTheory.CxPts p (RingHom.id ℂ)} (hy : y ∈ ptsIn p (RingHom.id ℂ) U) :
    x ⤳ y.1 (IsLocalRing.closedPoint ℂ) ↔
      ∀ f ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal, ev p (RingHom.id ℂ) U f y = 0 := by
  rw [specializes_iff_basicOpen hU (mem_ptsIn.1 hy)]
  refine forall_congr' fun f => ?_
  rw [mem_basicOpen_iff_notMem hU hx, ← mem_ptsIn, mem_ptsIn_basicOpen hy]
  exact not_imp_not

theorem nonempty_and_isPreconnected : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), LocallyOfFiniteType p →
    ∀ (U : X.Opens), IsAffineOpen U → ∀ x ∈ U,
    (∃ y : GlobalTheory.CxPts p (RingHom.id ℂ), y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧
      x ⤳ y.1 (IsLocalRing.closedPoint ℂ)) ∧
    _root_.IsPreconnected {y : GlobalTheory.CxPts p (RingHom.id ℂ) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ x ⤳ y.1 (IsLocalRing.closedPoint ℂ)} := by
  intro X p hp U hU x hx
  let : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType ℂ Γ(X, U) := hft
  let P : Ideal Γ(X, U) := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have : P.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  let Φ (φ : (Γ(X, U) ⧸ P) →ₐ[ℂ] ℂ) : GlobalTheory.CxPts p (RingHom.id ℂ) :=
    ofHom hU (φ.comp (Ideal.Quotient.mkₐ ℂ P)).toRingHom
      fun a => (φ.comp (Ideal.Quotient.mkₐ ℂ P)).commutes a
  have hmem (φ) : Φ φ ∈ ptsIn p (RingHom.id ℂ) U := ofHom_mem _ _ _
  have hev (φ) (f : Γ(X, U)) : ev p (RingHom.id ℂ) U f (Φ φ) = φ (Ideal.Quotient.mk P f) :=
    ev_ofHom _ _ _ f
  have hc : Continuous Φ := by
    refine continuous_iff_continuousAt.2 fun φ => tendsto_subtype_rng.2
      (GlobalTheory.Points.tendsto_of_isAffineOpen hU (hmem φ) (Filter.Eventually.of_forall hmem)
        fun f => ?_)
    have h := (continuous_eval (R := ℂ) (C := ℂ) (Ideal.Quotient.mk P f)).tendsto φ
    simp only [← hev] at h
    exact h
  have hr : Set.range Φ = {y : GlobalTheory.CxPts p (RingHom.id ℂ) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ x ⤳ y.1 (IsLocalRing.closedPoint ℂ)} := by
    ext y
    constructor
    · rintro ⟨φ, rfl⟩
      refine ⟨mem_ptsIn.1 (hmem φ), (specializes_iff_ev hU hx (hmem φ)).2 fun f hf => ?_⟩
      rw [hev, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
    · rintro ⟨hy, hxy⟩
      have hy' := mem_ptsIn.2 hy
      let ψ : Γ(X, U) →ₐ[ℂ] ℂ :=
        { evHom hy' with commutes' := fun a => (ev_eq hy' _).symm.trans (ev_algX hy' a) }
      refine ⟨Ideal.Quotient.liftₐ P ψ fun f hf =>
        (ev_eq hy' f).symm.trans ((specializes_iff_ev hU hx hy').1 hxy f hf), ?_⟩
      refine Subtype.ext (GlobalTheory.Points.ext_of_valR hU (hmem _) hy' fun f => ?_)
      exact (hev _ f).trans (ev_eq hy' f).symm
  constructor
  · obtain ⟨φ⟩ := nonempty_point (Γ(X, U) ⧸ P)
    have h := Set.mem_range_self (f := Φ) φ
    rw [hr] at h
    exact ⟨_, h⟩
  · have := GlobalTheory.RootConst.preconnectedSpace_algHom (Γ(X, U) ⧸ P)
    rw [← hr]
    exact isPreconnected_range hc

end GlobalTheory.SpecialisationPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMixedEmbeddingNatMulLe
section
open NumberField

noncomputable section

open scoped Classical

namespace GlobalTheory.RatPointSum

variable {F : Type} [Field F] [NumberField F]

theorem norm_mixedEmbedding_le_sum (x : F) : ‖mixedEmbedding F x‖ ≤ ∑ w : InfinitePlace F, w x := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply]
  exact Finset.single_le_sum (f := fun w : InfinitePlace F => w x) (fun w _ => AbsoluteValue.nonneg _ _)
    (Finset.mem_univ w)

theorem norm_mixedEmbedding_nat_mul_le {κ : Type} [Fintype κ] (M : ℕ) (ξ : κ → F) :
    ‖(fun i => mixedEmbedding F ((M : F) * ξ i))‖ ≤ (M : ℝ) * ∑ i, ∑ w : InfinitePlace F, w (ξ i) := by
  have h0 : ∀ i, 0 ≤ ∑ w : InfinitePlace F, w (ξ i) := fun i => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [map_mul, map_natCast, ← nsmul_eq_mul]
  refine norm_nsmul_le.trans ?_
  refine mul_le_mul_of_nonneg_left ((norm_mixedEmbedding_le_sum (ξ i)).trans ?_) (Nat.cast_nonneg M)
  exact Finset.single_le_sum (f := fun i => ∑ w : InfinitePlace F, w (ξ i)) (fun i _ => h0 i) (Finset.mem_univ i)

end GlobalTheory.RatPointSum

open GlobalTheory.RatPointSum in

theorem GlobalTheory.RatPointSum.norm_thetaSum_le : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (M : ℕ) (B : ℝ) (Ψ : (κ → AdeleRing (𝓞 F) F) → ℂ), 1 ≤ M →
      (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ≠ 0 → ∀ i, ∃ o : 𝓞 F, (M : F) * ξ i = o) →
      (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ *
        (1 + ∑ i, ∑ w : InfinitePlace F, w (ξ i)) ^ N ≤ B) →
      ‖GlobalTheory.WeilM.thetaSum F Ψ‖ ≤ C * B * (M : ℝ) ^ N := by
  intro F _ _ κ _
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ one_pos
  set L := GlobalTheory.WeilM.denomLattice F κ 1 with hLdef
  set r := Module.finrank ℤ L + 1 with hr
  have hL := GlobalTheory.SchwartzMajorant.summable_one_add_norm_pow_inv L
  have hLn : ∀ z : L, 0 ≤ ((1 + ‖z‖) ^ r)⁻¹ := fun z => inv_nonneg.2 (by positivity)
  refine ⟨r, ∑' z : L, ((1 + ‖z‖) ^ r)⁻¹, tsum_nonneg hLn, ?_⟩
  intro M B Ψ hM hsupp hdec
  have hB : 0 ≤ B := le_trans (by positivity) (hdec 0)
  let S : Set (κ → F) := {ξ | ∀ i, ∃ o : 𝓞 F, (M : F) * ξ i = o}
  let v : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ i => mixedEmbedding F ((M : F) * ξ i)
  have hmem : ∀ ξ ∈ S, v ξ ∈ L := by
    intro ξ hξ i
    obtain ⟨o, ho⟩ := hξ i
    rw [Nat.cast_one, one_smul]
    show mixedEmbedding F ((M : F) * ξ i) ∈ mixedEmbedding.integerLattice F
    rw [ho]
    exact ⟨o, rfl⟩
  let j : S → L := fun ξ => ⟨v ξ.1, hmem ξ.1 ξ.2⟩
  have hMF : (M : F) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
    mul_left_cancel₀ hMF (mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i)))
  let G : (κ → F) → ℝ := S.indicator fun ξ => B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹
  have hGs : Summable G := by
    rw [← summable_subtype_iff_indicator]
    exact (hL.comp_injective hj).mul_left _
  have hbound : ∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ ≤ G ξ := by
    intro ξ
    by_cases h0 : Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = 0
    · rw [h0, norm_zero]
      exact Set.indicator_nonneg (fun ξ _ => by positivity) ξ
    have hξ : ξ ∈ S := hsupp ξ h0
    rw [show G ξ = B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹ from Set.indicator_of_mem hξ _]
    set s := ∑ i, ∑ w : InfinitePlace F, w (ξ i) with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => AbsoluteValue.nonneg _ _
    have hv := norm_mixedEmbedding_nat_mul_le M ξ
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have h1 : 1 + ‖v ξ‖ ≤ (M : ℝ) * (1 + s) := by
      show 1 + ‖(fun i => mixedEmbedding F ((M : F) * ξ i))‖ ≤ _
      nlinarith
    have hpos : 0 < (1 + s) ^ r := by positivity
    have hvpos : 0 < (1 + ‖v ξ‖) ^ r := by positivity
    have h2 : ‖Ψ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ ≤ B / (1 + s) ^ r := by
      rw [le_div_iff₀ hpos]; exact hdec ξ
    refine h2.trans ?_
    rw [div_eq_mul_inv, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [← div_eq_mul_inv, le_div_iff₀ hvpos, inv_mul_eq_div, div_le_iff₀ hpos]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 r
  calc ‖GlobalTheory.WeilM.thetaSum F Ψ‖ ≤ ∑' ξ, G ξ := tsum_of_norm_bounded hGs.hasSum hbound
    _ = ∑' ξ : S, B * (M : ℝ) ^ r * ((1 + ‖v ξ‖) ^ r)⁻¹ := (tsum_subtype S _).symm
    _ = B * (M : ℝ) ^ r * ∑' ξ : S, (fun z : L => ((1 + ‖z‖) ^ r)⁻¹) (j ξ) := tsum_mul_left
    _ ≤ B * (M : ℝ) ^ r * ∑' z : L, ((1 + ‖z‖) ^ r)⁻¹ :=
        mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hL hLn hj) (by positivity)
    _ = _ := by ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormScalarPoincareDetRatioLactLeOne
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

open Matrix

noncomputable section

theorem normSq_det_of_isUpq {p q : ℕ} {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    Complex.normSq g.det = 1 := by
  have hJ : (Jf p q).det * (Jf p q).det = 1 := by
    rw [← det_mul, sumBdJf_mul_Jf, det_one]
  have hJ0 : (Jf p q).det ≠ 0 := left_ne_zero_of_mul_eq_one hJ
  have h1 := congrArg det (show gᴴ * Jf p q * g = Jf p q from h)
  rw [det_mul, det_mul, det_conjTranspose] at h1
  have h2 : ((Complex.normSq g.det : ℂ) - 1) * (Jf p q).det = 0 := by
    rw [Complex.normSq_eq_conj_mul_self]
    have : star g.det = (starRingEnd ℂ) g.det := rfl
    rw [this] at h1
    linear_combination h1
  have h3 := (mul_eq_zero.1 h2).resolve_right hJ0
  exact_mod_cast sub_eq_zero.1 h3

theorem norm_det_of_isUpq {p q : ℕ} {g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq g) :
    ‖g.det‖ = 1 := by
  have h1 := normSq_det_of_isUpq h
  rw [Complex.normSq_eq_norm_sq] at h1
  have h0 := norm_nonneg g.det
  nlinarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem Mx_self (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (τ : X.Ψ) :
    KU.Mx X x0 x0 τ = 1 := by
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [KU.Mx, Matrix.nonsing_inv_mul _ hu, KU.tl, Matrix.submatrix_one_equiv]

theorem norm_fac_lact (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    ‖(KU.Mx X x0 (lact γ x0) τ).det / (KU.Mx X x0 (lact γ x0) τ).toBlocks₂₂.det ^ 2‖ =
      (Complex.normSq (KU.gm X x0 γ τ).toBlocks₂₂.det)⁻¹ := by
  rw [KU.Mx_lact X ho, Mx_self X ho, Matrix.mul_one, norm_div, norm_pow,
    norm_det_of_isUpq (KU.gm_upq X ho hγ τ), Complex.normSq_eq_norm_sq, one_div]

theorem one_add_fsq_le (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    1 + sumBdFsq (KU.gm X x0 γ τ).toBlocks₁₂ ≤ Complex.normSq (KU.gm X x0 γ τ).toBlocks₂₂.det :=
  sumBd_detD_ge (KU.gm_upq X ho hγ τ)

theorem norm_qS_lact_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ γ ∈ X.Γ, ‖qS X x0 1 (lact γ x0)‖ ≤ 1 ∧
      (‖qS X x0 1 (lact γ x0)‖ = 1 → ∀ τ, (KU.gm X x0 γ τ).toBlocks₁₂ = 0) := by
  intro E _ _ _ r X x0 ho γ hγ
  classical
  set N : X.Ψ → ℝ := fun τ => Complex.normSq (KU.gm X x0 γ τ).toBlocks₂₂.det with hNdef
  have hF : ∀ τ, 1 + sumBdFsq (KU.gm X x0 γ τ).toBlocks₁₂ ≤ N τ := fun τ => one_add_fsq_le X ho hγ τ
  have hN1 : ∀ τ, 1 ≤ N τ := fun τ => by
    have := sumBdFsq_nonneg (KU.gm X x0 γ τ).toBlocks₁₂; linarith [hF τ]
  have hq : ‖qS X x0 1 (lact γ x0)‖ = ∏ τ, (N τ)⁻¹ := by
    simp only [qS, pow_one]
    rw [norm_prod]
    exact Finset.prod_congr rfl fun τ _ => norm_fac_lact X ho hγ τ
  have ha0 : ∀ τ, 0 ≤ (N τ)⁻¹ := fun τ => inv_nonneg.2 (by linarith [hN1 τ])
  have ha1 : ∀ τ, (N τ)⁻¹ ≤ 1 := fun τ => inv_le_one_of_one_le₀ (hN1 τ)
  refine ⟨?_, fun h1 σ => ?_⟩
  · rw [hq]; exact Finset.prod_le_one (fun τ _ => ha0 τ) (fun τ _ => ha1 τ)
  · rw [hq, ← Finset.mul_prod_erase _ _ (Finset.mem_univ σ)] at h1
    have hP0 : 0 ≤ ∏ τ ∈ Finset.univ.erase σ, (N τ)⁻¹ := Finset.prod_nonneg fun τ _ => ha0 τ
    have hP1 : ∏ τ ∈ Finset.univ.erase σ, (N τ)⁻¹ ≤ 1 := Finset.prod_le_one (fun τ _ => ha0 τ) (fun τ _ => ha1 τ)
    have hs : 1 ≤ (N σ)⁻¹ := by
      calc (1 : ℝ) = (N σ)⁻¹ * ∏ τ ∈ Finset.univ.erase σ, (N τ)⁻¹ := h1.symm
        _ ≤ (N σ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hP1 (ha0 σ)
        _ = (N σ)⁻¹ := mul_one _
    have hNs : N σ ≤ 1 := by
      have hpos : 0 < N σ := by linarith [hN1 σ]
      rw [le_inv_comm₀ one_pos hpos, inv_one] at hs
      exact hs
    have hF0 : sumBdFsq (KU.gm X x0 γ σ).toBlocks₁₂ ≤ 0 := by linarith [hF σ]
    ext i j
    have he := sumBd_entry_le_fsq (KU.gm X x0 γ σ).toBlocks₁₂ i j
    have : Complex.normSq ((KU.gm X x0 γ σ).toBlocks₁₂ i j) = 0 :=
      le_antisymm (by linarith) (Complex.normSq_nonneg _)
    simpa using this

end

end GlobalTheory.ScalarPoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedLineBundleIsoCocycleIdentityStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalised_lineBundleIso_cocycle_identity : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X), e ≫ p = 𝟙 Y → FnBij p → ∀ (V : Y.Opens) (W₁ W₂ W₃ W₁₂ W₂₃ W₁₃ : X.Opens) (L₁ L₂ L₃ : LB X) (w₁₂ : Cmp W₁₂ L₁ L₂) (w₂₃ : Cmp W₂₃ L₂ L₃) (w₁₃ : Cmp W₁₃ L₁ L₃) (r₁ : RigD e L₁) (r₂ : RigD e L₂) (r₃ : RigD e L₃), IsOn W₁ L₁ → IsOn W₂ L₂ → IsOn W₃ L₃ → p ⁻¹ᵁ V ≤ W₁ ⊓ W₂ ⊓ W₃ → p ⁻¹ᵁ V ≤ W₁₂ ⊓ W₂₃ ⊓ W₁₃ → IsoOn W₁₂ L₁ L₂ w₁₂ → IsoOn W₂₃ L₂ L₃ w₂₃ → IsoOn W₁₃ L₁ L₃ w₁₃ → Norm e W₁₂ L₁ L₂ w₁₂ r₁ r₂ → Norm e W₂₃ L₂ L₃ w₂₃ r₂ r₃ → Norm e W₁₃ L₁ L₃ w₁₃ r₁ r₃ → ∀ (x : X) (a : L₁.ι) (b : L₂.ι) (c : L₃.ι), p x ∈ V → x ∈ L₁.U a → x ∈ L₂.U b → x ∈ L₃.U c → gm (𝟙 X) x _ (w₁₂ a b) * gm (𝟙 X) x _ (w₂₃ b c) = gm (𝟙 X) x _ (w₁₃ a c) := by
  first | exact @GlobalTheory.PicGlue.norm_cocycle | exact GlobalTheory.PicGlue.norm_cocycle | (intros; apply GlobalTheory.PicGlue.norm_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemeDvrSectionsMulEquivGeneric
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
namespace GlobalTheory.LevExt

noncomputable def pullPtsEquiv {S S' : Scheme.{0}} (A : Over S') [GrpObj A] (G : Over S) [GrpObj G] (f : S' ⟶ S)
    (φ : A.left ⟶ G.left) (h : IsGrpPullback A G f φ) (T : Over S') :
    (T ⟶ A) ≃* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MulEquiv.mk' (Equiv.ofBijective
    (fun x => Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.1.w, ← Category.assoc, Over.w]))
    (by
      constructor
      · intro x x' hx
        have hx' : x.left ≫ φ = x'.left ≫ φ := congrArg CommaMorphism.left hx
        ext1
        exact h.1.hom_ext hx' (by rw [Over.w, Over.w])
      · intro z
        refine ⟨Over.homMk (h.1.lift z.left T.hom (by simpa using z.w)) (by simp), ?_⟩
        ext1
        exact h.1.lift_fst _ _ _))
    (by
      intro x y
      ext1
      exact (h.2 T x y (Over.homMk (x.left ≫ φ) (by
          simp only [Over.mk_hom, Category.assoc]
          rw [h.1.w, ← Category.assoc, Over.w])) (Over.homMk (y.left ≫ φ) (by
          simp only [Over.mk_hom, Category.assoc]
          rw [h.1.w, ← Category.assoc, Over.w])) rfl rfl).symm)

@[simp] lemma pullPtsEquiv_left {S S' : Scheme.{0}} (A : Over S') [GrpObj A] (G : Over S) [GrpObj G] (f : S' ⟶ S)
    (φ : A.left ⟶ G.left) (h : IsGrpPullback A G f φ) (T : Over S') (x : T ⟶ A) :
    (pullPtsEquiv A G f φ h T x).left = x.left ≫ φ := rfl

noncomputable def precompEquiv {C : Type*} [Category C] [CartesianMonoidalCategory C] {T₁ T₂ M : C} [GrpObj M]
    (i : T₁ ≅ T₂) : (T₂ ⟶ M) ≃* (T₁ ⟶ M) where
  toFun x := i.hom ≫ x
  invFun x := i.inv ≫ x
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := MonObj.comp_mul _ _ _

end GlobalTheory.LevExt

namespace GlobalTheory.LevExt

theorem sections_generic_mulEquiv : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsProper G.hom → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∃ e : (𝟙_ (Over (Sp L)) ⟶ A) ≃* (𝟙_ (Over (Sp W)) ⟶ G), ∀ y, y.left ≫ φ = spMap (algebraMap W L) ≫ (e y).left := by
  intro W L _ _ _ _ _ _ G _ A _ φ hP hφ
  obtain ⟨e1, he1⟩ := GlobalTheory.T.proper_group_scheme_points_valuationRing_mulEquiv W L (Sp W) G hP (𝟙 (Sp W))
  let i : Over.mk (spMap (algebraMap W L) ≫ 𝟙 (Sp W)) ≅ Over.mk ((𝟙_ (Over (Sp L))).hom ≫ spMap (algebraMap W L)) :=
    Over.isoMk (Iso.refl _) (by simp)
  let e : (𝟙_ (Over (Sp L)) ⟶ A) ≃* (𝟙_ (Over (Sp W)) ⟶ G) :=
    ((pullPtsEquiv A G (spMap (algebraMap W L)) φ hφ _).trans (precompEquiv i)).trans e1.symm
  refine ⟨e, fun y => ?_⟩
  have h1 := he1 (e y)
  have h2 : e1 (e y) = i.hom ≫ pullPtsEquiv A G (spMap (algebraMap W L)) φ hφ _ y := e1.apply_symm_apply _
  rw [h2] at h1
  simp only [i] at h1
  simp only [Over.isoMk_hom_left, Iso.refl_hom, Over.comp_left] at h1
  rw [← h1]
  simp only [Category.id_comp]
  rfl

end GlobalTheory.LevExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationBoundOverDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramification_bound_over_dvr : ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (O : Type) [CommRing O] (β : O →+* K), Function.Injective β → (∀ x : K, x ∈ Set.range β ↔ la.valuation K x ≤ 1) → ∃ (_ : IsDomain O) (_ : IsDiscreteValuationRing O), (letI := β.toAlgebra; IsFractionRing O K) ∧ ∀ (T : CDVR) (io : K →+* T.Fr) (b : O →+* T.V), IsLocalHom b → (algebraMap T.V T.Fr).comp b = io.comp β → ∃ e : ℕ, OverLa la T.V io e := by
  first | exact @GlobalTheory.PlaceLocalRing.dvr_and_overLa | exact GlobalTheory.PlaceLocalRing.dvr_and_overLa | (intros; apply GlobalTheory.PlaceLocalRing.dvr_and_overLa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalCoefficientElementarySymmStatement
section
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_coefficient_elementary_symm : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) (k : ℕ), ParGL P n lab c s → k ≤ n → lab (dualLab (splitLab n k)) → c (dualLab (splitLab n k)) = (qV E P : ℂ) ^ (((k : ℂ) * ((n : ℂ) - k)) / 2) * s.esymm k := by
  first | exact @GlobalTheory.SphPar.parGL_dualLab_splitLab | exact GlobalTheory.SphPar.parGL_dualLab_splitLab | (intros; apply GlobalTheory.SphPar.parGL_dualLab_splitLab <;> assumption)
end

