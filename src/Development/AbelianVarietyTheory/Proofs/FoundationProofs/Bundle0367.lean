import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0365
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0362
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0364
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NvalDetFrChgConst
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0114
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0366

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphicRepWeightEmbeddingStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_rep_weight_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι] (σ : ι → (E →+* ℂ)) (lam : ι → DomWeight n), Function.Injective (fun τ => InfinitePlace.mk (σ τ)) → ∀ (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → ∀ (f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] (UA E n → ℂ)), f ≠ 0 → (∀ v, f v ∈ π) → (∀ (x : infU E n) v, f (((Formalism.L2.DIV.rhoK (K := ℂ) lam).comp ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)).comp (infU E n).subtype)) x v) = RU E n x (f v)) → ∀ τ, HasWeightAt π (σ τ) (lam τ) ∧ HasWeightAt π (ComplexEmbedding.conjugate (σ τ)) (lam τ).dual := by
  first | exact @GlobalTheory.DefU.EquivWt.hasWeightAt_of_equivariant | exact GlobalTheory.DefU.EquivWt.hasWeightAt_of_equivariant | (intros; apply GlobalTheory.DefU.EquivWt.hasWeightAt_of_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteUnitaryFinitePointsExistsOpenCompactStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ K : Subgroup (finU E n), IsOpen (K : Set (finU E n)) ∧ IsCompact (K : Set (finU E n)) := by
  first | exact @GlobalTheory.DefU.FinCompact.exists_open_compact | exact GlobalTheory.DefU.FinCompact.exists_open_compact | (intros; apply GlobalTheory.DefU.FinCompact.exists_open_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylInvariantPairingStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_weyl_invariant_pairing : ∀ (n : ℕ) (ν : Fin n → ℕ), ∃ b : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ, (∀ u ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, u ≠ 0 → ∃ v ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν, b v u ≠ 0) ∧ ∀ (g : GL (Fin n) ℂ) v u, b (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g : Matrix (Fin n) (Fin n) ℂ).transpose v) (Formalism.UG.dwAct ℂ n n g u) = b v u := by
  first | exact @GlobalTheory.FischerInvariance.fischer_dualWeyl_invariant | exact GlobalTheory.FischerInvariance.fischer_dualWeyl_invariant | (intros; apply GlobalTheory.FischerInvariance.fischer_dualWeyl_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalVectorValuedDefiniteUnitaryFormStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_vectorValued_definiteUnitaryForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (K : Subgroup (finU E n)), IsOpen (K : Set (finU E n)) → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)), (∀ f ∈ M, (∀ v, ∀ γ ∈ ratU E n, ∀ g, f v (γ * g) = f v g) ∧ (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) ∧ ∀ k ∈ K, ∀ v, RU E n (k : UA E n) (f v) = f v) → FiniteDimensional ℂ M := by
  first | exact @GlobalTheory.DefU.finiteDimensional_vecForms | exact GlobalTheory.DefU.finiteDimensional_vecForms | (intros; apply GlobalTheory.DefU.finiteDimensional_vecForms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSecInhabited
section
noncomputable section

namespace GlobalTheory.FlatLine.Definite

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem comp_eq {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) {k k' : U.Comp}
    (x : (U.X k).dom) (x' : (U.X k').dom) (h : (U.un k x).x = (U.un k' x').x) : k' = k := by
  obtain ⟨b, -, -, hb, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor (Formalism.L2.PjFree.Unf.ofPj U) hU hσ k x (U.un k' x') h
  obtain ⟨γ, -, b', -, e⟩ := (hU.2.2.2.1 k k' ⟨_, hb⟩ x').1 ⟨t, ht⟩
  exact congrArg Sigma.fst e

theorem nonempty_flatSec {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (hq : Dw.q = 0) (hp : 1 ≤ Dw.p)
    (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hF : FnAlgClosed Xo c)
    (Z : Comp Xo c) (τ : Psi H) : Nonempty (FlatSec U x Z τ) := by
  have hpq : 1 ≤ Dw.p + Dw.q := by omega
  have hP := hasPts U hpq hg hU Z
  obtain ⟨y₀, h₀, hy₀⟩ := GlobalTheory.FlatLine.DefinitePoint.main E H Dw l Xo c hq hF Z
  obtain ⟨f, f', m₁, m₂, i₁, i₂, hm, hv⟩ := exists_flatRule E H Dw l Xo c hq Z τ y₀ h₀ hy₀
  have chg : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S), LiesOn Z y →
      FrMap (Algebra.ofId c.F S) y₀ z → ∃ (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) S)) (a : Sˣ), (∀ ρ, IsUnit (g ρ).det) ∧ FrChg g (a : S) y z :=
    fun S _ _ y z hy hz => (frChg_exists_unique E H Dw l Xo c S y z).1 (hz.1.trans (hy₀ S y hy).symm)

  have hinf : ∀ σ : c.F →+* ℂ, ∃ b : ℝ, 0 < b ∧ homN (U (goodOf c σ)) x (wtOf Dw (flatWt Dw τ) 0) f ''
      framesOn (U (goodOf c σ)) Z = {b} := by
    intro σ₀
    obtain ⟨⟨⟨k, x₀⟩, hx₀⟩, ht⟩ := hP.1 σ₀
    have hσ := goodEmb_goodOf c σ₀
    generalize goodOf c σ₀ = σ at *
    have hV := hU σ hσ
    obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (CAt σ)) y₀
    have hτ : ∀ k, relab c σ τ.1 ∈ ((U σ).X k).Ψ := fun k => ((hV.2.1 k).2 _).2 (by
      have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
      exact (congrArg σ (Subtype.ext τ.2)).trans hσ0)
    have rd : ∀ k y (hy : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z) g a,
        FrChg g a ((U σ).un k ⟨y, hy.1⟩) z → rdU (U σ) f k y = toC (g τ.1).det := fun k y hy g a hc => by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hy.1, dif_pos]
      exact congrArg toC (hv _ _ z g a (ht _ hy hy.1) hz hc)
    have hh : IsHorizontal (U σ) Z τ f := fun k => by
      by_cases hne : ∃ y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
      · obtain ⟨y₁, h₁⟩ := hne
        refine ⟨hτ k, rdU (U σ) f k y₁ * (mat y₁ ⟨_, hτ k⟩).det, fun y hy => ?_⟩
        obtain ⟨g₁, a₁, -, c₁⟩ := chg _ _ z h₁.2 hz
        obtain ⟨g, a, -, c₂⟩ := (frChg_exists_unique E H Dw l Xo c _ ((U σ).un k ⟨y, hy.1⟩)
          ((U σ).un k ⟨y₁, h₁.1⟩)).1 ((hy₀ _ _ h₁.2).trans (hy₀ _ _ hy.2).symm)
        have c₃ := (frChg_refl_and_comp E H Dw l Xo c _ _ _ _).2 _ _ _ _ c₂ c₁
        have e := GlobalTheory.FlatChange.det_frChg E H Dw l Xo c σ r (U σ) hq hσ hV k ⟨y, hy.1⟩ ⟨y₁, h₁.1⟩ τ (hτ k) g a c₂
        rw [rd k y hy _ _ c₃, rd k y₁ h₁ _ _ c₁, e, horizGen, Matrix.det_mul, mul_assoc, mul_assoc,
          mul_inv_cancel₀ (hy.1 _).1, mul_one]
        rfl
      · exact ⟨hτ k, 0, fun y hy => absurd ⟨y, hy⟩ hne⟩
    obtain ⟨b, hb⟩ := hh.homN_const hσ hV x k
    refine ⟨b, ?_, image_eq_singleton_iff.2 ⟨⟨_, hx₀⟩, ?_⟩⟩
    · have h1 := homN_mul (U σ) x (even_wtOf (-flatWt Dw τ) 0) (even_wtOf (flatWt Dw τ) 0) f' f ⟨k, x₀⟩ hx₀.1
      rw [← wtOf_add', neg_add_cancel, wtOf_zero, mul_comm f', hm, homN_idem _ x hx₀.1 hx₀.2 (ht _ hx₀ _),
        hb x₀ hx₀] at h1
      refine lt_of_le_of_ne (hb x₀ hx₀ ▸ homN_nonneg _ _ _ _ _) fun h0 => ?_
      rw [← h0, mul_zero] at h1
      exact one_ne_zero h1
    · rintro ⟨k', y⟩ hy
      obtain rfl : k' = k := comp_eq hσ hV ⟨x₀, hx₀.1⟩ ⟨y, hy.1⟩ ((hy₀ _ _ hx₀.2).trans (hy₀ _ _ hy.2).symm)
      exact hb y hy
  choose cI hI₁ hI₂ using hinf

  choose ρ hρ using GlobalTheory.FlatLine.PlaceConst.nval_det_frChg_const E H Dw l Xo c hpq hg y₀ τ.1
  obtain ⟨S, hS0, hS⟩ := GlobalTheory.FlatLine.exists_finset_integral_of_definite E H Dw l Xo c hq hp hg y₀
  refine ⟨⟨f, f', m₁, m₂, i₁, i₂, hm, cI, hI₁, hI₂, ρ, fun w => image_eq_singleton_iff.2 ⟨hP.2 w, ?_⟩, ?_⟩⟩
  · rintro _ ⟨⟨_, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
    letI := io.toAlgebra
    obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F T.Fr) y₀
    obtain ⟨g, a, -, hc⟩ := chg _ y.1 z hy.2 hz
    show nval T.V e (evR Xo c f y.1) = _
    rw [hv _ _ z g a y.2.1 hz hc, hρ w T io e ho y.1 z g a y.2.2 hz hc]
    simp [flDefect_vw, hq]
  · refine (S.finite_toSet.biUnion fun s hs => finite_vAdd (hS0 s hs)).subset fun w hw => ?_
    by_contra hn
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not, Int.cast_eq_zero] at hn
    obtain ⟨_, ⟨_, T, io, e, ho, -⟩, -⟩ := hP.2 w
    letI := io.toAlgebra
    obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F T.Fr) y₀
    have hi := hS T io (fun s hs => by rw [ho.2 s]; exact mul_eq_zero_of_right _ (hn s hs)) z hz
    have h1 := hρ w T io e ho z z _ _ hi hz (frChg_refl_and_comp E H Dw l Xo c _ z z z).1
    rw [Matrix.det_one, nval_of_ne one_ne_zero, EReal.coe_eq_coe_iff] at h1
    exact hw (h1.symm.trans (by simp [vV]))

theorem exists_flatSec (x : ℝ) : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E)
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ (Dw.p + Dw.q)) (Z : Comp Xo c) (τ : Psi H),
    1 ≤ Dw.p ∧ (∀ σ, GoodEmb c σ → IsUnf (U σ)) ∧ Nonempty (FlatSec U x Z τ) := by
  obtain ⟨D, hp, hq⟩ := GlobalTheory.CM.CyclotomicTwentyEight.exists_datum
  have hpq : 1 ≤ D.p + D.q := by omega
  obtain ⟨l, -, hg, -⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx _ GlobalTheory.CM.CyclotomicTwentyEight.host 1 one_pos
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ _ D l hpq
  obtain ⟨c₀⟩ : Nonempty (Coeff l) := inferInstance
  obtain ⟨-, c, -, hc⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ D l Xo c₀ hpq
  obtain ⟨⟨Z⟩, -⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ D l Xo c hpq
  have hU : ∀ σ : c.F →+* ℂ, ∃ U : Unf Xo c σ (D.p + D.q), GoodEmb c σ → IsUnf U := fun σ => by
    by_cases hσ : GoodEmb c σ
    · obtain ⟨U, hU⟩ := GlobalTheory.IsUnfEx.exists_isUnf GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.QNorm.hasseNormSt
        GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.abelianSchemeLaws_all.2.secTwist _ _ D l Xo c σ hpq hσ
      exact ⟨U.toPj, fun _ => hU⟩
    · exact ⟨{ Comp := PEmpty, X := fun k => k.elim, un := fun k => k.elim }, fun h => absurd h hσ⟩
  choose U hU using hU
  obtain ⟨τ⟩ : Nonempty (Psi GlobalTheory.CM.CyclotomicTwentyEight.host) := by
    obtain ⟨ρ⟩ : Nonempty (GlobalTheory.CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight →+* ℂ) := inferInstance
    by_cases h : ρ (GlobalTheory.CM.CyclotomicTwentyEight.host.rt : GlobalTheory.CM.CyclotomicTwentyEight.CyclotomicFieldTwentyEight) = GlobalTheory.CM.CyclotomicTwentyEight.host.rt0
    exacts [⟨⟨ρ, h⟩⟩, ⟨⟨_, conj_mem h⟩⟩]
  exact ⟨_, _, _, _, _, D, l, Xo, c, U, Z, τ, hp.ge, hU,
    nonempty_flatSec U x hq hp.ge hg hU (hc c le_rfl) Z τ⟩

end GlobalTheory.FlatLine.Definite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAbelianGaloisHost
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

section Host

variable (D : D7) (H : Geo.Tor.Host D.host.E)

theorem isAbelianGalois_host : IsAbelianGalois ℚ D.host.E := by
  have hE := D.host.hostE_isGalois
  have hmul := D.host.galE_mul
  have hbij := D.host.galE_bijective
  have : IsMulCommutative Gal(D.host.E/ℚ) := ⟨⟨fun σ τ => hbij.1 (by rw [hmul, hmul, _root_.mul_comm])⟩⟩
  exact {}

theorem not_cube_dvd (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : ((D.host.d : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ¬ w.asIdeal ^ 3 ∣ Ideal.span {((D.host.d : ℕ) : 𝓞 D.host.E)} := by
  have hE := D.host.hostE_isGalois
  have hmul := D.host.galE_mul
  have hbij := D.host.galE_bijective
  have hp := D.host.hyp.2.1
  have : IsGaloisGroup Gal(D.host.E/ℚ) ℤ (𝓞 D.host.E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ D.host.E
  have := w.isPrime
  have hmax : (Ideal.span {(D.host.d : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  have : w.asIdeal.LiesOver (Ideal.span {(D.host.d : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; simpa using hw)⟩
  have hb : (Ideal.span {(D.host.d : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  have hIn : Nat.card (w.asIdeal.inertia Gal(D.host.E/ℚ)) = 2 := by
    have e : Nat.card (w.asIdeal.inertia Gal(D.host.E/ℚ)) =
        Nat.card ({1, D.R.toFrame.iod} : Set (D.R.GG)) :=
      Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ hbij) fun σ => by
        rw [AddSubgroup.mem_inertia]
        exact D.host.der.inertia_d w.asIdeal σ)
    rw [e, Nat.card_coe_set_eq, Set.ncard_pair]
    intro h
    have := congrArg (fun g : D.R.GG => g.1.2) h
    exact absurd (show (1 : ℤˣ) = -1 from this) (by decide)
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(D.host.E/ℚ)) (Ideal.span {(D.host.d : ℤ)}) w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(D.host.E/ℚ),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(D.host.d : ℤ)}) w.asIdeal hb] at hIn
  intro h
  have hm : Ideal.map (algebraMap ℤ (𝓞 D.host.E)) (Ideal.span {(D.host.d : ℤ)}) =
      Ideal.span {((D.host.d : ℕ) : 𝓞 D.host.E)} := by
    rw [Ideal.map_span, Set.image_singleton]; simp
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity (by rw [hm]; simpa using hp.ne_zero) w.isPrime, hm] at hIn
  have hf : FiniteMultiplicity w.asIdeal (Ideal.span {((D.host.d : ℕ) : 𝓞 D.host.E)}) := by
    by_contra hn
    rw [multiplicity_eq_one_of_not_finiteMultiplicity hn] at hIn
    omega
  have := hf.le_multiplicity_of_pow_dvd h
  omega

theorem isHostField (hd : H.d = D.host.d) : EigenvectorLieDegree.IsHostField H := by
  have hA := isAbelianGalois_host D
  obtain ⟨-, -, hdisc, hmov⟩ := PlaceInt.host_galois_discr_moves D H
  refine (HostRamif.isHostField_iff _ H).2 ⟨hA, fun l w hl hdv hw hlw => ?_⟩
  have h1 : l ∣ D.host.condN := hdisc l hl hdv
  have h2 : l ∈ D.host.small ∨ l = D.host.q ∨ l = D.host.d := (D.host.toHostRaw.dvd_condN_iff_small hl).1 h1
  refine ⟨fun h => ?_, fun h => (HostRamif.isSquare_iff H hl hw hlw h).1 ?_, fun h h3 => ?_⟩
  · obtain ⟨x, hx, hx'⟩ := (hmov l (Nat.mem_primeFactors.2 ⟨hl, h1, D.host.toHostRaw.condN_ne_zero⟩)).2 w hw.isPrime hlw
    exact hx' (h ▸ Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hx)
  · rcases h2 with h2 | rfl | h2
    · by_cases e2 : l = 2
      · subst e2
        exact FiniteField.isSquare_of_char_two (ZMod.ringChar_zmod_n 2) _
      · have := Fact.mk hl
        have := ZMod.isSquare_of_jacobiSym_eq_one
          (D.host.QS_split l hl e2 ((D.host.toHostRaw.mem_small_iff).1 h2).2)
        rw [hd]
        simpa using this
    · have := Fact.mk hl
      have := ZMod.isSquare_of_jacobiSym_eq_one D.host.hyp.2.2.2.2
      rw [hd]
      simpa using this
    · exact absurd (h2.trans hd.symm) h
  · obtain rfl : l = D.host.d := h.trans hd
    have hb : w ≠ ⊥ := fun e => by
      rw [e, Ideal.mem_bot] at hlw
      exact hl.ne_zero (by exact_mod_cast hlw)
    exact not_cube_dvd D ⟨w, hw.isPrime, hb⟩ hlw (Ideal.dvd_span_singleton.2 h3)

end Host

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_eigenBasis {S : Scheme.{0}} {T : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S} {t : SAB H (Sp R)}
    (n : SABMap t T x) {χ : 𝓞 E →+* R} {m : ℕ} {v : Fin m → (epsR R ⟶ t.G)} (hv : EigenvectorLieDegree.IsEigBasis t.act χ v) :
    ∃ u : Fin m → (FramedFlatCoordinates.epsAt x ⟶ T.G), FramedFlatCoordinates.IsEigenBasis T.act x χ u ∧ ∀ i, (v i).left ≫ n.φ = (u i).left := by
  have h := n.cart
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _).symm
  have one : (1 : Over.mk x ⟶ T.G).left = η[t.G].left ≫ n.φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsR R ⟶ t.G), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    exact (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans (sc c)
  have hP : ∀ v : epsR R ⟶ t.G, EigenvectorLieDegree.IsEigVec t.act χ v ↔ FramedFlatCoordinates.IsEigenTangent T.act x χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he, IsTangent]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w η[t.G]).symm
      exact (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans fs
    · have E : e (v ≫ t.act.act c) = e v ≫ T.act.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, n.act, Category.assoc])
      rw [hR, E]
  have pr : ∀ u : Fin m → (epsR R ⟶ t.G), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  refine ⟨fun i => e (v i), ⟨fun i => (hP _).1 (hv.1 i), fun w hw => ?_⟩, fun i => (he _).symm⟩
  obtain ⟨w, rfl⟩ := e.surjective w
  refine (existsUnique_congr fun c => ⟨?_, ?_⟩).1 (hv.2 w ((hP _).2 hw))
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
  · rintro ⟨u, hu, hw⟩
    refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
    rw [pr, hw]
    simp

variable {Y : Model Xo c β} {Xc : (Xo.XF c).Opens} {τ : E →+* ℂ}

def LiesOver {R : Type} [CommRing R] {j : c.F →+* R} (a : FramedFlatCoordinates.Framed Y Xc τ R j) (y : Sp R ⟶ Xo.XF c) : Prop :=
  a.x = y ≫ Y.jQ ∧ ∀ z, y z ∈ Xc

def IsFibre {R : Type} [CommRing R] {j : c.F →+* R} (a : FramedFlatCoordinates.Framed Y Xc τ R j) (t : SAB H (Sp R))
    (v : Fin Dw.p → (epsR R ⟶ t.G)) (w : Fin Dw.q → (epsR R ⟶ t.G)) : Prop :=
  ∃ n : SABMap t Y.t (a.x ≫ pullback.fst _ _),
    (∀ i, (v i).left ≫ n.φ = (a.v i).left) ∧ ∀ i, (w i).left ≫ n.φ = (a.w i).left

def NormAtAlgebraic (sig : FramedFlatCoordinates.Rule Y Xc τ) (R : (c.F →+* ℂ) → ℝ) : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (j : c.F →+* L) (a : FramedFlatCoordinates.Framed Y Xc τ L j) (y : Sp L ⟶ Xo.XF c)
    (t : SAB H (Sp L)) (v : Fin Dw.p → (epsR L ⟶ t.G)) (w : Fin Dw.q → (epsR L ⟶ t.G)) (σ : L →+* ℂ) (N N' : ℝ),
    LiesOver a y → IsFibre a t v w → EigenvectorLieDegree.IsArchSq t.G t.PP.L v σ N → EigenvectorLieDegree.IsArchSq t.G t.PP.L w σ N' →
    ‖σ (sig L j a)‖ ^ 2 * (N / N') = R (σ.comp j) ^ 2

def ValAtAlgebraic (sig : FramedFlatCoordinates.Rule Y Xc τ) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ) : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (j : c.F →+* L) (a : FramedFlatCoordinates.Framed Y Xc τ L j) (y : Sp L ⟶ Xo.XF c)
    (t : SAB H (Sp L)) (v : Fin Dw.p → (epsR L ⟶ t.G)) (w : Fin Dw.q → (epsR L ⟶ t.G))
    (𝔭 : HeightOneSpectrum (𝓞 c.F)) (𝔓 : HeightOneSpectrum (𝓞 L)) (e : ℕ) (r r' : ℝ),
    LiesOver a y → IsFibre a t v w → (∀ z, 𝔓.valuation L (j z) = 𝔭.valuation c.F z ^ e) →
    EigenvectorLieDegree.IsLocOrd t.G v 𝔓 r → EigenvectorLieDegree.IsLocOrd t.G w 𝔓 r' →
    (vAdd 𝔓 (sig L j a) : ℝ) + (r - r' - Dw.q * (EigenvectorLieDegree.ordTwist H (EigenvectorLieDegree.embIn c j τ) 𝔓 : ℝ)) = e * ρ 𝔭

theorem adDeg_sq {K : Type} [Field K] [NumberField K] (ρ : HeightOneSpectrum (𝓞 K) → ℝ) (R : (K →+* ℂ) → ℝ) :
    EigenvectorLieDegree.adDeg ρ (fun σ => R σ ^ 2) = FlatLine.lineDeg R ρ := by
  simp only [EigenvectorLieDegree.adDeg, FlatLine.lineDeg, lw, Real.log_pow, ← Finset.mul_sum, div_eq_mul_inv, ← _root_.mul_assoc]
  rw [← finsum_mul]
  push_cast
  ring

theorem adDeg_mul {K : Type} [Field K] [NumberField K] {s : K} (hs : s ≠ 0) {ρ : HeightOneSpectrum (𝓞 K) → ℝ}
    (hρ : (Function.support ρ).Finite) {N : (K →+* ℂ) → ℝ} (hN : ∀ σ, 0 < N σ) :
    EigenvectorLieDegree.adDeg (fun 𝔭 => (vAdd 𝔭 s : ℝ) + ρ 𝔭) (fun σ => ‖σ s‖ ^ 2 * N σ) = EigenvectorLieDegree.adDeg ρ N := by
  have h := FlatLine.lineDeg_mul (r := fun σ : K →+* ℂ => ‖σ s‖) (r' := fun σ => √(N σ))
    (fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hs)) (fun σ => Real.sqrt_pos.2 (hN σ)) (FlatLine.finite_vAdd hs) hρ
  rw [FlatLine.lineDeg_num hs, zero_add, ← adDeg_sq, ← adDeg_sq] at h
  simp only [Pi.mul_apply, mul_pow, Real.sq_sqrt (hN _).le] at h
  exact h

end Point

section Record

theorem finite_up {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] {i : k →+* k'}
    {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)} {ε : HeightOneSpectrum (𝓞 k') → ℕ}
    (h : IsUnder i π ε) {ρ : HeightOneSpectrum (𝓞 k) → ℝ} (hρ : (Function.support ρ).Finite) :
    (Function.support (up π ε ρ)).Finite := by
  choose s hs _ using h.sum
  refine (hρ.biUnion fun 𝔭 _ => (s 𝔭).finite_toSet).subset fun 𝔓 h𝔓 => ?_
  simp only [Set.mem_iUnion, Finset.mem_coe]
  exact ⟨π 𝔓, right_ne_zero_of_mul h𝔓, (hs _ _).2 rfl⟩

variable {D : D7} (large₂ : SizeData₂ D) {X : DivX D} (Lc : placeRankTwoOne.Loc D X)

end Record

end GlobalTheory.FlatRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightModuleFiniteContinuousStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_module_finite_continuous : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ), (∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)))) ∧ FiniteDimensional ℂ (NablaT ℂ n mu) ∧ ∀ (u : NablaT ℂ n mu) (ℓ : Module.Dual ℂ (NablaT ℂ n mu)), Continuous fun g : ι → GL (Fin n) ℂ => ℓ (wtOp ℂ n mu sh g u) := by
  first | exact @GlobalTheory.WtCont.finite_continuous_wtOp | exact GlobalTheory.WtCont.finite_continuous_wtOp | (intros; apply GlobalTheory.WtCont.finite_continuous_wtOp <;> assumption)
end

