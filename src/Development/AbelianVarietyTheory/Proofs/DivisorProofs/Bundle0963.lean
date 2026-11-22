import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0937
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEntireLatticeSumOfHeckeLContinuation
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormal
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdLieMatrixSmoothCommGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nbhd_lie_matrix_smooth_comm_group : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], Smooth A.hom →
  ∀ (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A) (z : S),
    ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ (n : ℕ) (M : O →+* Matrix (Fin n) (Fin n) Γ(S, U)),
      ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'),
        ∃ e : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A ≃ₗ[R'] (Fin n → R'),
          ∀ (c : O) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A),
            e (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := spMap f ≫ hU.fromSpec) (S := R') act c v) = matAct M f c (e v) := by
  first | (exact @GlobalTheory.exists_affine_lieMatrix) | (exact GlobalTheory.exists_affine_lieMatrix) | (intros; apply GlobalTheory.exists_affine_lieMatrix  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyPvNeZero
section
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

theorem dense_of_rat_of_span {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousSMul ℝ V] (S : Set V) (h0 : (0 : V) ∈ S) (ha : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S)
    (hq : ∀ q : ℚ, ∀ u ∈ S, (q : ℝ) • u ∈ S) (hS : Submodule.span ℝ S = ⊤) : Dense S := by
  let P : Submodule ℝ V :=
    { carrier := closure S
      zero_mem' := subset_closure h0
      add_mem' := fun {a b} h1 h2 => map_mem_closure₂ continuous_add h1 h2 ha
      smul_mem' := fun t a h1 => by
        have ht : t ∈ closure (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast t
        refine map_mem_closure₂ (f := fun (s : ℝ) (v : V) => s • v) continuous_smul ht h1 ?_
        rintro _ ⟨q, rfl⟩ u hu
        exact hq q u hu }
  have hP : Submodule.span ℝ S ≤ P := Submodule.span_le.2 subset_closure
  intro z
  exact hP (hS ▸ Submodule.mem_top)

theorem denseRange_pv {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : DenseRange (pv X idx x) := by
  have hq (q : ℚ) (v : Fin r → E) : pv X idx x ((q : E) • v) = (q : ℝ) • pv X idx x v := by
    rw [pv_smul]
    funext j
    simp
  refine dense_of_rat_of_span _ ⟨0, ?_⟩ ?_ ?_ (span_range_pv idx hs hx)
  · simpa using hq 0 0
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    refine ⟨u + v, ?_⟩
    rw [pv, pv, pv, per_add]
    rfl
  · rintro q _ ⟨u, rfl⟩
    exact ⟨_, hq q u⟩

theorem exists_apply_pv_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ x ∈ X.dom, ∀ θ : (Fin g → ℂ) → ℂ, Continuous θ → θ ≠ 0 → ∃ v : Fin r → E, θ (pv X idx x v) ≠ 0 := by
  intro E _ _ _ r X g bas idx hs x hx θ hθ h0
  by_contra h
  push Not at h
  exact h0 ((denseRange_pv idx hs hx).equalizer hθ continuous_const (funext h))

end GlobalTheory.FrameEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeTrivialLocusRigidified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.AffineTrivLocus

theorem exists_closed_triv : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ Sp R), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro R _ A _ L₀ N hA hL₀ hamp hN hrig
  have hproj : GlobalTheory.AbLaw.IsProjBy A.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral (Sp R) A L₀ hA hL₀ hamp R (𝟙 _)
      A.left (𝟙 _) A.hom (IsPullback.id_horiz A.hom)).1
  let T0 : Over (Sp R) := Over.mk (𝟙 _)
  have h₀ : IsPullback (pullback.snd T0.hom A.hom) (fst T0 A).left A.hom T0.hom :=
    (IsPullback.of_hasPullback T0.hom A.hom).flip
  obtain ⟨F, hFd⟩ : ∃ F : LB (T0 ⊗ A).left, F = N.pull (pullback.snd T0.hom A.hom) := ⟨_, rfl⟩
  have hF : F.IsLB := hFd ▸ LB.isLB_pull hN _
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.TrivSubscheme.exists_closed_locTriv GlobalTheory.SemiRigid.globalFns R T0 A hA hproj F hF
  refine ⟨H.left, j.left, hj, ?_⟩
  intro T t A' _ φ' hφ
  let T' : Over (Sp R) := Over.mk t
  let x : T' ⟶ T0 := Over.homMk t (Category.comp_id t)
  have hR : (∃ y : T' ⟶ H, y ≫ j = x) ↔ ∃ z : T ⟶ H.left, z ≫ j.left = t := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (fun g => g.left) hy⟩
    · rintro ⟨z, hz⟩
      refine ⟨Over.homMk z ?_, ?_⟩
      · change z ≫ H.hom = t
        rw [← Over.w j]
        change z ≫ j.left ≫ 𝟙 _ = t
        rw [Category.comp_id, hz]
      · exact Over.OverMorphism.ext hz
  rw [← hR, ← hH T' x]
  have h₄ : IsPullback (x ▷ A).left (fst T' A).left (fst T0 A).left x.left := by
    refine IsPullback.of_right ?_ (Over.whiskerRight_left_fst x) h₀
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom A.hom).flip
  have hw : φ' ≫ A.hom = (A'.hom ≫ t) ≫ T0.hom := by
    rw [hφ.1.w]; exact (Category.comp_id _).symm
  let φ'' : A'.left ⟶ (T0 ⊗ A).left := h₀.lift φ' (A'.hom ≫ t) hw
  have hsq : IsPullback φ'' A'.hom (fst T0 A).left t := by
    refine IsPullback.of_right (h₁₂ := pullback.snd T0.hom A.hom) (h₂₂ := T0.hom) ?_ (h₀.lift_snd _ _ _) h₀
    rw [h₀.lift_fst]
    exact (Category.comp_id t).symm ▸ hφ.1
  have e₁ : (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧
      GlobalTheory.AbLaw.Triv ((F.pull (x ▷ A).left).pull ((fst T' A).left ⁻¹ᵁ U).ι)) ↔
      GlobalTheory.TrivSubscheme.LocTrivOver (fst T0 A).left F T'.left x.left := by
    rw [GlobalTheory.TrivSubscheme.locTrivOver_iff h₄]
    exact forall_congr' fun p => exists_congr fun U => and_congr_right fun _ =>
      GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _
  rw [e₁]
  show _ ↔ GlobalTheory.TrivSubscheme.LocTrivOver (fst T0 A).left F T t
  rw [GlobalTheory.TrivSubscheme.locTrivOver_iff hsq]
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  constructor
  · intro ht τ
    refine ⟨⊤, trivial, ?_⟩
    rw [hFd, GlobalTheory.TrivSubscheme.triv_pull_iff, Category.assoc, h₀.lift_fst]
    exact GlobalTheory.AbLaw.CubeOpen.triv_comp _ rfl ht
  · intro h
    refine GlobalTheory.T.exists_generator_rigidified_locally_trivial T A' (N.pull φ') hA' (LB.isLB_pull hN φ') (GlobalTheory.PolBaseChange.rigidified_pull hφ hrig)
      fun τ => ?_
    obtain ⟨V, hV, ht⟩ := h τ
    refine ⟨V, hV, ?_⟩
    rw [hFd, GlobalTheory.TrivSubscheme.triv_pull_iff, Category.assoc, h₀.lift_fst] at ht
    exact (GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _).2 ht

end GlobalTheory.AffineTrivLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmLatticeDataUnfoldingSignatureOneZeroStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmLattice_data_unfolding_signature_one_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (r : ℕ) (U : Formalism.L2.Pj.Unf Xo c c.F.val.toRingHom r), Formalism.L2.Pj.IsUnf U → 0 < r → ∀ (D₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), D₁.p = 1 → D₁.q = 0 → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt U k x₀) (lam : Fin r → Fin r → E), (∀ j, lam j ∈ (U.X k).Λ) → LinearIndependent E lam → (∀ j k' : Fin r, (j : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (k' : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam k') = 0) → (∀ j : Fin r, (j : ℕ) < (U.X k).p0 → ∀ τ : (U.X k).Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re) → (∀ j : Fin r, (U.X k).p0 ≤ (j : ℕ) → ∀ τ : (U.X k).Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re < 0) → (∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀.1 τ) (Fin.castLE (U.X k).p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE (U.X k).p0_le a)))) → Nonempty (GlobalTheory.CM.CMLat W.per Dw.p Dw.q) := by
  first | exact @GlobalTheory.LamT.CMRankOne.exists_cmLat_unfAt_rankOne | exact GlobalTheory.LamT.CMRankOne.exists_cmLat_unfAt_rankOne | (intros; apply GlobalTheory.LamT.CMRankOne.exists_cmLat_unfAt_rankOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubeValuationEqDiscriminant
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_mem_valuation_cube_eq_Δ : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ V : ValuationSubring ℂ,
      ∃ A ∈ F, A ≠ 0 ∧ V.valuation A ^ 3 = V.valuation (latticeCurve L).Δ := by
  intro p F L t hp h4 h3 hD V
  obtain ⟨N, ι, _, T, hNodd, hN3, hNv, hcard, hst, hT⟩ := GlobalTheory.T.exists_galoisStable_torsion_family_ker p F L t hp h4 h3 hD V
  have hΔ0 := latticeCurve_Δ_ne_zero L
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (latticeCurve L).Δ (by norm_num : 0 < 12)
  have hu0 : u ≠ 0 := by rintro rfl; exact hΔ0 (by rw [← hu]; simp)
  have hvu : V.valuation u ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have hvΔ : V.valuation (latticeCurve L).Δ = V.valuation u ^ 12 := by rw [← hu, map_pow]
  have hβ : (sqrtNegNat p).im ≠ 0 := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    simp [sqrtNegNat, Real.sqrt_ne_zero'.2 this]
  have hN3' : ¬ 3 ∣ N := by omega
  have hU := fun i => GlobalTheory.T.valuation_weierstrassP_sub_two_mul_eq_sq L (sqrtNegNat p) u V N hD.mul hβ hvΔ.symm hNv hNodd hN3' (T i)
    (hT i).1 (hT i).2
  have hmem := (GlobalTheory.T.galoisStable_lattice_points_symmetric_mem F L ι T hD.g₂_mem hD.g₃_mem hst (fun i => (hT i).1)).2.2.2
    (fun i => (hU i).1)
  have hΔmem : (latticeCurve L).Δ ∈ F := by
    rw [latticeCurve_Δ]
    exact sub_mem (pow_mem hD.g₂_mem 3)
      (mul_mem (by simpa using natCast_mem F 27) (pow_mem hD.g₃_mem 2))
  set U := ∏ i, (L.weierstrassP (T i) - L.weierstrassP (2 * T i)) with hUdef
  obtain ⟨n, hn⟩ : ∃ n, N = 3 * n + 2 := ⟨N / 3, by omega⟩
  have hvU : V.valuation U = V.valuation u ^ (12 * n) * V.valuation u ^ 4 := by
    rw [hUdef, map_prod]
    simp_rw [fun i => (hU i).2]
    rw [Finset.prod_const, Finset.card_univ, hcard, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hU0 : U ≠ 0 := by
    intro h
    rw [h, map_zero] at hvU
    exact (mul_ne_zero (pow_ne_zero _ hvu) (pow_ne_zero _ hvu)) hvU.symm
  refine ⟨U / (latticeCurve L).Δ ^ n, div_mem hmem (pow_mem hΔmem n),
    div_ne_zero hU0 (pow_ne_zero _ hΔ0), ?_⟩
  rw [map_div₀, map_pow, hvU, hvΔ, ← pow_mul, mul_comm 12 n, mul_div_cancel_left₀ _ (pow_ne_zero _ hvu),
    ← pow_mul]

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEntireLatticeSumOfHeckeLContinuationStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_entire_latticeSum_of_heckeL_continuation : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 c : Ideal (OF E)) (χ : HChar E), UnramFin E → 1 ≤ s → IsBaseCond 𝔣 → 𝔣 ∣ c → c ≠ ⊥ → IsUnitary χ → HasInf χ φ (fun i => (κ i : ℤ) + s) → (∀ y ∈ hatOUnits c, finPart χ y = 1) → ∀ y : (Af E)ˣ, ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S := by
  first | exact @GlobalTheory.CMVal.LatEnt.exists_isLatSum | exact GlobalTheory.CMVal.LatEnt.exists_isLatSum | (intros; apply GlobalTheory.CMVal.LatEnt.exists_isLatSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicGLAgreeOutsideTrivialOnFinset
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

namespace GlobalTheory

theorem outsideS_elt : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (k : GL (Fin a) (Af E)), ∃ k' : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k' = GeneralLinearGroup.map (pLoc E w) k) ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k' = 1 := by
  intro E _ _ a S k
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨k, fun w _ => rfl, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert w S hwS ih =>
    obtain ⟨k', h1, h2⟩ := ih
    refine ⟨k' * (locGL E a w (GeneralLinearGroup.map (pLoc E w) k'))⁻¹, ?_, ?_⟩
    · intro v hv
      have hvw : v ≠ w := fun e => hv (e ▸ Finset.mem_insert_self _ _)
      rw [map_mul, map_inv, pLoc_locGL_of_ne hvw, inv_one, mul_one]
      exact h1 v (fun h => hv (Finset.mem_insert_of_mem h))
    · intro v hv
      rw [map_mul, map_inv]
      by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL, mul_inv_cancel]
      · rw [pLoc_locGL_of_ne hvw, inv_one, mul_one]
        exact h2 v ((Finset.mem_insert.1 hv).resolve_left hvw)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePrimeSetAvoidingGridPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_primeSet_avoiding_gridPlaces : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (U : Set T), U.Finite →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → w.under (𝓞 D.host.F) ∉ G.pl.S0 ∧
      (∀ t ∈ U, ∀ w' ∈ L.Q t, w.under (𝓞 D.host.F) ≠ w'.under (𝓞 D.host.F)) ∧
      ((D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  first | exact @GlobalTheory.FunObj.exists_std_primes | exact GlobalTheory.FunObj.exists_std_primes | (intros; apply GlobalTheory.FunObj.exists_std_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalSectionUnitStalk
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.DivGlue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG exists_chart)

theorem resG_app {Y Z : Scheme.{0}} (ι : Y ⟶ Z) {U U' : Z.Opens} (e : U' ≤ U) {V : Y.Opens}
    (h : V ≤ ι ⁻¹ᵁ U') (h' : V ≤ ι ⁻¹ᵁ U) (x : Γ(Z, U)) :
    resG Y h' ((ι.app U).hom x) = resG Y h ((ι.app U').hom (resG Z e x)) := by
  have h1 : ι.app U ≫ Y.presheaf.map (homOfLE h').op = ι.appLE U V h' := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have h2 : Z.presheaf.map (homOfLE e).op ≫ ι.app U' ≫ Y.presheaf.map (homOfLE h).op =
      ι.appLE U V h' := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  exact (congrArg (fun f => f.hom x) h1).trans (congrArg (fun f => f.hom x) h2).symm

theorem glue : ∀ (Y Z : Scheme.{0}) (ι : Y ⟶ Z) (D : LB Z), D.IsLB → ∀ t : (D.pull ι).Gen, t.IsGen →
  ∀ (M : ℕ) (a : ∀ i, Γ(Z, D.U i)),
  (∀ i j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) (a i) * ((D.g i j : Γ(Z, D.U i ⊓ D.U j))) ^ M =
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG Z (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) (a j)) →
  ∃ h : Γ(Y, ⊤), ∀ (i : D.ι) (y : Y) (hy : ι y ∈ D.U i), ∃ u : (Y.presheaf.stalk y)ˣ,
    (Y.presheaf.germ ⊤ y trivial).hom h = (ι.stalkMap y).hom ((Z.presheaf.germ (D.U i) (ι y) hy).hom (a i)) * (u : Y.presheaf.stalk y) := by
  intro Y Z ι D hD t ht M a ha
  let j : D.ι → (PUnit → D.ι) := fun i _ => i
  let W : D.ι → Y.Opens := fun i => (D.pull ι).U (j i)
  have hW : ∀ i, W i ≤ ι ⁻¹ᵁ D.U i := fun i => LB.wchart_le D _ (j i) PUnit.unit
  let b : ∀ i, Γ(Y, W i) := fun i =>
    resG Y (hW i) ((ι.app (D.U i)).hom (a i)) * ((t.s (j i) ^ M : Γ(Y, (D.pull ι).U (j i))ˣ) : Γ(Y, (D.pull ι).U (j i)))
  have cover : (⊤ : Y.Opens) ≤ iSup W := fun y _ => by
    obtain ⟨i, hi⟩ := exists_chart hD (ι y)
    exact Opens.mem_iSup.2 ⟨i, Set.mem_iInter.2 fun _ => hi⟩
  obtain ⟨h, hh⟩ := GlobalTheory.LB.exists_fun_of_cover W (fun _ => le_top) cover b (by
    intro i i'
    have hV : W i ⊓ W i' ≤ ι ⁻¹ᵁ (D.U i ⊓ D.U i') := fun y hy => ⟨hW i hy.1, hW i' hy.2⟩
    have hA := congrArg (fun x => resG Y hV ((ι.app _).hom x)) (ha i i')
    simp only [map_mul, map_pow] at hA
    simp only [b, map_mul, GlobalTheory.LB.resG_resG]
    rw [← GlobalTheory.LB.val_res, ← GlobalTheory.LB.val_res, map_pow, map_pow, ht (j i) (j i'), mul_pow, Units.val_mul]
    have hG : (((D.pull ι).g (j i) (j i') : Γ(Y, W i ⊓ W i')ˣ) : Γ(Y, W i ⊓ W i')) =
        resG Y hV ((ι.app _).hom (D.g i i' : Γ(Z, D.U i ⊓ D.U i'))) := by
      show ((∏ _k : PUnit, (res hV (pullU ι _ (D.g i i'))) ^ (1 : ℤ) : Γ(Y, W i ⊓ W i')ˣ) :
        Γ(Y, W i ⊓ W i')) = _
      rw [Finset.univ_unique, Finset.prod_singleton, zpow_one]
      rfl
    rw [Units.val_pow_eq_pow_val, hG, resG_app ι inf_le_left hV, resG_app ι inf_le_right hV, ← hA]
    ring)
  refine ⟨h, fun i y hy => ?_⟩
  have hyW : y ∈ W i := Set.mem_iInter.2 fun _ => hy
  refine ⟨Units.map (Y.presheaf.germ (W i) y hyW).hom.toMonoidHom (t.s (j i) ^ M), ?_⟩
  rw [← Y.presheaf.germ_res_apply (homOfLE (le_top : W i ≤ ⊤)) y hyW h]
  change (Y.presheaf.germ (W i) y hyW).hom (resG Y le_top h) = _
  rw [hh i, map_mul]
  congr 1
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact Y.presheaf.germ_res_apply (homOfLE (hW i)) y hyW _

end GlobalTheory.DivGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOfLevelLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_of_levelLift : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (T : Over S) (lv : D.La → (T ⟶ o.A)), IsLift o N' T lv → ∃ (o'' : Obj b N' (T.hom ≫ s)) (mm : ObjMap (o''.forget N hd hc) o T.hom), ∀ a, (o''.eta a).left ≫ mm.φ = (lv a).left := by
  first | exact @GlobalTheory.HTLift.exists_obj_of_isLift | exact GlobalTheory.HTLift.exists_obj_of_isLift | (intros; apply GlobalTheory.HTLift.exists_obj_of_isLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralChangeBaseFrameOrthonormalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_change_baseFrame_orthonormal : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ u : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (β * intGL D.host.F D.host.E V.rank u).val * V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * (β * intGL D.host.F D.host.E V.rank u).val = 1 := by
  first | exact @GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame | exact GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame | (intros; apply GlobalTheory.AdelicOrthFrame.exists_orthonormal_baseFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDetRoot
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetOnto

theorem sigR_mem_intAE (D : D7) {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig y ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    exact AddSubgroup.subset_closure ⟨a, ha,
      ⟨D.sp.cm.sig x, (x.2 : IsIntegral ℤ (x : D.host.E)).map D.sp.cm.sig.toRingHom.toIntAlgHom⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem sigR_sigR (D : D7) (a : Af D.host.F ⊗[D.host.F] D.host.E) :
    sigR (Af D.host.F) D.sp.cm.sig (sigR (Af D.host.F) D.sp.cm.sig a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact congrArg (fun x => a ⊗ₜ[D.host.F] x) (star_star b)
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ext_parts (D : D7) {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) :
    a = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  exact Prod.ext ((he a).1.trans (h1.trans (he b).1.symm)) ((he a).2.trans (h2.trans (he b).2.symm))

theorem norm_one {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) {a b : R} (h : a * b = 1) :
    a * σ b * σ (a * σ b) = 1 := by
  have h' := congrArg σ h
  rw [map_mul, map_one] at h'
  rw [map_mul, hσ]
  linear_combination (σ a * σ b) * h + h'

theorem infPart_det {D : D7} (V : HSp D) (k : GA D V) (hk : k ∈ GfC V) : infPart D (matHom V k).1.det = 1 := by
  have h : infHom V k = 1 := hk
  have h' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  rw [← h', h, Units.val_one, Matrix.det_one]

theorem infPart_sigR (D : D7) (x : AE D) :
    infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) :=
  GlobalTheory.DetRootCong.map_sigR _ _ x

theorem finPart_det {D : D7} (V : HSp D) (k : GA D V) : finPart D (matHom V k).1.det = (finHom V k).1.det :=
  (finPart D).map_det _

end GlobalTheory.DetOnto
end

