import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIso
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdelicCoordinatesLatticeMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOrbit
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothCyclic

open GlobalTheory.LowTypeDetermined

theorem eq_zero_of_orbit : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
    (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → ∀ v ∈ M.sm τ, v ≠ 0 →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ℓ (M.rep τ g v) = 0) → ∀ w ∈ M.sm τ, ℓ w = 0 := by
  intro D V S M τ ℓ hℓ v hv hv0 h0 w hw
  obtain ⟨_, -, hσ, hi, -⟩ := M.ds τ
  have hs : M.sm τ = smooth (gramAt D V τ) (M.rep τ) := Submodule.span_eq (smooth (gramAt D V τ) (M.rep τ))
  have hP := M.fr_unit τ
  have h := M.fr_gram τ
  refine eq_zero_of_translates hσ hi hP h hℓ (hs.le hv) hv0 (fun g hg => ?_) (hs.le hw)
  have e : M.rep τ ((M.fr τ)⁻¹ * g * M.fr τ) = M.σ τ g := congrArg (M.σ τ) (conj_conj hP g)
  rw [← e]
  exact h0 _ (conj_inv_mem hP h hg)

end GlobalTheory.SmoothCyclic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_unitaryPair_keeps_completedLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∃ G : Set (WO S T), G.Finite ∧ (∀ u ∈ G, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ U : AddSubgroup (WO S T), (∀ α ∈ intAf D.host.F, ∀ u ∈ G, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u ∈ U) → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), u ∈ U) → (∀ᶠ p : GA D S × GA D T in 𝓝 1, ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ∧ ∀ x : WO S T, x.map (infPart D) = 0 → ∀ N : ℕ, 0 < N → ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  first | exact @GlobalTheory.LatNhds.eventually_actO | exact GlobalTheory.LatNhds.eventually_actO | (intros; apply GlobalTheory.LatNhds.eventually_actO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdLieMatrixSmoothCommGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LieFrameCoord

open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

section Lin

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {n : ℕ}

def coordEquiv (b : Fin n → M) (h : ∀ m : M, ∃! a : Fin n → R, m = ∑ i, a i • b i) : M ≃ₗ[R] (Fin n → R) :=
  (LinearEquiv.ofBijective (Fintype.linearCombination R b)
    ⟨fun a a' haa' => by
        obtain ⟨c, -, hc⟩ := h (Fintype.linearCombination R b a)
        have e1 := hc a (by rw [Fintype.linearCombination_apply])
        have e2 := hc a' (by rw [haa', Fintype.linearCombination_apply])
        rw [e1, e2],
     fun m => by
        obtain ⟨a, ha, -⟩ := h m
        exact ⟨a, by rw [Fintype.linearCombination_apply, ha]⟩⟩).symm

theorem coordEquiv_symm_apply (b : Fin n → M) (h : ∀ m : M, ∃! a : Fin n → R, m = ∑ i, a i • b i)
    (a : Fin n → R) : (coordEquiv b h).symm a = ∑ i, a i • b i := by
  unfold coordEquiv
  rw [LinearEquiv.symm_symm]
  change Fintype.linearCombination R b a = _
  rw [Fintype.linearCombination_apply]

theorem coordEquiv_symm_single (b : Fin n → M) (h : ∀ m : M, ∃! a : Fin n → R, m = ∑ i, a i • b i)
    (j : Fin n) : (coordEquiv b h).symm (Pi.single j 1) = b j := by
  rw [coordEquiv_symm_apply]
  simp [Pi.single_apply]

theorem coord_transport {R' M' : Type} [CommRing R'] [AddCommGroup M'] [Module R' M'] (f : R →+* R')
    (e : M ≃ₗ[R] (Fin n → R)) (e' : M' ≃ₗ[R'] (Fin n → R')) (T : M →+ M')
    (hT : ∀ (a : R) (m : M), T (a • m) = f a • T m)
    (hb : ∀ j, T (e.symm (Pi.single j 1)) = e'.symm (Pi.single j 1))
    (α : M →ₗ[R] M) (α' : M' →ₗ[R'] M') (hα : ∀ m, T (α m) = α' (T m)) (v : M') :
    e' (α' v) = ((Matrix.of fun i j => e (α (e.symm (Pi.single j 1))) i).map f).mulVec (e' v) := by
  have hTe : ∀ m, e' (T m) = fun i => f (e m i) := by
    intro m
    have hm : m = ∑ j, e m j • e.symm (Pi.single j 1) := by
      apply e.injective
      simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hm]
    simp only [map_sum, hT, hb, map_smul, LinearEquiv.apply_symm_apply]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : v = ∑ j, e' v j • T (e.symm (Pi.single j 1)) := by
    simp_rw [hb]
    apply e'.injective
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, ← hα, hTe]
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

end Lin

section Geo

variable {X0 : Scheme.{0}} {A : Over X0} [GrpObj A] [IsCommMonObj A]

theorem dualMapR_comp_alg {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') :
    (Chart.dualMapR g).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp g := by
  apply RingHom.ext
  intro r
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMapR_comp_epsMul {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (a : R) :
    (Chart.dualMapR g).comp (epsMul a) = (epsMul (g a)).comp (Chart.dualMapR g) := by
  apply RingHom.ext
  intro r
  ext <;> simp [Chart.dualMapR, epsMul, mul_comm]

theorem dualMapR_comp_dualMapR {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (g : R' →+* R'')
    (h : R →+* R') : (Chart.dualMapR g).comp (Chart.dualMapR h) = Chart.dualMapR (g.comp h) := by
  apply RingHom.ext
  intro r
  ext <;> simp [Chart.dualMapR]

variable {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') (x0 : Sp R ⟶ X0) (x' : Sp R' ⟶ X0)
  (hx : spMap g ≫ x0 = x')

def liftEps : overAt x' (DualNumber R') ⟶ overAt x0 (DualNumber R) :=
  Over.homMk (spMap (Chart.dualMapR g)) (by
    show spMap (Chart.dualMapR g) ≫ spMap (algebraMap R (DualNumber R)) ≫ x0 =
      spMap (algebraMap R' (DualNumber R')) ≫ x'
    rw [← hx, ← Category.assoc, ← Category.assoc, PullbackSections.spMap_comp_spMap, PullbackSections.spMap_comp_spMap,
      dualMapR_comp_alg])

variable {g x0 x' hx}

theorem smT_liftEps (a : R) (p : overAt x0 (DualNumber R) ⟶ A) :
    smT x' (g a) (liftEps g x0 x' hx ≫ p) = liftEps g x0 x' hx ≫ smT x0 a p := by
  apply Over.OverMorphism.ext
  rw [smT_left, Over.comp_left, Over.comp_left, smT_left]
  simp only [liftEps, Over.homMk_left]
  rw [← Category.assoc, ← Category.assoc, PullbackSections.spMap_comp_spMap, PullbackSections.spMap_comp_spMap, dualMapR_comp_epsMul]

variable (g x0 x' hx)

def tanMap : TanM x0 A →+ TanM x' A where
  toFun v := mkT (liftEps g x0 x' hx ≫ tv v) (by rw [← map_zero g, smT_liftEps, tv_mem, MonObj.comp_one])
  map_zero' := tanM_ext (by rw [tv_mkT, tv_zero, tv_zero, MonObj.comp_one])
  map_add' u v := tanM_ext (by rw [tv_mkT, tv_add, tv_add, tv_mkT, tv_mkT, MonObj.comp_mul])

variable {g x0 x' hx}

theorem tv_tanMap (v : TanM x0 A) : tv (tanMap g x0 x' hx v) = liftEps g x0 x' hx ≫ tv v := rfl

theorem tanMap_smul (a : R) (v : TanM x0 A) : tanMap g x0 x' hx (a • v) = g a • tanMap g x0 x' hx v :=
  tanM_ext (by rw [tv_tanMap, tv_smul, tv_smul, tv_tanMap, smT_liftEps])

theorem tanMap_actR {O : Type} [CommRing O] (act : OAct O A) (c : O) (v : TanM x0 A) :
    tanMap g x0 x' hx (actR (x0 := x0) (S := R) act c v) = actR (x0 := x') (S := R') act c (tanMap g x0 x' hx v) :=
  tanM_ext (by rw [tv_tanMap, tv_actR, tv_actR, tv_tanMap, Category.assoc])

theorem tangent_vector_finset_sum_eq_prod {S0 : Type} [CommRing S0] {y : Sp S0 ⟶ X0} {κ : Type} (s : Finset κ) (w : κ → TanM y A) :
    tv (∑ i ∈ s, w i) = ∏ i ∈ s, tv (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, tv_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, tv_add, ih]

end Geo

end GlobalTheory.LieFrameCoord

namespace GlobalTheory.LieFrameCoord

open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

variable {X0 : Scheme.{0}} {A : Over X0} [GrpObj A] [IsCommMonObj A]

theorem exists_frame {U : X0.Opens} (hU : IsAffineOpen U) {n : ℕ} (v₀ : Fin n → (Sp (DualNumber Γ(X0, U)) ⟶ A.left))
    (hv : ∀ (R' : Type) [CommRing R'] (f : Γ(X0, U) →+* R') (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ A.left),
      IsGrpPullback G' A (spMap f ≫ hU.fromSpec) φ →
        ∃ v' : Fin n → (epsR R' ⟶ G'), (∀ j, (v' j).left ≫ φ = spMap (Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v')
    (R' : Type) [CommRing R'] (f : Γ(X0, U) →+* R') :
    ∃ b : Fin n → TanM (spMap f ≫ hU.fromSpec) A, (∀ j, (tv (b j)).left = spMap (Chart.dualMapR f) ≫ v₀ j) ∧
      ∀ m, ∃! a : Fin n → R', m = ∑ i, a i • b i := by
  have h := isGrpPullback_pullback A (spMap f ≫ hU.fromSpec)
  obtain ⟨v', hleft, hvb⟩ := hv R' f _ _ h
  let b : Fin n → TanM (spMap f ≫ hU.fromSpec) A := fun i =>
    mkT (pushHom h (epsR R') (v' i)) ((isTangent_iff h _).1 (hvb.1 i))
  refine ⟨b, fun j => hleft j, fun m => ?_⟩
  obtain ⟨w', hw'⟩ := push_surj h (tv m)
  have htan : IsTangent w' := (isTangent_iff h w').2 (by rw [hw']; exact tv_mem m)
  have key : ∀ a : Fin n → R', IsLieComb a v' w' ↔ m = ∑ i, a i • b i := by
    intro a
    rw [isLieComb_iff h, hw']
    constructor
    · intro h1
      apply tanM_ext
      rw [h1, tangent_vector_finset_sum_eq_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [tv_smul]
      rfl
    · intro h1
      rw [h1, tangent_vector_finset_sum_eq_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [tv_smul]
      rfl
  obtain ⟨C, hC, hCu⟩ := hvb.2 w' htan
  exact ⟨C, (key C).1 hC, fun a ha => hCu a ((key a).2 ha)⟩

end GlobalTheory.LieFrameCoord

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieFrameCoord

theorem exists_affine_lieMatrix : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], Smooth A.hom →
  ∀ (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A) (z : S),
    ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ (n : ℕ) (M : O →+* Matrix (Fin n) (Fin n) Γ(S, U)),
      ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'),
        ∃ e : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A ≃ₗ[R'] (Fin n → R'),
          ∀ (c : O) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A),
            e (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := spMap f ≫ hU.fromSpec) (S := R') act c v) = matAct M f c (e v) := by
  intro O _ S A _ _ hsm act z
  haveI := hsm
  obtain ⟨U, hU, hzU, -, n, v₀, hv⟩ := GlobalTheory.exists_affine_lieBasis_baseChange S A z ⊤ trivial
  refine ⟨U, hU, hzU, n, ?_⟩
  have hfr := exists_frame hU v₀ hv
  obtain ⟨b0, hb0l, hb0⟩ := hfr Γ(S, U) (RingHom.id _)
  let E0 := coordEquiv b0 hb0
  let B0 := Module.Basis.ofEquivFun E0
  let M : O →+* Matrix (Fin n) (Fin n) Γ(S, U) := (LinearMap.toMatrixAlgEquiv B0).toRingEquiv.toRingHom.comp
    (actR (x0 := spMap (RingHom.id Γ(S, U)) ≫ hU.fromSpec) (S := Γ(S, U)) act)
  refine ⟨M, fun R' _ f => ?_⟩
  obtain ⟨bf, hbfl, hbf⟩ := hfr R' f
  refine ⟨coordEquiv bf hbf, fun c v => ?_⟩
  have hx : spMap f ≫ spMap (RingHom.id Γ(S, U)) ≫ hU.fromSpec = spMap f ≫ hU.fromSpec := by
    rw [← Category.assoc, PullbackSections.spMap_comp_spMap, RingHom.comp_id]
  have hb : ∀ j, tanMap f _ _ hx (E0.symm (Pi.single j 1)) = (coordEquiv bf hbf).symm (Pi.single j 1) := by
    intro j
    rw [coordEquiv_symm_single, coordEquiv_symm_single]
    apply tanM_ext
    apply Over.OverMorphism.ext
    rw [tv_tanMap, Over.comp_left, hb0l, hbfl]
    simp only [liftEps, Over.homMk_left]
    rw [← Category.assoc, PullbackSections.spMap_comp_spMap, dualMapR_comp_dualMapR, RingHom.comp_id]
  have key := coord_transport f E0 (coordEquiv bf hbf) (tanMap f _ _ hx) (fun a m => tanMap_smul a m) hb
    (actR act c) (actR act c) (fun m => tanMap_actR act c m) v
  have hM : M c = Matrix.of fun i j => E0 (actR act c (E0.symm (Pi.single j 1))) i := by
    ext i j
    simp [M, B0, LinearMap.toMatrixAlgEquiv_apply]
  rw [matAct_apply, hM]
  exact key

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanMatrixSmoothingNeZeroAtOneStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archimedeanMatrixSmoothing_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (W : GL (Fin n) (Cinf E) → ℂ), Continuous W → W 1 ≠ 0 → ∃ α : (Fin n → Fin n → Cinf E) → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ {x | IsUnit (Matrix.of x)} ∧ smoothMatInf α W 1 ≠ 0 := by
  first | exact @GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one | exact GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one | (intros; apply GlobalTheory.JSW.MirCinf.exists_smoothMatInf_ne_zero_at_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffPullbackBaseChangeStableSectionBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coeff_pullback_baseChangeStableSectionBasis : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ) (mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) (φA' : A'.left ⟶ A.left), IsPullback φA' A'.hom A.hom t → ∀ (ψA : A'.left ⟶ (topS Rg ⊗ A).left), ψA ≫ (snd (topS Rg) A).left = φA' → ∀ s : LB.Sec (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ)), ∃ c : Fin mA → Γ(Sp R, ⊤), ∀ q : Fin 1 → L.ι, s.f q = ∑ i, (A'.hom.appLE ⊤ (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) (fun _ _ => trivial)).hom (c i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) q) (LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) q) (GlobalTheory.HomFixMat.wchart_comp_le L ψA (snd (topS Rg) A).left q)).hom ((bA i).f q) := by
  first | (exact @GlobalTheory.HomFixMat.exists_coeff_of_isBCBasis) | (exact GlobalTheory.HomFixMat.exists_coeff_of_isBCBasis) | (intros; apply GlobalTheory.HomFixMat.exists_coeff_of_isBCBasis  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLatticeStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_of_adelic_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ y : (Af E)ˣ,
    ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ lattice c y) ∧ ∀ x ∈ lattice c y, IsIntegral ℤ ((N : E) * x) := by
  first | exact @GlobalTheory.CMVal.LatBound.lattice_between | exact GlobalTheory.CMVal.LatBound.lattice_between | (intros; apply GlobalTheory.CMVal.LatBound.lattice_between <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryGroupIsoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicUnitaryGroup_iso : ∀ {D : D7} (V V' : HSp D) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (j' : Matrix (Fin V.rank) (Fin V'.rank) (EAf D)), HMul.hMul j j' = 1 → HMul.hMul j' j = 1 → HMul.hMul (HMul.hMul (Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) j) (V'.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))) j = V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) → ∃ Φ : GfC V ≃ₜ* GfC V', ∀ g : GfC V, HMul.hMul (finE V' (Φ g : GA D V')).val j = HMul.hMul j (finE V (g : GA D V)).val := by
  first | exact @GlobalTheory.FinIsoGrp.exists_finIso | exact GlobalTheory.FinIsoGrp.exists_finIso | (intros; apply GlobalTheory.FinIsoGrp.exists_finIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePrimeSetAvoidingGridPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

theorem exists_primeFactor_mem_of_natCast_mem {D : D7} (w : Pl D.host.E) {M : ℕ} (hM : M ≠ 0)
    (h : (M : 𝓞 D.host.E) ∈ w.asIdeal) : ∃ p ∈ M.primeFactors, (p : 𝓞 D.host.E) ∈ w.asIdeal := by
  have e := Nat.factorization_prod_pow_eq_self hM
  rw [← e, Finsupp.prod, Nat.cast_prod] at h
  obtain ⟨p, hp, hmem⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 h
  refine ⟨p, by simpa [Nat.support_factorization] using hp, ?_⟩
  rw [Nat.cast_pow] at hmem
  exact w.isPrime.mem_of_pow_mem _ hmem

theorem natCast_mem_of_under_eq {D : D7} (w : Pl D.host.E) {v : Pl D.host.F} (h : w.under (𝓞 D.host.F) = v) (n : ℕ)
    (hn : (n : 𝓞 D.host.F) ∈ v.asIdeal) : (n : 𝓞 D.host.E) ∈ w.asIdeal := by
  subst h
  have : (n : 𝓞 D.host.F) ∈ w.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := hn
  rw [Ideal.mem_comap, map_natCast] at this
  exact this

theorem exists_std_primes : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (U : Set T), U.Finite →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → w.under (𝓞 D.host.F) ∉ G.pl.S0 ∧
      (∀ t ∈ U, ∀ w' ∈ L.Q t, w.under (𝓞 D.host.F) ≠ w'.under (𝓞 D.host.F)) ∧
      ((D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  intro D T L sc G U hU
  set N : ℕ := D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK with hN
  set A : ℕ := ∏ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal with hA
  set B : ℕ := ∏ t ∈ hU.toFinset, ∏ w' ∈ L.Q t, Ideal.absNorm (w'.under (𝓞 D.host.F)).asIdeal with hB
  have hN0 : N ≠ 0 := by
    have h1 := D.host.hyp.1.ne_zero
    have h2 := D.host.hyp.2.1.ne_zero
    have h3 := (D.host.g_prime 0).ne_zero
    have h4 := (D.host.g_prime 1).ne_zero
    have h5 : Ideal.absNorm D.host.ccK ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
    have h0 : D.host.QS ≠ 0 := D.host.QS_pos.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3) h4) h5
  have hA0 : A ≠ 0 := by
    rw [hA, Finset.prod_ne_zero_iff]
    intro v _
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hB0 : B ≠ 0 := by
    rw [hB, Finset.prod_ne_zero_iff]
    intro t _
    rw [Finset.prod_ne_zero_iff]
    intro w' _
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (w'.under (𝓞 D.host.F)).ne_bot
  have hM0 : N * A * B ≠ 0 := mul_ne_zero (mul_ne_zero hN0 hA0) hB0
  refine ⟨(N * A * B).primeFactors, fun p hp => Nat.prime_of_mem_primeFactors hp, ?_⟩
  intro w hw
  have key : ∀ n : ℕ, n ∣ N * A * B → (n : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro n hn hmem
    obtain ⟨k, hk⟩ := hn
    have hM : ((N * A * B : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [hk, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hmem
    obtain ⟨p, hp, hpm⟩ := exists_primeFactor_mem_of_natCast_mem w hM0 hM
    exact hw p hp hpm
  refine ⟨fun hv => ?_, fun t ht w' hw' heq => ?_, key N (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)⟩
  · apply key (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hv) _) _
    · exact natCast_mem_of_under_eq w rfl _ (Ideal.absNorm_mem _)
  · apply key (Ideal.absNorm (w'.under (𝓞 D.host.F)).asIdeal)
    · exact dvd_mul_of_dvd_right ((Finset.dvd_prod_of_mem (fun w'' : Pl D.host.E => Ideal.absNorm (w''.under (𝓞 D.host.F)).asIdeal) hw').trans
        (Finset.dvd_prod_of_mem (fun t => ∏ w'' ∈ L.Q t, Ideal.absNorm (w''.under (𝓞 D.host.F)).asIdeal)
          (hU.mem_toFinset.2 ht))) _
    · exact natCast_mem_of_under_eq w heq _ (Ideal.absNorm_mem _)

end GlobalTheory.FunObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOfLevelLift
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.HTLift

open GlobalTheory.SiegelPull

theorem push_comp' {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {α : A' ⟶ A'} {β : A ⟶ A}
    (hab : α.left ≫ φ = φ ≫ β.left) (T : Over S') (x : T ⟶ A') : pushHom h T (x ≫ α) = pushHom h T x ≫ β :=
  Over.OverMorphism.ext (by
    show (x.left ≫ α.left) ≫ φ = (x.left ≫ φ) ≫ β.left
    rw [Category.assoc, hab, Category.assoc])

theorem exists_obj_of_isLift : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (T : Over S)
    (lv : D.La → (T ⟶ o.A)), IsLift o N' T lv → ∃ (o'' : Obj b N' (T.hom ≫ s))
    (mm : ObjMap (o''.forget N hd hc) o T.hom), ∀ a, (o''.eta a).left ≫ mm.φ = (lv a).left := by
  intro p _ D R _ b N N' hd hc S s o T lv hL
  obtain ⟨hadd, hker, hlin, hlev, hgeom⟩ := hL
  obtain ⟨oT, ⟨mT⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N S T.left s T.hom o
  have pb := mT.cart
  let eta : D.La → (𝟙_ (Over T.left) ⟶ oT.A) := fun a =>
    Over.homMk (pb.1.lift (lv a).left (𝟙 _) (by rw [Over.w, Category.id_comp])) (pb.1.lift_snd _ _ _)
  have etaφ : ∀ a, (eta a).left ≫ mT.φ = (lv a).left := fun a => pb.1.lift_fst _ _ _
  let u : Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key : ∀ a, pushHom pb _ (eta a) = u ≫ lv a := fun a => Over.OverMorphism.ext (by
    show (eta a).left ≫ mT.φ = 𝟙 T.left ≫ (lv a).left
    rw [Category.id_comp]; exact etaφ a)
  let o'' : Obj b N' (T.hom ≫ s) :=
    { A := oT.A
      ab := oT.ab
      act := oT.act
      P := oT.P
      isLB := oT.isLB
      rig₁ := oT.rig₁
      rig₂ := oT.rig₂
      symm := oT.symm
      ample := oT.ample
      kerP := oT.kerP
      rosati := oT.rosati
      lie := oT.lie
      lieRank := oT.lieRank
      eta := eta
      eta_add := fun y z => push_injective pb _ (by
        rw [map_mul, key, key, key, hadd, MonObj.comp_mul])
      eta_lin := fun c y => push_injective pb _ (by
        rw [push_comp' pb (mT.act c), key, key, hlin, Category.assoc])
      eta_ker := fun y => push_injective pb _ (by
        rw [key, hker, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        obtain ⟨I, hI⟩ := hgeom k x
        let e : (Over.mk x ⟶ oT.A) ≃* (Over.mk (x ≫ T.hom) ⟶ o.A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
          ⟨push_injective pb _, push_surjective pb _⟩
        have ea : ∀ c g, e (g ≫ oT.act.act c) = e g ≫ o.act.act c := fun c g => push_comp' pb (mT.act c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ mT.φ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        have dg := diag_iso mT.sq mT.pol
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm S T.left o.A oT.A T.hom mT.φ _ _
                    (pull_isLB o.isLB _) (pull_isLB oT.isLB _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _
                    (ex _) (ex _)).2 (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ eta y = e.symm (I.ev N' y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        apply Over.OverMorphism.ext
        show x ≫ (lv y).left = ((toUnit (Over.mk x)).left ≫ (eta y).left) ≫ mT.φ
        rw [Category.assoc, etaφ, Over.toUnit_left]
        rfl }
  let mm : ObjMap (o''.forget N hd hc) o T.hom :=
    { φ := mT.φ, φ₂ := mT.φ₂, cart := mT.cart, sq := mT.sq, act := mT.act, pol := mT.pol,
      eta := fun y => by
        show (eta ((N' / N) • y)).left ≫ mT.φ = T.hom ≫ (o.eta y).left
        rw [etaφ, hlev, Over.comp_left, Over.toUnit_left] }
  exact ⟨o'', mm, fun a => etaφ a⟩

end GlobalTheory.HTLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdelicCoordinatesLatticeModStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_adelic_coordinates_lattice_mod : ∀ (D : D7) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)), LatticeBasisLifts.IsLatBasis V hr β → ∀ (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V ι → ∀ M : ℕ, 0 < M → ∃ ρ : La →+ (Fin r → LatticeBasisLifts.OAf D), (∀ (b : 𝓞 D.host.E) (a : La), ρ (b • a) = Formalism.L2.DIV.oToS D.host.F D.host.E b • ρ a) ∧ (∀ s : Fin r → LatticeBasisLifts.OAf D, ∃ (a : La) (s' : Fin r → LatticeBasisLifts.OAf D), s = ρ a + M • s') ∧ (∀ I J : Ideal (𝓞 D.host.E), I * J = Ideal.span {(M : 𝓞 D.host.E)} → ∀ a : La, (∀ i, ρ a i ∈ Formalism.L2.DIV.idS D.host.F I) → a ∈ I • (⊤ : Submodule (𝓞 D.host.E) La)) ∧ ∀ (κ : GA D V) (y : GL (Fin r) (LatticeBasisLifts.OAf D)), LatticeBasisLifts.finR V hr κ = Formalism.L2.DIV.frGL β y → ∀ a a' : La, (∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = M • w) ↔ ∃ s : Fin r → LatticeBasisLifts.OAf D, y.1.mulVec (ρ a) - ρ a' = M • s := by
  first | exact @GlobalTheory.GeoActCompare.exists_lattice_coord | exact GlobalTheory.GeoActCompare.exists_lattice_coord | (intros; apply GlobalTheory.GeoActCompare.exists_lattice_coord <;> assumption)
end

