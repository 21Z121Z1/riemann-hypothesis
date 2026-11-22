import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0600
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0144
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2192
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPowMultipleDegreeDescendsNormal
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH

namespace GlobalTheory.UMin.NormIso

def toFld (K : Type) [Field K] : ((Sp K).presheaf.stalk (IsLocalRing.closedPoint K))ˣ →* Kˣ :=
  Units.map (stalkClosedPointIso (CommRingCat.of K)).hom.hom.toMonoidHom

theorem toFld_gm {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) (U : X.Opens)
    (h : x (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X, U)ˣ) :
    (toFld K (gm x _ U a)).val = valF x U a.val := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff x U).2 h
  have e := GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap x U hU
  refine Eq.trans ?_ ((congrArg (fun φ => φ.hom a.val) e).trans (GlobalTheory.Points.valR_eq x U hU _).symm)
  exact congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((gm_val x _ U h a).trans
    (Scheme.Hom.germ_stalkMap_apply x U (IsLocalRing.closedPoint K) h a.val).symm)

theorem toFld_gm_spMap {K K' : Type} [Field K] [Field K'] (σ : K →+* K') {X : Scheme.{0}} (x : Sp K ⟶ X)
    (U : X.Opens) (h : x (IsLocalRing.closedPoint K) ∈ U) (a : Γ(X, U)ˣ) :
    toFld K' (gm (spMap σ ≫ x) _ U a) = Units.map σ.toMonoidHom (toFld K (gm x _ U a)) := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff x U).2 h
  apply Units.ext
  rw [toFld_gm (spMap σ ≫ x) U (hU (x := spMap σ (IsLocalRing.closedPoint K')) trivial)]
  show _ = σ (toFld K (gm x _ U a)).val
  rw [toFld_gm x U h]
  exact GlobalTheory.Points.valR_spMap_comp σ x U hU _

variable {k Ω : Type} [CommRing k] [Field Ω] [Algebra k Ω] {M : RatModel k Ω}

theorem pt_mem {U : M.Z.Opens} (hU : (U : Set M.Z).Nonempty) : M.pt (IsLocalRing.closedPoint Ω) ∈ U :=
  M.top_le_preimage_pt hU (x := IsLocalRing.closedPoint Ω) trivial

theorem unit_ext_pt {U : M.Z.Opens} {a b : Γ(M.Z, U)ˣ}
    (h : M.pt (IsLocalRing.closedPoint Ω) ∈ U → toFld Ω (gm M.pt _ U a) = toFld Ω (gm M.pt _ U b)) : a = b := by
  by_cases hU : (U : Set M.Z).Nonempty
  · have e := congrArg Units.val (h (pt_mem hU))
    rw [toFld_gm _ _ (pt_mem hU), toFld_gm _ _ (pt_mem hU)] at e
    exact Units.ext (M.valF_injective hU e)
  · exact unit_ext fun x hx => absurd ⟨x, hx⟩ hU

theorem exists_unit {U : M.Z.Opens} (c : Ωˣ) (h : ∀ z ∈ U, c.val ∈ M.O z ∧ (c⁻¹).val ∈ M.O z) :
    ∃ a : Γ(M.Z, U)ˣ, M.pt (IsLocalRing.closedPoint Ω) ∈ U → toFld Ω (gm M.pt _ U a) = c := by
  by_cases hU : (U : Set M.Z).Nonempty
  · obtain ⟨f, hf⟩ := (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).1)
    obtain ⟨g, hg⟩ := (RatModel.mem_ringOn_iff_exists hU).1 (RatModel.mem_ringOn.2 fun z hz => (h z hz).2)
    have e : f * g = 1 := M.res_injective U hU (by
      rw [map_mul, map_one, M.res_apply, M.res_apply, hf, hg, c.mul_inv])
    exact ⟨⟨f, g, e, (mul_comm _ _).trans e⟩, fun hp => Units.ext ((toFld_gm _ _ hp _).trans hf)⟩
  · exact ⟨1, fun hp => absurd ⟨_, hp⟩ hU⟩

variable {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] {M' : RatModel k Ω'}
  {π : M'.Z ⟶ M.Z}

theorem norm_mem_O [FiniteDimensional Ω Ω'] (hN : Geo.Tor.IsNormalScheme M.Z) [IsFinite π]
    (hπ : M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt) {z : M.Z} {U : M.Z.Opens} (hz : z ∈ U) {W : M'.Z.Opens}
    (hW : π ⁻¹ᵁ U ≤ W) (f : Γ(M'.Z, W)) : Algebra.norm Ω (valF M'.pt W f) ∈ M.O z := by
  have hH : M.IsHom M' (IsScalarTower.toAlgHom k Ω Ω') π := hπ
  obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle' : π ⁻¹ᵁ V ≤ W := fun y hy => hW (hle hy)
  have hne : (V : Set M.Z).Nonempty := ⟨z, hzV⟩
  have hne' : ((π ⁻¹ᵁ V : M'.Z.Opens) : Set M'.Z).Nonempty := by
    refine ⟨M'.pt (IsLocalRing.closedPoint Ω'), ?_⟩
    show (M'.pt ≫ π) (IsLocalRing.closedPoint Ω') ∈ V
    rw [hπ]
    exact M.top_le_preimage_pt hne (x := spMap (algebraMap Ω Ω') (IsLocalRing.closedPoint Ω')) trivial
  have hfin : (π.app V).hom.Finite := IsFinite.finite_app π V hV
  have hint := hfin.to_isIntegral (resG M'.Z hle' f)
  let ρ : Γ(M.Z, V) →+* M.O z := (M.res V hne).codRestrict (M.O z) fun a => by
    rw [M.res_apply]; exact RatModel.valF_mem_O hzV a
  have hc : (algebraMap (M.O z) Ω').comp ρ = (M'.res _ hne').comp (π.app V).hom := by
    ext a
    show algebraMap Ω Ω' (M.res V hne a) = M'.res _ hne' (π.app V a)
    rw [M.res_apply, M'.res_apply, hH.valF_app hne]
    rfl
  have h1 : IsIntegral (M.O z) (valF M'.pt W f) := by
    obtain ⟨P, hP, hP0⟩ := hint
    refine ⟨P.map ρ, hP.map ρ, ?_⟩
    rw [Polynomial.eval₂_map, hc, ← M'.valF_resG hle' hne', ← M'.res_apply _ hne', ← Polynomial.hom_eval₂, hP0,
      map_zero]
  have := M.isIntegrallyClosed_O hN z
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm Ω h1)
  exact hy ▸ y.2

theorem lbIso_lbPow_finrank [FiniteDimensional Ω Ω'] (hN : Geo.Tor.IsNormalScheme M.Z) [IsFinite π]
    (hπ : M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt) (A B : LB M.Z) (e : ℕ)
    (H : LBIso (A.pull π) (B.pull π)) :
    LBIso (lbPow A (Module.finrank Ω Ω' * e)) (lbPow B (Module.finrank Ω Ω' * e)) := by
  obtain ⟨w, hw⟩ := H
  set d := Module.finrank Ω Ω' * e with hd
  let N : Ω'ˣ →* Ωˣ := Units.map (Algebra.norm Ω)
  have hNa : ∀ c : Ωˣ, N (Units.map (algebraMap Ω Ω').toMonoidHom c) = c ^ Module.finrank Ω Ω' := fun c =>
    Units.ext (Algebra.norm_algebraMap c.val)
  have hle : ∀ p : (PUnit → B.ι) × (PUnit → A.ι), π ⁻¹ᵁ ((LB.div (lbPow B d) (lbPow A d)).U p) ≤
      (LB.div (B.pull π) (A.pull π)).U p := fun p y hy =>
    ⟨mem_pull.2 (mem_powChart.1 hy.1), mem_pull.2 (mem_powChart.1 hy.2)⟩
  have hpt : ∀ {U : M.Z.Opens}, M.pt (IsLocalRing.closedPoint Ω) ∈ U →
      π (M'.pt (IsLocalRing.closedPoint Ω')) ∈ U := fun {U} h => by
    show (M'.pt ≫ π) (IsLocalRing.closedPoint Ω') ∈ U
    rw [hπ]
    exact M.top_le_preimage_pt ⟨_, h⟩ (x := spMap (algebraMap Ω Ω') (IsLocalRing.closedPoint Ω')) trivial
  have hex : ∀ p : (PUnit → B.ι) × (PUnit → A.ι), ∃ a : Γ(M.Z, (LB.div (lbPow B d) (lbPow A d)).U p)ˣ,
      M.pt (IsLocalRing.closedPoint Ω) ∈ (LB.div (lbPow B d) (lbPow A d)).U p →
      toFld Ω (gm M.pt _ _ a) = N (toFld Ω' (gm M'.pt _ _ (w.s p))) ^ e := fun p => by
    refine exists_unit _ fun z hz => ?_
    have hp := hle p (hpt (pt_mem ⟨z, hz⟩))
    have key : ∀ u : Γ(M'.Z, (LB.div (B.pull π) (A.pull π)).U p)ˣ,
        (N (toFld Ω' (gm M'.pt _ _ u)) ^ e).val ∈ M.O z := fun u => by
      rw [Units.val_pow_eq_pow_val]
      refine pow_mem ?_ e
      show Algebra.norm Ω (toFld Ω' (gm M'.pt _ _ u)).val ∈ _
      rw [toFld_gm _ _ hp]
      exact norm_mem_O hN hπ hz (hle p) _
    refine ⟨key _, ?_⟩
    rw [← inv_pow, ← map_inv, ← map_inv, ← map_inv]
    exact key _
  choose s hs using hex
  refine ⟨⟨s⟩, fun p q => unit_ext_pt fun hy => ?_⟩
  have hy' : M'.pt (IsLocalRing.closedPoint Ω') ∈ (LB.div (B.pull π) (A.pull π)).U p ⊓
      (LB.div (B.pull π) (A.pull π)).U q := ⟨hle p (hpt hy.1), hle q (hpt hy.2)⟩
  have e₁ := congrArg (gm M'.pt (IsLocalRing.closedPoint Ω') _) (hw p q)
  rw [gm_res _ _ _ hy', map_mul, gm_res _ _ _ hy'] at e₁
  replace e₁ := e₁.trans (congrArg (· * _) (gm_div (A.pull π) (B.pull π) _ _ p q hy'))
  rw [gm_pull_g B π _ _ _ _ hy'.1.1 hy'.2.1, gm_pull_g A π _ _ _ _ hy'.1.2 hy'.2.2, hπ] at e₁
  have e₂ := congrArg (fun u => N (toFld Ω' u) ^ e) e₁
  simp only [map_mul, map_inv] at e₂
  have hB : M.pt (IsLocalRing.closedPoint Ω) ∈ B.U (p.1 PUnit.unit) ⊓ B.U (q.1 PUnit.unit) :=
    ⟨mem_powChart.1 hy.1.1, mem_powChart.1 hy.2.1⟩
  have hA : M.pt (IsLocalRing.closedPoint Ω) ∈ A.U (p.2 PUnit.unit) ⊓ A.U (q.2 PUnit.unit) :=
    ⟨mem_powChart.1 hy.1.2, mem_powChart.1 hy.2.2⟩
  rw [toFld_gm_spMap (algebraMap Ω Ω') M.pt _ hB, toFld_gm_spMap (algebraMap Ω Ω') M.pt _ hA, hNa, hNa] at e₂
  rw [gm_res _ _ _ hy, map_mul, gm_res _ _ _ hy]
  refine Eq.trans ?_ (congrArg (fun u => toFld Ω (u * _)) (gm_div (lbPow A d) (lbPow B d) _ _ p q hy)).symm
  rw [gm_lbPow_g d _ _ _ _ hy.1.1 hy.2.1, gm_lbPow_g d _ _ _ _ hy.1.2 hy.2.2, map_mul, map_mul, map_inv, map_pow,
    map_pow, hs p hy.1, hs q hy.2, e₂, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul]

theorem lbIso_lbPow_of_pull : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω'] [FiniteDimensional Ω Ω'] (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z) (A B : LB M.Z) (d : ℕ), Geo.Tor.IsNormalScheme M.Z → IsFinite π → M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt → A.IsLB → B.IsLB → Module.finrank Ω Ω' ∣ d → LBIso (A.pull π) (B.pull π) → LBIso (lbPow A d) (lbPow B d) := by
  intro k Ω _ _ _ _ _ M Ω' _ _ _ _ _ M' π A B d hN _ hπ _ _ ⟨e, he⟩ H
  subst he
  exact lbIso_lbPow_finrank hN hπ A B e H

end GlobalTheory.UMin.NormIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionRefineFinerBasisStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (L : LB X₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (C D : Type) [Category.{0} C] [Category.{0} D] (G : C ⥤ AffOp X₀) (K : D ⥤ AffOp X₀) (H : D ⥤ C) (_ : H ⋙ G ⟶ K), ObAt S α L G ((extMap R₁ (CoefMap.restrict (OAff s₀) G)).pull2 c) → ObAt S α L K ((extMap R₁ (CoefMap.restrict (OAff s₀) K)).pull2 c) := by
  first | exact @GlobalTheory.LBObs.obAt_refine | exact GlobalTheory.LBObs.obAt_refine | (intros; apply GlobalTheory.LBObs.obAt_refine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnPullbackSquaresOfLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleTrivialOnPullbackSquares_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Out.Rigidified A N → ∀ (T : Scheme.{0}) (t : T ⟶ S), (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ TrivCond A N V (V.ι ≫ t)) → TrivCond A N T t := by
  first | (exact @GlobalTheory.TrivLocus.trivCond_of_local) | (exact GlobalTheory.TrivLocus.trivCond_of_local) | (intros; apply GlobalTheory.TrivLocus.trivCond_of_local  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSmallSectionsGeOfShiftNef
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_ball_one_ge_of_shift_nef : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (M : HermLB p) (α t₀ : ℝ), P.Rep a c M → M.IsSelfInter α → (M.shift (fun _ => t₀) fun _ => rfl).IsNef D → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a) (m * c) 1 := by
  intro hHS hAC k _ X _ p D hX P b s t hG a c M α t₀ hRep hSI hNef ε hε
  exact GlobalTheory.T.eventually_log_ncard_seminormBall_one_ge X.functionField (fun m : ℕ => P.H (m * a) (m * c)) (fun m : ℕ => P.Bl (m * a) (m * c))
    (D + 1) (Nat.succ_pos D) (fun m => GlobalTheory.T.isSeminormBallFamily_sectionBalls k X p P _ _)
    (fun m R => GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG _ _ R hAC)
    (α / (D + 1).factorial) ((D + 1) * gdeg M D / (D + 1).factorial) t₀
    (fun t ht => GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hAC k X p D hX P a c M α t₀ hRep hSI hNef t ht) ε hε

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativeTransitionUnitsIsoLineBundlesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDerivative_transitionUnits_isoLineBundles : ∀ {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M) (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {B : Type} [CommRing B] (x : Sp B ⟶ Y) (w : Sp (DualNumber B) ⟶ Y) (hwx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) (h₁ : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ x ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))), (valR w _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val = (valR (w ≫ m) _ (L.g j₁ j₂).val).snd * valR (x ≫ m) _ (L.g j₁ j₂)⁻¹.val + ((valR w _ (wg.s (p₁, fun _ => j₁)).val).snd * valR x _ (wg.s (p₁, fun _ => j₁))⁻¹.val - (valR w _ (wg.s (p₂, fun _ => j₂)).val).snd * valR x _ (wg.s (p₂, fun _ => j₂))⁻¹.val) := by
  first | exact @GlobalTheory.CechKS.dlog_transition_iso | exact GlobalTheory.CechKS.dlog_transition_iso | (intros; apply GlobalTheory.CechKS.dlog_transition_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogSumBadPrimesLeSq
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

set_option maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BadLogCov

theorem logSum_badPrimes_le_sq : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
  intro _
  refine ⟨37, by norm_num, fun D T hT j hj Y e o hY Lb hL hM hE hfr => ?_⟩
  have hQ := hT.pins
  have hM0 : Y.d.l₂.M ≠ 0 := by have := Y.d.l₂.three_le; omega
  have h1 := UpperTheory.KR.sum_log_bad_le D.host.toHostAx Y.d.l₂.M (badPrimes T.Q.H Y.d.l₂) hM0 fun p hp => by
    obtain ⟨hp, h'⟩ := mem_badPrimes.1 hp
    refine ⟨hp, ?_⟩
    rcases h' with h' | h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (h'.trans hQ.1.1))
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))
    · rw [hY.lev.2] at h'
      exact absurd (Nat.dvd_one.1 h') hp.ne_one
  have hrd : Real.log D.host.rd ≤ fieldSz D.host.E := by
    refine le_trans (le_of_eq ?_) (log_rd_le_fieldSz D.host.E)
    unfold Formalism.HC.HostRaw.rd
    rw [Real.log_rpow (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E))]; ring
  have hsum : GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ 37 * Lb := by
    refine le_trans h1 ?_; linarith
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1' := D.R.two_le_m
  have h2' := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hfr1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := one_le_mul_of_one_le_of_one_le hf hr
  have hX : Lb ≤ ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
    have a : Lb ≤ (D.R.f : ℝ) * D.R.r * Lb := le_mul_of_one_le_left (by linarith) hfr1
    have b : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * Lb := hL.trans a
    nlinarith
  linarith

end GlobalTheory.BadLogCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerPairFormula
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Div.LowerPairFormula

theorem lower_pair_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq (E →+* K)] (H : Type) [AddCommGroup H]
    [Module R H] (I : Type) (φ : I → E →+* K) (ρ : orderC c →+* Module.End R H) (Fil : Submodule R H)
    (B : LinearMap.BilinForm R H) (e f : I → H) (N : Module.End K (K ⊗[R] H)) (i : I),
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice φ ρ Fil B → DirectSum.IsInternal (fun σ : E →+* K ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ) →
    (∀ σ σ' : E →+* K, σ' ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ,
      ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ', B.baseChange K x y = 0) →
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsGens φ ρ e f → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsLower ρ (φ i) (e i) (f i) N →
    B (e i) (f i) ≠ 0 ∧ ∀ w, N w = (B.baseChange K w (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i)) / algebraMap R K (B (e i) (f i))) •
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i) := by
  intro E _ _ _ c R _ _ _ K _ _ _ _ H _ _ I φ ρ Fil B e f N i hL hdir horth hG hN
  obtain ⟨hfree, -, -, hlines, -, -, hbij, -, -⟩ := hL
  have hBK : ∀ u v : H, B.baseChange K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H u) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H v) = algebraMap R K (B u v) := by
    intro u v
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK, LinearMap.BilinForm.baseChange_tmul, Algebra.algebraMap_eq_smul_one]
  have he_mem : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (e i) ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (φ i) := by
    have hm : e i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (K := K) ρ (φ i) := by rw [(hG i).1]; exact Submodule.mem_span_singleton_self _
    exact hm
  have hf_mem : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i) ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)) := by
    have hm : f i ∈ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (K := K) ρ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)) := by
      rw [(hG i).2]; exact Submodule.mem_span_singleton_self _
    exact hm
  have hei : e i ≠ 0 := by
    intro h0
    obtain ⟨g, hg0, hg⟩ := GlobalTheory.EigenLattice.exists_ne_mem ρ (φ i) (hlines (φ i))
    rw [(hG i).1, h0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hg
    exact hg0 hg
  have he0 : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (e i) ≠ 0 := GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero hfree hei
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ z : K ⊗[R] H, z ∈ ⨆ σ : E →+* K, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ := fun z => by
    rw [hdir.submodule_iSup_eq_top]; exact Submodule.mem_top
  have hb : B (e i) (f i) ≠ 0 := by
    intro hb0
    have hBe : B (e i) ≠ 0 := fun h => hei (hbij.1 (by rw [h, map_zero]))
    obtain ⟨u, hu⟩ : ∃ u, B (e i) u ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hBe (LinearMap.ext hcon)
    have hall : ∀ v : K ⊗[R] H, B.baseChange K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (e i)) v = 0 := by
      intro v
      refine Submodule.iSup_induction (fun σ : E →+* K => GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ)
        (motive := fun v => B.baseChange K (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (e i)) v = 0) (hmem v) ?_ (by simp) ?_
      · intro σ' v hv
        by_cases hσ : σ' = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)
        · subst hσ
          obtain ⟨k, rfl⟩ := GlobalTheory.Div.eigen_line_bilinear.eq_smul_of_line (hlines _) hf_mem
            (GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero hfree (fun h0 => by
              obtain ⟨g, hg0, hg⟩ := GlobalTheory.EigenLattice.exists_ne_mem ρ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)) (hlines _)
              rw [(hG i).2, h0, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hg
              exact hg0 hg)) hv
          rw [map_smul, hBK, hb0, map_zero, smul_zero]
        · exact horth (φ i) σ' hσ _ he_mem v hv
      · intro x y hx hy
        rw [map_add, hx, hy, add_zero]
    have := hall (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H u)
    rw [hBK] at this
    exact hu (hinj (by rw [this, map_zero]))
  have hb' : algebraMap R K (B (e i) (f i)) ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
  refine ⟨hb, fun w => ?_⟩
  refine Submodule.iSup_induction (fun σ : E →+* K => GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ σ)
    (motive := fun w => N w = (B.baseChange K w (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i)) / algebraMap R K (B (e i) (f i))) •
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.inK K H (f i)) (hmem w) ?_ (by simp) ?_
  · intro σ w hw
    by_cases hσ : σ = φ i
    · subst hσ
      obtain ⟨k, rfl⟩ := GlobalTheory.Div.eigen_line_bilinear.eq_smul_of_line (hlines _) he_mem he0 hw
      rw [map_smul, hN.1, map_smul, LinearMap.smul_apply, hBK, smul_eq_mul, mul_div_assoc, div_self hb', _root_.mul_one]
    · have hne : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ := by
        intro h
        apply hσ
        have := congrArg GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar h
        rw [GlobalTheory.Div.eigen_line_bilinear.bar_bar, GlobalTheory.Div.eigen_line_bilinear.bar_bar] at this
        exact this.symm
      rw [hN.2 σ hσ w hw, horth σ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i)) hne w hw _ hf_mem, zero_div, zero_smul]
  · intro x y hx hy
    rw [map_add, hx, hy, map_add, LinearMap.add_apply, add_div, add_smul]

end GlobalTheory.Div.LowerPairFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MK
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.HomMum

abbrev MK : Type := ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2))

variable {S : Scheme.{0}}

def mφ (H₁ H₂ : Over S) [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] (a b : H₁ ⟶ H₂) :
    MK → ((H₁ ⊗ H₁).left ⟶ H₁.left ⨿ H₂.left) :=
  Sum.elim (fun I => (lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b)).left ≫ (psum H₂ (x2 H₂) I.down).left ≫ coprod.inr)
    (fun I => (psum H₁ (x2 H₁) I.down).left ≫ coprod.inl)

def mε : MK → ℤ :=
  Sum.elim (fun I => (-1 : ℤ) ^ (2 - I.down.card)) (fun I => -((-1 : ℤ) ^ (2 - I.down.card)))

def IsNrm {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {a b : H₁ ⟶ H₂}
    {L₁ : LB H₁.left} {L₂ : LB H₂.left} (u : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε)) : Prop :=
  u.IsGen ∧ ∀ (y : (𝟙_ (Over S)).left) (J), Good (join L₁ L₂) y J →
    val u (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left y J = 1

end GlobalTheory.HomMum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumCmp

section Maps

variable {X Y X' : Scheme.{0}} (L : LB X) (L' : LB X') {J : Type} [Fintype J]

lemma mapsAtExp_le_b (pr : J → (X' ⟶ X)) (ε : J → ℤ) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (jN, jL) ≤ LB.wchart L (fun i => p ≫ pr i) jN := by
  intro y hy
  refine Set.mem_iInter.2 fun i => ?_
  have h1 : p.base y ∈ LB.wchart L pr jN := hy.1
  exact Set.mem_iInter.1 h1 i

lemma mapsAtExp_le_a (pr : J → (X' ⟶ X)) (ε : J → ℤ) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (jN, jL) ≤ LB.wchart L' (fun _ : PUnit => p) (fun _ => jL) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

def MapsAtExp (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))) : Prop :=
  ∀ (jN : J → L.ι) (jL : L'.ι),
    res (mapsAtExp_le_b L L' pr ε p jN jL) (b.s jN) =
      (pullU p _ (w.s (jN, jL))) ^ n * res (mapsAtExp_le_a L L' pr ε p jN jL) (a.s (fun _ => jL))

end Maps

variable {R : Type} [CommRing R] [IsDomain R]

def twφ (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A) : Fin 3 → (D₀.P.A.left ⟶ D.P.A.left) :=
  ![(padd D.P.A β (toUnit D₀.P.A ≫ b)).left, (toUnit D₀.P.A ≫ b).left, (toUnit D₀.P.A ≫ η[D.P.A]).left]

def twε : Fin 3 → ℤ := ![1, -1, 1]

def IsTwist (D₀ D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) : Prop :=
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β.hom g.b) twε), w.IsGen ∧
      ∀ χ : D₀.X, ∃ t : LB.Gen (LB.LinComb D.P.L (fun i => D₀.xK χ ≫ twφ D₀ D β.hom g.b i) (fun i => -1 * twε i)),
        MapsAtExp D.P.L D₀.P.L (twφ D₀ D β.hom g.b) twε w (D₀.xK χ) (-1) (D₀.psi χ) t ∧
        LB.Gen.Corr D.P.L _ _ _ _ t
          (LB.mulGen D.P.L _ _ _ _ (D.psi (xe χ)) (LB.pullGen D.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left))

end GlobalTheory.MumCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalOfConnectedDensityStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_of_connected_density : ConnSt → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ → DensSt → PrincSt := by
  first | exact @GlobalTheory.FlatModel.princSt_of_connSt_propZ_densSt | exact GlobalTheory.FlatModel.princSt_of_connSt_propZ_densSt | (intros; apply GlobalTheory.FlatModel.princSt_of_connSt_propZ_densSt <;> assumption)
end

