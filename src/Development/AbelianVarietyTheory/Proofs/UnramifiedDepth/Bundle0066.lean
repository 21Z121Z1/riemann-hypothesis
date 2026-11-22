import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StSiegPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0064
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0038

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SiegPairPBNonempty
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv in

theorem siegPairPB_nonempty : ReciprocityTheory.ChartRestriction.G.Pdiv.StSiegPull := by
  intro S S' h M₁ B _ ζ s o f
  have hab : IsAbelianScheme ((Over.pullback f).obj o.A) :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  have hP := pull_isLB o.isLB (PullbackComparison.pφ₂ f o.A)
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  exact ⟨{
    A := (Over.pullback f).obj o.A
    ab := hab
    φ := PullbackComparison.pφ f o.A
    φ₂ := PullbackComparison.pφ₂ f o.A
    pb := PullbackComparison.isGrpPullback f o.A
    sq := PullbackComparison.isSquare f o.A
    P := o.P.pull (PullbackComparison.pφ₂ f o.A)
    isLB := hP
    iso := PullbackComparison.gen_refl _ hP
    rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ f o.A)
      (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
    rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ f o.A)
      (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
    symm := LBIso.chartPull (chartPullPull o.P _ _ rfl)
      (chartPullLinComb o.P _ _ _ _ (PullbackComparison.pφ₂ f o.A) (fun _ => PullbackComparison.lift_swap f o.A)) o.symm }⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniformizationSplitFormalGroupLawEquivariant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private noncomputable def starMat {X : Type} [AddCommGroup X] {r : ℕ} (β : Module.Basis (Fin r) ℤ X)
    (OE : Type) [CommRing OE] [StarRing OE] [Module OE X] : OE →+* Matrix (Fin r) (Fin r) ℤ where
  toFun a := Matrix.of fun i k => β.repr (star a • β i) k
  map_one' := by
    ext i k
    simp [Matrix.one_apply, Finsupp.single_apply]
  map_mul' a b := by
    ext i k
    have h : star (a * b) • β i = ∑ j, β.repr (star a • β i) j • (star b • β j) := by
      rw [star_mul, mul_smul]
      conv_lhs => rw [← β.sum_repr (star a • β i)]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    simp only [Matrix.of_apply, Matrix.mul_apply, h, map_sum, map_zsmul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  map_zero' := by
    ext i k
    simp
  map_add' a b := by
    ext i k
    simp [add_smul]

theorem unif_extSer_equivariant : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) [IsAdicComplete I R] (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam D.toPre.P.A g), NilChart G F.F x → NilChart D.toPre.P.A FB.F xB → ∃ (r : ℕ) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q ∧ ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (α : OE → Fin d → PS R 1 d) (αB : OE → Fin g → PS R 1 g), (∀ a, Reads x x (io.act a) (α a)) → (∀ a, Reads xB xB (oD.onB.act a) (αB a)) → ∃ N : OE →+* Matrix (Fin r) (Fin r) ℤ, ∀ a, lin Q * lin (α a) = lin (αB a) * lin Q ∧ lin (α a) * lin J = lin J * (N a).map (Int.castRingHom R) := by
  intro R _ _ I D A G _ _ U _ d g F FB x xB hx hxB
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_torus_extension_points_of_uniformisation R I D A G U
  let β : Module.Basis (Fin (Module.finrank ℤ D.toPre.X)) ℤ D.toPre.X := Module.finBasis ℤ D.toPre.X
  obtain ⟨Q, hQ, hQ'⟩ := GlobalTheory.T.toricPointExtension_abelianPart_formalGroup_hom R I G D.toPre.P.A D.toPre.X E d g F FB x xB hx hxB
  obtain ⟨J, hJ, hJ'⟩ := GlobalTheory.T.exists_formalGroupSeries_toricPointExtension R I G D.toPre.P.A D.toPre.X E d g F FB x xB hx hxB _ β
  refine ⟨_, J, Q, ⟨hJ, hQ, GlobalTheory.T.toricPointExtension_tangentSeq_splitExact R I G D.toPre.P.A D.toPre.X E d g F FB x xB hx hxB _ β J Q
    hJ.1 hQ.1 hQ' hJ'⟩, ?_⟩
  intro OE _ _ _ io oD oA hO α αB hα hαB
  refine ⟨starMat β OE, fun a => ?_⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.toricPointExtension_tangentSeq_equivariant R I G D.toPre.P.A D.toPre.X E d g F FB x xB hx hxB _ β J Q
    hJ.1 hQ.1 hQ' hJ' (io.act a) (α a) (hα a)
  refine ⟨h1 _ _ (hαB a) (fun S _ _ h => (hE OE io oD oA hO a S h).1), ?_⟩
  exact h2 (DistribSMul.toAddMonoidHom D.toPre.X (star a)) (fun S _ _ h => (hE OE io oD oA hO a S h).2)

end GlobalTheory
end

