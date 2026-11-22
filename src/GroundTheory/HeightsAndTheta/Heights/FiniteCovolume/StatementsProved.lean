import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Assembly
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.OfUnfolding
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MainOf
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnitsInvHaar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PRadicalTorusModulus
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0026

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

universe u

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

theorem TorusEmbedding.full {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W) : TorusEmbedding.Statement h v :=
  TorusEmbedding.proof h v (HermAtPlace.full h v) (GramAtData.full h v)

theorem TorusModulus.full {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W) : TorusModulus.Statement h v :=
  TorusModulus.proof h v (HermAtPlace.full h v) (GramAtData.full h v) (ComplementForm.full h)
    (StabilizerLevi.proof h v) (UnipotentModulus.proof h v) (RadicalTorusModulus.proof h v)
    (fun _ _ _ _ _ => SemidirectHaar.proof _ _)

theorem UnipotentHorizontal.full {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipotentHorizontal.Statement h v :=
  UnipotentHorizontal.proof h v (RationalUnipotent.proof h) (UnipRadicalOfRational.proof h v)
    (ComplementArchCocompact.proof h v)

theorem UnipotentCentral.full {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipotentCentral.Statement h v :=
  UnipotentCentral.proof h v (RationalUnipotent.proof h) (UnipRadicalOfRational.proof h v)
    ImaginaryLatticeCocompact.proof

variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem UnfoldingIntegral.full (h : HermitianForm F E W) (v : Basis ι E W) :
    UnfoldingIntegral.Statement h v :=
  UnfoldingIntegral.of_remaining.{u}
    (fun _ _ _ _ h _ v => TorusEmbedding.full h v) (fun _ _ _ _ h _ v => LineEigenvalue.closed h v)
    (fun _ _ _ _ h _ v => TorusModulus.full h v) (fun _ _ _ _ _ _ _ => SemidirectHaar.proof _ _)
    (UnitsInvHaar.proof _) (fun _ _ _ _ h _ v => UnipotentCoordProper.proof h v)
    (fun _ _ _ _ h _ v => UnipotentHorizontal.full h v)
    (fun _ _ _ _ h _ v => UnipotentCentral.full h v)
    h v (TorusEmbedding.full h v) (LineEigenvalue.closed h v) (TorusModulus.full h v)
    (SemidirectHaar.proof _ _) (UnipotentCoordProper.proof h v) (UnipotentHorizontal.full h v)
    (UnipotentCentral.full h v)

theorem ScalingLaw.full (h : HermitianForm F E W) (v : Basis ι E W) : ScalingLaw.Statement h v :=
  ScalingLaw.of_remaining.{u}
    (fun _ _ _ _ h _ v => TorusEmbedding.full h v) (fun _ _ _ _ h _ v => LineEigenvalue.closed h v)
    (fun _ _ _ _ h _ v => TorusModulus.full h v) (fun _ _ _ _ _ _ _ => SemidirectHaar.proof _ _)
    (UnitsInvHaar.proof _) (fun _ _ _ _ h _ v => UnipotentCoordProper.proof h v)
    (fun _ _ _ _ h _ v => UnipotentHorizontal.full h v)
    (fun _ _ _ _ h _ v => UnipotentCentral.full h v)
    h v (TorusEmbedding.full h v) (LineEigenvalue.closed h v) (TorusModulus.full h v)
    (SemidirectHaar.proof _ _) (UnipotentCoordProper.proof h v) (UnipotentHorizontal.full h v)
    (UnipotentCentral.full h v)

theorem ArithmeticCovolumeFinite.full (h : HermitianForm F E W) (v : Basis ι E W) :
    ArithmeticCovolumeFinite.Statement h v :=
  ArithmeticCovolumeFinite.of_remaining.{u}
    (fun _ _ _ _ h _ v => TorusEmbedding.full h v) (fun _ _ _ _ h _ v => LineEigenvalue.closed h v)
    (fun _ _ _ _ h _ v => TorusModulus.full h v) (fun _ _ _ _ _ _ _ => SemidirectHaar.proof _ _)
    (UnitsInvHaar.proof _) (fun _ _ _ _ h _ v => UnipotentCoordProper.proof h v)
    (fun _ _ _ _ h _ v => UnipotentHorizontal.full h v)
    (fun _ _ _ _ h _ v => UnipotentCentral.full h v)
    h v (TorusEmbedding.full h v) (LineEigenvalue.closed h v) (TorusModulus.full h v)
    (SemidirectHaar.proof _ _) (UnipotentCoordProper.proof h v) (UnipotentHorizontal.full h v)
    (UnipotentCentral.full h v)

theorem AdelicCovolumeFinite.full (h : HermitianForm F E W) (v : Basis ι E W) :
    AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.of_remaining.{u}
    (fun _ _ _ _ h _ v => TorusEmbedding.full h v) (fun _ _ _ _ h _ v => LineEigenvalue.closed h v)
    (fun _ _ _ _ h _ v => TorusModulus.full h v) (fun _ _ _ _ _ _ _ => SemidirectHaar.proof _ _)
    (UnitsInvHaar.proof _) (fun _ _ _ _ h _ v => UnipotentCoordProper.proof h v)
    (fun _ _ _ _ h _ v => UnipotentHorizontal.full h v)
    (fun _ _ _ _ h _ v => UnipotentCentral.full h v)
    h v (TorusEmbedding.full h v) (LineEigenvalue.closed h v) (TorusModulus.full h v)
    (SemidirectHaar.proof _ _) (UnipotentCoordProper.proof h v) (UnipotentHorizontal.full h v)
    (UnipotentCentral.full h v)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
