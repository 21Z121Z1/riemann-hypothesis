import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PGlueModulesStar
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.SpreadIsoModelIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

theorem BlowUpChart.full : BlowUpChart.Statement := BlowUpChart.proof

theorem ChartGlue.full : ChartGlue.Statement := ChartGlue.proof

theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement := FiniteIntegralClosure.proof

theorem GenericGermInjective.full : GenericGermInjective.Statement := GenericGermInjective.proof

theorem GenericSectionsInj.full : GenericSectionsInj.Statement := GenericSectionsInj.proof

theorem GlueModulesStar.full : GlueModulesStar.Statement := GlueModulesStar.proof

theorem HeightOneIntersection.full : HeightOneIntersection.Statement := HeightOneIntersection.proof

theorem InvOpenInside.full : InvOpenInside.Statement := InvOpenInside.proof

theorem InvOpenInsideRat.full : InvOpenInsideRat.Statement := InvOpenInsideRat.proof

theorem MertensUpper.full : MertensUpper.Statement := MertensUpper.proof

theorem PrimeOpensCover.full : PrimeOpensCover.Statement := PrimeOpensCover.proof

theorem RatLocalAffine.full : RatLocalAffine.Statement := RatLocalAffine.proof

theorem SectionNef.full : SectionNef.Statement := SectionNef.proof

theorem SectionNefGenerated.full : SectionNefGenerated.Statement := SectionNefGenerated.proof

theorem TorsionFreeQuotientLength.full : TorsionFreeQuotientLength.Statement := TorsionFreeQuotientLength.proof

theorem VectorBundleLocal.full : VectorBundleLocal.Statement := VectorBundleLocal.proof

theorem VectorBundleRestrict.full : VectorBundleRestrict.Statement := VectorBundleRestrict.proof

theorem PullbackFaithful.full : PullbackFaithful.Statement.{0} := PullbackFaithful.proof

theorem KrullAkizukiQuotientLength.full : KrullAkizukiQuotientLength.Statement :=
  KrullAkizukiQuotientLength.proof TorsionFreeQuotientLength.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.proof KrullAkizukiQuotientLength.full

theorem DominatingDVR.full : DominatingDVR.Statement :=
  DominatingDVR.proof KrullAkizuki.full BlowUpChart.full

theorem HeightOneSections.full : HeightOneSections.Statement :=
  HeightOneSections.proof GenericGermInjective.full

theorem BundlesAgree.full : BundlesAgree.Statement :=
  BundlesAgree.proof GenericGermInjective.full HeightOneSections.full

theorem ChartBundlesAgree.full : ChartBundlesAgree.Statement :=
  ChartBundlesAgree.proof HeightOneIntersection.full

theorem LatticesAgree.full : LatticesAgree.Statement :=
  LatticesAgree.proof HeightOneIntersection.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.proof MertensUpper.full

theorem SpreadHomInj.full : SpreadHomInj.Statement :=
  SpreadHomInj.proof GenericSectionsInj.full PullbackFaithful.full

theorem FiniteNormalization.full : FiniteNormalization.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.normalization_of_scheme
    (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.scheme_of_alg
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.FiniteIntegralClosure.alg_iff.mp FiniteIntegralClosure.full))

theorem ClearDenominators.of_open (hPB : PullbackBasis.Statement.{0}) :
    ClearDenominators.Statement :=
  ClearDenominators.proof hPB RatLocalAffine.full

theorem SpreadLocal.of_open (hFB : FreeSheafBasis.Statement.{0})
    (hBI : BasisIsoFree.Statement.{0}) : SpreadLocal.Statement :=
  SpreadLocal.proof hFB hBI

theorem SpreadBundleNbhd.of_open (hFB : FreeSheafBasis.Statement.{0})
    (hBI : BasisIsoFree.Statement.{0}) (hSS : SpreadStep.Statement) :
    SpreadBundleNbhd.Statement :=
  SpreadBundleNbhd.proof (SpreadLocal.of_open hFB hBI) hSS

theorem SpreadBundle.of_open (hFB : FreeSheafBasis.Statement.{0})
    (hBI : BasisIsoFree.Statement.{0}) (hSS : SpreadStep.Statement) : SpreadBundle.Statement :=
  SpreadBundle.proof (SpreadBundleNbhd.of_open hFB hBI hSS) InvOpenInside.full

theorem SpreadHomNbhd.of_open (hDH : DescendHom.Statement) (hGP : GenericPullInj.Statement)
    (hHS : SpreadHomSections.Statement) : SpreadHomNbhd.Statement :=
  SpreadHomNbhd.proof hDH hGP hHS

theorem SpreadHom.of_open (hDH : DescendHom.Statement) (hGP : GenericPullInj.Statement)
    (hHS : SpreadHomSections.Statement) : SpreadHom.Statement :=
  SpreadHom.proof (SpreadHomNbhd.of_open hDH hGP hHS) InvOpenInsideRat.full

theorem SpreadIso.of_open (hDH : DescendHom.Statement) (hGP : GenericPullInj.Statement)
    (hHS : SpreadHomSections.Statement) : SpreadIso.Statement :=
  SpreadIso.proof (SpreadHom.of_open hDH hGP hHS) SpreadHomInj.full

theorem GlueBundles.of_open (hFB : FreeSheafBasis.Statement.{0})
    (hBI : BasisIsoFree.Statement.{0}) (hSS : SpreadStep.Statement)
    (hDH : DescendHom.Statement) (hGP : GenericPullInj.Statement)
    (hHS : SpreadHomSections.Statement) : GlueBundles.Statement :=
  GlueBundles.proof (SpreadBundle.of_open hFB hBI hSS) (SpreadIso.of_open hDH hGP hHS)
    PrimeOpensCover.full GlueModulesStar.full VectorBundleRestrict.full VectorBundleLocal.full

end GroundTheory.Heights₂.Heights.Model

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem BlowUpChart.full : BlowUpChart.Statement :=
  BlowUpChart.equiv.mp GroundTheory.Heights₂.Heights.Model.BlowUpChart.full

theorem BundlesAgree.full : BundlesAgree.Statement :=
  BundlesAgree.equiv.mp GroundTheory.Heights₂.Heights.Model.BundlesAgree.full

theorem HeightOneIntersection.full : HeightOneIntersection.Statement :=
  HeightOneIntersection.equiv.mp GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.full

theorem KrullAkizuki.full : KrullAkizuki.Statement :=
  KrullAkizuki.equiv.mp GroundTheory.Heights₂.Heights.Model.KrullAkizuki.full

theorem LatticesAgree.full : LatticesAgree.Statement :=
  LatticesAgree.equiv.mp GroundTheory.Heights₂.Heights.Model.LatticesAgree.full

theorem MertensUpper.full : MertensUpper.Statement :=
  MertensUpper.equiv.mp GroundTheory.Heights₂.Heights.Model.MertensUpper.full

theorem SumCp.full : SumCp.Statement :=
  SumCp.equiv.mp GroundTheory.Heights₂.Heights.Model.SumCp.full

theorem SectionNef.full : SectionNef.Statement :=
  SectionNef.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.SectionNef.full,
    GroundTheory.Heights₂.Heights.Model.SectionNefGenerated.full⟩

theorem FiniteIntegralClosure.full : FiniteIntegralClosure.Statement :=
  FiniteIntegralClosure.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full,
    GroundTheory.Heights₂.Heights.Model.FiniteNormalization.full⟩

theorem DominatingDVR.of_open (hS : GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.Statement) :
    DominatingDVR.Statement :=
  DominatingDVR.equiv.mp ⟨GroundTheory.Heights₂.Heights.Model.DominatingDVR.full, hS⟩

theorem ClearDenominators.of_open
    (hPB : GroundTheory.Heights₂.Heights.Model.PullbackBasis.Statement.{0}) :
    ClearDenominators.Statement :=
  ClearDenominators.equiv.mp (GroundTheory.Heights₂.Heights.Model.ClearDenominators.of_open hPB)

theorem SpreadBundle.of_open (hFB : GroundTheory.Heights₂.Heights.Model.FreeSheafBasis.Statement.{0})
    (hBI : GroundTheory.Heights₂.Heights.Model.BasisIsoFree.Statement.{0})
    (hSS : GroundTheory.Heights₂.Heights.Model.SpreadStep.Statement) : SpreadBundle.Statement :=
  SpreadBundle.equiv.mp (GroundTheory.Heights₂.Heights.Model.SpreadBundle.of_open hFB hBI hSS)

theorem SpreadIso.of_open (hDH : GroundTheory.Heights₂.Heights.Model.DescendHom.Statement)
    (hGP : GroundTheory.Heights₂.Heights.Model.GenericPullInj.Statement)
    (hHS : GroundTheory.Heights₂.Heights.Model.SpreadHomSections.Statement) : SpreadIso.Statement :=
  SpreadIso.equiv.mp (GroundTheory.Heights₂.Heights.Model.SpreadIso.of_open hDH hGP hHS)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
