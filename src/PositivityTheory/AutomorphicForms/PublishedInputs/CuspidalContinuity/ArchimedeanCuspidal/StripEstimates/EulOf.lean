import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0571
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0582
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.ScalarIntegralEstimates
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0567
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NeZeroOfRePos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0565
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentsTransferOneOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0557
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0584
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0587
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StripTransport
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.SecondDifferenceCpowBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0581
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootCountOfNotDvdJacobi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharpolyFactorCoeffZeroValuationEqProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumFloorHalf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0562
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0574
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0585
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCuspZeroFourierExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HalfIntegralEisensteinContinuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0578
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0569
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0568
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0586
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSetTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0579
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0570
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563

namespace Ad3.S

theorem t1 : T1 := (@GlobalTheory.CompanionTheory.HalfTheta.t1 : T1)

theorem t2 : T2 := (@GlobalTheory.CompanionTheory.HalfWeight.finite_sum_splitting : T2)

theorem t3 : T3 := (@Ad3.S.third_estimate_of_first_two : T1 → T2 → T3) t1 t2

theorem t4 : T4 := (@GlobalTheory.CompanionTheory.HalfWeight.gauss_sum_conjugation : T4)

theorem t5 : T5 := (@GlobalTheory.CompanionTheory.HalfWeightUnfold.term_of_theta : T3 → T4 → T5) t3 t4

theorem u0 : U0 := (@GlobalTheory.CompanionTheory.ModularTiling.exists_weight_Gamma0 : U0)

theorem u1 : U1 := (@GlobalTheory.CompanionTheory.Unfolding.unfolding_strip : U1)

theorem b1 : B1 := (@GlobalTheory.CompanionTheory.CuspDecay.b1 : B1)

theorem b2 : B2 := (@GlobalTheory.CompanionTheory.ThetaBound.b2 : B2)

theorem u2a : HorizontalIntegralTwisted := (@GlobalTheory.CompanionTheory.HalfIntegralWeight.unfolding_of_bound : B2 → HorizontalIntegralTwisted) b2

theorem u2 : U2 := (@GlobalTheory.CompanionTheory.HalfWt.strip_integral : B1 → B2 → HorizontalIntegralTwisted → U2) b1 b2 u2a

theorem d1 : D1 := (@GlobalTheory.CompanionTheory.CuspHeight.integrableOn_translate_fd : D1)

theorem lB : LB := (@Ad3.S.lB_of : LB)

theorem n1 : N1 := (@GlobalTheory.CompanionTheory.SquareRootCount.rr_eq : N1)

theorem n2 : N2 := (@GlobalTheory.CompanionTheory.SqrtCount.countingSquareRoots : N2)

theorem a2 : A2 := (@GlobalTheory.CompanionTheory.SquareEuler.euler_coeff : N1 → N2 → A2) n1 n2

theorem a1 : A1 := (@GlobalTheory.CompanionTheory.HalfInt.charpoly_factor_coeff_zero_valuation_eq_prod : LB → N2 → A2 → A1) lB n2 a2

theorem a0 : A0 := (@GlobalTheory.CompanionTheory.HalfIntZero.main : LB → N2 → A2 → A0) lB n2 a2

theorem w0 : W0 := (@GlobalTheory.CompanionTheory.HalfWeight.w0 : W0)

theorem w1 : W1 := (@GlobalTheory.CompanionTheory.HalfIntegral.kernel_fourier_integration_by_parts : W0 → W1) w0

theorem w2 : W2 := (@GlobalTheory.CompanionTheory.HalfWeight.kernel_fourier_continuation_decay : W0 → W1 → W2) w0 w1

theorem p1 : P1 := (@GlobalTheory.CompanionTheory.HalfWeightKernel.poisson_kernel : W0 → W2 → P1) w0 w2

theorem p2 : P2 := (@GlobalTheory.CompanionTheory.EisensteinPoissonSummation.eisenstein_cusp_zero_fourier_expansion : P1 → P2) p1

theorem e0 : E0 := (@GlobalTheory.CompanionTheory.HalfInt.half_integral_eisenstein_continuation : A0 → A1 → W0 → W1 → W2 → P2 → E0) a0 a1 w0 w1 w2 p2

theorem pR : PR := (@GlobalTheory.CompanionTheory.HalfIntPR.pr : PR)

theorem g0 : G0 := (@GlobalTheory.CompanionTheory.InvGammaStrip.g0 : G0)

theorem hI : HI := (@GlobalTheory.CompanionTheory.RgAds.holomorphy_integral_param : HI)

theorem s1 : S1 := (@GlobalTheory.CompanionTheory.HalfWeight.unfolded_identity_of : T5 → U1 → U2 → B2 → S1) t5 u1 u2 b2

theorem shim : Shim := (@GlobalTheory.CompanionTheory.ShimStep.shim_of : U0 → B2 → D1 → E0 → PR → G0 → HI → S1 → Shim) u0 b2 d1 e0 pR g0 hI s1

theorem e1 : E1 := (@GlobalTheory.CompanionTheory.HalfIntegral.e1 : E1)

theorem e1b : faceMap_comp_succAbove_castSucc := (@GlobalTheory.CompanionTheory.Rgads.e1b : faceMap_comp_succAbove_castSucc)

theorem e2a : E2a := (@GlobalTheory.CompanionTheory.HeckeEig.e2a : E2a)

theorem e2b : E2b := (@GlobalTheory.CompanionTheory.HalfIntWeight.localSeries : E2b)

theorem e2 : E2 := (@GlobalTheory.CompanionTheory.UnramifiedEisensteinCoefficients.e2 : faceMap_comp_succAbove_castSucc → E2a → E2b → E2) e1b e2a e2b

theorem e3 : E3 := (@GlobalTheory.CompanionTheory.EulerThree.HalfWt.adjoint_lift_twisted_euler_product : faceMap_comp_succAbove_castSucc → E3) e1b

theorem eulOf : EulOf := (@GlobalTheory.CompanionTheory.HalfInt.eulOf_of_faceMap_comp_succAbove_castSucc : E1 → faceMap_comp_succAbove_castSucc → E2 → E3 → EulOf) e1 e1b e2 e3

theorem anOf : AnOf := (@GlobalTheory.CompanionTheory.AdjointLift.anOf : AnOf)

end Ad3.S
