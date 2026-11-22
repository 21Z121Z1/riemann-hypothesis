import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0472
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0468
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomApproxIntegralMatrixMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHatMxHomLatIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfRationalLevelInvariantAgreeChosen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ExtInv

theorem eq_of_invariant : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (M : ℕ), 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ φ ψ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g) → (∀ k, C.LevK Lv k 1 → ∀ g, φ (g * k) = φ g) → (∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a)) → φ = ψ := by
  intro D S T C Lv M hM hM𝔪 gL hgL φ ψ hφ hψ hφk hψk hag
  have hΛ : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [Red.fmt_one]; exact Red.isMov_one _
  obtain ⟨-, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hI : C.under Lv ≠ ⊥ := (hL Lv 1 _ hΛ.1 hm1).2.2.1
  have hgrp := ((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.1
  have hcomm := ((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.2.2.1
  funext g
  obtain ⟨γ, hγ, a, ha, g', hg', k, hk, hg, ht, -, hck, hcJ⟩ := GlobalTheory.T.exists_rational_real_trivialAt_congruent_factor D T C.X.Λ (C.under Lv) M hΛ hI hM g
  have hinv : fmt T g' * fmt T g'⁻¹ = 1 := by rw [← (hgrp g' g'⁻¹).2.1, mul_inv_cancel, Red.fmt_one]
  obtain ⟨L, hLf, hLm⟩ := ((GlobalTheory.T.finiteAdelicLatticeTransport_laws D _ C.X.Λ hΛ).2.2.2 _ _ hinv).1
  have hLl : L ∈ Lv.lats := (hL Lv g' L hLf.1 hLm).2.1 ht
  obtain ⟨h1, h2, h3⟩ := hgL L hLl
  have hk1 : C.LevK Lv k 1 := Red.levK_one C Lv k hk hck.1 (hcJ _ hM𝔪)
  have hk2 : C.LevK Lv ((gL L)⁻¹ * g') 1 := GlobalTheory.T.level_group_congruent_of_two_lattice_moves D S T C Lv (gL L) g' L h1 hg' h2 ht hLf.1 h3 hLm
  have e : g = γ * (gL L * a * ((gL L)⁻¹ * g') * k) := by
    rw [hg, ← (hcomm a ha).2.2 _ h1]
    group
  rw [e, hφ γ hγ, hψ γ hγ, hφk k hk1, hψk k hk1, hφk _ hk2, hψk _ hk2]
  exact hag L hLl a ha

end GlobalTheory.Ker.ExtInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGeneratorHeckeIsogenyLineBundleQuotient
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_gen_isoLB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), ∃ β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP (hkMap Z hx hx') ((p : ℤ) ^ 2)), β.IsGen := by
  intro E _ _ _ H Dw l Xo P p i Z T _ h x x' hx hx'
  have hL : Xo.univ.t.PP.L.IsLB := Xo.univ.t.PP.isLB
  have hL₁ : Z.o₁.t.PP.L.IsLB := Z.o₁.t.PP.isLB
  have hL₂ : Z.o₂.t.PP.L.IsLB := Z.o₂.t.PP.isLB
  obtain ⟨w₁, hw₁, -⟩ := Z.m₁.lin
  obtain ⟨w₂, hw₂, -⟩ := Z.m₂.lin
  have i₁ : LBIso Z.o₁.t.PP.L (Xo.univ.t.PP.L.pull Z.m₁.cm.F) := ⟨w₁, hw₁⟩
  have i₂ : LBIso Z.o₂.t.PP.L (Xo.univ.t.PP.L.pull Z.m₂.cm.F) := ⟨w₂, hw₂⟩
  have i₃ : LBIso (lbPow Z.o₁.t.PP.L (p ^ 2)) (Xo.univ.t.PP.L.pull (Z.ψ.left ≫ Z.m₂.cm.F)) :=
    GlobalTheory.ThetaAffineGlue.lbIso_comp (isLB_lbPow hL₁ _) hL₂ hL Z.isog.1.2.2.2.2.2 i₂
  have i₄ := GlobalTheory.ThetaAffineGlue.lbIso_pull i₃ (hkLift Z h hx)
  have i₅ := GlobalTheory.Spread.lbIso_pow_pull_comp hL hL₁ i₁ (hkLift Z h hx) (hkLift_φ Z hx).symm (p ^ 2)
  have i₆ := lbIso_lbPow_pull hL₁ (hkLift Z h hx) (p ^ 2)
  have i₇ := GlobalTheory.EmbVA.lbIso_pow hL (snd (Over.mk x) Xo.univ.t.G).left (p ^ 2) ((p : ℤ) ^ 2) (by push_cast; rfl)
  have i₈ := ((i₇.trans (LB.isLB_linComb hL _ _) (pull_isLB (isLB_lbPow hL _) _)
    (isLB_lbPow (pull_isLB hL₁ _) _) i₅.symm).trans (LB.isLB_linComb hL _ _) (isLB_lbPow (pull_isLB hL₁ _) _)
    (pull_isLB (isLB_lbPow hL₁ _) _) i₆).trans (LB.isLB_linComb hL _ _) (pull_isLB (isLB_lbPow hL₁ _) _)
    (pull_isLB hL _) i₄
  have e := (GlobalTheory.PrimNorm.lbIso_iff hL _ _ _ _).1 i₈
  rw [Fin.prod_univ_one, Fintype.prod_unique, zpow_one] at e
  refine (GlobalTheory.PrimNorm.hasGen_iff hL (isoφ Xo.univ.t.G (hkMap Z hx hx')) ![(p : ℤ) ^ 2, -1]).2 ?_
  rw [prod_iso', hkMap_snd, e, mul_inv_cancel]

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeElementIdempotentPartSplitPlaceLatticStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeElement_idempotentPart_splitPlace_lattice : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ ∀ v ∈ latG V g,
      (finPart D e • finVec V v ∈ latGHat V (g * a₀) ↔
        finPart D e • finVec V v ∈ GlobalTheory.AdLat.hat D.host.F (M : Set (Fin V.rank → D.host.E))) := by
  first | exact @GlobalTheory.HeckeLocLift.exists_hecke_ePart | exact GlobalTheory.HeckeLocLift.exists_hecke_ePart | (intros; apply GlobalTheory.HeckeLocLift.exists_hecke_ePart <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomLatticeCosetIndicatorEqLatticeHomCoset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7}

theorem prod_eq_inf (P : Finset (Pl D.host.E)) (d : Pl D.host.E → ℕ) :
    (∏ w ∈ P, w.asIdeal ^ d w) = P.inf fun w => w.asIdeal ^ d w :=
  (HeightOneSpectrum.inf_pow_eq_prod _ _ _ fun _ _ _ _ hne h => hne h).symm

theorem prod_ne_bot (P : Finset (Pl D.host.E)) (d : Pl D.host.E → ℕ) :
    (∏ w ∈ P, w.asIdeal ^ d w) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)

theorem idem_mem_OA {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : toEAf D e ∈ OA D := by
  obtain ⟨-, e1, e2⟩ := cpt_idemSum he
  refine (mem_OA_iff _).2 fun w => ?_
  by_cases hw : w ∈ P
  · rw [e1 w hw]; exact one_mem _
  · rw [e2 w hw]; exact zero_mem _

theorem one_sub_idem_mem {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (d : Pl D.host.E → ℕ) :
    (1 - ⟨toEAf D e, idem_mem_OA he⟩ : OA D) ∈ idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w) := by
  obtain ⟨-, e1, -⟩ := cpt_idemSum he
  refine mem_idS_of_v_le (w := fun w => w) (prod_ne_bot P d) (prod_eq_inf P d) fun w hw => ?_
  show Valued.v (cpt (D := D) w (1 - toEAf D e)) ≤ _
  rw [RingHom.map_sub, RingHom.map_one, e1 w hw, sub_self, Valuation.map_zero]
  exact zero_le'

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}

theorem half_map (hx : IsHalf e x) : x.map (toEAf D) = toEAf D e • x.map (toEAf D) :=
  Matrix.ext fun i j => by
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← RingHom.map_mul, hx i j]

theorem fr_half (hx : IsHalf e x) (i : Fin T.V.rank) (j : Fin S.V.rank) :
    fr T.β S.β (x.map (toEAf D)) i j = toEAf D e * fr T.β S.β (x.map (toEAf D)) i j := by
  have h1 : fr T.β S.β (x.map (toEAf D)) i j = fr T.β S.β (toEAf D e • x.map (toEAf D)) i j := by
    rw [← half_map hx]
  rw [fr_smul, Matrix.smul_apply, smul_eq_mul] at h1
  exact h1

variable {S T : GlobalTheory.Grid.Node D}

theorem frMapO_eq_fr (x : WO S.V T.V) : frMapO S.V T.V S.β T.β x = fr T.β S.β (x.map (toEAf D)) := by
  unfold frMapO fr
  rfl

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

theorem alg_one {R : Type} [CommRing R] {s t A A' X Y E eS : R} (hs : s = E * (X - Y)) (ht : t = Y - A') (ha : A = A')
    (he : eS = E) (hx : X = E * X) : s + eS * t - (1 - eS) * A + A = X := by
  subst hs ht ha he
  linear_combination -hx

theorem alg_two {R : Type} [CommRing R] {s t A X eS : R} (h : s + eS * t - (1 - eS) * A + A = X) :
    X - A = s + eS * t - (1 - eS) * A := by
  rw [← h]; ring

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}

theorem half_sub (hx : IsHalf e x) (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (i : Fin T.V.rank)
    (j : Fin S.V.rank) : (x - e • y.map (incA D)) i j = e * (x i j - incA D (y i j)) := by
  rw [mul_sub, hx]; rfl

theorem fr_half_sub (hx : IsHalf e x) (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (i : Fin T.V.rank)
    (j : Fin S.V.rank) : fr T.β S.β ((x - e • y.map (incA D)).map (toEAf D)) i j =
      toEAf D e * (fr T.β S.β (x.map (toEAf D)) i j - fr T.β S.β (y.map (eToEAf D)) i j) := by
  have h : (x - e • y.map (incA D)).map (toEAf D) = toEAf D e • (x.map (toEAf D) - y.map (eToEAf D)) :=
    Matrix.ext fun i j => by rw [Matrix.map_apply, half_sub hx, RingHom.map_mul, RingHom.map_sub]; rfl
  rw [h, fr_smul, fr_sub]; rfl

theorem sub_mem_hatMx {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ) (hT : IsFrame T.β T.Λ)
    (he : IsIdemSum e P) (x₀ : homLat S.Λ T.Λ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (hx : IsHalf e x)
    (h : ∀ i j, ∃ hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I) :
    x - e • (x₀.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ) := by
  obtain ⟨e0, -, -⟩ := cpt_idemSum he
  refine (mem_hatMx_iff hS hT _ _).2 ⟨fun i j => by rw [half_sub hx, RingHom.map_mul, e0, zero_mul], fun i j => ?_⟩
  obtain ⟨hX, h'⟩ := h i j
  refine ⟨⟨toEAf D e, idem_mem_OA he⟩ * (⟨_, hX⟩ - a i j), Ideal.mul_mem_left _ _ h', ?_⟩
  refine Eq.trans ?_ (fr_half_sub hx x₀.1 i j).symm
  exact congrArg (toEAf D e * ·) (congrArg₂ (· - ·) rfl (ha i j))

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}

set_option maxHeartbeats 1000000 in

theorem frMapO_sub_mem {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ) (hT : IsFrame T.β T.Λ) (eS : OA D)
    (heS : eS.1 = toEAf D e) (he1 : 1 - eS ∈ idS D.host.F I)
    (x₀ : homLat S.Λ T.Λ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (hx : IsHalf e x) (y : homLat S.Λ T.Λ)
    (hyx : y.1 - x₀.1 ∈ I • homLat S.Λ T.Λ)
    (hz : x - e • (y.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ))
    (i : Fin T.V.rank) (j : Fin S.V.rank) : ∃ hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I := by
  obtain ⟨s, hs, hs'⟩ := ((mem_hatMx_iff hS hT _ _).1 hz).2 i j
  obtain ⟨t, ht, ht'⟩ := fr_mem_idS hS hT hyx i j
  have hs'' := hs'.trans (fr_half_sub hx y.1 i j)
  have hyA : t.1 = fr T.β S.β (y.1.map (eToEAf D)) i j - fr T.β S.β (x₀.1.map (eToEAf D)) i j := by
    rw [ht', Matrix.map_sub _ (RingHom.map_sub _), fr_sub, Matrix.sub_apply]
  have hz0 : s.1 + eS.1 * t.1 - (1 - eS.1) * (a i j).1 + (a i j).1 = fr T.β S.β (x.map (toEAf D)) i j :=
    alg_one hs'' hyA (ha i j) heS (fr_half hx i j)
  have hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have hz1 : ((s + eS * t - (1 - eS) * a i j + a i j : OA D) : EAf D) = fr T.β S.β (x.map (toEAf D)) i j := by
      simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one]
      exact hz0
    rw [frMapO_eq_fr, ← hz1]
    exact (s + eS * t - (1 - eS) * a i j + a i j).2
  refine ⟨hX, ?_⟩
  have : (⟨_, hX⟩ : OA D) - a i j = s + eS * t - (1 - eS) * a i j := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one]
    rw [frMapO_eq_fr]
    exact alg_two hz0
  rw [this]
  exact sub_mem (add_mem hs (Ideal.mul_mem_left _ _ ht)) (Ideal.mul_mem_right _ _ he1)

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D}

set_option maxHeartbeats 1000000 in

theorem cosetInd_eq_of {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ)
    (hT : IsFrame T.β T.Λ) (he : IsIdemSum e P) (he1 : (1 - ⟨toEAf D e, idem_mem_OA he⟩ : OA D) ∈ idS D.host.F I)
    (κ : Cos S.Λ T.Λ I) (x₀ : homLat S.Λ T.Λ) (hx₀ : Cos.mk I x₀ = κ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (c : Coset S T I)
    (hc : ∀ i j, cmpS D.host.F I (c i j) = Ideal.Quotient.mk (idS D.host.F I) (a i j)) :
    cosetInd S T e I c = cosInd e κ := by
  funext x
  have key : IsHalf e x → (InCosetOf S T I c x ↔ ∃ y : homLat S.Λ T.Λ, Cos.mk I y = κ ∧
      x - e • (y.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ)) := by
    intro hx
    have hq : ∀ i j (hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
        Ideal.Quotient.mk (idS D.host.F I) ⟨_, hX⟩ = cmpS D.host.F I (c i j) ↔ (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I :=
      fun i j hX => by rw [hc i j, Ideal.Quotient.eq]
    constructor
    · intro h
      exact ⟨x₀, hx₀, sub_mem_hatMx hS hT he x₀ a ha hx fun i j => ⟨(h i j).1, (hq i j _).1 (h i j).2⟩⟩
    · rintro ⟨y, hy, hz⟩ i j
      obtain ⟨hX, h'⟩ := frMapO_sub_mem hS hT _ rfl he1 x₀ a ha hx y (sub_mem_of_mk_eq (hy.trans hx₀.symm)) hz i j
      exact ⟨hX, (hq i j hX).2 h'⟩
  have hiff : (IsHalf e x ∧ InCosetOf S T I c x) ↔ x ∈ cosSet e κ :=
    ⟨fun ⟨h1, h2⟩ => ⟨h1, (key h1).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (key h1).2 h2⟩⟩
  unfold GlobalTheory.Grid.cosetInd GlobalTheory.ChiGrid.cosInd
  by_cases h : x ∈ cosSet e κ
  · rw [if_pos (hiff.2 h), Set.indicator_of_mem h]; rfl
  · rw [if_neg (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]

theorem cosInd_eq_cosetInd : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), Formalism.L2.DIV.IsFrame S.β S.Λ → Formalism.L2.DIV.IsFrame T.β T.Λ → IsIdemSum e P → ∀ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ (∏ w ∈ P, w.asIdeal ^ d w), ∃ c : GlobalTheory.Grid.Coset S T (∏ w ∈ P, w.asIdeal ^ d w), GlobalTheory.Grid.cosetInd S T e (∏ w ∈ P, w.asIdeal ^ d w) c = GlobalTheory.ChiGrid.cosInd e κ := by
  intro D S T e P d hS hT he κ
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : homLat S.Λ T.Λ, Cos.mk (∏ w ∈ P, w.asIdeal ^ d w) x₀ = κ :=
    Submodule.Quotient.mk_surjective _ κ
  have hA : ∀ i j, ∃ s : OA D, s.1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j := fun i j => by
    obtain ⟨s, -, hs⟩ := fr_mem_idS hS hT (𝔪 := ⊤) (y := x₀.1) (by rw [Submodule.top_smul]; exact x₀.2) i j
    exact ⟨s, hs⟩
  choose a ha using hA
  choose c hc using fun i j => cmpS_surj (F := D.host.F) _ (prod_ne_bot P d)
    (Ideal.Quotient.mk (idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w)) (a i j))
  exact ⟨fun i j => c i j, cosetInd_eq_of hS hT he (one_sub_idem_mem he d) κ x₀ hx₀ a ha _ fun i j => hc i j⟩

end GlobalTheory.CosToCoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepIntertwinerChainStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lastStep_intertwiner_chain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.IsChainW → R.ex_ItX := by
  first | exact @GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner | exact GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner | (intros; apply GlobalTheory.Twist.LastStepExists.exists_lastStep_intertwiner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomApproxIntegralMatrixModStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeHom_approx_integralMatrix_mod : ∀ {D : D7} {m n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)), Formalism.L2.DIV.IsFrame β Λ → Formalism.L2.DIV.IsFrame β' Λ' → ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ (N : Matrix (Fin m) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)), ∃ x₀ ∈ GlobalTheory.ChiGrid.homLat Λ Λ', ∀ i j, ∃ s ∈ Formalism.L2.DIV.idS D.host.F I, (s : EAf D) = HMul.hMul (HMul.hMul (β'⁻¹).val (x₀.map (eToEAf D))) β.val i j - (N i j : EAf D) := by
  first | exact @GlobalTheory.FunObj.HatFrame.homLat_approx_mod | exact GlobalTheory.FunObj.HatFrame.homLat_approx_mod | (intros; apply GlobalTheory.FunObj.HatFrame.homLat_approx_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeLevelOpenStabilizerUnitaryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_level_open_stabilizer_unitary : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (N : AddSubgroup (WO S T)) (K : Subgroup (GA D T)), N ≤ U ∧ IsOpen (K : Set (GA D T)) ∧ (∀ x : WO S T, ∃ γ ∈ ratL T S, ∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T (x - γ) l) = 1) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ u ∈ N, u.map (infPart D) = 0 → actO S T 1 k u ∈ N ∧ (actO S T 1 k u).map (infPart D) = 0) ∧ (∀ k ∈ K, k ∈ GfC T → ∀ w : WO S T, (∀ l ∈ N, l.map (infPart D) = 0 → ψ (symplO S T w l) = 1) → actO S T 1 k w - w ∈ N ∧ (actO S T 1 k w - w).map (infPart D) = 0 ∧ ψ (symplOH S T w (actO S T 1 k w - w)) = 1) := by
  first | exact @GlobalTheory.WeilLevelStab.exists_level_stab | exact GlobalTheory.WeilLevelStab.exists_level_stab | (intros; apply GlobalTheory.WeilLevelStab.exists_level_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenEqOneOfContinuousMulFinitePointsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_eq_one_of_continuous_mul_finitePoints : ∀ {D : D7} (T : HSp D) (K : Subgroup (GA D T)), IsOpen (K : Set (GA D T)) → ∀ F : GA D T → ℂ, Continuous F → F 1 = 1 → (∀ a ∈ K, a ∈ GfC T → ∀ b ∈ K, b ∈ GfC T → F (a * b) = F a * F b) → ∃ U : Subgroup (GA D T), IsOpen (U : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC T → F k = 1 := by
  first | exact @GlobalTheory.OpenKer.eq_one_on_finite_of_mul | exact GlobalTheory.OpenKer.eq_one_on_finite_of_mul | (intros; apply GlobalTheory.OpenKer.eq_one_on_finite_of_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPointStandardSourceUnitaryComponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdRealLift

theorem exists_real_point : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (v : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, (v τ)ᴴ * v τ = 1) → ∃ h ∈ GinfC S, ∀ τ, compAt C.θ τ (mt S h) = v τ := by
  intro D S T C v hv
  obtain ⟨L, hL, -⟩ := GlobalTheory.RealLift.exists_real_lift D C.θ S C.inf
  have hu : v ∈ HolDict.UG (gramAt D S) := by
    intro τ
    have hg : gramAt D S τ = 1 := by
      unfold gramAt
      rw [C.m.gS]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    show (v τ)ᴴ * gramAt D S τ * v τ = gramAt D S τ
    rw [hg, Matrix.mul_one]
    exact hv τ
  refine ⟨L v, (hL v hu).1, fun τ => ?_⟩
  rw [← (hL v hu).2 τ]
  clear hL hu hv
  unfold compAt archM
  ext i j
  rfl

end GlobalTheory.StdRealLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarOfCommuteSchrodingerOperatorsStatement
section
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_of_commute_schrodingerOperators : ∀ (l : Type) [Fintype l] (S : Sch l →ₗ[ℂ] Sch l), (∀ f, ∫ x, ‖S f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(S f₁) = rhoFun w ⇑(S f)) → ∃ c : ℂ, ∀ f, S f = c • f := by
  first | exact @GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun | exact GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun | (intros; apply GlobalTheory.RealWeil.exists_eq_smul_of_commute_rhoFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteMatrixIotaEqFinitePartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteMatrix_iota_eq_finitePart : ∀ {D : D7} (κ : GA D (Yc D 0)), (GlobalTheory.SeeConjGroup.II D).fmat ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = (finE (Yc D 0) κ).val := by
  first | exact @GlobalTheory.SeeConjGroup.fmat_iota_eq_finE | exact GlobalTheory.SeeConjGroup.fmat_iota_eq_finE | (intros; apply GlobalTheory.SeeConjGroup.fmat_iota_eq_finE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableDiagonalModSmallStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagPairingTable_diagonal_modSmall : ∀ {M A : Type} [Zero M] [Ring A] (p : M → M → A) (sm : A → Prop) (ρ k n : ℕ), n = 2 * ρ + k + 1 → ∀ (e f : Fin ρ → M) (b b' : Fin k → M) (z : M), PairTable p sm e f b b' z → ∀ a c : Fin n, sm (p (flagV ρ k n f e b' z a) (flagV ρ k n e f b z c) - if a = c then sgnD ρ k a else 0) := by
  first | exact @GlobalTheory.SeeConjRead.flagV_pair_table | exact GlobalTheory.SeeConjRead.flagV_pair_table | (intros; apply GlobalTheory.SeeConjRead.flagV_pair_table <;> assumption)
end

