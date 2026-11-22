import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1900
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialZeroLocusCoordinates
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0495
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeCentraliserClassNumberFiniteBorel
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls.Fin

theorem classes_finite_of_locus (hloc : ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D),
  ∃ (N : ℕ) (S : Set (MvPolynomial (Fin N × Fin N) ℚ)) (hS : HeckeCharacterZeroLocus.IsGroupLocus S)
    (φ : ∀ (R : Type) [CommRing R] [Algebra ℚ R], HeckeCharacterZeroLocus.locusSubgroup S hS R →* (R ⊗[ℚ] D)ˣ × Rˣ),
    (∀ (R : Type) [CommRing R] [Algebra ℚ R], Function.Injective (φ R) ∧
      ∀ z : (R ⊗[ℚ] D)ˣ × Rˣ, GlobalTheory.TorCls.TC D σ β y R z ↔ z ∈ Set.range (φ R)) ∧
    (∀ (R R' : Type) [CommRing R] [Algebra ℚ R] [CommRing R'] [Algebra ℚ R'] (f : R →ₐ[ℚ] R')
      (g : HeckeCharacterZeroLocus.locusSubgroup S hS R) (g' : HeckeCharacterZeroLocus.locusSubgroup S hS R'),
      (g' : GL (Fin N) R') = Units.map (f.toRingHom.mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R').toMonoidHom (g : GL (Fin N) R) →
      φ R' g' = (Units.map (Algebra.TensorProduct.map f (AlgHom.id ℚ D)).toRingHom.toMonoidHom (φ R g).1,
        Units.map f.toRingHom.toMonoidHom (φ R g).2)) ∧
    (∀ (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R],
      letI : TopologicalSpace (R ⊗[ℚ] D) := moduleTopology R (R ⊗[ℚ] D)
      Continuous (φ R))) :
    ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime], letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D); letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D); ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) → ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ), GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ (γ.1 : D)).unop = algebraMap ℚ D (γ.2 : ℚ) * β ∧ Commute (γ.1 : D) y ∧ ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u :=
  fun D _ _ _ σ β y p _ => GlobalTheory.TorCls.Borel.classes_finite hloc GlobalTheory.classNumberFinite_holds D σ β y p

theorem classes_finite :
    ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime], letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D); letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D); ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → z ∈ U) → ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z : ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ), GlobalTheory.CentCls.TC D σ β y (AfP p) z.1 → GlobalTheory.CentCls.TC D σ β y ℚ_[p] z.2 → ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ (γ.1 : D)).unop = algebraMap ℚ D (γ.2 : ℚ) * β ∧ Commute (γ.1 : D) y ∧ ∃ s ∈ S, ∃ u ∈ U, z = GlobalTheory.TorCls.dg D p γ * s * u :=
  classes_finite_of_locus GlobalTheory.TorLoc.exists_locus

end GlobalTheory.CentCls.Fin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplittingPreservesLocalSchwartz
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LocSplitOp

theorem exists_locOp : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {G : Type} [Group G] (act : G → W → W) (om : G →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    ∀ (v : Pl F) (p : G), (∀ u, At (evFin F v) u → At (evFin F v) (act p u)) →
    (∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om p) Φ Φ₁) →
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ,
      (∀ Φ ∈ SB (κ → Fv F v), S Φ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) (om p) Φ (S Φ)) ∧
      ∀ u, At (evFin F v) u → ∀ Φ ∈ SB (κ → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
          schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (act p u)) (S Φ) := by
  intro F _ _ W _ _ Bf κ _ dd ψ hψ G _ act om hsp v p hat hex
  choose! S hS using hex
  refine ⟨S, hS, ?_⟩
  intro u hu Φ hΦ
  have hc : Continuous ψ := hψ.1
  have hw := GlobalTheory.SchrSB.schr_mem_SB ψ hc v (GlobalTheory.LatVac.locCo dd v u) Φ hΦ
  have restS : ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) Φ r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) (S Φ) r :=
    fun r hr => ⟨hr.1, by rw [← (hS Φ hΦ).2 r hr]; exact hsp.pres p _ hr.2⟩
  refine GlobalTheory.TensUniq.eq_of_tens_eq v Φ _ _ hΦ fun r hr => ?_
  have hb1 := GlobalTheory.VacBridge.rho_acts_locCo dd ψ v u hu Φ r hr
  have hRw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v)
      (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) r :=
    ⟨hr.1, by rw [← hb1]; exact GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ _ _ hr.2⟩
  rw [← (hS _ hw).2 r hRw, ← hb1, hsp.impl _ _ _ hr.2, (hS Φ hΦ).2 r hr,
    GlobalTheory.VacBridge.rho_acts_locCo dd ψ v _ (hat u hu) (S Φ) r (restS r hr)]

end GlobalTheory.LocSplitOp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuCharConductorExponentsPosProdModulus
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SqTop.CondExpo

theorem levelLe_of_le {K : Type} [Field K] [NumberField K] {χ : Formalism.L2.Host.HChar K} {v : HeightOneSpectrum (𝓞 K)}
    {a b : ℕ} (h : χ.LevelLe v a) (hab : a ≤ b) : χ.LevelLe v b :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hab))))

theorem expAt_succ {K : Type} [Field K] [NumberField K] {χ : Formalism.L2.Host.HChar K} {v : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (h : χ.LevelLe v (n + 1)) (h' : ¬ χ.LevelLe v n) : GlobalTheory.CMVal.ExpAt χ v (n + 1) := fun m =>
  ⟨fun hm => by
    by_contra hlt
    exact h' (levelLe_of_le hm (by omega)), fun hm => levelLe_of_le h hm⟩

end GlobalTheory.SqTop.CondExpo

open GlobalTheory.SqTop.CondExpo in

theorem GlobalTheory.SqTop.CondExpo.expo_modul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T}, L.Is μ₀ →
    ∀ (t : T) (i j : Fin D.R.m) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), (∀ w ∈ locPl G t, GlobalTheory.CMVal.ExpAt (nuH G t i j) w (c w)) →
    (∀ w ∈ locPl G t, 1 ≤ c w) ∧ modul (locPl G t) c = GlobalTheory.SqTop.modT G t := by
  intro D T L sc G μ₀ hL t i j c hc
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  have hμ := L.C.isMu0 j
  have enu : nuH G t i j = L.C.mu0 j * L.xiH t * (G.ch.chiH (D.R.m - i))⁻¹ := by
    rw [nuH, div_eq_mul_inv]
  have echi : G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH t * (nuH G t i j)⁻¹ := by
    rw [enu, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]

  have hW : ∀ v ∈ G.pl.S0, GlobalTheory.CMVal.ExpAt (nuH G t i j) (G.pl.w v) (SqNum.condExp G.pl v) := by
    intro v hv
    have hu := G.pl.under_w hv
    by_cases h0 : v = G.pl.v0
    · subst h0
      rw [SqNum.condExp, if_pos rfl]
      refine expAt_succ (n := 0) ?_ ?_
      · rw [enu]
        exact ((hμ.tame _).mul (hL.xi_tame t _)).mul (G.ch.lev0 _ k1 k2 _ hu).1.inv
      · intro h
        exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
    · have h1 : v ∈ S1 D := (G.pl.mem_S0_of_sum_eq.1 hv).resolve_left h0
      rw [SqNum.condExp, if_neg h0]
      have hl := G.ch.lev1 _ k1 k2 (G.pl.w v) (by rw [hu]; exact h1)
      refine expAt_succ (n := 1) ?_ ?_
      · rw [enu]
        exact ((levelLe_of_le (hμ.tame _) (by omega)).mul (levelLe_of_le (hL.xi_tame t _) (by omega))).mul hl.1.inv
      · intro h
        apply hl.2
        rw [echi]
        exact ((hμ.tame _).mul (hL.xi_tame t _)).mul h.inv

  have hQ : ∀ w ∈ twPl G t, GlobalTheory.CMVal.ExpAt (nuH G t i j) w 1 := by
    intro w hw
    have hw' : w ∈ L.Q t ∧ w ∉ G.pl.W0 := by
      simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hw
      exact ⟨hw.1.resolve_left hw.2, hw.2⟩
    have hS1 : w.under (𝓞 D.host.F) ∉ S1 D := fun h => by
      refine hw'.2 ?_
      rw [G.pl.w_Q t w hw'.1 h]
      exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
    have hS0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
      (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t w hw'.1) hS1
    refine expAt_succ (n := 0) ?_ ?_
    · rw [enu]
      exact ((hμ.tame _).mul (hL.xi_tame t _)).mul
        (Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ k1 k2 w hS0) 1).inv
    · intro h
      exact GlobalTheory.SqTop.nuH_not_unrAt_twPl G hL t i j w hw ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
  have cW : ∀ v ∈ G.pl.S0, c (G.pl.w v) = SqNum.condExp G.pl v := fun v hv =>
    (hc _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv))).unique (hW v hv)
  have cQ : ∀ w ∈ twPl G t, c w = 1 := fun w hw =>
    (hc w (Finset.mem_filter.1 hw).1).unique (hQ w hw)
  refine ⟨fun w hw => ?_, ?_⟩
  · by_cases h : w ∈ G.pl.W0
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      rw [cW v hv, SqNum.condExp]
      split_ifs <;> omega
    · rw [cQ w (Finset.mem_filter.2 ⟨hw, h⟩)]
  · rw [modul, modT, ← Finset.prod_filter_mul_prod_filter_not (locPl G t) (fun w => w ∈ G.pl.W0)]
    have e1 : (locPl G t).filter (fun w => w ∈ G.pl.W0) = G.pl.W0 := by
      ext w
      simp only [Finset.mem_filter, GlobalTheory.FunObj.locPl, Finset.mem_union]
      tauto
    have e2 : (locPl G t).filter (fun w => w ∉ G.pl.W0) = twPl G t := rfl
    rw [e1, e2]
    congr 1
    · rw [Places.W0, Finset.prod_image fun v hv v' hv' h =>
        (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv'))]
      exact Finset.prod_congr rfl fun v hv => by rw [cW v hv]
    · exact Finset.prod_congr rfl fun w hw => by rw [cQ w hw, pow_one]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharHalfSymplecticMovedFinitePointTrivia
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.MovedTrChar
open GlobalTheory.BotClassDict (finQ finStd)
open scoped TensorProduct

def secF (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

def secI (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem decomp {D : D7} (a : AE D) : a = secI D (infPart D a) + secF D (finPart D a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, LinearMap.map_zero, LinearMap.map_zero, add_zero]
  | add a b ha hb =>
    rw [RingHom.map_add, RingHom.map_add, LinearMap.map_add, LinearMap.map_add]
    conv_lhs => rw [ha, hb]
    abel
  | tmul c e =>
    have hc : c = LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F) (fstA D.host.F c) +
        LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) (sndA D.host.F c) := by
      refine Prod.ext ?_ ?_
      · exact (add_zero _).symm
      · exact (zero_add _).symm
    conv_lhs => rw [hc]
    erw [TensorProduct.add_tmul]
    rfl

theorem infPart_secF {D : D7} (y : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (secF D y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | add a b ha hb => rw [LinearMap.map_add, RingHom.map_add, ha, hb, add_zero]
  | tmul c e =>
    show fstA D.host.F (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) c) ⊗ₜ[D.host.F] e = 0
    have : fstA D.host.F (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) c) = 0 := rfl
    rw [this, TensorProduct.zero_tmul]

theorem finPart_secF {D : D7} (y : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (secF D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | add a b ha hb => rw [LinearMap.map_add, RingHom.map_add, ha, hb]
  | tmul c e =>
    show sndA D.host.F (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) c) ⊗ₜ[D.host.F] e = c ⊗ₜ[D.host.F] e
    have : sndA D.host.F (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F) c) = c := rfl
    rw [this]

theorem finQ_eq {D : D7} (a : AE D) : finQ D a = (GlobalTheory.BotFormula.toAfE D).symm (finPart D a) := rfl

theorem recon_ex {D : D7} (q : Formalism.MainNotions.StandardLatticesGL3.AE D) : ∃ a : AE D, infPart D a = 0 ∧ finQ D a = q :=
  ⟨secF D (GlobalTheory.BotFormula.toAfE D q), infPart_secF _, by rw [finQ_eq, finPart_secF, RingEquiv.symm_apply_apply]⟩

theorem recon_uniq {D : D7} (a b : AE D) (h1 : infPart D a = infPart D b) (h2 : finQ D a = finQ D b) : a = b := by
  have h3 : finPart D a = finPart D b := by
    rw [finQ_eq, finQ_eq] at h2
    exact (GlobalTheory.BotFormula.toAfE D).symm.injective h2
  rw [decomp a, decomp b, h1, h3]

end GlobalTheory.MovedTrChar

namespace GlobalTheory.MovedTrChar
open GlobalTheory.BotClassDict (finQ finStd)
open scoped TensorProduct

theorem finPt_parts {D : D7} (S T : HSp D) (r : D.host.E) (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    infPart D (finPt (S := S) (T := T) rfl rfl r z i j) = 0 ∧
      finQ D (finPt (S := S) (T := T) rfl rfl r z i j) = -(Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * Formalism.MainNotions.StandardLatticesGL3.inc D (z i j)) := by
  have e0 : finPt (S := S) (T := T) rfl rfl r z i j = pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-(r⁻¹ * z i j)) := rfl
  rw [e0]
  constructor
  · show fstA D.host.F (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (-(r⁻¹ * z i j)) = 0
    rw [show fstA D.host.F (pairA D.host.F 0 1) = 0 from rfl]
    erw [TensorProduct.zero_tmul]
  · have e1 : finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (-(r⁻¹ * z i j))) = finPart D (incA D (-(r⁻¹ * z i j))) := rfl
    rw [finQ_eq, e1, ← finQ_eq]
    erw [GlobalTheory.BotClassDict.finQ_inclR]
    rw [RingHom.map_neg, RingHom.map_mul]

theorem uComp {D : D7} (S T : HSp D) (hGS : HSpace.gram S = 1) (hGT : HSpace.gram T = 1)
    (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T)
    (hg : IsFinPt S g x) (hh : IsFinPt T h y) (w : WO S T) (hw : ∀ i j, infPart D (w i j) = 0) (i : Fin T.rank) (j : Fin S.rank) :
    infPart D (actO S T g h w i j) = 0 ∧
      finQ D (actO S T g h w i j) =
        (((y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin T.rank) (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * w.map (finQ D) *
          (((x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j := by
  have hy : finStd T hGT h = y := GlobalTheory.BotClassDict.finStd_of_isFinPt T hGT hh
  have hx : finStd S hGS g⁻¹ = x⁻¹ := by rw [map_inv, GlobalTheory.BotClassDict.finStd_of_isFinPt S hGS hg]
  have eh : (Formalism.L2.Theta.mt T h).map (finQ D) = ((y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin T.rank) (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
    ext k l
    rw [Matrix.map_apply, ← hy, GlobalTheory.BotClassDict.finStd_apply]
    rfl
  have eg : (Formalism.L2.Theta.mt S g⁻¹).map (finQ D) =
      (((x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
    ext k l
    rw [Matrix.map_apply]
    have := GlobalTheory.BotClassDict.finStd_apply S hGS g⁻¹ k l
    rw [hx] at this
    exact this.symm
  have key : ∀ {R : Type} [Ring R] (f : AE D →+* R), (actO S T g h w).map f =
      (Formalism.L2.Theta.mt T h).map f * w.map f * (Formalism.L2.Theta.mt S g⁻¹).map f := by
    intro R _ f
    simp only [actO, Matrix.map_mul]
  constructor
  · have hw0 : w.map (infPart D) = 0 := by ext k l; exact hw k l
    have := congrFun (congrFun (key (infPart D)) i) j
    rw [Matrix.map_apply, hw0, Matrix.mul_zero, Matrix.zero_mul] at this
    exact this
  · have := congrFun (congrFun (key (finQ D)) i) j
    rw [Matrix.map_apply, eh, eg] at this
    exact this

end GlobalTheory.MovedTrChar

namespace GlobalTheory.MovedTrChar
open GlobalTheory.BotClassDict (finQ finStd)

theorem symplOH_neg_self {D : D7} (S T : HSp D) (u : WO S T) : symplOH S T (-u) u = 0 := by
  have h0 := Formalism.IndefR.Fin.symplOH_add_left S T u (-u) u
  rw [add_neg_cancel, GlobalTheory.FinTranslate.symplOH_self, zero_add, GlobalTheory.FinTranslate.symplOH_zero_left] at h0
  exact h0.symm

theorem ent_smul {D : D7} {m n : ℕ} (Y : Matrix (Fin m) (Fin m) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (Z : Matrix (Fin m) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D))
    (X : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (c : Formalism.MainNotions.StandardLatticesGL3.AE D) (i : Fin m) (j : Fin n) :
    (Y * (c • Z) * X) i j = c * (Y * Z * X) i j := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

set_option maxHeartbeats 1000000 in

theorem psi_sympl_moved_eq_one : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    ψ (symplOH S T (finPt hS hT r z') (actO S T g h (finPt hS hT r z) - finPt hS hT r z')) = 1 := by
  intro D ψ θ S T a d hS hT cc δ r hset x y g h hg hh z
  subst hS; subst hT
  obtain ⟨A0, hA0⟩ : ∃ A0, A0 = actO S T g h (finPt rfl rfl r z) := ⟨_, rfl⟩
  obtain ⟨N, hN, hC⟩ := GlobalTheory.T.exists_nsmul_symplecticPairing_character_trivial ψ hset.std.1.1 hset.std.1.2.1 S T A0
  obtain ⟨M, hM, hMint⟩ := GlobalTheory.T.exists_pos_nat_mul_inv_idealLattice_mem_integral cc r
  refine ⟨N * M, by positivity, fun z' hz' => ?_⟩
  choose t ht hte using hz'
  obtain ⟨u, hu⟩ : ∃ u : WO S T, u = A0 - finPt rfl rfl r z' := ⟨_, rfl⟩
  choose v hv1 hv2 using fun i j => recon_ex (D := D) ((M : Formalism.MainNotions.StandardLatticesGL3.AE D) * (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * t i j))
  have hNv : ∀ i j, (N • Matrix.of v : WO S T) i j = (N : AE D) * v i j := fun i j => by
    rw [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
  have hmap : (finPt (S := S) (T := T) rfl rfl r z).map (finQ D) = (-(Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹)) • z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) := by
    ext i j; rw [Matrix.map_apply, (finPt_parts S T r z i j).2, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, neg_mul]
  have huv : u = N • (Matrix.of v) := by
    ext i j
    have e1 := (uComp S T hset.gS hset.gT x y g h hg hh _ (fun i j => (finPt_parts S T r z i j).1) i j)
    have e2 := finPt_parts S T r z' i j
    apply recon_uniq
    · rw [hNv, map_mul, hv1, mul_zero, hu, Matrix.sub_apply, map_sub, hA0, e1.1, e2.1, sub_zero]
    · rw [hNv, map_mul, hv2]
      rw [hu, Matrix.sub_apply, map_sub]
      rw [hA0, e1.2, e2.2]
      rw [hmap]
      rw [ent_smul]
      rw [map_natCast]
      have h3 := hte i j
      rw [Matrix.sub_apply, Matrix.map_apply] at h3
      push_cast at h3 ⊢
      linear_combination (Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹) * h3
  have hself : symplOH S T (-u) u = 0 := symplOH_neg_self S T u
  have hsum : finPt rfl rfl r z' + u = A0 := by rw [hu]; abel
  have geq : actO S T g h (finPt rfl rfl r z) - finPt rfl rfl r z' = u := by subst hA0; exact hu.symm
  have h1 := Formalism.IndefR.Fin.symplOH_add_left S T (finPt rfl rfl r z') u u
  rw [hsum, GlobalTheory.FinTranslate.symplOH_self, add_zero] at h1
  rw [geq, ← h1, huv]
  exact hC _ (fun i j => hv1 i j) (fun i j => by rw [Matrix.of_apply, hv2]; exact hMint _ (ht i j))

end GlobalTheory.MovedTrChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramified
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.PsiStdCond

theorem psi_std_conductor : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) ∧ ∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1 := by
  classical
  intro F _ _ ψ hψ
  refine ⟨?_, ?_⟩
  · have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ differentIdeal ℤ (𝓞 F)}.Finite :=
      Ideal.finite_factors differentIdeal_ne_bot
    refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
    by_contra h
    exact hv (GlobalTheory.StdCharUnrF.psiUnr_of_not_le F ψ hψ v fun h' => h (Ideal.dvd_iff_le.2 h'))
  · intro v
    by_contra hcon
    push_neg at hcon
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
    set c : ℤ := FractionalIdeal.count F v (GlobalTheory.StdDual.codiff F) with hc
    set x : Fv F v := algebraMap F (Fv F v) (π ^ (c - 1)) with hx
    have hmem := (GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ)
      (GlobalTheory.AdelicU.singleFin v x)).2 (fun β hβ => by
        have e : β * GlobalTheory.AdelicU.singleFin v x = GlobalTheory.AdelicU.singleFin v (x * β v) := by
          apply GlobalTheory.AdelicU.af_ext
          intro u
          by_cases hu : u = v
          · subst hu
            rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
            change β u * x = x * β u
            ring
          · rw [map_mul, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
        rw [e]
        exact hcon _)
    have h1 := (GlobalTheory.Idele.mem_adelicIdeal_iff GlobalTheory.StdDual.codiff_ne_zero).1 hmem v
    have h2 : Valued.v (GlobalTheory.AdelicU.singleFin v x v) = Valued.v x := by
      change Valued.v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ v (GlobalTheory.AdelicU.singleFin v x)) = _
      rw [GlobalTheory.AdelicU.evalV_singleFin_self]
    have h3 : Valued.v x = WithZero.exp (-(c - 1)) := by
      rw [hx, GlobalTheory.Idele.valued_algebraMap, map_zpow₀, hπ, ← WithZero.exp_zsmul]
      congr 1
      simp
    rw [← hc] at h1
    rw [h2, h3, WithZero.exp_le_exp] at h1
    omega

end GlobalTheory.PsiStdCond
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepVariablesCountGridLocalFlipGridLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

theorem varCount_le_of_rank_le {k : Type*} [Field k] (G : Grid k) (hs : 1 ≤ G.s) (N : ℕ)
    (hN : ∀ j < G.m, G.rank (G.m, j) ≤ N) : varCount G ≤ G.m * N ^ 2 := by
  unfold varCount
  have hterm : ∀ j : Fin (G.m - 1),
      Nat.card (StepVar (Fin (topRank G (j + 1))) (G.m - 2 - j) (Fin (topRank G j))) ≤ N ^ 2 := by
    intro j
    have hj := j.2
    refine (Finite.card_subtype_le _).trans ?_
    rw [Nat.card_prod, Nat.card_sum, Nat.card_sum]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    have h1 := topRank_add hs (G := G) (j + 1)
    have h2 := topRank_add hs (G := G) j
    have h3 := hN (j + 1) (by omega)
    have h4 := hN j (by omega)
    rw [sq]
    exact Nat.mul_le_mul (by omega) (by omega)
  calc _ ≤ ∑ _j : Fin (G.m - 1), N ^ 2 := Finset.sum_le_sum fun j _ => hterm j
    _ = (G.m - 1) * N ^ 2 := by simp
    _ ≤ G.m * N ^ 2 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)

theorem varCount_locGrid_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E),
    varCount (locGrid G t w) ≤ D.R.m * bigN D ^ 2 := by
  intro D T L sc G t w
  refine varCount_le_of_rank_le (locGrid G t w) (show 1 ≤ D.R.r + 6 by omega) _ fun j hj => ?_
  change j < D.R.m at hj
  have h1 := Nat.mul_le_mul_right D.R.t hj.le
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + D.R.m * (D.R.r + 6) ≤ D.R.k + D.R.m * (D.R.t + (D.R.r + 6) + 1)
  nlinarith

end GlobalTheory.UnfoldLoss
end

