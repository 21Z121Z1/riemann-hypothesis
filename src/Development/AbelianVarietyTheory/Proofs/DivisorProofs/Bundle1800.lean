import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1698
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1774
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1754
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1768
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1767
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1731
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNontrivialHeckeChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenKLeFockStab
section
open NumberField MeasureTheory Finset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup)
open GlobalTheory.FunObj.SqNum GlobalTheory.SqTop
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.NormAdelic

noncomputable section
namespace GlobalTheory.NormAdelic
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q}

def fockStab (X : GlobalTheory.NormDict.Data P) : Subgroup (GA D X.A) where
  carrier := {g | ∀ T, X.om (g, 1) (X.fock T) = X.fock T}
  mul_mem' := by
    intro a b ha hb T
    have e : ((a * b, (1 : GA D X.B)) : GA D X.A × GA D X.B) = (a, 1) * (b, 1) := by simp
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [e, map_mul, Module.End.mul_apply, hb T, ha T]
  one_mem' := by
    intro T
    rw [show ((1 : GA D X.A), (1 : GA D X.B)) = 1 from rfl, map_one, Module.End.one_apply]
  inv_mem' := by
    intro a ha T
    simp only [Set.mem_setOf_eq] at ha ⊢
    have e : ((a⁻¹, (1 : GA D X.B)) : GA D X.A × GA D X.B) * (a, 1) = 1 := by simp
    calc X.om (a⁻¹, 1) (X.fock T) = X.om (a⁻¹, 1) (X.om (a, 1) (X.fock T)) := by rw [ha T]
      _ = X.fock T := by rw [← Module.End.mul_apply, ← map_mul, e, map_one, Module.End.one_apply]

theorem minorPol_ne_zero {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : GlobalTheory.NormSum.minorPol D T ≠ 0 := by
  unfold GlobalTheory.NormSum.minorPol
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  set f : Fin a × Fin a → Formalism.MainNotions.GL3Theta.Idx D a d := fun p => (τ, (T τ j).1 p.1, p.2) with hf
  have hfi : Function.Injective f := by
    intro p q e
    simp only [hf, Prod.mk.injEq] at e
    exact Prod.ext ((T τ j).2.injective e.2.1) e.2.2
  have e : (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
      (MvPolynomial.rename f).toRingHom.mapMatrix (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ) := by
    ext i i'
    simp [Matrix.mvPolynomialX, hf]
  rw [e, ← RingHom.map_det]
  intro h0
  exact Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ
    ((MvPolynomial.rename_injective f hfi) (h0.trans (map_zero _).symm))

end GlobalTheory.NormAdelic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedModelThetaFunctionBounded
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.TowerFD

theorem thetaFunOF_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
      ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ ψ f → ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  intro F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ hψ f hf
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  have hKc : IsCompact (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :
      Set (WOF F E nS nT)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  have hmem : ratWF (Matrix.of fun i j => c (w i j)) + w ∈
      (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) : Set (WOF F E nS nT)) :=
    fun i _ j _ => hc (w i j)
  have h := hC _ hmem
  have hq := hf.quasi (Matrix.of fun i j => c (w i j)) w
  have h2 : ‖f w‖ = ‖f (ratWF (Matrix.of fun i j => c (w i j)) + w)‖ := by
    rw [hq, norm_mul, hψ.2.1, one_mul]
  exact h2.trans_le h

end GlobalTheory.TowerFD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginDatumValueHalfIntegerPowPlaceAA
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Flat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

open Classical in

theorem flatTensor_moved_box (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (hν : IsUnitVol ν)
    (ϖ : kˣ) (a a' : ℤ) (hψ : ∀ y : k, valuation k y ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) → ψ y = 1)
    (g : G.VertexGroup) (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j) :
    flatTensor hs ψ ν (moved G false g (Set.indicator
      {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 =
    ((oppositePath G.m).map fun b => apow (gdet (g b.src))⁻¹ ((G.rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-(G.rank b.src : ℂ) / 2)).prod *
      ∏ j, ∏ v, ((nabs k (ϖ ^ boxExp G a a' j v) : ℝ) : ℂ) := by
  set P := ((oppositePath G.m).map fun b => apow (gdet (g b.src))⁻¹ ((G.rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-(G.rank b.src : ℂ) / 2)).prod
  have key : flatIntegrand hs ψ (moved G false g (Set.indicator
      {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 =
      (box G ϖ a a').indicator fun _ => P := by
    funext e
    rw [flatIntegrand, moved_false, GlobalTheory.T.indicator_moveArgs_origin_eq_box_indicator G hs ϖ a a' g hg e]
    by_cases he : e ∈ box G ϖ a a'
    · have h1 := GlobalTheory.T.unfoldingCharacterPhase_origin_valuation_le_box G ϖ a a' e he
      rw [Set.indicator_of_mem he, Set.indicator_of_mem he, hψ _ (by rwa [Valuation.map_neg])]
      simp only [Pi.one_apply, mul_one, Circle.coe_one, P]
    · rw [Set.indicator_of_notMem he, Set.indicator_of_notMem he]
      simp
  rw [flatTensor, key, integral_indicator_const _ (measurableSet_box G ϖ a a'), Measure.real, vol_box G ν hν ϖ a a',
    Complex.real_smul, mul_comm]
  push_cast
  rfl

end Flat
end GlobalTheory.OriginBox

namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Expo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]

theorem flatTensor_moved_box_apow (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (hν : IsUnitVol ν)
    (ϖ : kˣ) (a a' : ℤ) (hψ : ∀ y : k, valuation k y ≤ valuation k ((ϖ ^ (a + a') : kˣ) : k) → ψ y = 1)
    (g : G.VertexGroup) (hg : ∀ j, g (G.m, j) = colDiag G ϖ a a' j) (hg' : ∀ i j, i ≠ G.m → g (i, j) = 1) :
    flatTensor hs ψ ν (moved G false g (Set.indicator
      {z : G.Args | ∀ b ∈ oppositePath G.m, ∀ i j, (((ϖ ^ a)⁻¹ : kˣ) : k) * z b i j ∈ 𝒪[k]} 1)) 0 0 =
    apow ϖ (-(expo G a a' : ℂ) / 2) := by
  classical
  have hn : ∀ x : kˣ, ((nabs k x : ℝ) : ℂ) = apow x 1 := fun x => by simp [apow]
  rw [flatTensor_moved_box G hs ψ ν hν ϖ a a' hψ g hg]
  simp_rw [gdet_eq ϖ a a' g hg hg', ← _root_.zpow_neg, apow_zpow, ← apow_add, hn, apow_zpow, prod_apow_finset,
    prod_apow_list, ← apow_add]
  congr 1
  have hl : ∀ l : List Edge, (l.map fun b => ((-vtxDet G a a' b.src : ℤ) : ℂ) * ((G.rank b.tgt : ℂ) / 2) +
      ((-vtxDet G a a' b.tgt : ℤ) : ℂ) * (-(G.rank b.src : ℂ) / 2)).sum =
      -(((l.map fun b => vtxDet G a a' b.src * G.rank b.tgt - vtxDet G a a' b.tgt * G.rank b.src).sum : ℤ) : ℂ) / 2 := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring
  rw [hl, expo]
  push_cast
  simp only [mul_one]
  ring

end Expo
end GlobalTheory.OriginBox
namespace GlobalTheory.OriginBox
open GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

section Generic
variable {k : Type} [Field k]

theorem colDiag_eq_one (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (a a' : ℤ) {j : ℕ} (hj : G.m - 1 ≤ j) :
    colDiag G ϖ a a' j = 1 := by
  refine Units.ext ?_
  rw [colDiag, diagGL_val, Units.val_one, ← diagonal_one]
  congr 1
  funext x
  have h := topRank_add hs j
  have hx := x.2
  rw [vtxExp, if_neg (by omega), zpow_zero, Units.val_one]

end Generic

variable {D : D7}

theorem aaElt_eq (w : Pl D.host.E) (j : ℕ) :
    aaElt w j = colDiag (bareGrid w) (unifAt w) (FractionalIdeal.count D.host.E w D.host.AA)
      (FractionalIdeal.count D.host.E w D.host.AAbar) j := by
  refine Units.ext ?_
  rw [aaElt, colDiag, diagGL_val, diagGL_val]
  congr 1
  funext x
  have h := topRank_add (G := bareGrid w) one_le_sLen j
  have hx := x.2
  simp only [vtxExp]
  split_ifs with h1
  · simp only [genAt, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_neg, ← _root_.zpow_add, Units.val_zpow_eq_zpow_val]
    congr 1
    have : x.val - topRank (bareGrid w) j < D.R.m - 1 - j := by
      change topRank (bareGrid w) j + D.R.m = (bareGrid w).rank ((bareGrid w).m, j) + j + 1 at h
      change (x : ℕ) < (bareGrid w).rank ((bareGrid w).m, j) at hx
      omega
    change _ = _ * (((D.R.m - 1 - j : ℕ) : ℤ) - _) - _
    push_cast [Nat.sub_sub]
    rw [show D.R.m - (1 + j + (x.val - topRank (bareGrid w) j)) = D.R.m - (1 + j) - (x.val - topRank (bareGrid w) j) by omega,
      Nat.cast_sub (by omega)]
    ring
  · simp

theorem aaElt_elt_col (w : Pl D.host.E) (j : ℕ) :
    (Reps.through (G := bareGrid w) one_le_sLen (fun _ => KO _ _) (aaElt w)).elt
      (fun i => DoubleCoset.mk _ _ (aaElt w (i + 1))) ((bareGrid w).m, j) =
    colDiag (bareGrid w) (unifAt w) (FractionalIdeal.count D.host.E w D.host.AA)
      (FractionalIdeal.count D.host.E w D.host.AAbar) j := by
  unfold Reps.elt
  rw [onColumn_apply]
  cases j with
  | zero => exact aaElt_eq w 0
  | succ i =>
    simp only [Reps.through]
    split_ifs with h
    · exact aaElt_eq w (i + 1)
    · exact (colDiag_eq_one _ one_le_sLen _ _ _ (by omega)).symm

theorem aaElt_elt_off (w : Pl D.host.E) (i j : ℕ) (hi : i ≠ (bareGrid w).m) :
    (Reps.through (G := bareGrid w) one_le_sLen (fun _ => KO _ _) (aaElt w)).elt
      (fun i => DoubleCoset.mk _ _ (aaElt w (i + 1))) (i, j) = 1 := by
  simp [Reps.elt, onColumn, hi]

theorem rank_le_bigN (w : Pl D.host.E) (i j : ℕ) (hi : i ≤ (bareGrid w).m) (hj : j ≤ (bareGrid w).m) :
    (bareGrid w).rank (i, j) ≤ bigN D := by
  have h1 := Nat.mul_le_mul_right D.R.t hj
  have h2 := Nat.mul_le_mul_right (sLen D) hi
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + i * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
  change i ≤ D.R.m at hi
  change j ≤ D.R.m at hj
  nlinarith

theorem aaTerm_datum_origin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (w : Pl D.host.E), (∀ a : Kw w, valuation (Kw w) a ≤ valuation (Kw w) ((genAt w D.host.AA * genAt w D.host.AAbar : (Kw w)ˣ) : Kw w) → psiAt W w a = 1) → ∃ n : ℤ, (aaTerm W w).datum 0 0 = (resCard (Kw w) : ℂ) ^ ((n : ℂ) / 2) ∧ |n| ≤ 8 * ((D.R.m : ℤ) ^ 3 * (bigN D : ℤ) ^ 2 * (|FractionalIdeal.count D.host.E w D.host.AA| + |FractionalIdeal.count D.host.E w D.host.AAbar|)) := by
  intro D T L sc G W w hψ
  have hψ' : ∀ y : Kw w, valuation (Kw w) y ≤ valuation (Kw w) (((unifAt w) ^ (FractionalIdeal.count D.host.E w D.host.AA +
      FractionalIdeal.count D.host.E w D.host.AAbar) : (Kw w)ˣ) : Kw w) → psiAt W w y = 1 := fun y hy =>
    hψ y (by rwa [genAt, genAt, ← _root_.zpow_add])
  have key := flatTensor_moved_box_apow (bareGrid w) one_le_sLen (psiAt W w) (unitVol w) (isUnitVol_unitVol w) (unifAt w)
    _ _ hψ' _ (aaElt_elt_col w) (aaElt_elt_off w)
  refine ⟨expo (bareGrid w) (FractionalIdeal.count D.host.E w D.host.AA) (FractionalIdeal.count D.host.E w D.host.AAbar),
    ?_, GlobalTheory.T.abs_originBoxValueExponent_le (bareGrid w) one_le_sLen _ _ (bigN D) (rank_le_bigN w)⟩
  change flatTensor _ _ _ _ 0 0 = _
  rw [aaVac, genAt] at *
  rw [key, IsUnif.apow_eq (isUnif_unifAt w)]
  congr 1
  ring

end GlobalTheory.OriginBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftUnfold

theorem exists_fin_mul_real {D : D7} (V : HSp D) (u : GA D V) : ∃ k ∈ GfC V, ∃ a ∈ GinfC V, u = k * a ∧ fin V k = fin V u := by
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (finHom V u)
  have hk : k ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 u.2).2⟩
  let k' : GA D V := ⟨k, hk⟩
  have e : finHom V k' = finHom V u := k2
  refine ⟨k', k1, k'⁻¹ * u, ?_, (mul_inv_cancel_left _ _).symm, Subtype.ext e⟩
  show finHom V (k'⁻¹ * u) = 1
  rw [map_mul, map_inv, e, inv_mul_cancel]

theorem integrand_right {H G' Gf W X : Type} [Group H] [Group G'] [Group Gf] [AddCommGroup W] [Module ℂ W]
    (om : H × G' →* Module.End ℂ (X → ℂ)) (ρ : H →* Module.End ℂ W) (p : H →* Gf) (L : W →ₗ[ℂ] (X → ℂ)) (f : Gf → W)
    (u k a : H) (hu : u = k * a) (c : ℂˣ) (hk : ρ k⁻¹ = 1) (ha : p a = 1) (hf : ∀ z, f (z * p k) = (c : ℂ) • f z)
    (hLk : ∀ w, om (k, 1) (L w) = (c : ℂ)⁻¹ • L w) (hLa : ∀ w, om (a, 1) (L w) = L (ρ a w)) (x : H) (g : G') :
    om (x * u, g) (L (ρ (x * u)⁻¹ (f (p (x * u))))) = om (x, g) (L (ρ x⁻¹ (f (p x)))) := by
  subst hu
  have e1 : (x * (k * a), g) = (x, g) * (k, (1 : G')) * (a, (1 : G')) := by simp [mul_assoc]
  have e2 : ρ a * ρ (x * (k * a))⁻¹ = ρ x⁻¹ := by
    rw [← map_mul, show a * (x * (k * a))⁻¹ = k⁻¹ * x⁻¹ by group, map_mul, hk, one_mul]
  rw [e1, map_mul om, map_mul om, Module.End.mul_apply, Module.End.mul_apply, hLa, ← Module.End.mul_apply (ρ a), e2, hLk,
    map_mul p, map_mul p, ha, mul_one, hf, map_smul (ρ x⁻¹), map_smul L, smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]

theorem form_right {H Γ W : Type} [Group H] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) {J : Subgroup H} {χ : J →* ℂˣ} {f : H → W} (hf : f ∈ Bridge.AdForms ι ρ J χ) (k : J) (z : H) :
    f (z * k) = (χ k : ℂ) • f z := by
  have := hf 1 z k
  rwa [map_one, map_one, one_mul] at this

theorem integral_theta {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (hL : ∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β (Lev.flag1L L))
    {f : Bridge.Gf S → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ)
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ (levEnv S β L).J, ∀ w,
      om (k, 1) (Λ w) = (((levEnv S β L).χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : IsMeasDef S (Formalism.L2.DIV.lev D.sp.cm S.gram β L) ν 𝓕)
    (J' : Subgroup (Bridge.Gf S)) (Cl : Type) [Fintype Cl] (h : Cl → GA D S) (hle : J' ≤ (levEnv S β L).J)
    (hN : J'.relIndex (levEnv S β L).J ≠ 0) (hy : Bridge.IsReps (Bridge.ratF S) J' (fun k => fin S (h k)))
    (hh : ∀ k, h k ∈ GfC S) (g : GA D T) :
    ∫ x in 𝓕, thetaKO om x g (Λ (c.ext f x)) ∂ν = ∑ k, ((J'.relIndex (levEnv S β L).J : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (Bridge.ratF S) J' (fin S (h k))) : ℕ) : ℂ)⁻¹ * thetaKO om (h k) g (Λ (f (fin S (h k)))) := by
  rw [GlobalTheory.ClsInt.integral_eq_classSum_of_le D S β L ν 𝓕 hp hs hν hL J' Cl h hle hN hy hh
    (fun x => thetaKO om x g (Λ (c.ext f x))) ?_ ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [ext_fin c hc f (hh k)]
  · intro γ hγ x
    have e : (γ * x, g) = ((γ, 1) : GA D S × GA D T) * (x, g) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hΛ _))
  · intro u hu x
    refine (exists_fin_mul_real S u).elim fun k hk0 => hk0.2.elim fun a ha0 => ?_
    have hk := hk0.1
    have ha := ha0.1
    have e := ha0.2.2
    have hk' : fin S k ∈ (levEnv S β L).J := by rw [e]; exact hu
    have h1 : c.ρ k⁻¹ = 1 := hc.1 _ (inv_mem hk)
    have h2 : (finHom S).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    have h3 := form_right (Bridge.ratF S) c.coef.ρ hf ⟨fin S k, hk'⟩
    have h4 := integrand_right om c.ρ (finHom S).rangeRestrict Λ f u k a ha0.2.1 ((levEnv S β L).χ ⟨fin S k, hk'⟩)
      h1 h2 h3 (hΛk k hk hk') (hΛa a ha) x g
    exact congrFun h4 0

set_option maxHeartbeats 1000000 in

theorem thF_eq_classSum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m) (t : T0) (K' : Type) [Field K'] (σ' : K' →+* ℂ) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)) (bad : ℕ) (J' : Subgroup (Bridge.Gf (Vc D i))) (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K'), VStd D i → RepsR R i t h bad J' Lh gam vol → ∀ (y : (R.HV i t).H) (x : Cl → VsV D i K'), Place R i t h c0' y x → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t y (fun ρ => u ρ) g = ∑ k, σ' (vol * ((gam k : K'))⁻¹) * thetaKO (R.ωP i t) (h k) g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (c0' (x k)))) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t K' _ σ' c0' Cl _ h bad J' Lh gam vol hV hrep y x hpl u g
  refine (hR.thP.thF i t).elim fun thP hPF => ?_
  have hle := hrep.2.2.1
  have hN := hrep.2.2.2.1
  have hvol := hrep.2.2.2.2.1
  have hy := hrep.2.2.2.2.2.1
  have hk := hrep.2.2.2.2.2.2
  have hx : (R.HV i t).e y ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hR.models.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ levJ R i t, ∀ P, R.ωP i t (k, 1) (R.ptP i t P) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hR.models.inf
      (hR.thP.ωP i t) _ _ _ _ _ (hR.thP.pt_theta i t) k hk 1 (one_mem _) _
      (GlobalTheory.T.realisation_nonarchimedean_compat D G Pl0 T0 A Ks R F hR i t k hV hk hk')
  have key := integral_theta (hR.thP.ωP i t) (D.sp.V_sig _) (hR.models.vpos i) (R.cV i) (hR.models.cV i) (R.βV i)
    (R.datVt i t) (fun _ => Iff.rfl) hx
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun w => hR.thP.pt_theta i t _)
    (fun a ha w => (hR.thP.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hR.models.νV i t) J' Cl h hle hN hy (fun k => (hk k).1.1) g
  have h1 := congrFun (hPF.2 y u) g
  have h2 := hPF.1.eq ((R.extV i t).rangeRestrict y) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans (Finset.sum_congr rfl fun k _ => ?_))))
  · rfl
  have h3 : σ' (vol * ((gam k : K'))⁻¹) = ((J'.relIndex (levJ R i t) : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin (Vc D i) (h k))) : ℕ) : ℂ)⁻¹ := by
    rw [map_mul σ', hvol, map_inv₀ σ', map_inv₀ σ', map_natCast σ', map_natCast σ', (hk k).2.2]
  rw [h3, ← hpl k]
  rfl

end GlobalTheory.LiftUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupDatumOfConnectedDualConnected
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem isConn_of_retract {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Nontrivial O] {G H : PDivGroup p O}
    (f : H ⟶ G) (r : G ⟶ H) (h : f ≫ r = 𝟙 H) (hG : GlobalTheory.PDivLat.IsConn G) : GlobalTheory.PDivLat.IsConn H := by
  intro n
  have hs : Function.Surjective (f.app n) := fun a => ⟨r.app n a, by
    have := congrArg (fun g => Hom.app g n) h
    exact DFunLike.congr_fun this a⟩
  haveI : Nontrivial (H.A n) :=
    (Bialgebra.counitAlgHom O (H.A n) : H.A n →+* O).domain_nontrivial
  haveI := hG n
  exact IsLocalRing.of_surjective' (f.app n : G.A n →+* H.A n) hs

theorem hasDatum_of_conn_dual_conn : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → GlobalTheory.PDivLat.IsConn G.dual → HasDatum hε G) → ∀ G : PDivGroup p O, HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε hyp G
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨G₁, G₂, hs, hc₁, hk₂⟩ := GlobalTheory.ConnConstSplit.exists_isSum_conn_const p C v O hv G
  obtain ⟨H₁, H₂, hs', hcH, hkH⟩ := GlobalTheory.ConnConstSplit.exists_isSum_conn_const p C v O hv G₁.dual
  obtain ⟨i₁, -, q₁, -, e₁, -⟩ := id hs'
  have hD : GlobalTheory.PDivLat.IsConn H₁.dual :=
    isConn_of_retract (dualHom _ _ q₁ ≫ G₁.bidual.inv) (G₁.bidual.hom ≫ dualHom _ _ i₁)
      (by rw [Category.assoc, Iso.inv_hom_id_assoc, ← dualHom_comp, e₁, dualHom_id]) hc₁
  have dD := GlobalTheory.SumDatum.hasDatum_of_isSum p C v O hv ε hε _ _ _ hs' (hyp H₁ hcH hD)
    (GlobalTheory.PDivLat.hasDatum_of_isConst p C v O hv ε hε H₂ hkH)
  have d₁ := GlobalTheory.PDivLat.hasDatum_of_iso p C v O hv ε hε _ _ ⟨G₁.bidual.symm⟩
    (GlobalTheory.DualDatum.hasDatum_dual p C v O hv ε hε _ dD)
  exact GlobalTheory.SumDatum.hasDatum_of_isSum p C v O hv ε hε G G₁ G₂ hs d₁ (GlobalTheory.PDivLat.hasDatum_of_isConst p C v O hv ε hε G₂ hk₂)

end GlobalTheory.PDivLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfNeronOggShafarevich
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem potentialGoodReduction_of_neronOggShafarevich :
    GlobalTheory.Published.NeronOggShafarevichSt → GlobalTheory.Published.PotentialGoodReductionSt := by
  intro h R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA l _ hl
  exact ⟨GlobalTheory.T.finite_image_inertia_of_potentialGoodReduction_alt h R K Ω V hV A hA l hl, GlobalTheory.T.hasPotentialGoodReduction_of_finite_image_inertia_alt h R K Ω V hV A hA l hl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorMemSchwartzAdelic
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.PureIndO

theorem pure_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = GlobalTheory.FinComm.indO v) →
    pure f φ ∈ schA F κ := by
  intro F _ _ κ _ f φ hSB hstd
  exact Submodule.subset_span ⟨f, fun y => ∏ᶠ v, φ v fun i => evalV F v (y i),
    GlobalTheory.AdelicCoordSB.finprod_mem_SB F κ φ hSB hstd, rfl⟩

end GlobalTheory.PureIndO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticCharacterExtendsToIdeleClassStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_character_extends_to_idele_class : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ η : (AdeleRing (𝓞 F) F)ˣ →* Circle, Continuous η → (∀ b, η (b * b) = 1) →
    ∃ ψ : (AdeleRing (𝓞 F) F ⊗[F] E)ˣ →* Circle, Continuous ψ ∧ (∀ b, ψ (ideleMap F E b) = 1 ∨ ψ (ideleMap F E b) = -1) ∧
      ∀ b : (AdeleRing (𝓞 F) F)ˣ, (b : AdeleRing (𝓞 F) F).2 = 1 → ψ (ideleMap F E b) = η b := by
  first | exact @GlobalTheory.ArchSignChar.exists_arch_sign_char | exact GlobalTheory.ArchSignChar.exists_arch_sign_char | (intros; apply GlobalTheory.ArchSignChar.exists_arch_sign_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftIntertwinesLevelLiftsLowestKTypeStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_intertwines_levelLifts_lowestKType : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → ∀ y y' : (R.HV i t).H, (∀ h, R.extV i t y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ)) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)), R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  first | exact @GlobalTheory.ThetaShift.thF_shift_of_models | exact GlobalTheory.ThetaShift.thF_shift_of_models | (intros; apply GlobalTheory.ThetaShift.thF_shift_of_models <;> assumption)
end

