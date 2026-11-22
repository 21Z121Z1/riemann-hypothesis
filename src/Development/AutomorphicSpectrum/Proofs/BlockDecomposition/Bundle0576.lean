import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0006
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SummableUnitBounds.SBoundOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.StSmooth
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0545
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicLeviDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLFactorRankThreeUnramified
section
open Ad3 Ad3.S

noncomputable section

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)

namespace GlobalTheory.CompanionTheory.EulerThree.HalfWt

open GlobalTheory.CompanionTheory.EulerThree

theorem unr_mul {v : Pl} {μ κ : (Qv v)ˣ →* ℂˣ} (hμ : IsUnramifiedChar μ)
    (hκ : IsUnramifiedChar κ) : IsUnramifiedChar (μ * κ) := by
  intro u hu
  have h1 : μ u = 1 := hμ hu
  have h2 : κ u = 1 := hκ hu
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply, h1, h2, one_mul]

theorem unr_inv {v : Pl} {μ : (Qv v)ˣ →* ℂˣ} (hμ : IsUnramifiedChar μ) :
    IsUnramifiedChar μ⁻¹ := by
  intro u hu
  have h1 : μ u = 1 := hμ hu
  rw [MonoidHom.mem_ker, MonoidHom.inv_apply, h1, inv_one]

def parA (D : Dat) (c : HeckeCharacter ℚ) (v : Pl) : ℂ :=
  (((D.ν v * localChar c v) (unifUnit (Qv v)) : ℂˣ) : ℂ)

def parB (c : HeckeCharacter ℚ) (v : Pl) : ℂ :=
  ((localChar c v (unifUnit (Qv v)) : ℂˣ) : ℂ)

def parC (D : Dat) (c : HeckeCharacter ℚ) (v : Pl) : ℂ :=
  ((((D.ν v)⁻¹ * localChar c v) (unifUnit (Qv v)) : ℂˣ) : ℂ)

theorem norm_localChar (c : HeckeCharacter ℚ) (v : Pl) (x : (Qv v)ˣ) :
    ‖((localChar c v x : ℂˣ) : ℂ)‖ = 1 :=
  Circle.norm_coe _

theorem norm_parA (D : Dat) (c : HeckeCharacter ℚ) (v : Pl) : ‖parA D c v‖ = 1 := by
  rw [parA, MonoidHom.mul_apply, Units.val_mul, norm_mul, (D.unit v).2, norm_localChar, one_mul]

theorem norm_parB (c : HeckeCharacter ℚ) (v : Pl) : ‖parB c v‖ = 1 :=
  norm_localChar c v _

theorem norm_parC (D : Dat) (c : HeckeCharacter ℚ) (v : Pl) : ‖parC D c v‖ = 1 := by
  rw [parC, MonoidHom.mul_apply, Units.val_mul, norm_mul, MonoidHom.inv_apply,
    Units.val_inv_eq_inv_val, norm_inv, (D.unit v).2, inv_one, norm_localChar, one_mul]

theorem two_le_pOf (hE : faceMap_comp_succAbove_castSucc) (v : Pl) : 2 ≤ pOf v := by
  obtain ⟨e, he⟩ := hE.1
  rw [← he v]
  exact (e v).2.two_le

theorem pOf_injective (hE : faceMap_comp_succAbove_castSucc) : Function.Injective pOf := by
  obtain ⟨e, he⟩ := hE.1
  intro v w h
  apply e.injective
  apply Subtype.ext
  rw [he, he, h]

theorem local_l_factor_rank_three_unramified (hE : faceMap_comp_succAbove_castSucc) {D : Dat} {c : HeckeCharacter ℚ} {δ : Bool} {S : Finset Pl}
    (hA : admitted D c δ S) {v : Pl} (hv : v ∉ S) (s : ℂ) :
    lf3 (D.ν v) (localChar c v) s = cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) s := by
  have hν : IsUnramifiedChar (D.ν v) := D.unr v (fun h => hv (hA.bad h))
  have hc : IsUnramifiedChar (localChar c v) := hA.unr v hv
  rw [lf3, cubicFactor, hE.2 v _ (unr_mul hν hc), hE.2 v _ hc, hE.2 v _ (unr_mul (unr_inv hν) hc)]
  rfl

theorem multipliable_sub (hE : faceMap_comp_succAbove_castSucc) (D : Dat) (c : HeckeCharacter ℚ) (A : Set Pl) {s : ℂ}
    (hs : 1 < s.re) :
    Multipliable fun v : A => cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) s :=
  multipliable_cubicFactor (p := fun v : A => pOf v) (a := fun v : A => parA D c v)
    (b := fun v : A => parB c v) (c := fun v : A => parC D c v)
    ((pOf_injective hE).comp Subtype.val_injective) (fun v => two_le_pOf hE v)
    (fun v => norm_parA D c v) (fun v => norm_parB c v) (fun v => norm_parC D c v) hs

theorem eul_eq (hE : faceMap_comp_succAbove_castSucc) {D : Dat} {c : HeckeCharacter ℚ} {δ : Bool} {S : Finset Pl}
    (hA : admitted D c δ S) {T : Finset Pl} (hST : S ⊆ T) (s : ℂ) :
    eul D c T s = ∏' v : {v : Pl // v ∉ T},
      cubicFactor (pOf v.1) (parA D c v.1) (parB c v.1) (parC D c v.1) s := by
  unfold eul
  exact tprod_congr fun v => local_l_factor_rank_three_unramified hE hA (fun h => v.2 (hST h)) s

theorem norm_lt_one {p : ℕ} (hp : 2 ≤ p) {a s : ℂ} (ha : ‖a‖ = 1) (hs : 0 < s.re) :
    ‖a * (p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_param_mul hp ha]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < p)) (by linarith)

theorem one_sub_ne_zero {p : ℕ} (hp : 2 ≤ p) {a s : ℂ} (ha : ‖a‖ = 1) (hs : 0 < s.re) :
    1 - a * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : a * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.1 h).symm
  have := norm_lt_one hp ha hs
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

theorem differentiableAt_factor {p : ℕ} (hp : 2 ≤ p) {a s : ℂ} (ha : ‖a‖ = 1) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => (1 - a * (p : ℂ) ^ (-z))⁻¹) s := by
  have hp0 : (p : ℂ) ≠ 0 := by
    have : p ≠ 0 := by omega
    exact_mod_cast this
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hp0)
  exact ((differentiableAt_const _).sub ((differentiableAt_const _).mul hpow)).inv
    (one_sub_ne_zero hp ha hs)

theorem norm_factor_le {p : ℕ} (hp : 2 ≤ p) {a s : ℂ} (ha : ‖a‖ = 1) (hs : 1 / 4 ≤ s.re) :
    ‖(1 - a * (p : ℂ) ^ (-s))⁻¹‖ ≤ (1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have ht1 : (p : ℝ) ^ (-(1 / 4 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  have hx : ‖a * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [norm_param_mul hp ha]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  have hlow : 1 - (p : ℝ) ^ (-(1 / 4 : ℝ)) ≤ ‖1 - a * (p : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (a * (p : ℂ) ^ (-s))
    rw [norm_one] at this
    linarith
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hlow

theorem differentiableOn_cubicFactor {p : ℕ} (hp : 2 ≤ p) {a b c : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) : DifferentiableOn ℂ (cubicFactor p a b c) (HP 0) := by
  intro s hs
  have hs : 0 < s.re := hs
  exact (((differentiableAt_factor hp ha hs).mul (differentiableAt_factor hp hb hs)).mul
    (differentiableAt_factor hp hc hs)).differentiableWithinAt

theorem norm_cubicFactor_le {p : ℕ} (hp : 2 ≤ p) {a b c s : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hs : 1 / 4 ≤ s.re) :
    ‖cubicFactor p a b c s‖ ≤ ((1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹) ^ 3 := by
  have hA := norm_factor_le hp ha hs
  have hB := norm_factor_le hp hb hs
  have hC := norm_factor_le hp hc hs
  have hK : 0 ≤ (1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := (norm_nonneg _).trans hA
  rw [cubicFactor, norm_mul, norm_mul, pow_three, ← mul_assoc]
  exact mul_le_mul (mul_le_mul hA hB (norm_nonneg _) hK) hC (norm_nonneg _) (mul_nonneg hK hK)

open Classical in

theorem adjoint_lift_twisted_euler_product : faceMap_comp_succAbove_castSucc → E3 := by
  intro hE D c δ S hA
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hd := differentiableOn_tprod_cubicFactor (p := fun v : {v : Pl // v ∉ S} => pOf v.1)
      (a := fun v => parA D c v.1) (b := fun v => parB c v.1) (c := fun v => parC D c v.1)
      ((pOf_injective hE).comp Subtype.val_injective) (fun v => two_le_pOf hE v.1)
      (fun v => norm_parA D c v.1) (fun v => norm_parB c v.1) (fun v => norm_parC D c v.1)
    have he : eul D c S = fun s => ∏' v : {v : Pl // v ∉ S},
        cubicFactor (pOf v.1) (parA D c v.1) (parB c v.1) (parC D c v.1) s :=
      funext (eul_eq hE hA (subset_refl S))
    rw [he]
    exact hd s hs
  · intro T hST s hs
    set G : Pl → ℂ := fun v => cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) s with hG
    have h1 : ∏ v ∈ T \ S, lf3 (D.ν v) (localChar c v) s = ∏ v ∈ T \ S, G v :=
      Finset.prod_congr rfl fun v hv => local_l_factor_rank_three_unramified hE hA (Finset.mem_sdiff.1 hv).2 s
    rw [h1, eul_eq hE hA (subset_refl S), eul_eq hE hA hST]
    change (∏' v : ({v | v ∉ S} : Set Pl), G v) = (∏ v ∈ T \ S, G v) * ∏' v : ({v | v ∉ T} : Set Pl), G v
    rw [tprod_subtype, tprod_subtype, ← Finset.tprod_subtype' (T \ S) G, tprod_subtype]
    have m1 : Multipliable ((↑(T \ S) : Set Pl).mulIndicator G) :=
      (multipliable_subtype_iff_mulIndicator).1 (multipliable_sub hE D c _ hs)
    have m2 : Multipliable (({v | v ∉ T} : Set Pl).mulIndicator G) :=
      (multipliable_subtype_iff_mulIndicator).1 (multipliable_sub hE D c _ hs)
    rw [← m1.tprod_mul m2]
    refine tprod_congr fun v => ?_
    by_cases hS : v ∈ S
    · have hT : v ∈ T := hST hS
      simp [Set.mulIndicator_apply, hS, hT]
    · by_cases hT : v ∈ T
      · simp [Set.mulIndicator_apply, hS, hT]
      · simp [Set.mulIndicator_apply, hS, hT]
  · intro v hv
    have he : lf3 (D.ν v) (localChar c v) =
        cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) := funext (local_l_factor_rank_three_unramified hE hA hv)
    rw [he]
    refine ⟨differentiableOn_cubicFactor (two_le_pOf hE v) (norm_parA D c v) (norm_parB c v)
      (norm_parC D c v), _, fun s hs => norm_cubicFactor_le (two_le_pOf hE v) (norm_parA D c v)
      (norm_parB c v) (norm_parC D c v) hs⟩

end GlobalTheory.CompanionTheory.EulerThree.HalfWt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedDiagonalAction
section
open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LocalUnramified

theorem exists_unit_eq_uniformizer_zpow_ord_mul (F : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a : Fˣ) :
    ∃ u : 𝒪[F]ˣ, (a : F) = (GLnLocal.uniformizer F : F) ^ ord (a : F) * ((u : 𝒪[F]) : F) := by
  have hϖ := irreducible_uniformizer F
  refine ⟨(unitsEquivIntProd hϖ a).2, ?_⟩
  have hx : a = unitsOfIntProd hϖ (unitsEquivIntProd hϖ a) := by
    rw [← unitsEquivIntProd_symm_apply, MulEquiv.symm_apply_apply]
  have h := coe_unitsOfIntProd hϖ (unitsEquivIntProd hϖ a).1 (unitsEquivIntProd hϖ a).2
  rw [Prod.mk.eta, ← hx, unitsEquivIntProd_fst hϖ a, toAdd_ofAdd] at h
  exact h

theorem sDg : Ad3.LU.SDg := by
  intro F _ _ _ _ a b c
  obtain ⟨u, hu⟩ := exists_unit_eq_uniformizer_zpow_ord_mul F a
  obtain ⟨v, hv⟩ := exists_unit_eq_uniformizer_zpow_ord_mul F b
  obtain ⟨w, hw⟩ := exists_unit_eq_uniformizer_zpow_ord_mul F c
  refine ⟨integralGLHom F 3 (Ad3.dg u v w), ⟨_, rfl⟩, ?_⟩
  apply Units.ext
  ext i j
  rw [Units.val_mul, coe_torusPow]
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.dg, integralGLHom, Matrix.diagonal_mul, ← hu, ← hv, ← hw]

end GlobalTheory.CompanionTheory.LocalUnramified
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnramifiedShellFormula
section
open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open MeasureTheory
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LU

theorem sShell : Ad3.LU.SShell := by
  intro F _ _ _ _ _ _ g hg
  have hmeas : Measurable (fun a : Fˣ => g (ord (a : F))) := by
    have hord : Measurable (fun a : Fˣ => ord (a : F)) :=
      measurable_to_countable' fun k => measurableSet_ordShell (K := F) k
    exact (Measurable.of_discrete (f := g)).comp hord
  have hfin : ∑' k, ‖g k‖ₑ ≠ ⊤ := by
    simp_rw [← ofReal_norm]
    exact hg.tsum_ofReal_ne_top
  have hI : Integrable (fun a : Fˣ => g (ord (a : F))) (multHaar F) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hle := lintegral_multHaar_le_tsum (K := F) (fun u => ‖g (ord (u : F))‖ₑ)
      (fun k => ‖g k‖ₑ) (fun _ => le_rfl)
    exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hfin)
  refine ⟨hI, ?_⟩
  have hs := hasSum_setIntegral_ordShell hI
  have hk : ∀ k : ℤ, ∫ u in ordShell F k, g (ord (u : F)) ∂multHaar F = g k := by
    intro k
    have hc : Set.EqOn (fun u : Fˣ => g (ord (u : F))) (fun _ => g k) (ordShell F k) :=
      fun u hu => by simp only [mem_ordShell.mp hu]
    rw [setIntegral_congr_fun (measurableSet_ordShell k) hc, setIntegral_const, measureReal_def,
      multHaar_ordShell]
    simp
  simp only [hk] at hs
  exact hs.tsum_eq.symm

end GlobalTheory.CompanionTheory.LU
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogNormContinuousOffDivisor
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.ArchInt

theorem continuousOn_logNorm_offSupp {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {q : X ⟶ Sp k} {σ : k →+* ℂ} {L : LB X} (ψ : GlobalTheory.Weight q σ L) (hψ : ψ.IsCInf)
    {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) :
    ContinuousOn (GlobalTheory.Cartier.logNorm ψ r) (offSupp q σ (divOfRatSec ψ.isLB hr)) := by
  intro y hy
  obtain ⟨i, hi⟩ := GlobalTheory.CxPts.exists_mem_ptsIn (p := q) (σ := σ) ψ.isLB.cover y
  have hu : GlobalTheory.Cartier.UnitAt (GlobalTheory.Cartier.under y) ((r i : X.functionField)) :=
    GlobalTheory.Cartier.IsRatSec.unitAt ψ.isLB hr hy hi
  obtain ⟨V, hyV, hV⟩ := GlobalTheory.Cartier.UnitAt.exists_nhds hu
  have hgV : genericPoint X ∈ V := GlobalTheory.Cartier.gen_mem hyV
  obtain ⟨a, ha⟩ := GlobalTheory.Cartier.exists_unit_fnOf_eq hV
  have hyV' : y ∈ GlobalTheory.CxPts.ptsIn q σ V := GlobalTheory.CxPts.mem_ptsIn.2 hyV
  have hNo : IsOpen (GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr)) :=
    ((GlobalTheory.CxPts.isOpen_ptsIn V).inter (GlobalTheory.CxPts.isOpen_ptsIn _)).inter
      (GlobalTheory.Cartier.isOpen_offSupp _)
  have hyN : y ∈ GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr) := ⟨⟨hyV', hi⟩, hy⟩
  have heq : ∀ z ∈ GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr),
      Real.log ‖GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V)) z‖ - ψ.φ i z / 2 =
        GlobalTheory.Cartier.logNorm ψ r z := by
    rintro z ⟨⟨hzV, hzi⟩, hz⟩
    rw [GlobalTheory.Cartier.logNorm_eq ψ hr hz hzi, ← ha hgV, GlobalTheory.Cartier.ratVal_fnOf hzV]
  have hne : GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V)) y ≠ 0 := by
    rw [← GlobalTheory.Cartier.ratVal_fnOf hyV' hgV, ha hgV]
    exact GlobalTheory.Cartier.ratVal_ne_zero hu
  have hev : ContinuousAt (GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V))) y :=
    (GlobalTheory.CxPts.continuousOn_ev _).continuousAt ((GlobalTheory.CxPts.isOpen_ptsIn V).mem_nhds hyV')
  have hφ : ContinuousAt (ψ.φ i) y := (hψ i y hi).continuousAt
  have hg : ContinuousAt (fun z => Real.log ‖GlobalTheory.CxPts.ev q σ V
      (a : X.presheaf.obj (Opposite.op V)) z‖ - ψ.φ i z / 2) y :=
    (hev.norm.log (norm_ne_zero_iff.2 hne)).sub (hφ.div_const 2)
  exact (hg.congr (Filter.eventuallyEq_of_mem (hNo.mem_nhds hyN) heq)).continuousWithinAt

end GlobalTheory.CompanionTheory.MixZ.ArchInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPointEqPointMapRing
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.ConjPointDict

theorem mapPoint_eq_pointMapRing : ∀ [DecidableEq ℂ] (X : WeierstrassCurve ℂ) (σ : ℂ →+* ℂ)
    (P : X.toAffine.Point), GlobalTheory.ConjPoint.mapPoint X σ P = GroundTheory.Global.pointMapRing σ X P := by
  intro _ X σ P
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e⟩ := GroundTheory.Global.pointMapRing_some σ X h
    rw [e]
    rfl

end GlobalTheory.CompanionTheory.ConjPointDict
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableRealWhittakerInverse
section
noncomputable section

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.GodementWeight

open Ad3.LR

theorem measurable_det_of : Measurable (fun h : M22 => (Matrix.of h).det) := by
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  fun_prop

theorem measurable_inv_entry (i j : Fin 2) :
    Measurable (fun h : M22 => ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  have hd : Measurable (fun h : M22 => ((Matrix.of h).det)⁻¹) := measurable_det_of.inv
  have key : (fun h : M22 => ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) i j) =
      fun h : M22 => ((Matrix.of h).det)⁻¹ * (Matrix.adjugate (Matrix.of h)) i j := by
    funext h
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [key]
  refine hd.mul ?_
  simp only [Matrix.adjugate_fin_two, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem measurable_det_inv :
    Measurable (fun h : M22 => ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det) := by
  simp only [Matrix.det_fin_two]
  exact ((measurable_inv_entry 0 0).mul (measurable_inv_entry 1 1)).sub
    ((measurable_inv_entry 0 1).mul (measurable_inv_entry 1 0))

theorem measurable_sg {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) :
    Measurable (fun a => sg (f a)) := by
  unfold sg
  exact Measurable.ite (hf measurableSet_Iio) measurable_const measurable_const

theorem measurable_Wm_inv (k : ℕ) :
    Measurable (fun h : M22 => Wm k ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hD := measurable_det_inv
  have e : ∀ i j : Fin 2, Measurable
      (fun h : M22 => ((((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) i j : ℝ) : ℂ)) :=
    fun i j => Complex.measurable_ofReal.comp (measurable_inv_entry i j)
  unfold Wm
  refine Measurable.ite (measurableSet_lt measurable_const hD) ?_ measurable_const
  have hden := (e 1 1).sub ((e 1 0).mul_const Complex.I)
  have hnum := (e 0 1).sub ((e 0 0).mul_const Complex.I)
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · exact Complex.measurable_ofReal.comp (hD.pow_const _)
  · exact hden.pow_const _
  · exact Complex.measurable_exp.comp ((hnum.div hden).const_mul _)

theorem measurable_weight (k : ℕ) :
    Measurable (fun h : M22 => Wm k (Matrix.of h)⁻¹ * sg (Matrix.of h).det *
      ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)) := by
  refine ((measurable_Wm_inv k).mul (measurable_sg measurable_det_of)).mul ?_
  exact Complex.measurable_ofReal.comp (measurable_det_of.abs.pow_const _)

end GlobalTheory.CompanionTheory.GodementWeight

theorem GlobalTheory.CompanionTheory.GodementWeight.main : ∀ k : ℕ, Measurable (fun h : Ad3.LR.M22 => Ad3.LR.Wm k (Matrix.of h)⁻¹ * Ad3.LR.sg (Matrix.of h).det * ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)) :=
  GlobalTheory.CompanionTheory.GodementWeight.measurable_weight
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableUnipotentFourierIntegral
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.GodementInt

lemma continuous_mul_blk :
    Continuous (fun p : Ad3.LR.M22 × (Fin 2 → ℝ) =>
      (Matrix.of.symm (Matrix.of p.1 * Ad3.LR.blk p.2) : Ad3.LR.M23)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]
  fin_cases j <;> simp [Ad3.LR.blk] <;> fun_prop

theorem measurable_integral_mul_blk (Ψ : Ad3.LR.M23 → ℂ) (β : ℝ) (hΨ : Continuous Ψ) :
    Measurable (fun h : Ad3.LR.M22 =>
      ∫ x : Fin 2 → ℝ, Ψ (Matrix.of.symm (Matrix.of h * Ad3.LR.blk x)) * Ad3.psiR (-(β * x 1))) := by
  have hψ : Continuous (fun p : Ad3.LR.M22 × (Fin 2 → ℝ) => Ad3.psiR (-(β * p.2 1))) := by
    unfold Ad3.psiR
    fun_prop
  have hf : Continuous (fun p : Ad3.LR.M22 × (Fin 2 → ℝ) =>
      Ψ (Matrix.of.symm (Matrix.of p.1 * Ad3.LR.blk p.2)) * Ad3.psiR (-(β * p.2 1))) :=
    (hΨ.comp continuous_mul_blk).mul hψ
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

end GlobalTheory.CompanionTheory.GodementInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurePreservingMixedSpaceReal
section
open MeasureTheory NumberField
open scoped Classical

namespace GlobalTheory.CompanionTheory.RealAdele

theorem isEmpty_isComplex : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
  ⟨fun a => by
    have h : a.1 = Ad3.GP.wR := Subsingleton.elim _ _
    have h2 := a.2
    rw [h] at h2
    exact InfinitePlace.not_isReal_iff_isComplex.mpr h2 Ad3.GP.wR_isReal⟩

end GlobalTheory.CompanionTheory.RealAdele
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLeviMinimalOfCommutesProjectionsStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_levi_minimal_of_commutes_projections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) = (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ leviMin σ J X Y ∧ γ ∈ minParOne σ J X := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.mem_leviMin_of_comm | exact GlobalTheory.CompanionTheory.ParCocompact.mem_leviMin_of_comm | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.mem_leviMin_of_comm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemParabolicOfFlagPreservingStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_parabolic_of_flag_preserving : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r) (δ : GF V),
    (∀ l : Fin r, l ≤ j → ∃ b : Fin r → D.host.E, δ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) →
    δ ∈ (frameFlag (isIsoFrame_firstCols hW j)).parRat D.sp.cm := by
  first | exact @GlobalTheory.CompanionTheory.RegInt.mem_parRat_frameFlag_firstCols | exact GlobalTheory.CompanionTheory.RegInt.mem_parRat_frameFlag_firstCols | (intros; apply GlobalTheory.CompanionTheory.RegInt.mem_parRat_frameFlag_firstCols <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicLeviDecompositionStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_levi_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ p ∈ minParOne σ J X, ∃ u ∈ unipMin σ J X, ∃ m ∈ leviMin σ J X Y, m ∈ minParOne σ J X ∧ p = u * m := by
  first | exact @GlobalTheory.CompanionTheory.LeviDecomp.levi_decomp | exact GlobalTheory.CompanionTheory.LeviDecomp.levi_decomp | (intros; apply GlobalTheory.CompanionTheory.LeviDecomp.levi_decomp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthInductionStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_depth_induction : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (y : Fin (n + 1) → k) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (uM (n + 1) y) v) v' (((ψ (y (Fin.last n)) : Circle) : ℂ) * A) ∧ EvVal ν ψ T B v (T' (uM (n + 1) y) v') (((ψ (-y (Fin.last n)) : Circle) : ℂ) * A) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.EvVal_translate | exact GlobalTheory.CompanionTheory.MirPair.EvVal_translate | (intros; apply GlobalTheory.CompanionTheory.MirPair.EvVal_translate <;> assumption)
end

