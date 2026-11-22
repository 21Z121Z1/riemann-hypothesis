import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0096
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Formalism.LocalToGlobal.AlgebraicTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitFrameSelfDualLatticeCompletion
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitFrame

open GlobalTheory.IdemModTwo (fj inF inF_finPart inF_tmul)
open GlobalTheory.SplitHeckeLabel (exists_local_lattice smul_mem_latHat mul_mem_intA intA)

theorem exists_gl_of_lattice (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {K : Type} [Field K]
    [Algebra O K] [IsFractionRing O K] {n : ℕ} (Λ : Submodule O (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ β : GL (Fin n) K, ∀ w, w ∈ Λ ↔ ∀ i, IsInt O (((β⁻¹).1 *ᵥ w) i) := by
  classical
  have : Submodule.IsLattice K Λ := ⟨hfg, hsp⟩
  have hr : Module.finrank O Λ = n := by
    rw [Submodule.IsLattice.finrank_of_pi K Λ, Fintype.card_fin]
  let b : Module.Basis (Fin n) O Λ := Module.finBasisOfFinrankEq O Λ hr
  let c : Module.Basis (Fin n) K (Fin n → K) := b.extendOfIsLattice K
  let s := Pi.basisFun K (Fin n)
  refine ⟨⟨s.toMatrix c, c.toMatrix s, Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩, fun w => ?_⟩
  have hw : c.toMatrix s *ᵥ w = c.repr w := by
    exact Module.Basis.toMatrix_mulVec_repr s c w
  change _ ↔ ∀ i, IsInt O ((c.toMatrix s *ᵥ w) i)
  rw [hw]
  have hc : ∀ i, c i = (b i : Fin n → K) := fun i => Module.Basis.extendOfIsLattice_apply K b i
  constructor
  · intro h i
    refine ⟨b.repr ⟨w, h⟩ i, ?_⟩
    have h1 : w = ∑ j, algebraMap O K (b.repr ⟨w, h⟩ j) • c j := by
      have := congrArg Subtype.val (b.sum_repr ⟨w, h⟩)
      rw [Submodule.coe_sum] at this
      refine this.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [hc, algebraMap_smul]
      rfl
    conv_rhs => rw [h1]
    rw [c.repr_sum_self]
  · intro h
    choose o ho using h
    rw [← c.sum_repr w]
    refine Λ.sum_mem fun j _ => ?_
    rw [← ho, algebraMap_smul, hc]
    exact Λ.smul_mem _ (b j).2

variable {D : D7}

theorem finPart_inF (z : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (inF D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [AddMonoidHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [AddMonoidHom.map_add, RingHom.map_add, hx, hy]

theorem exists_factor {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (h : Chart e v π) : ∃ φ : Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v, ∀ z, φ (finPart D z) = π z := by
  have h1 : π (fj D 1) = 1 := (h.2.2.1 _).trans (map_one (evalV D.host.F v))
  refine ⟨(finPart D).liftOfRightInverse (inF D) finPart_inF ⟨π, fun z hz => ?_⟩, fun z =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ z⟩
  rw [RingHom.mem_ker] at hz ⊢
  have h2 := inF_finPart z
  rw [hz, AddMonoidHom.map_zero] at h2
  have h3 := congrArg π h2
  rwa [RingHom.map_zero, RingHom.map_mul, h1, one_mul, eq_comm] at h3

theorem finPart_mul_eq {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (h : Chart e v π) {φ : Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v} (hφ : ∀ z, φ (finPart D z) = π z)
    (y : AE D) (z : Af D.host.F ⊗[D.host.F] D.host.E) (hy : π y = φ z) : finPart D (e * y) = finPart D e * z := by
  have h1 : π y = π (inF D z) := by
    rw [← hφ (inF D z), finPart_inF]
    exact hy
  have h2 := (h.2.1 (y - inF D z)).1 (by rw [RingHom.map_sub, h1, sub_self])
  rw [mul_sub, sub_eq_zero] at h2
  rw [h2, RingHom.map_mul, finPart_inF]

theorem exists_frame : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ V : HSp D, ∃ β : GL (Fin V.rank) (Fv D.host.F v), Frame V e π β := by
  intro D e v π he h V
  obtain ⟨φ, hφ⟩ := exists_factor h
  have hei : finPart D e ∈ intA D.host.F D.host.E :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])
  have hπe : π e = 1 := by
    have := (h.2.1 (e - 1)).2 (by rw [mul_sub, he.1, mul_one, sub_self])
    rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := Set.ext fun y => by
    change _ ↔ ∑ i, y i • V.frame i ∈ V.L0
    rw [← V.frame.equivFun_symm_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change V.frame.equivFun.symm (V.frame.equivFun x) ∈ V.L0
      rwa [LinearEquiv.symm_apply_apply]
    · exact fun h => ⟨_, h, V.frame.equivFun.apply_symm_apply y⟩
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    change Submodule.span _ (V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V)) = ⊤
    rw [← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  obtain ⟨Λ, hfg, hΛ, hmem⟩ := exists_local_lattice (F := D.host.F) L (V.standardTuple_isLattice.fg.map _) hsp v φ
    (fun a => (hφ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 a))).trans (h.2.2.1 _))
    (fun x hx => by
      rw [← finPart_inF x, hφ, ← isInt_Ov, ← h.2.2.2, RingHom.map_mul, finPart_inF]
      exact mul_mem_intA hei hx)
  obtain ⟨β, hβ⟩ := exists_gl_of_lattice (Ov D v) Λ hfg hΛ
  refine ⟨β, fun y => ?_⟩
  rw [← hβ, hmem, LamHat, ← hL]
  constructor
  · intro hy
    refine ⟨_, hy, funext fun i => ?_⟩
    rw [Function.comp_apply, hφ, RingHom.map_mul, hπe, one_mul]
  · rintro ⟨z, hz, hy⟩
    have : (fun i => finPart D (e * y i)) = finPart D e • z := funext fun i =>
      finPart_mul_eq h hφ (y i) (z i) (congrFun hy i)
    rw [this]
    exact smul_mem_latHat L hei hz

end GlobalTheory.SplitFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentShapeOfIntegralClassOneLetter
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.OneLetter

open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)

theorem localLogarithm_eq_single_variable_oneLetter (D : D7) (p : ℕ) [Fact p.Prime] (h1 : nP D p = 1) {β : Type} (v : OrbitPlaces.Pl D × β) :
    OrbitPlaces.logPl D p v = at1 v (lgF ℂ_[p] p) := by
  rw [Formalism.L2.Th1.D.SingleLetterLog.at_variable_artin_hasse_eq_one_log]
  ext m
  have hb : ∀ e : ℕ, OrbitPlaces.backPl D p v.1 e = v.1 := fun e => by
    simp [OrbitPlaces.backPl, h1, posPl_zero]
  show (∑ e ∈ Finset.range (JetTdeg m + 1), _) = ∑ e ∈ Finset.range (m.degree + 1), _
  have hd : JetTdeg m = m.degree := rfl
  rw [hd]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hb]

theorem owOK_one {K : Type} [NormedField K] (σ : K →+* K) :
    OwOK 2 σ (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) :=
  ⟨fun _ => ⟨by simp, by simp⟩, fun _ => ⟨Formalism.L2.Th1.D.SingleLetterLog.iter_one σ 2, Formalism.L2.Th1.D.SingleLetterLog.iter_one σ 2⟩⟩

theorem trDual_one {K : Type} [NormedField K] (σ : K →+* K) :
    TrDual 2 σ (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) := by
  refine ⟨by simp, fun r r' => ?_⟩
  have hr : r = r' := Fin.ext (by have := r.isLt; have := r'.isLt; omega)
  rw [Formalism.L2.Th1.D.SingleLetterLog.univ_two, Finset.sum_pair (by decide)]
  have h1 : (1 : ZMod 2).val = 1 := rfl
  simp [h1, hr]

theorem beMean_fin_unit {K : Type} [Field K] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K) (ζ : K) :
    Formalism.L2.Th1.D.beMean (d := 2) l σ be0 (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) ζ =
      Formalism.L2.Th1.D.beMean (d := 2) l σ be0 (fun _ : Unit => (1 : K)) (fun _ => 1) ζ := by
  have h : Formalism.L2.Th1.D.beTil (d := 2) l σ be0 (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) =
      Formalism.L2.Th1.D.beTil (d := 2) l σ be0 (fun _ : Unit => (1 : K)) (fun _ => 1) := by
    unfold Formalism.L2.Th1.D.beTil
    rw [Finset.sum_const, Finset.sum_const]
    simp
  unfold Formalism.L2.Th1.D.beMean
  rw [h]

end GlobalTheory.KerStd.OneLetter

namespace GlobalTheory.KerStd

open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open OneLetter

theorem expShape_of_integralClass : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → nP D p = 1 → ∀ (N N' : ℕ) (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), ‖ep‖ = 1 → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) → OrbitPlaces.ThetaExpansionRealPlaces D p Th := by
  intro D p _ g2 g3 s2 ε σ F hC h1 N N' ep Th hep hH
  obtain ⟨h5, hg2, hg3, hε, hth, hσ, hF, hN⟩ := hC
  have hl : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨f1, f2, hph⟩ := Formalism.L2.Th1.D.FAux.ffs p Formalism.L2.Th1.D.first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.FAux.exists_root2 p
  set B : MvPowerSeries (ZMod 2) (MaximalUnramifiedExtension p) :=
    Formalism.L2.Th1.D.beMean (d := 2) p σ (cob F (phFF p g2 g3 s2 ε)) (fun _ : Unit => (1 : MaximalUnramifiedExtension p)) (fun _ => 1) ζ with hBdef
  set Bc : MvPowerSeries (ZMod 2) ℂ_[p] := MvPowerSeries.map (MaximalUnramifiedExtension p).subtype B with hBc
  have hstd : BeStd p 2 Bc := ⟨σ, F, cob F (phFF p g2 g3 s2 ε), fun _ => 1, fun _ => 1, ζ,
    ⟨hσ, hF, f1, f2, owOK_one σ, trDual_one σ, hζ⟩, by rw [beOf, beMean_fin_unit]⟩
  have hB14 := GlobalTheory.T.standard_series_b_conditions_large_prime p 2 Bc h5 le_rfl even_two hstd

  have hO := Formalism.L2.Th1.D.oneLetterHalf (MaximalUnramifiedExtension p) p σ hσ F hF _ f1 f2 ζ hζ _ hph
  have h2 := (Formalism.InvariantFactorPaths.G7.Top.mapSimeq (MaximalUnramifiedExtension p) ℂ_[p] Unit (MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.FAux.norm_coe p)).1 _ _ hO
  have hsL0 : MvPowerSeries.HasSubst (fun _ : ZMod 2 => (lgF (MaximalUnramifiedExtension p) p : MvPowerSeries Unit (MaximalUnramifiedExtension p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => Formalism.L2.Th1.D.Pair.cc_lgF hl)
  have hsL : MvPowerSeries.HasSubst (fun _ : ZMod 2 => (lgF ℂ_[p] p : MvPowerSeries Unit ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => Formalism.L2.Th1.D.Pair.cc_lgF hl)
  have e2 : MvPowerSeries.map (MaximalUnramifiedExtension p).subtype (MvPowerSeries.C ((2 : MaximalUnramifiedExtension p)⁻¹) *
      MvPowerSeries.subst (fun _ : ZMod 2 => (lgF (MaximalUnramifiedExtension p) p : MvPowerSeries Unit (MaximalUnramifiedExtension p))) B) =
      MvPowerSeries.C ((2 : ℂ_[p])⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => (lgF ℂ_[p] p : MvPowerSeries Unit ℂ_[p])) Bc := by
    rw [map_mul, MvPowerSeries.map_C, MvPowerSeries.map_subst hsL0, map_inv₀, map_ofNat]
    have e3 : MvPowerSeries.map (MaximalUnramifiedExtension p).subtype (lgF (MaximalUnramifiedExtension p) p : MvPowerSeries Unit (MaximalUnramifiedExtension p)) = lgF ℂ_[p] p :=
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF (MaximalUnramifiedExtension p).subtype p
    simp only [e3, hBc]
  rw [e2] at h2
  obtain ⟨-, hsymm, -, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] (OrbitPlaces.Pl D × Fin N × Fin N')
  have hsub := (Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] Unit).2.2.2.2 (OrbitPlaces.Pl D × Fin N × Fin N')
  have h3 : ∀ x : OrbitPlaces.Pl D × Fin N × Fin N', Simeq (at1 x (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)))
      (MvPowerSeries.C ((2 : ℂ_[p])⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => at1 x (lgF ℂ_[p] p)) Bc) := by
    intro x
    have hsx : MvPowerSeries.HasSubst
        (fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    have h4 := hsub _ _ (fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (fun _ => by simp) (fun _ => Formalism.InvariantFactorPaths.G7.TwoS.integral_X x) h2
    rw [MvPowerSeries.subst_mul hsx, MvPowerSeries.subst_C,
      MvPowerSeries.subst_comp_subst_apply hsL hsx] at h4
    exact h4
  have h5s := Formalism.L2.Th1.D.B4.simeq_sum Finset.univ _ _ fun x _ => h3 x
  obtain ⟨h50, h5I⟩ := hsymm _ _ h5s
  set f : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    ∑ x : OrbitPlaces.Pl D × Fin N × Fin N', at1 x (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)) with hf
  set g : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    ∑ x : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C ((2 : ℂ_[p])⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => at1 x (lgF ℂ_[p] p)) Bc with hg
  have hm0 : PowerSeries.constantCoeff (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.L2.Th1.D.FAux.cc_phFF hl, map_zero]
  have hf0 : MvPowerSeries.constantCoeff f = 0 := by
    rw [hf, map_sum]
    exact Finset.sum_eq_zero fun x _ => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero x hm0
  have hg0 : MvPowerSeries.constantCoeff g = 0 := by
    have h := h50
    rw [map_sub, hf0, sub_zero] at h
    exact h
  have hng0 : MvPowerSeries.constantCoeff (-g) = 0 := by rw [map_neg, hg0, neg_zero]
  have hnf0 : MvPowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf0, neg_zero]

  have hsA : MvPowerSeries.HasSubst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i (Formalism.L2.Th1.D.Pair.cc_lgF hl)
  have hsE : MvPowerSeries.HasSubst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
      (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by simp
  have hlogfun : (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => MvPowerSeries.C ep * OrbitPlaces.logPl D p v) =
      fun v => MvPowerSeries.C ep * at1 v (lgF ℂ_[p] p) := funext fun v => by rw [localLogarithm_eq_single_variable_oneLetter D p h1]
  have hlog2 : (OrbitPlaces.logPl D p (β := Fin N × Fin N')) = fun v => at1 v (lgF ℂ_[p] p) :=
    funext fun v => localLogarithm_eq_single_variable_oneLetter D p h1 v
  have hS : MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => MvPowerSeries.C ep * OrbitPlaces.logPl D p v) Th =
      MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p))
        (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
          (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th) := by
    rw [hlogfun, MvPowerSeries.subst_comp_subst_apply hsE hsA]
    congr 1
    funext v
    rw [MvPowerSeries.subst_mul hsA, MvPowerSeries.subst_C, MvPowerSeries.subst_X hsA]

  have hE : ∀ z : OrbitPlaces.Pl D, ∀ a : Fin N, ∀ b : Fin N',
      MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])
        else MvPowerSeries.C (1 : ℂ_[p]) * MvPowerSeries.X (z, a, b)) Bc =
      MvPowerSeries.subst (fun _ : ZMod 2 =>
        (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Bc := by
    intro z a b
    simp only [map_one, one_mul, ite_self]
  have hsX : ∀ x : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.HasSubst
      (fun _ : ZMod 2 => (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    fun x => MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by simp
  set E' : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    ((-1 : ℂ_[p]) / 2) • ∑ x : OrbitPlaces.Pl D × Fin N × Fin N',
      MvPowerSeries.subst (fun _ : ZMod 2 =>
        (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Bc with hE'
  have hsubE : MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p)) E' = -g := by
    rw [hE', ← MvPowerSeries.coe_substAlgHom hsA, map_smul, MvPowerSeries.coe_substAlgHom hsA,
      Formalism.L2.Th1.D.Pair.subst_sum hsA, hg, MvPowerSeries.smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPowerSeries.subst_comp_subst_apply (hsX x) hsA]
    simp only [MvPowerSeries.subst_X hsA]
    rw [← neg_mul, ← map_neg]
    congr 2
    ring
  have hE0 : MvPowerSeries.constantCoeff E' = 0 := by
    rw [← HostLog.constantCoeff_subst (fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i (Formalism.L2.Th1.D.Pair.cc_lgF hl)) E',
      hsubE, hng0]
  have hsum : (∑ z : OrbitPlaces.Pl D, ((-1 : ℂ_[p]) / 2) • ∑ a : Fin N, ∑ b : Fin N',
      MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])
        else MvPowerSeries.C (1 : ℂ_[p]) * MvPowerSeries.X (z, a, b)) Bc) = E' := by
    simp only [hE, hE', Fintype.sum_prod_type, Finset.smul_sum]
  have e5 : mvExp (g - f) * mvExp (-g) = mvExp (-f) := by
    rw [← Formalism.InvariantFactorPaths.G7.mvExp_add h50 hng0]
    congr 1
    ring
  have e6 : mvExp (-f) * mvExp f = 1 := by
    rw [← Formalism.InvariantFactorPaths.G7.mvExp_add hnf0 hf0, neg_add_cancel, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.mvExp_zero']
  refine ⟨ep, hep, fun _ => Bc, fun _ => hB14, fun _ => 1, fun _ => norm_one, fun _ => -1, fun _ => Or.inr rfl,
    mvExp (g - f) * (mvExp f * MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p))
        (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
          (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th)),
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' h5I hH, ?_⟩
  show _ = _ * MvPowerSeries.subst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) (product_zeroth_first_parts.expS ℂ_[p]
    (∑ z : OrbitPlaces.Pl D, ((-1 : ℂ_[p]) / 2) • ∑ a : Fin N, ∑ b : Fin N',
      MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])
        else MvPowerSeries.C (1 : ℂ_[p]) * MvPowerSeries.X (z, a, b)) Bc))
  rw [hS, hsum, hlog2]
  show _ = _ * MvPowerSeries.subst _ (mvExp E')
  rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hsA hE0, hsubE]
  calc _ = (mvExp (-f) * mvExp f) * MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p))
        (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
          (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th) := by
        rw [e6, one_mul]
    _ = _ := by rw [← e5]; ring

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfDiagMulFinPartI
section
noncomputable section

namespace GlobalTheory.UnUnitCmp.Val

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L]

def intFin (L : Type) [Field L] [NumberField L] : Subring (FiniteAdeleRing (𝓞 L) L) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers L}
  one_mem' := fun _ => one_mem _
  zero_mem' := fun _ => zero_mem _
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  mul_mem' := fun ha hb v => mul_mem (ha v) (hb v)
  neg_mem' := fun ha v => neg_mem (ha v)

theorem finite_quot (N : ℕ) (hN : 0 < N) : Finite (intFin L ⧸ Ideal.span {(N : intFin L)}) := by
  let ι : 𝓞 L →+* intFin L :=
    ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap (𝓞 L) L)).codRestrict _
      fun x v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v x
  have : Finite (𝓞 L ⧸ Ideal.span {(N : 𝓞 L)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 L)})
    (Ideal.span {(N : intFin L)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : intFin L)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat L N hN).2 z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : FiniteAdeleRing (𝓞 L) L) - algebraMap L _ (x : L) = ((N : intFin L) : FiniteAdeleRing (𝓞 L) L) * w
    rw [h, add_sub_cancel_left, nsmul_eq_mul]
    simp

theorem finUnit_pow (χ : HChar L) (hχ : χ.IsUnitary) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Ideles L, IsFinIdele u → u ∈ unitIdl L → ((χ.1 u : ℂˣ) : ℂ) ^ m = 1 := by
  let ψ : Ideles L →* Circle :=
    { toFun := fun x => ⟨(χ.1 x : ℂˣ), by simpa [Submonoid.unitSphere] using hχ x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => Subtype.ext (congrArg Units.val (map_mul χ.1 x y)) }
  have hψ : Continuous ψ := (Units.continuous_val.comp χ.2.1).subtype_mk _
  obtain ⟨-, -, -, m, hm, h⟩ := GlobalTheory.CharFin.finite_order_of_small (R := AdeleRing (𝓞 L) L)
    (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (RingHom.snd _ _) id continuous_id (fun _ => rfl) (intFin L)
    (fun W hW => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele L W hW) finite_quot ψ hψ
  refine ⟨m, hm, fun u h1 h2 => ?_⟩
  have := h u ⟨funext h1, fun v => (h2 v).le, fun v => ((unitIdl L).inv_mem h2 v).le⟩
  exact congrArg (fun z : Circle => (z : ℂ)) this

theorem infDiag_mul_finPartI (k : Lˣ) : infDiag k * finPartI L (diagUnits L k) = diagUnits L k := by
  classical
  have h : ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) = ι (fun w => algebraMap L w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem exists_pow_eq (x : Ideles L) (hx : IsFinIdele x) :
    ∃ h : ℕ, 0 < h ∧ ∃ (u : Ideles L) (k : Lˣ), IsFinIdele u ∧ u ∈ unitIdl L ∧ x ^ h * infDiag k = u * diagUnits L k := by
  have := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
  refine ⟨_, Nat.pos_of_ne_zero this.index_ne_zero, ?_⟩
  obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((unitIdl L ⊔ (diagUnits L).range).pow_index_mem x)
  have hf : finPartI L x = x := Units.ext (Prod.ext (funext hx).symm rfl)
  refine ⟨finPartI L u, k, fun _ => rfl, hu, ?_⟩
  rw [← hf, ← map_pow, ← e, map_mul, mul_assoc, mul_comm _ (infDiag k), infDiag_mul_finPartI]

theorem exists_pow_mem {I : Type} [Fintype I] (φ : I → L →+* ℂ) (K : Subfield ℂ) (h1 : ∀ i x, φ i x ∈ K)
    (h2 : ∀ i x, starRingEnd ℂ (φ i x) ∈ K) (χ : HChar L) (hχ : χ.IsUnitary) (n : I → ℤ) (hn : χ.HasInf φ n)
    (x : Ideles L) (hx : IsFinIdele x) : ∃ m : ℕ, 0 < m ∧ ((χ.1 x : ℂˣ) : ℂ) ^ m ∈ K := by
  obtain ⟨m, hm, hu⟩ := finUnit_pow χ hχ
  obtain ⟨h, hh, u, k, u1, u2, e⟩ := exists_pow_eq x hx
  have e1 := congrArg χ.1 e
  rw [map_mul, map_mul, map_pow, χ.2.2 k, mul_one, ← eq_mul_inv_iff_mul_eq] at e1
  have hK : ((χ.1 (infDiag k) : ℂˣ) : ℂ) ^ 2 ∈ K := by
    have : ((χ.1 (infDiag k) : ℂˣ) : ℂ) = _ := hn k
    rw [this, ← Finset.prod_pow]
    refine prod_mem fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, div_pow, ← Complex.mul_conj']
    exact zpow_mem (div_mem (pow_mem (h1 _ _) _) (mul_mem (h1 _ _) (h2 _ _))) _
  refine ⟨h * (m * 2), by positivity, ?_⟩
  rw [pow_mul, ← Units.val_pow_eq_pow_val (χ.1 x), e1, Units.val_mul, mul_pow, pow_mul, hu u u1 u2, one_pow, one_mul,
    Units.val_inv_eq_inv_val, inv_pow, mul_comm, pow_mul]
  exact inv_mem (pow_mem hK _)

theorem exists_pow_mem_host {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) (hχ : χ.IsUnitary)
    (n : R.Psi → ℤ) (hn : χ.HasInf (embPsi H) n) (x : Ideles H.E) (hx : IsFinIdele x) :
    ∃ m : ℕ, 0 < m ∧ ((χ.1 x : ℂˣ) : ℂ) ^ m ∈ H.φ₀.fieldRange := by
  have hcm : IsCMField H.E := H.isCMField_hostE
  refine exists_pow_mem (embPsi H) H.φ₀.fieldRange (fun i y => ⟨H.sigmaOf _ y, rfl⟩) (fun i y => ?_) χ hχ n hn x hx
  exact ⟨IsCMField.complexConj H.E (H.sigmaOf _ y), IsCMField.complexEmbedding_complexConj H.E H.φ₀ _⟩

end GlobalTheory.UnUnitCmp.Val
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPullbackFromSpecAppPreimage
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh
open GlobalTheory.CechDR

theorem isPullback_fromSpec_app_preimage {X Y : Scheme.{0}} (π : X ⟶ Y) {W : Y.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen (π ⁻¹ᵁ W)) :
    IsPullback hV.fromSpec (Spec.map (π.app W)) π hW.fromSpec := by
  refine (IsOpenImmersion.isPullback (Spec.map (π.app W)) hV.fromSpec hW.fromSpec π ?_ ?_).flip
  · rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec π hW hV le_rfl]
  · rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]

end GlobalTheory.HodgeCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationIntertwinerPrimeIndexStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalisation_intertwiner_prime_index : Formalism.L2.AlgTh.LocNormInter := by
  first | exact @GlobalTheory.locNormInter | exact GlobalTheory.locNormInter | (intros; apply GlobalTheory.locNormInter <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalNormalisationTensorPowersStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormalisation_tensorPowers : Formalism.L2.AlgTh.LocNormPow := by
  first | exact @GlobalTheory.locNormPow_tensorPowers | exact GlobalTheory.locNormPow_tensorPowers | (intros; apply GlobalTheory.locNormPow_tensorPowers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelMapsStepWeightValuesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_kernel_maps_step_weight_values : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)) f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → IsVal (O.frm (i + 1)) (lamTG M (i + 1)) (RingHom.id ℂ) (C.Kmap i c c' f) := by
  first | exact @GlobalTheory.KerJ.Kmap_isVal | exact GlobalTheory.KerJ.Kmap_isVal | (intros; apply GlobalTheory.KerJ.Kmap_isVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelTermTargetStabiliserLawStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_kernel_term_target_stabiliser_law : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (Pm : PeriodMap D.R C) (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm) (O : GL3Theta.LiftObj D C) (i : ℕ), i < D.R.m → UnfIs O i (nuT D u i) → ∀ (c : C.cls i) (c' : C.cls (i + 1)), Differentiable ℂ (O.Th i c c') → ∀ g, TermLaw O i c c' g → ∀ f, IsVal (O.frm i) (lamTG M i) (RingHom.id ℂ) f → LawAt O (i + 1) g (C.Kmap i c c' f) := by
  first | exact @GlobalTheory.KerJ.lawAt_Kmap | exact GlobalTheory.KerJ.lawAt_Kmap | (intros; apply GlobalTheory.KerJ.lawAt_Kmap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitChartUniformiserAndResidueCardStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitChart_uniformiser_and_residueCard : ∀ {D : D7} (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → Chart e v π → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (∃ p : Ov D v, algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D (ϖ : D.host.E)) ∧ Irreducible p) ∧ Nat.card (IsLocalRing.ResidueField (Ov D v)) = Ideal.absNorm P.asIdeal := by
  first | exact @GlobalTheory.SplitUnif.unif_chart | exact GlobalTheory.SplitUnif.unif_chart | (intros; apply GlobalTheory.SplitUnif.unif_chart <;> assumption)
end

