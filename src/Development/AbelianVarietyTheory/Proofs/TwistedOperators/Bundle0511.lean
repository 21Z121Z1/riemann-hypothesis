import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHatMxHomLatIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0481
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0383
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0075
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HomLatticeCosetIndicatorPrimePowersIntegralCoset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosetIndCompare

variable {D : D7}

theorem frame_smul {m n : ℕ} (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)) (a : AE D) (Y : Mx D m n) :
    HMul.hMul (HMul.hMul (β'⁻¹).val ((a • Y).map (toEAf D))) β.val =
      toEAf D a • HMul.hMul (HMul.hMul (β'⁻¹).val (Y.map (toEAf D))) β.val := by
  have : (a • Y).map (toEAf D) = toEAf D a • Y.map (toEAf D) := by
    ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [this]
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem frame_sub {m n : ℕ} (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)) (Y Z : Mx D m n) :
    HMul.hMul (HMul.hMul (β'⁻¹).val ((Y - Z).map (toEAf D))) β.val =
      HMul.hMul (HMul.hMul (β'⁻¹).val (Y.map (toEAf D))) β.val -
        HMul.hMul (HMul.hMul (β'⁻¹).val (Z.map (toEAf D))) β.val := by
  rw [Matrix.map_sub _ (map_sub (toEAf D)), Matrix.mul_sub, Matrix.sub_mul]

theorem frame_incA {m n : ℕ} (y : Matrix (Fin m) (Fin n) D.host.E) :
    (y.map (incA D)).map (toEAf D) = y.map (eToEAf D) := by
  ext i j; rfl

theorem frame_mem_idS {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {β : GL (Fin n) (EAf D)} {β' : GL (Fin m) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hβ' : Formalism.L2.DIV.IsFrame β' Λ') (I : Ideal (𝓞 D.host.E))
    {y : GlobalTheory.ChiGrid.homLat Λ Λ'} (hy : y ∈ (I • ⊤ : Submodule (𝓞 D.host.E) (GlobalTheory.ChiGrid.homLat Λ Λ'))) (i : Fin m)
    (j : Fin n) : ∃ t ∈ Formalism.L2.DIV.idS D.host.F I,
      (t : EAf D) = HMul.hMul (HMul.hMul (β'⁻¹).val ((y : Matrix (Fin m) (Fin n) D.host.E).map (eToEAf D))) β.val i j := by
  have h1 : (y : Matrix (Fin m) (Fin n) D.host.E) ∈ I • GlobalTheory.ChiGrid.homLat Λ Λ' := by
    have := Submodule.mem_map_of_mem (f := (GlobalTheory.ChiGrid.homLat Λ Λ').subtype) hy
    rwa [Submodule.map_smul'', Submodule.map_subtype_top] at this
  have h2 : (y : Matrix (Fin m) (Fin n) D.host.E).map (eToEAf D) ∈
      GlobalTheory.FunObj.HatFrame.genGrp D.host.F (I • GlobalTheory.ChiGrid.homLat Λ Λ') :=
    AddSubgroup.subset_closure ⟨1, one_mem _, _, h1, by ext a b; rfl⟩
  exact GlobalTheory.FunObj.HatFrame.genGrp_le_frGrp hβ hβ' (H := GlobalTheory.ChiGrid.homLat Λ Λ') (fun _ hx => hx) I h2 i j

theorem frame_smul_incA {m n : ℕ} (β : GL (Fin n) (EAf D)) (β' : GL (Fin m) (EAf D)) (a : AE D)
    (y : Matrix (Fin m) (Fin n) D.host.E) :
    HMul.hMul (HMul.hMul (β'⁻¹).val ((a • y.map (incA D)).map (toEAf D))) β.val =
      toEAf D a • HMul.hMul (HMul.hMul (β'⁻¹).val (y.map (eToEAf D))) β.val := by
  rw [frame_smul, frame_incA]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem quot_iff (I : Ideal (𝓞 E)) (y : E ⊗[F] Formalism.L2.Herm.Af F) (r : 𝓞 E) :
    (∃ h : y ∈ Formalism.L2.Herm.intAf F E, Ideal.Quotient.mk (Formalism.L2.DIV.idS F I) ⟨y, h⟩ =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS F I) (Formalism.L2.DIV.oToS F E r)) ↔
    y ∈ Formalism.L2.Herm.intAf F E ∧ ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - Formalism.L2.DIV.oToS F E r := by
  constructor
  · rintro ⟨h, hq⟩
    exact ⟨h, _, Ideal.Quotient.eq.1 hq, rfl⟩
  · rintro ⟨h, t, ht, et⟩
    refine ⟨h, Ideal.Quotient.eq.2 ?_⟩
    have : (⟨y, h⟩ : Formalism.L2.Herm.intAf F E) - Formalism.L2.DIV.oToS F E r = t := Subtype.ext et.symm
    rw [this]; exact ht

theorem step_fwd {I : Ideal (𝓞 E)} {y N a s : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E)
    (hq : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - N)
    (hv : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = a - N)
    (hs : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = 1 - s) :
    ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - s * a := by
  obtain ⟨t1, h1, e1⟩ := hq
  obtain ⟨t2, h2, e2⟩ := hv
  obtain ⟨t3, h3, e3⟩ := hs
  refine ⟨t1 - t2 + t3 * ⟨a, ha⟩, add_mem (sub_mem h1 h2) (Ideal.mul_mem_right _ _ h3), ?_⟩
  simp only [Subring.coe_add, Subring.coe_mul, AddSubgroupClass.coe_sub, e1, e2, e3]
  ring

theorem step_bwd {I : Ideal (𝓞 E)} {y N a a' s : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E)
    (hN : N ∈ Formalism.L2.Herm.intAf F E) (hsi : s ∈ Formalism.L2.Herm.intAf F E)
    (ht : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - s * a')
    (hu : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = a' - a)
    (hv : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = a - N)
    (hs : ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = 1 - s) :
    y ∈ Formalism.L2.Herm.intAf F E ∧ ∃ t ∈ Formalism.L2.DIV.idS F I, (t : E ⊗[F] Formalism.L2.Herm.Af F) = y - N := by
  obtain ⟨t1, h1, e1⟩ := ht
  obtain ⟨t2, h2, e2⟩ := hu
  obtain ⟨t3, h3, e3⟩ := hv
  obtain ⟨t4, h4, e4⟩ := hs
  have hy : y = ((t1 + ⟨s, hsi⟩ * t2 + ⟨s, hsi⟩ * ⟨a, ha⟩ : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) := by
    simp only [Subring.coe_add, Subring.coe_mul, e1, e2]
    ring
  refine ⟨hy ▸ Subtype.property _, t1 + ⟨s, hsi⟩ * t2 - t4 * ⟨a, ha⟩ + t3,
    add_mem (sub_mem (add_mem h1 (Ideal.mul_mem_left _ _ h2)) (Ideal.mul_mem_right _ _ h4)) h3, ?_⟩
  simp only [Subring.coe_add, Subring.coe_mul, AddSubgroupClass.coe_sub, e1, e2, e3, e4]
  ring

end Gen

theorem cmpS_mk (I : Ideal (𝓞 D.host.E)) (r : 𝓞 D.host.E) :
    Formalism.L2.DIV.cmpS D.host.F I (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS D.host.F I) (Formalism.L2.DIV.oToS D.host.F D.host.E r) := by
  unfold Formalism.L2.DIV.cmpS
  exact Ideal.quotientMap_mk

set_option maxHeartbeats 1600000 in

theorem mem_cosSet_iff {S T : GlobalTheory.Grid.Node D} {e : AE D} (hS : Formalism.L2.DIV.IsFrame S.β S.Λ)
    (hT : Formalism.L2.DIV.IsFrame T.β T.Λ) (he0 : infPart D e = 0) {I : Ideal (𝓞 D.host.E)}
    (he_int : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h1s : ∃ t ∈ Formalism.L2.DIV.idS D.host.F I, (t : EAf D) = 1 - toEAf D e)
    (c : GlobalTheory.Grid.Coset S T I) (r : Fin T.V.rank → Fin S.V.rank → 𝓞 D.host.E)
    (hcos : ∀ i j, Formalism.L2.DIV.cmpS D.host.F I (c i j) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS D.host.F I) (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j)))
    (x₀ : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (hx₀ : x₀ ∈ GlobalTheory.ChiGrid.homLat S.Λ T.Λ)
    (hN : ∀ i j, ∃ t ∈ Formalism.L2.DIV.idS D.host.F I, (t : EAf D) =
      HMul.hMul (HMul.hMul (T.β⁻¹).val (x₀.map (eToEAf D))) S.β.val i j -
        (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j) : EAf D)) (x : WO S.V T.V) :
    (IsHalf e x ∧ InCosetOf S T I c x) ↔ x ∈ GlobalTheory.ChiGrid.cosSet e (GlobalTheory.ChiGrid.Cos.mk I ⟨x₀, hx₀⟩) := by
  have hAint : ∀ i j, (HMul.hMul (HMul.hMul (T.β⁻¹).val (x₀.map (eToEAf D))) S.β.val :
      Matrix (Fin T.V.rank) (Fin S.V.rank) (EAf D)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.FunObj.HatFrame.frame_int hS hT hx₀

  have hfr : ∀ y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E,
      HMul.hMul (HMul.hMul (T.β⁻¹).val ((x - e • y.map (incA D)).map (toEAf D))) S.β.val =
        frMapO S.V T.V S.β T.β x - toEAf D e • HMul.hMul (HMul.hMul (T.β⁻¹).val (y.map (eToEAf D))) S.β.val := by
    intro y
    rw [frame_sub, frame_smul_incA]; rfl
  change _ ↔ IsHalf e x ∧ ∃ x₀' : GlobalTheory.ChiGrid.homLat S.Λ T.Λ, GlobalTheory.ChiGrid.Cos.mk I x₀' = GlobalTheory.ChiGrid.Cos.mk I ⟨x₀, hx₀⟩ ∧
    x - e • (x₀' : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈
      GlobalTheory.ChiGrid.hatMx (I • GlobalTheory.ChiGrid.homLat S.Λ T.Λ)
  refine and_congr_right fun hx => ?_
  have hx' : ∀ i j, e * x i j = x i j := hx
  have hinf : ∀ (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) i j,
      infPart D ((x - e • y.map (incA D)) i j) = 0 := by
    intro y i j
    have h1 : (x - e • y.map (incA D)) i j = e * (x i j - y.map (incA D) i j) := by
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, hx' i j]
    rw [h1, map_mul, he0, zero_mul]
  constructor
  · intro hc
    unfold InCosetOf at hc
    refine ⟨⟨x₀, hx₀⟩, rfl, ?_⟩
    rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D S.Λ T.Λ S.β T.β hS hT I]
    refine ⟨hinf x₀, fun i j => ?_⟩
    rw [hfr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    have hq := ((quot_iff I _ (r i j)).1 ((hc i j).imp fun _ h => h.trans (hcos i j))).2
    exact step_fwd (hAint i j) hq (hN i j) h1s
  · rintro ⟨y, hyc, hmem⟩
    rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_homLat_iff D S.Λ T.Λ S.β T.β hS hT I] at hmem
    have hdiff := (Submodule.Quotient.eq _).1 hyc
    unfold InCosetOf
    intro i j
    have et := hmem.2 i j
    rw [hfr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at et
    have hu := frame_mem_idS hS hT I hdiff i j
    rw [Submodule.coe_sub, Matrix.map_sub _ (map_sub (eToEAf D)), Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply] at hu
    have h := step_bwd (hAint i j) (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j)).2 he_int et hu (hN i j) h1s
    exact ((quot_iff I _ (r i j)).2 h).imp fun _ h => h.trans (hcos i j).symm

theorem cosetInd_eq_cosInd {S T : GlobalTheory.Grid.Node D} {e : AE D} (hS : Formalism.L2.DIV.IsFrame S.β S.Λ)
    (hT : Formalism.L2.DIV.IsFrame T.β T.Λ) (he0 : infPart D e = 0) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥)
    (he_int : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h1s : ∃ t ∈ Formalism.L2.DIV.idS D.host.F I, (t : EAf D) = 1 - toEAf D e)
    (c : GlobalTheory.Grid.Coset S T I) :
    ∃ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ I, GlobalTheory.Grid.cosetInd S T e I c = GlobalTheory.ChiGrid.cosInd e κ := by
  choose r hr using fun i j => Ideal.Quotient.mk_surjective (I := I) (c i j)
  obtain ⟨x₀, hx₀, hN⟩ := GlobalTheory.T.exists_latticeHom_approx_integralMatrix_mod S.Λ T.Λ S.β T.β hS hT I hI (fun i j => Formalism.L2.DIV.oToS D.host.F D.host.E (r i j))
  have hcos : ∀ i j, Formalism.L2.DIV.cmpS D.host.F I (c i j) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS D.host.F I) (Formalism.L2.DIV.oToS D.host.F D.host.E (r i j)) := fun i j =>
    (congrArg (Formalism.L2.DIV.cmpS D.host.F I) (hr i j)).symm.trans (cmpS_mk I (r i j))
  refine ⟨GlobalTheory.ChiGrid.Cos.mk I ⟨x₀, hx₀⟩, funext fun x => ?_⟩
  have key := mem_cosSet_iff hS hT he0 he_int h1s c r hcos x₀ hx₀ hN x
  unfold GlobalTheory.Grid.cosetInd GlobalTheory.ChiGrid.cosInd
  classical
  rw [Set.indicator_apply]
  by_cases h : IsHalf e x ∧ InCosetOf S T I c x
  · rw [if_pos h, if_pos (key.1 h)]; rfl
  · rw [if_neg h, if_neg fun h' => h (key.2 h')]

theorem coset_eq_cos : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), Formalism.L2.DIV.IsFrame S.β S.Λ → Formalism.L2.DIV.IsFrame T.β T.Λ → IsIdemSum e P → ∀ c : GlobalTheory.Grid.Coset S T (∏ w ∈ P, w.asIdeal ^ d w), ∃ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ (∏ w ∈ P, w.asIdeal ^ d w), GlobalTheory.Grid.cosetInd S T e (∏ w ∈ P, w.asIdeal ^ d w) c = GlobalTheory.ChiGrid.cosInd e κ := by
  intro D S T e P d hS hT he c
  obtain ⟨he0, he_int, h1s⟩ := GlobalTheory.T.idempotentSum_infPart_integral_one_sub_mem e P d he
  refine cosetInd_eq_cosInd hS hT he0 ?_ he_int h1s c
  rw [← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)

end GlobalTheory.CosetIndCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunTransportS
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

open GlobalTheory.GridJoin

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

structure RowMatchS (ch : Choice R) (G' : GlobalTheory.Grid.GridPre R) : Prop where

  V : ∀ i, i ≤ D.R.m → SameSp (ch.G.V (.grid i 0)) (G'.V i 0).V

  ν : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).ν (ch.M.ν (.grid i 0))

  fd : ∀ i, i ≤ D.R.m → HEq (G'.measCol i).fd (ch.M.fd (.grid i 0))

  ker : ∀ (ρ : ch.G.RealVec) (Φ : ch.G.Datum) (i : Fin D.R.m), ∃ f,
    GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f ∧ ∃ p,
      HEq (fun h g => thetaKO (G'.X i 0).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G'.V ((i : ℕ) + 1) 0) (G'.V i 0) f p))
        (fun h g => ch.W.kerA (.right (i : ℕ) 0) (ch.W.datum ρ Φ i) g h)

theorem transport_stepS {A A' B B' : HSp D} (eA : SameSp A' A) (eB : SameSp B' B)
    {ν : Measure (GA D A)} {fd : Set (GA D A)} {ν' : Measure (GA D A')} {fd' : Set (GA D A')}
    (hν : HEq ν ν') (hfd : HEq fd fd') {K : GA D B → GA D A → ℂ} {K' : GA D A' → GA D B' → ℂ}
    (hK : HEq K (fun h g => K' g h)) {φ : GA D A → ℂ} {φ' : GA D A' → ℂ} (hφ : HEq φ φ') {ψ : GA D B → ℂ}
    (hI : ∀ h, IntegrableOn (fun g => K h g * φ g) fd ν) (hE : ∀ h, ∫ g in fd, K h g * φ g ∂ν = ψ h) :
    (∀ h, IntegrableOn (fun g => K' g h * φ' g) fd' ν') ∧ HEq ψ (fun h => ∫ g in fd', K' g h * φ' g ∂ν') := by
  obtain ⟨L, h1, h2, rfl⟩ := eA
  obtain ⟨L', h1', h2', rfl⟩ := eB
  obtain rfl := eq_of_heq hν
  obtain rfl := eq_of_heq hfd
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq hK
  exact ⟨hI, heq_of_eq (funext hE).symm⟩

theorem isAutFun_transportS {V V' : HSp D} (e : SameSp V' V) {φ : GA D V → ℂ} {φ' : GA D V' → ℂ} (h : HEq φ φ')
    (hφ : IsAutFun V φ) : IsAutFun V' φ' := by
  obtain ⟨L, h1, h2, rfl⟩ := e
  obtain rfl := eq_of_heq h
  exact ⟨hφ.left, hφ.level, hφ.cont⟩

end GlobalTheory.RowLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDatumLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem isDatum_linear : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z), IsDatum M ψ crd 0 0 ∧ ∀ (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ) (c : ℂ), IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + c • Φ') (f + c • f') := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z crd
  have hn : ∀ x, ‖ψ x‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  refine ⟨⟨Submodule.zero_mem _, fun u => ?_⟩, fun Φ Φ' f f' c h h' =>
    ⟨Submodule.add_mem _ h.1 (Submodule.smul_mem _ c h'.1), fun u => ?_⟩⟩
  · have e : M.co.rho ψ u (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := funext fun x => by
      simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    rw [e]
    simp [GlobalTheory.WeilM.thetaSum]
  · have s1 : Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u Φ (fun i => algebraMap F (AF F) (ξ i)) :=
      (GlobalTheory.ThetaTrCont.schA_cont F ψ hψ.1 hn h.1).1 (M.co.e u)
    have s2 : Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u Φ' (fun i => algebraMap F (AF F) (ξ i)) :=
      (GlobalTheory.ThetaTrCont.schA_cont F ψ hψ.1 hn h'.1).1 (M.co.e u)
    have e : M.co.rho ψ u (Φ + c • Φ') = M.co.rho ψ u Φ + c • M.co.rho ψ u Φ' := funext fun x => by
      simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← h.2 u, ← h'.2 u]
    unfold GlobalTheory.WeilM.thetaSum
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [s1.tsum_add (s2.mul_left c), tsum_mul_left]

end GlobalTheory.SquareAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMeasDefOfIsTermVol
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowClaim.TermVolDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

theorem isDefiniteSpace_of_isV {X : LSp D} {ν : ℕ} (h : X.IsV ν 0) : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace X.sp :=
  ⟨h.sigOK, fun τ => Or.inl (by rw [h.sig τ, h.rank, Nat.sub_zero])⟩

theorem isMeasDef_of_isTermVol {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U)
    {μ₀ : T} (hL : L.Is μ₀) (t : T) (Φ : G.Datum) (β : CosFam G t) (M : Vol G) (hM : IsTermVol t S Φ β M) :
    (∀ j (h : j < D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace (G.V (.top j)) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel (G.V (.top j)) (S.levTop t Φ β j h) ∧
      IsMeasDef (G.V (.top j)) (S.levTop t Φ β j h) (M.ν (.top j)) (M.fd (.top j))) ∧
    ∀ i (h : i ≤ D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace (G.V (.grid i D.R.m)) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel (G.V (.grid i D.R.m)) (S.levRow t i h) ∧
      IsMeasDef (G.V (.grid i D.R.m)) (S.levRow t i h) (M.ν (.grid i D.R.m)) (M.fd (.grid i D.R.m)) := by
  refine ⟨fun j h => ⟨?_, S.isCO_levTop W t Φ β h, ?_⟩, fun i h => ⟨?_, S.isCO_levRow W t h, ?_⟩⟩
  · exact isDefiniteSpace_of_isV (node_isV G hL (X := .top j) h.le)
  · have e := hM.1 j h
    unfold Vol.IsAt at e
    rw [if_pos (by simp [Node.neg])] at e
    exact e
  · have hV := node_isV G hL (X := .grid i D.R.m) ⟨h, le_rfl⟩
    have e : Node.neg D.R.m (.grid i D.R.m) = 0 := by simp [Node.neg]
    rw [e] at hV
    exact isDefiniteSpace_of_isV hV
  · have e := hM.2 i h
    unfold Vol.IsAt at e
    rw [if_pos (by simp [Node.neg])] at e
    exact e

end GlobalTheory.RowClaim.TermVolDef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionFunctionIsUnfoldingNoCompactCore
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
open GlobalTheory.Unf.FB

noncomputable section

open GlobalTheory.ThLaws in

theorem GlobalTheory.th_isTh_lev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → ∀ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) → IsTh ψ J.d B.V x₀ (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) := by
  intro D ψ hψ σ J B y hy x₀ hx₀
  obtain ⟨hcont, -, hleft, hcen, -, -⟩ := GlobalTheory.T.jacobiActionUnipotent_laws D ψ hψ σ J B y hy
  beta_reduce at hcen hleft
  obtain ⟨x₁, hx₁, -, -, hlast, hq⟩ := GlobalTheory.T.besselBasePoint_isUnfoldingBasePoint_spec D σ B
  have e : x₁ = x₀ := rat_injective (hx₁.trans hx₀.symm)
  refine ⟨hcont.comp continuous_subtype_val, fun γ hγQ hγN n hn => hleft γ hγN hγQ n hn, fun c n hn => ?_, ?_⟩
  · rw [hcen c n hn, hx₀, hq]
  intro j a ha1 ha0 hg
  have hl : a (Fin.last σ) = 0 := hlast a (by rw [e]; exact hg)
  have hj : j.1 < σ := by
    by_contra hc
    have : j = Fin.last σ := Fin.ext (by have := j.2; simp only [Fin.val_last]; omega)
    rw [this, hl] at ha1
    exact zero_ne_one ha1
  let j' : Fin (σ + 1) := ⟨j.1 + 1, by omega⟩
  have hjj : j < j' := by rw [Fin.lt_def]; simp [j']
  obtain ⟨t, ht⟩ := exists_psiE_ne_one hψ
  let A : Fin (σ + 1) → AE D := GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a
  let Bv : Fin (σ + 1) → AE D := fun k => if k = j' then cA D t else 0
  have hB0 : ∀ k, k ≠ j' → Bv k = 0 := fun k hk => if_neg hk
  have hA0 : ∀ i, j < i → A i = 0 := fun i hi => by
    show incA D (a i) = 0
    rw [ha0 i hi, map_zero]
  have hN : ∀ i k, ¬(i ≤ j ∧ k = j') → A i * cA D (Bv k) = 0 := by
    intro i k hik
    by_cases hk : k = j'
    · rw [hA0 i (not_le.1 fun hi => hik ⟨hi, hk⟩), zero_mul]
    · rw [hB0 k hk, map_zero, mul_zero]
  have hAB : (fun k => cA D (Bv k)) ⬝ᵥ A = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_comm]
    exact hN k k fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj)
  have hupper : tvGL A Bv hAB ∈ upperUni (σ + 1) (AE D) := fun i k => by
    refine ⟨fun hki => ?_, ?_⟩
    · rw [tvGL_val, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hki), tvN_apply,
        hN i k fun h => absurd (h.2 ▸ hki) (not_lt.2 (le_of_lt (lt_of_le_of_lt h.1 hjj))), zero_add]
    · rw [tvGL_val, Matrix.add_apply, Matrix.one_apply_eq, tvN_apply,
        hN i i fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj), add_zero]
  have hUX : tvGL A Bv hAB ∈ UX D (σ + 1) := mem_UX.2 hupper
  have hu : J.d.levi (tvGL A Bv hAB) ∈ flagN J.d := J.d.levi_mem_NFlag hupper
  have hup : upSum (tvN A Bv) = t := by
    unfold upSum
    rw [Finset.sum_eq_single j, Finset.sum_eq_single j']
    · rw [if_pos (by simp [j']), tvN_apply, show Bv j' = cA D t from if_pos rfl, cA_cA']
      show incA D (a j) * t = t
      rw [ha1, map_one, one_mul]
    · intro k _ hk
      rw [tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro i _ hi
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = j'
      · rw [if_neg]
        intro h
        apply hi
        rw [hk] at h
        exact Fin.ext (by simp [j'] at h; omega)
      · rw [tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨J.d.jY *ᵥ Bv, J.d.levi (tvGL A Bv hAB), star (psiE ψ t), ?_, levi_isTransv J.d A Bv hAB,
    Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_iInf.2 fun i => ?_⟩, ?_, ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form J.W (J.d.jX *ᵥ A) (J.d.jY *ᵥ Bv) = 0
    rw [form_mulVec, ← J.d.pX_eq, Matrix.mulVec_mulVec, J.d.pX_jX, Matrix.one_mulVec, hAB]
  · rw [mem_fixer]
    have hcol : ∀ m, (tvGL A Bv hAB).1 m i.1 = (1 : Mx D (σ + 1) (σ + 1)) m i.1 := fun m => by
      rw [tvGL_val, Matrix.add_apply, tvN_apply,
        hN m i.1 fun h => absurd (h.2 ▸ i.2) (not_le.2 hjj), add_zero]
    ext k l
    have h1 := congrFun (congrFun (J.d.levi_jX (tvGL A Bv hAB)) k) i.1
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id] at h1 ⊢
    rw [h1]
    simp only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro h1
    apply ht
    rw [← star_star (psiE ψ t), h1, star_one]
  · intro n hn n' hn'
    have hx : ∀ u ∈ UX D (σ + 1), zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ := fun u hu => zEll_mul B.L B.ζ hu
    have hJu : jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.levi (tvGL A Bv hAB)) = id := by
      have := jacS_levi_mul ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (hx _ hUX) 1
      rwa [mul_one, jacS_one] at this
    have hpu : psiFlag ψ J.d (J.d.levi (tvGL A Bv hAB)) = psiE ψ t := by
      rw [psiFlag, blockX_levi, tvGL_val, upSum_add, upSum_one, zero_add, hup]
    beta_reduce
    rw [GlobalTheory.JacHom.jacS_mul J.d hx ψ (mul_mem hn hu) hn', GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hu, hJu,
      GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hn', psiFlag_mul J.d ψ (mul_mem hn hu) hn', psiFlag_mul J.d ψ hn hu,
      psiFlag_mul J.d ψ hn hn', hpu]
    simp only [id, star_mul']
    ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerMovedVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames

namespace GlobalTheory.RowClaim

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem toPair_mul (p : Pair T) (g g' : GA D (G.V p.small)) (h h' : GA D (G.V p.big)) :
    G.toPair p (g * g') (h * h') = G.toPair p g h * G.toPair p g' h' := by
  cases p <;> simp [GridData.toPair, map_mul, Prod.ext_iff]

end GlobalTheory.RowClaim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeLevelEqUnitaryInfFrameStabilizerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeLevel_eq_unitary_inf_frame_stabilizer : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.IndefR.Lev.IsBaseFrame V β Λ 1 → GlobalTheory.Mass.Levels.latLev V = Formalism.L2.DIV.UA D.sp.cm V.gram ⊓ Formalism.L2.DIV.St β := by
  first | exact @GlobalTheory.LatLevEq.latLev_eq_UA_inf_St | exact GlobalTheory.LatLevEq.latLev_eq_UA_inf_St | (intros; apply GlobalTheory.LatLevEq.latLev_eq_UA_inf_St <;> assumption)
end

