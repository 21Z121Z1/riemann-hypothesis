import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseLevelVectorOfPrincipalLevelFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section
namespace GlobalTheory.BaseVec

theorem coeff_conj_of_central {K : Type} [Field K] {H : Type} [Group H] (z : MonoidAlgebra K H)
    (hz : ∀ b, b * z = z * b) (g h : H) : z.coeff (g * h * g⁻¹) = z.coeff h := by
  have e := congrArg (fun y : MonoidAlgebra K H => y.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simpa [mul_assoc] using e.symm

section Levels

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem baseLevelDatum_level_eq (P' : LevelP R.Pg D.R.r ℂ) : (R.dat0 P').P = P' := by
  simp [LevCh.dat0, datY]

theorem mem_levS (P' : LevelP R.Pg D.R.r ℂ) (x : GA D (Yc D 0)) :
    x ∈ levS _ (R.βY 0) (R.dat0 P') ↔ x ∈ GfC (Yc D 0) ∧ finE (Yc D 0) x ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) ∧
      rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) x) ∈ P'.H := by
  show x ∈ GfC (Yc D 0) ∧ (finE (Yc D 0) x ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 P') ∧
      rTup (R.βY 0) (R.dat0 P') (finE (Yc D 0) x) ∈ (R.dat0 P').P.H) ↔ _
  rw [baseLevelDatum_level_eq]
  rfl

theorem principalRowLevelCharacter_trivial (P' : LevelP R.Pg D.R.r ℂ) (x : GA D (Yc D 0)) :
    levChi _ (R.βY 0) (R.dat0 P') x = ((ext1 P'.H P'.chi (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) x)) : ℂˣ) : ℂ) := by
  simp [levChi, levFn, LevCh.dat0, datY]
  rfl

theorem conj_mem_principal {x y : GA D (Yc D 0)} (hx : x ∈ levS _ (R.βY 0) (R.dat0 R.triv)) (hy1 : y ∈ GfC (Yc D 0))
    (hy2 : finE (Yc D 0) y ∈ parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv)) :
    y⁻¹ * x * y ∈ levS _ (R.βY 0) (R.dat0 R.triv) := by
  rw [mem_levS] at hx ⊢
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hyi := Subgroup.inv_mem _ hy2
  refine ⟨(GfC _).mul_mem ((GfC _).mul_mem ((GfC _).inv_mem hy1) hx1) hy1, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyi hx2) hy2
  · rw [map_mul, map_mul, map_inv, rTup_mul (Subgroup.mul_mem _ hyi hx2) hy2, rTup_mul hyi hx2, rTup_inv hy2]
    have : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) x) = 1 := Subgroup.mem_bot.1 hx3
    rw [this, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _

theorem lift_div_principal {g0 : G0 R.Pg D.R.r} {κ κ' : GA D (Yc D 0)}
    (hκ : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ) (hκ' : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0 κ') :
    κ⁻¹ * κ' ∈ levS _ (R.βY 0) (R.dat0 R.triv) := by
  rw [mem_levS]
  have hi := Subgroup.inv_mem _ hκ.2.1
  refine ⟨(GfC _).mul_mem ((GfC _).inv_mem hκ.1) hκ'.1, ?_, ?_⟩
  · rw [map_mul, map_inv]; exact Subgroup.mul_mem _ hi hκ'.2.1
  · refine Subgroup.mem_bot.2 ?_
    rw [map_mul, map_inv, rTup_mul hi hκ'.2.1, rTup_inv hκ.2.1, hκ.2.2, hκ'.2.2]
    exact inv_mul_cancel g0

end Levels

open Formalism.IndefR.principalLevelFrame in

theorem exists_base_vec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (π : Formalism.L2.NG.FinTyp D.host.E n) (v : Formalism.AUTREP.GAf D.host.E n → ℂ), v ∈ π.S → v ≠ 0 → principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v → (∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v) → ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levR F false))) (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ)) x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hne n PY π v hvS hv0 hvT hgood
  classical
  have hL := GlobalTheory.DimFull.liftsY' hC
  have hex : ∀ g : G, ∃ κ : Formalism.AUTREP.GAf D.host.E n,
      IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ κ) := by
    intro g
    obtain ⟨κ, hκ⟩ := hL (R.eG g)
    obtain ⟨h, rfl⟩ := PY.onto κ hκ.1
    exact ⟨h, hκ⟩
  choose k hk using hex
  set J0 := PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv) with hJ0
  have hvfix : ∀ c ∈ J0, Formalism.L2.NG.rt D.host.E n c v = v := fun c hc => by
    simpa using hvT c hc
  set Ws : Submodule ℂ (Formalism.AUTREP.GAf D.host.E n → ℂ) :=
    Submodule.span ℂ (Set.range fun g => Formalism.L2.NG.rt D.host.E n (k g) v) with hWs
  have hfix : ∀ w ∈ Ws, ∀ c ∈ J0, Formalism.L2.NG.rt D.host.E n c w = w := by
    intro w hw c hc
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have hc' : (k g)⁻¹ * c * k g ∈ J0 := by
        rw [hJ0, Set.mem_preimage]
        rw [map_mul, map_mul, map_inv]
        exact GlobalTheory.BaseVec.conj_mem_principal R hc (hk g).1 (hk g).2.1
      rw [rt_rt, show c * k g = k g * ((k g)⁻¹ * c * k g) by group, ← rt_rt, hvfix _ hc']
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  have hprod : ∀ g h, ∀ w ∈ Ws, Formalism.L2.NG.rt D.host.E n (k g) (Formalism.L2.NG.rt D.host.E n (k h) w) =
      Formalism.L2.NG.rt D.host.E n (k (g * h)) w := by
    intro g h w hw
    have hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (g * h)) (PY.ψ (k g * k h)) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [map_mul]; exact (GfC _).mul_mem (hk g).1 (hk h).1
      · rw [map_mul, map_mul]; exact Subgroup.mul_mem _ (hk g).2.1 (hk h).2.1
      · rw [map_mul, map_mul, rTup_mul (hk g).2.1 (hk h).2.1, (hk g).2.2, (hk h).2.2]
        exact (map_mul R.eG g h).symm
    have hc : (k (g * h))⁻¹ * (k g * k h) ∈ J0 := by
      rw [hJ0, Set.mem_preimage]
      rw [map_mul, map_inv]
      exact GlobalTheory.BaseVec.lift_div_principal R (hk (g * h)) hl
    rw [rt_rt, show k g * k h = k (g * h) * ((k (g * h))⁻¹ * (k g * k h)) by group, ← rt_rt, hfix w hw _ hc]
  have hk1 : k 1 ∈ J0 := by
    rw [hJ0, Set.mem_preimage, GlobalTheory.BaseVec.mem_levS]
    refine ⟨(hk 1).1, (hk 1).2.1, Subgroup.mem_bot.2 ?_⟩
    rw [(hk 1).2.2]
    exact map_one R.eG
  have hvWs : v ∈ Ws := by
    have : Formalism.L2.NG.rt D.host.E n (k 1) v ∈ Ws := Submodule.subset_span ⟨1, rfl⟩
    rwa [hvfix _ hk1] at this
  have hstab : ∀ g, ∀ w ∈ Ws, Formalism.L2.NG.rt D.host.E n (k g) w ∈ Ws := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hprod g h v hvWs]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Ws.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Ws.smul_mem a hx
  let ρ : Representation ℂ G Ws :=
    { toFun := fun g => (Formalism.L2.NG.rt D.host.E n (k g)).restrict (fun w hw => hstab g w hw)
      map_one' := LinearMap.ext fun w => Subtype.ext (hfix w w.2 _ hk1)
      map_mul' := fun g h => LinearMap.ext fun w => Subtype.ext (hprod g h w w.2).symm }
  haveI : FiniteDimensional ℂ Ws := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hX : ∀ χ ∈ A.X, IsAbsIrrChar χ := hOk.irr
  have hcen : ∀ g h : G, RealDat.eC (A := A) D.what₂.embLL (g * h * g⁻¹) = RealDat.eC (A := A) D.what₂.embLL h := fun g h => by
    unfold RealDat.eC
    rw [GlobalTheory.BaseVec.coeff_conj_of_central _ (fun b => idemOf_central A.X hX b) g h]
  have hgoodv : ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (k g) v = v := hgood k hk
  have hgoodW : ∀ w ∈ Ws, ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (k g) w = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      simp only [hprod _ h v hvWs]
      conv_rhs => rw [← hgoodv]
      rw [map_sum]
      simp only [map_smul, hprod h _ v hvWs]
      refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun g => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      rw [hcen, show h * (h⁻¹ * g * h⁻¹⁻¹) = g * h by group]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, smul_add, Finset.sum_add_distrib, hx, hy]
    | smul a x _ hx =>
      simp only [map_smul]
      simp only [smul_comm _ a, ← Finset.smul_sum, hx]
  have hbot : (⊤ : Submodule ℂ Ws) ≠ ⊥ := by
    intro h
    have h0 : (⟨v, hvWs⟩ : Ws) ∈ (⊥ : Submodule ℂ Ws) := h ▸ Submodule.mem_top
    exact hv0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h0))
  obtain ⟨u, -, hu0, hu⟩ := GlobalTheory.Hk3.exists_level_vector D.what₂.embLL A.X F.P0 F.ψ0 ρ ⊤ hX hne (fun _ => le_top) hbot
    (fun u _ => Subtype.ext (by
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hgoodW u u.2))
  refine ⟨(u : Formalism.AUTREP.GAf D.host.E n → ℂ), ?_, fun h => hu0 (Subtype.ext h), ?_⟩
  · exact (Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact π.stable _ _ hvS)) u.2
  · intro κ hκ
    obtain ⟨h1, h2, h3⟩ := (GlobalTheory.BaseVec.mem_levS R _ (PY.ψ κ)).1 hκ
    have hgP : R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))) ∈ F.P0 := h3
    have hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv)
        (R.eG (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))))) (PY.ψ κ) :=
      ⟨h1, h2, (MulEquiv.apply_symm_apply R.eG _).symm⟩
    have hc : (k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))))⁻¹ * κ ∈ J0 := by
      rw [hJ0, Set.mem_preimage]
      rw [map_mul, map_inv]
      exact GlobalTheory.BaseVec.lift_div_principal R (hk _) hl
    have e1 : Formalism.L2.NG.rt D.host.E n κ (u : _ → ℂ) =
        Formalism.L2.NG.rt D.host.E n (k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))))) u := by
      conv_lhs => rw [show κ = k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))) *
        ((k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))))⁻¹ * κ) by group]
      rw [← rt_rt, hfix u u.2 _ hc]
    have e2 := congrArg Subtype.val (hu ⟨_, hgP⟩)
    rw [e1]
    refine e2.trans ?_
    show _ = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ) • _
    rw [GlobalTheory.BaseVec.principalRowLevelCharacter_trivial, Submodule.coe_smul]
    congr 1
    exact ((congrArg (fun u : ℂˣ => (u : ℂ)) (extendOne_of_mem (R.levR F false).chi h3)).trans rfl).symm

end GlobalTheory.BaseVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisChoiceDetNeZero
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem exists_basis_choice_det_ne_zero : ∀ (F E A A' : Type) [Field F] [Field E] [Algebra F E] [AddCommGroup A] [Module F A] [AddCommGroup A'] [Module E A'] (ι : A →ₛₗ[algebraMap F E] A') (V : Submodule F A) (r δ : ℕ) (bb : Module.Basis (Fin r) F V) (res : A' →ₗ[E] (Fin δ → E)), (Submodule.span E (ι '' (V : Set A))).map res = ⊤ → ∃ σ : Fin δ → Fin r, (Matrix.of fun p' p => res (ι (bb (σ p))) p').det ≠ 0 := by
  intro F E A A' _ _ _ _ _ _ _ ι V r δ bb res h
  have hsub : ι '' (V : Set A) ⊆ Submodule.span E (Set.range fun i => ι (bb i)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x = ∑ i, bb.repr ⟨x, hx⟩ i • ((bb i : V) : A) := by
      have := congrArg Subtype.val (bb.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hx', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span E (Set.range fun i => res (ι (bb i))) = ⊤ := by
    have h1 := Submodule.map_mono (f := res) (Submodule.span_le.mpr hsub)
    rw [h, Submodule.map_span, ← Set.range_comp] at h1
    exact eq_top_iff.mpr h1
  obtain ⟨b, hb, hbspan, hli⟩ := exists_linearIndependent E (Set.range fun i => res (ι (bb i)))
  let bs := Module.Basis.mk hli (by rw [Subtype.range_coe, hbspan, hspan])
  let e := bs.indexEquiv (Pi.basisFun E (Fin δ))
  have hmem : ∀ p, ((e.symm p : b) : Fin δ → E) ∈ Set.range fun i => res (ι (bb i)) :=
    fun p => hb (e.symm p).2
  choose σ hσ using hmem
  refine ⟨σ, ?_⟩
  have hli2 : LinearIndependent E (fun p => res (ι (bb (σ p)))) := by
    have : (fun p => res (ι (bb (σ p)))) = ((↑) : b → Fin δ → E) ∘ e.symm := funext fun p => hσ p
    rw [this]
    exact hli.comp _ e.symm.injective
  have hunit : IsUnit (Matrix.of fun p' p => res (ι (bb (σ p))) p') := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli2
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockWordOfTypeProd
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem words_of_type (D t : ℕ) (α : Fin D →₀ ℕ) (hα : α.degree ≤ t) :
    ∃ β : Fin t → Fin (D + 1), (∀ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card = α i) ∧
      (α.degree = t → ∀ q, β q ≠ Fin.last D) ∧
      ∀ (M : Type) [Monoid M] (f : Fin (D + 1) → M),
        (List.ofFn fun q => f (β q)).prod =
          (List.ofFn fun i : Fin D => f i.castSucc ^ α i).prod * f (Fin.last D) ^ (t - α.degree) := by
  classical
  have hdeg : α.degree = ∑ i, α i := Finsupp.degree_eq_sum α
  set L : List (Fin (D + 1)) :=
    (List.ofFn fun i : Fin D => List.replicate (α i) i.castSucc).flatten ++
      List.replicate (t - α.degree) (Fin.last D) with hL
  have hlen : L.length = t := by
    simp only [hL, List.length_append, List.length_flatten, List.map_ofFn, List.length_replicate,
      List.sum_ofFn, Function.comp_def]
    omega
  refine ⟨fun q => L.get (Fin.cast hlen.symm q), ?_⟩
  set β : Fin t → Fin (D + 1) := fun q => L.get (Fin.cast hlen.symm q) with hβ
  have hofFn : List.ofFn β = L := by
    apply List.ext_get
    · simp [hlen]
    · intro n h1 h2
      simp [hβ]
  have hcount : ∀ x, (Finset.univ.filter fun q => β q = x).card = L.count x := by
    intro x
    rw [← hofFn, ← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map, Finset.card_def,
      Finset.filter_val]
    congr 1
    apply Multiset.filter_congr
    intro a _
    exact eq_comm
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hcount]
    simp [hL, List.count_flatten, List.count_replicate, Function.comp_def, Fin.castSucc_inj, List.sum_ofFn,
      (Fin.castSucc_ne_last i).symm]
  · intro ht q
    have hmem : β q ∈ L := List.get_mem _ _
    have h0 : t - α.degree = 0 := by omega
    simp only [hL, h0, List.replicate_zero, List.append_nil, List.mem_flatten, List.mem_ofFn] at hmem
    obtain ⟨l, ⟨j, rfl⟩, hl⟩ := hmem
    rw [List.mem_replicate] at hl
    rw [hl.2]
    exact Fin.castSucc_ne_last j
  · intro M _ f
    have : (List.ofFn fun q => f (β q)) = (List.ofFn β).map f := by
      rw [List.map_ofFn]; rfl
    rw [this, hofFn, hL]
    simp [List.prod_append, List.map_flatten, List.prod_flatten, List.map_ofFn, Function.comp_def,
      List.prod_replicate]

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoZpowLocalUnitsPowStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundleIso_zpow_local_units_pow : ∀ (X Y : Scheme.{0}) (φ : Y ⟶ X) (A : LB X) (H : LB Y) (w : LB.Iso H (A.pull φ)), w.IsGen → ∀ a : ℤ, ∃ wa : LB.Iso (GlobalTheory.AbLaw.pw H a) ((GlobalTheory.AbLaw.pw A a).pull φ), wa.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : H.ι), φ (r z) ∈ A.U k → r z ∈ H.U k' → Geo.Tor.gw wa r z k k' = Geo.Tor.gw w r z k k' ^ a := by
  first | exact @GlobalTheory.FormalAlg.lbIso_pw_pull_gw | exact GlobalTheory.FormalAlg.lbIso_pw_pull_gw | (intros; apply GlobalTheory.FormalAlg.lbIso_pw_pull_gw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

def frameTorMat {A : Type} [CommRing A] (s : A →+* A) {n r : ℕ} (J : Matrix (Fin n) (Fin n) A)
    (X Y : Matrix (Fin n) (Fin r) A) (d : Fin r → Aˣ) : Matrix (Fin n) (Fin n) A :=
  1 + X * diagonal (fun i => (d i : A) - 1) * (cT s Y * J) +
    Y * diagonal (fun i => s ((d i)⁻¹ : Aˣ) - 1) * (cT s X * J)

section Alg

variable {A : Type} [CommRing A] {s : A →+* A} {n r : ℕ} {J : Matrix (Fin n) (Fin n) A}
  {X Y : Matrix (Fin n) (Fin r) A}

theorem diagonal_sub_one' (a : Fin r → A) : diagonal (fun i => a i - 1) = diagonal a - 1 := by
  rw [← diagonal_one, diagonal_sub]

theorem frameTorMat_mul_X (xx : cT s X * J * X = 0) (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) :
    frameTorMat s J X Y d * X = X * diagonal fun i => (d i : A) := by
  simp only [frameTorMat, Matrix.add_mul, Matrix.mul_assoc _ (cT s Y * J), Matrix.mul_assoc _ (cT s X * J), xx, yx,
    diagonal_sub_one', Matrix.mul_sub]
  simp

theorem frameTorMat_mul_Y (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1) (d : Fin r → Aˣ) :
    frameTorMat s J X Y d * Y = Y * diagonal fun i => s ((d i)⁻¹ : Aˣ) := by
  simp only [frameTorMat, Matrix.add_mul, Matrix.mul_assoc _ (cT s Y * J), Matrix.mul_assoc _ (cT s X * J), yy, xy,
    diagonal_sub_one', Matrix.mul_sub]
  simp

theorem frameTorMat_mulVec {z : Fin n → A} (hx : (cT s X * J) *ᵥ z = 0) (hy : (cT s Y * J) *ᵥ z = 0)
    (d : Fin r → Aˣ) : frameTorMat s J X Y d *ᵥ z = z := by
  rw [frameTorMat, add_mulVec, add_mulVec, ← mulVec_mulVec, hy, mulVec_zero, ← mulVec_mulVec, hx, mulVec_zero]
  simp

theorem frameTorMat_mul_inv (xx : cT s X * J * X = 0) (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1)
    (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) : frameTorMat s J X Y d * frameTorMat s J X Y d⁻¹ = 1 := by
  conv_lhs => rw [show frameTorMat s J X Y d⁻¹ = 1 + _ + _ from rfl, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
  simp only [← Matrix.mul_assoc (frameTorMat s J X Y d), frameTorMat_mul_X xx yx, frameTorMat_mul_Y yy xy,
    Matrix.mul_assoc _ (diagonal _) (diagonal _), diagonal_mul_diagonal]
  have h1 : ∀ i, (d i : A) * (((d⁻¹) i : Aˣ) - 1) = 1 - d i := fun i => by
    rw [Pi.inv_apply, mul_sub, Units.mul_inv, mul_one]
  have h2 : ∀ i, s ((d i)⁻¹ : Aˣ) * (s (((d⁻¹) i)⁻¹ : Aˣ) - 1) = 1 - s ((d i)⁻¹ : Aˣ) := fun i => by
    rw [Pi.inv_apply, inv_inv, mul_sub, ← map_mul, Units.inv_mul, map_one, mul_one]
  simp only [h1, h2, frameTorMat, ← diagonal_sub, diagonal_one, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem frameTorMat_unitary (hs : ∀ a, s (s a) = a) (hJ : cT s J = J) (xx : cT s X * J * X = 0)
    (yy : cT s Y * J * Y = 0) (xy : cT s X * J * Y = 1) (yx : cT s Y * J * X = 1) (d : Fin r → Aˣ) :
    cT s (frameTorMat s J X Y d) * J * frameTorMat s J X Y d = J := by
  have cc : ∀ Z : Matrix (Fin n) (Fin r) A, cT s (cT s Z) = Z := fun Z => Matrix.ext fun i j => hs _
  have cd : ∀ a : Fin r → A, cT s (diagonal a) = diagonal fun i => s (a i) := fun a => by
    ext i j; by_cases h : i = j <;> simp [cT, diagonal, h, eq_comm]
  have ca : ∀ P Q : Matrix (Fin n) (Fin n) A, cT s (P + Q) = cT s P + cT s Q := fun P Q =>
    Matrix.ext fun i j => map_add s _ _
  have hU : cT s (frameTorMat s J X Y d) * J = J * frameTorMat s J X Y d⁻¹ := by
    simp only [frameTorMat, ca, Formalism.UG.cT_mul, Formalism.UG.cT_one, cc, hJ, cd, map_sub, map_one, hs, Pi.inv_apply, inv_inv,
      Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one]
    abel
  have hM' : frameTorMat s J X Y d⁻¹ * frameTorMat s J X Y d = 1 := by
    simpa only [inv_inv] using frameTorMat_mul_inv xx yy xy yx d⁻¹
  rw [hU, Matrix.mul_assoc, hM', Matrix.mul_one]

end Alg

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem continuous_frameTorMat {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] {s : B →+* B}
    (hs : Continuous s) {n r : ℕ} (J : Matrix (Fin n) (Fin n) B) (X Y : Matrix (Fin n) (Fin r) B) :
    Continuous (frameTorMat s J X Y) := by
  have h1 : Continuous fun d : Fin r → Bˣ => diagonal fun i => (d i : B) - 1 :=
    Continuous.matrix_diagonal (continuous_pi fun i => (Units.continuous_val.comp (continuous_apply i)).sub continuous_const)
  have h2 : Continuous fun d : Fin r → Bˣ => diagonal fun i => s ((d i)⁻¹ : Bˣ) - 1 :=
    Continuous.matrix_diagonal (continuous_pi fun i =>
      (hs.comp (Units.continuous_coe_inv.comp (continuous_apply i))).sub continuous_const)
  exact (continuous_const.add ((continuous_const.matrix_mul h1).matrix_mul continuous_const)).add
    ((continuous_const.matrix_mul h2).matrix_mul continuous_const)

theorem exists_continuous_isIdTorusElt {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
    {X Y : Matrix (Fin n) (Fin r) E} (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    ∃ t : (Fin r → (AF F ⊗[F] E)ˣ) → GAd σ J, Continuous t ∧ ∀ l, IsIdTorusElt σ J X Y l (t l) := by
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  set s := sigR (AF F) σ
  have hs : ∀ a, s (s a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma h x)
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT s (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c3 : ∀ {a : ℕ} (Z : Matrix (Fin n) (Fin a) E),
      (cT s (adMat F Z) * JR (AF F) J : Matrix (Fin a) (Fin n) (AF F ⊗[F] E)) = adMat F (cT (σ : E →+* E) Z * J) :=
    fun Z => by rw [c1]; simp only [adMat, JR, Matrix.map_mul] <;> rfl
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E,
      (cT s (adMat F Z) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Z' =
        adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c3]; simp only [adMat, Matrix.map_mul]
  have hJ' : cT s (JR (AF F) J) = JR (AF F) J :=
    (c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j))
  have xx : (cT s (adMat F X) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F X = 0 := by
    rw [c2, hW.xx]; exact Matrix.map_zero _ (map_zero _)
  have yy : (cT s (adMat F Y) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Y = 0 := by
    rw [c2, hW.yy]; exact Matrix.map_zero _ (map_zero _)
  have xy : (cT s (adMat F X) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F Y = 1 := by
    rw [c2, hW.xy]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have yx : (cT s (adMat F Y) * JR (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) * adMat F X = 1 := by
    rw [c2, GlobalTheory.StdPar.yx h hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
  let M := frameTorMat s (JR (AF F) J) (adMat F X) (adMat F Y)
  have hinv : ∀ d, M d * M d⁻¹ = 1 := frameTorMat_mul_inv xx yy xy yx
  have hinv' : ∀ d, M d⁻¹ * M d = 1 := fun d => by simpa only [inv_inv] using hinv d⁻¹
  let t : (Fin r → (AF F ⊗[F] E)ˣ) → GAd σ J := fun l =>
    ⟨⟨M l, M l⁻¹, hinv l, hinv' l⟩, frameTorMat_unitary hs hJ' xx yy xy yx l⟩
  have hc : Continuous M := continuous_frameTorMat (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ) _ _ _
  refine ⟨t, ?_, fun l => ⟨frameTorMat_mul_X xx yx l, ?_, fun z hz => ?_⟩⟩
  · refine Continuous.subtype_mk ((Units.continuous_iff (f := fun l => (⟨M l, M l⁻¹, hinv l, hinv' l⟩ : GL (Fin n) (AF F ⊗[F] E)))).2 ⟨hc, hc.comp continuous_inv⟩) _
  · refine (frameTorMat_mul_Y yy xy l).trans (congrArg (fun D => adMat F Y * diagonal D) (funext fun k => ?_))
    rw [← map_inv]; rfl
  · have key : ∀ C : Matrix (Fin n) (Fin r) E, z ∈ colPerp σ J C Set.univ →
        (cT s (adMat F C) * JR (AF F) J) *ᵥ z = 0 := fun C hC => by
      rw [c3]
      funext i
      have := (Submodule.mem_iInf _).1 hC i
      simpa using this
    exact frameTorMat_mulVec (key X hz.1) (key Y hz.2) l

end Main

end GlobalTheory.IdTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalCombinationOfLocalRegularIdealStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_combination_of_local_regular_ideal : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k Y) → ∀ (L : LB Y) (hL : L.IsLB) (n : ℕ) (t : Fin n → L.Sec) (F : Y.Modules) [IsFiniteQC F] (j₀ l : ℤ), RegSeq hL F (List.ofFn t) → VanishFrom L F j₀ → j₀ + n ≤ l + 1 → ∀ f : Γ(GlobalTheory.twistZ F L (l + 1), ⊤), (∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin n → Γ(GlobalTheory.twistZ F L l, W)), (GlobalTheory.twistZ F L (l + 1)).presheaf.map (homOfLE le_top).op f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app W (m i)) → ∃ m : Fin n → Γ(GlobalTheory.twistZ F L l, ⊤), f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app ⊤ (m i) := by
  first | exact @GlobalTheory.HSCore.exists_global_of_regSeq | exact GlobalTheory.HSCore.exists_global_of_regSeq | (intros; apply GlobalTheory.HSCore.exists_global_of_regSeq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoCrossPowersOfPullbackPowersStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_cross_powers_of_pullback_powers : ∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (A A' : LB X) (N : LB Y) (p q : ℤ) (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b)) (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)), A.IsLB → A'.IsLB → N.IsLB → w.IsGen → w'.IsGen → ∃ c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b), c.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : A'.ι) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U k' → r z ∈ N.U l → Geo.Tor.gw c r z k' (fun _ => k) = Geo.Tor.gw w' r z k' l ^ p * (Geo.Tor.gw w r z k l ^ q)⁻¹ := by
  first | exact @GlobalTheory.FormalAlg.exists_crossIso | exact GlobalTheory.FormalAlg.exists_crossIso | (intros; apply GlobalTheory.FormalAlg.exists_crossIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFramesOfPullbackPowerOnNonzeroLocusStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_frames_of_pullback_power_on_nonzeroLocus : ∀ (X X₀ : Scheme.{0}) (γ : X₀ ⟶ X) (H₀ : LB X₀) (s : LB.Sec H₀) (k : ℕ) (L : LB X), L.IsLB → H₀.IsLB → ∀ (w : LB.Iso (L.pull γ) (pw H₀ k)), w.IsGen → ∀ (D : X.Opens), γ ⁻¹ᵁ D = nonzeroLocus s → ∃ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) ∧ ∀ z m a, γ z ∈ D ⊓ L.U m → z ∈ H₀.U a → gs (𝟙 X₀) z _ (s.f a) ^ k = (gm (𝟙 X₀) z _ (u m)).val * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m))).val := by
  first | exact @GlobalTheory.Div.FramePull.frame_pull | exact GlobalTheory.Div.FramePull.frame_pull | (intros; apply GlobalTheory.Div.FramePull.frame_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryIrreducibleIsAdmissibleStatement
section
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_irreducible_is_admissible : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → GlobalTheory.RealInd.IsIrrAdm ε π := by
  first | exact @GlobalTheory.IrrAdm.isIrrAdm_of_irred | exact GlobalTheory.IrrAdm.isIrrAdm_of_irred | (intros; apply GlobalTheory.IrrAdm.isIrrAdm_of_irred <;> assumption)
end

