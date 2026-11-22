import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0670
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompletionPlaceData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.PlcAtW

variable {D : D7}

open Classical in

theorem cpt_atPl_self (w : Pl D.host.E) (x : Kw w) : cpt w (toEAf D (atPl w x)) = x := by
  rw [(atPl_spec w x).2 w, Pi.single_eq_same]

theorem atPl_zero (w : Pl D.host.E) : atPl w (0 : Kw w) = 0 := by
  have h := atPl_add w 0 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

def atPlHom (w : Pl D.host.E) : Kw w →+ AE D where
  toFun := atPl w
  map_zero' := atPl_zero w
  map_add' := atPl_add w

theorem atPl_cpt (w : Pl D.host.E) (a : AE D) : atPl w (cpt w (toEAf D a)) = atPl w 1 * a := by
  classical
  refine ae_ext ?_ fun Q => ?_
  · rw [(atPl_spec w _).1, map_mul, (atPl_spec w 1).1, zero_mul]
  · rw [(atPl_spec w _).2 Q, map_mul, map_mul, (atPl_spec w 1).2 Q]
    by_cases hQ : Q = w
    · subst hQ
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
    · rw [Pi.single_eq_of_ne hQ, Pi.single_eq_of_ne hQ, zero_mul]

theorem valuation_le_of_inv_mul {k : Type} [Field k] [ValuativeRel k] (u : kˣ) (b : k)
    (h : ValuativeRel.valuation k (((u⁻¹ : kˣ) : k) * b) ≤ 1) :
    ValuativeRel.valuation k b ≤ ValuativeRel.valuation k (u : k) := by
  have hne : ValuativeRel.valuation k (u : k) ≠ 0 := by simp
  rw [Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀] at h
  calc ValuativeRel.valuation k b
      = ValuativeRel.valuation k (u : k) * ((ValuativeRel.valuation k (u : k))⁻¹ * ValuativeRel.valuation k b) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ ≤ ValuativeRel.valuation k (u : k) * 1 := by gcongr
    _ = _ := mul_one _

theorem cpt_atPl_mul (w : Pl D.host.E) (x : Kw w) (z : AE D) :
    cpt w (toEAf D (atPl w x * z)) = x * cpt w (toEAf D z) := by
  rw [map_mul, map_mul, cpt_atPl_self]

theorem valuation_cpt_le_one (w : Pl D.host.E) (x : AE D) (h : finPart D x ∈ intAE D) :
    ValuativeRel.valuation (Kw w) (cpt w (toEAf D x)) ≤ 1 := by
  have h2 := ((GlobalTheory.StdFrames.comp_toAd D).int x).1 h w
  have h3 : cpt w (toEAf D x) ∈ (ValuativeRel.valuation (Kw w)).integer :=
    (GlobalTheory.FinPl.SplitPoint.mem_integer_iff D.host.E w _).2 h2
  exact h3

end GlobalTheory.PlcAtW

open scoped TensorProduct

namespace GlobalTheory.PlcAtW

variable {D : D7}

open scoped Topology in

theorem continuous_cpt_toEAf (w : Pl D.host.E) : Continuous fun a : AE D => cpt w (toEAf D a) := by
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, -⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hfc : Continuous (finPart D) := by
    have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  have h1 : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
    rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
    convert this using 1
    ext z
    simp
  haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero (Kw w)) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  let f : AE D →+ Kw w := ((cpt w).comp (toEAf D)).toAddMonoidHom
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero]
  refine (IsValuativeTopology.hasBasis_nhds_zero (Kw w)).tendsto_right_iff.2 fun γ _ => ?_
  have hϖ : ValuativeRel.valuation (Kw w) (unifAt w : Kw w) < 1 := by
    rw [isUnif_unifAt w]
    exact ValuativeRel.uniformizer_lt_one
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ γ
  set u : (Kw w)ˣ := unifAt w ^ n
  have hu : ValuativeRel.valuation (Kw w) (u : Kw w) < γ := by
    simpa [u, Units.val_pow_eq_pow_val, map_pow] using hn
  have hU : {z : AE D | finPart D (atPl w ((u⁻¹ : (Kw w)ˣ) : Kw w) * z) ∈ intAE D} ∈ 𝓝 (0 : AE D) := by
    refine IsOpen.mem_nhds (h1.preimage (hfc.comp (continuous_const.mul continuous_id))) ?_
    simp only [Set.mem_setOf_eq, mul_zero, map_zero]
    exact zero_mem _
  filter_upwards [hU] with z hz
  have h3 := valuation_cpt_le_one w _ hz
  rw [cpt_atPl_mul] at h3
  exact (valuation_le_of_inv_mul u _ h3).trans_lt hu

end GlobalTheory.PlcAtW

namespace GlobalTheory.PlcAtW

variable {D : D7}

theorem continuous_atPl (w : Pl D.host.E) : Continuous (atPl (D := D) w) := by
  classical
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, -, hes⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hs : Function.Bijective (Formalism.IndefR.Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).bijective
  have ht : Function.Bijective (toAd D) :=
    ⟨GlobalTheory.AdeleBaseChange.map_injective (toAd_spec D), GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)⟩
  let R : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    RingEquiv.ofBijective ((toAd D).comp (Formalism.IndefR.Lev.swapAE D)) (ht.comp hs)
  have hfin : ∀ y, finPart D (e.symm (0, y)) = y := fun y => by
    rw [← (he _).2, RingEquiv.apply_symm_apply]
  have hR : Continuous R.symm := by
    refine GlobalTheory.AdeleBaseChange.continuous_symm_finite D.host.F D.host.E R fun y => ?_
    have key := (GlobalTheory.StdFrames.comp_toAd D).int (e.symm (0, y))
    rw [hfin] at key
    have e1 : ((toAd D).comp (toEAf D)) (e.symm (0, y)) = R y := by
      show toAd D (Formalism.IndefR.Lev.swapAE D (finPart D (e.symm (0, y)))) = toAd D (Formalism.IndefR.Lev.swapAE D y)
      rw [hfin]
    rw [e1] at key
    exact key
  have hform : ∀ x, atPl w x = e.symm (0, R.symm (singleV D.host.E w x)) := fun x => by
    refine ae_ext ?_ fun Q => ?_
    · rw [(atPl_spec w x).1, ← (he _).1, RingEquiv.apply_symm_apply]
    · rw [(atPl_spec w x).2 Q]
      show _ = toAd D (Formalism.IndefR.Lev.swapAE D (finPart D (e.symm (0, R.symm (singleV D.host.E w x))))) Q
      rw [hfin]
      show _ = R (R.symm (singleV D.host.E w x)) Q
      rw [RingEquiv.apply_symm_apply]
      by_cases hQ : Q = w
      · subst hQ
        rw [Pi.single_eq_same]
        exact (RestrictedProduct.single_eq_same _ _ _).symm
      · rw [Pi.single_eq_of_ne hQ]
        exact (RestrictedProduct.single_eq_of_ne _ _ hQ).symm
  rw [funext hform]
  exact hes.comp (continuous_const.prodMk (hR.comp (GlobalTheory.FinPl.SplitPoint.continuous_single_at D.host.E w)))

end GlobalTheory.PlcAtW

namespace GlobalTheory.PlcAtW

theorem exists_plc : ∀ (D : D7) (w : Pl D.host.E) (e : AE D), IsIdemSum e {w} → ∃ p : Place D (Kw w), IsPlc w p ∧ p.e = e := by
  intro D w e he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_singleton]
  have h := hes w (Finset.mem_singleton_self w)
  have he1 := GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt h
  refine ⟨{ e := es w
            split := h.1
            π := (cpt w).comp (toEAf D)
            ι := atPlHom w
            π_ι := cpt_atPl_self w
            ι_π := fun a => by
              show atPl w (cpt w (toEAf D a)) = es w * a
              rw [atPl_cpt, ← he1]
            cont_π := continuous_cpt_toEAf w
            cont_ι := continuous_atPl w }, ⟨h, fun _ => rfl, fun _ => rfl⟩, rfl⟩

end GlobalTheory.PlcAtW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalModelMovedFrames
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace.MoveModel

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
  {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z']

def subH (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) : Matrix Y Y' k ≃ₜ Matrix Z Z' k where
  toFun x := ((εT⁻¹).val * x * εS.val).submatrix σT σS
  invFun z := εT.val * z.submatrix σT.symm σS.symm * (εS⁻¹).val
  left_inv x := by
    simp only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  right_inv z := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Equiv.symm_comp_self, Matrix.submatrix_id_id]
  continuous_toFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_submatrix _ _
  continuous_invFun := ((continuous_const.matrix_mul (continuous_id.matrix_submatrix _ _)).matrix_mul continuous_const)

theorem subH_apply (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) (x : Matrix Y Y' k) :
    subH εS εT σS σT x = ((εT⁻¹).val * x * εS.val).submatrix σT σS := rfl

theorem subH_add (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) (x y : Matrix Y Y' k) :
    subH εS εT σS σT (x + y) = subH εS εT σS σT x + subH εS εT σS σT y := by
  simp only [subH_apply, Matrix.mul_add, Matrix.add_mul]
  rfl

def pullS (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) : SB (Matrix Z Z' k) →ₗ[ℂ] SB (Matrix Y Y' k) where
  toFun Φ := ⟨fun x => Φ.1 (subH εS εT σS σT x),
    ⟨Φ.2.1.comp_continuous (subH εS εT σS σT).continuous, Φ.2.2.comp_homeomorph (subH εS εT σS σT)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sub_mul_sub {n m : Type} [Fintype n] [Fintype m] (P : Matrix Y n k) (Q : Matrix n m k) (R : Matrix m Y' k)
    (σS : Z' ≃ Y') (σT : Z ≃ Y) : P.submatrix σT id * Q * R.submatrix id σS = (P * Q * R).submatrix σT σS := by
  ext i j
  simp [Matrix.mul_apply]

end GlobalTheory.FlatPlace.MoveModel

namespace GlobalTheory.FlatPlace.MoveModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z']

theorem map_mt_inv_mul {S : HSp D} (g : GA D S) : (mt S g⁻¹).map p.π * (mt S g).map p.π = 1 := by
  rw [← Matrix.map_mul]
  have : mt S g⁻¹ * mt S g = 1 := by
    rw [show mt S g⁻¹ * mt S g = mt S (g⁻¹ * g) by simp [Formalism.L2.Theta.mt], inv_mul_cancel]
    simp [Formalism.L2.Theta.mt]
  rw [this, Matrix.map_one _ (map_zero _) (map_one _)]

theorem actO_up_mvFr {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (a : GA D S) (b : GA D T)
    (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y) (x : Matrix Y Y' k) :
    actO S T a b (p.up FS FT x) = p.up (mvFr p a FS εS σS) (mvFr p b FT εT σT) (subH εS εT σS σT x) := by
  have h1 : IsHalf p.e (actO S T a b (p.up FS FT x)) :=
    GlobalTheory.SplitHecke.isHalf_actO a b (Witness.up_half p FS FT x)
  rw [← Witness.up_down p (mvFr p a FS εS σS) (mvFr p b FT εT σT) h1]
  congr 1
  have hu : (p.up FS FT x).map p.π = FT.β * x * FS.γ := Matrix.ext fun _ _ => p.π_ι _
  have hA := map_mt_inv_mul p a
  have hB := map_mt_inv_mul p b
  unfold Place.down actO
  rw [Matrix.map_mul, Matrix.map_mul, hu, subH_apply]
  change ((εT⁻¹).val * FT.γ * (mt T b⁻¹).map p.π).submatrix σT id * _ * ((mt S a).map p.π * FS.β * εS.val).submatrix id σS = _
  rw [sub_mul_sub]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((mt T b⁻¹).map p.π), hB, Matrix.one_mul, ← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul,
    ← Matrix.mul_assoc ((mt S a⁻¹).map p.π), hA, Matrix.one_mul, ← Matrix.mul_assoc FS.γ FS.β, FS.γβ, Matrix.one_mul]

end GlobalTheory.FlatPlace.MoveModel

namespace GlobalTheory.FlatPlace

open GlobalTheory.FlatPlace.MoveModel in

theorem exists_isModel_mvFr : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Z Z' : Type) [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) Tm, p.IsModel ψ FS FT Tm → ∀ (a : GA D S) (b : GA D T) (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y), ∃ Tm', p.IsModel ψ (mvFr p a FS εS σS) (mvFr p b FT εT σT) Tm' ∧ ∀ (Φ : SB (Matrix Y Y' k)) (Φ' : SB (Matrix Z Z' k)), (∀ x, Φ.1 x = Φ'.1 (((εT⁻¹).val * x * εS.val).submatrix σT σS)) → Tm' Φ' = ω (a, b) (Tm Φ) := by
  intro D k _ _ _ _ p ψ S T χS χT ω hW Y Y' _ _ _ _ Z Z' _ _ _ _ FS FT Tm hm a b εS εT σS σT
  let L := pullS (k := k) εS εT σS σT
  let W₀ : Module.End ℂ (WO S T → ℂ) := ω (a, b)
  have hA := actO_up_mvFr p FS FT a b εS εT σS σT
  refine ⟨W₀ ∘ₗ Tm ∘ₗ L, ⟨fun Φ => hW.om_pres _ _ (hm.theta _), fun z Φ Φ₁ hΦ => ?_, fun y hy Φ Φ₁ hΦ => ?_⟩, fun Φ Φ' e => ?_⟩
  · set x := (subH εS εT σS σT).symm z with hx
    have hz : subH εS εT σS σT x = z := (subH εS εT σS σT).apply_symm_apply z
    have h1 : ∀ t, (L Φ₁).1 t = (L Φ).1 (t + x) := fun t => by
      change Φ₁.1 (subH εS εT σS σT t) = Φ.1 (subH εS εT σS σT (t + x))
      rw [hΦ, subH_add, hz]
    have h2 := hm.trans x (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (a, b) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), hA, hz]
  · set y₀ := actO S T a⁻¹ b⁻¹ y
    have hy₀ : IsHalf (cA D p.e) y₀ := GlobalTheory.SplitHecke.isHalf_actO a⁻¹ b⁻¹ hy
    have hyy : actO S T a b y₀ = y := by
      have := GlobalTheory.SplitHecke.actO_inv_actO a⁻¹ b⁻¹ y
      rwa [inv_inv, inv_inv] at this
    have h1 : ∀ t, (L Φ₁).1 t = ψ (symplO S T (p.up FS FT t) y₀) * (L Φ).1 t := fun t => by
      change Φ₁.1 (subH εS εT σS σT t) = _ * Φ.1 (subH εS εT σS σT t)
      rw [hΦ, ← hA, ← hyy, GlobalTheory.SplitHecke.symplO_actO]
    have h2 := hm.modul y₀ hy₀ (L Φ) (L Φ₁) h1
    simp only [LinearMap.comp_apply]
    rw [h2]
    show ω (a, b) _ = _
    rw [hW.om_heis _ _ _ _ (hm.theta _), hyy]
  · have : L Φ' = Φ := Subtype.ext (funext fun x => (e x).symm)
    show ω (a, b) (Tm (L Φ')) = _
    rw [this]

end GlobalTheory.FlatPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalModelOfSplitPlaceThetaFun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.LocMod.Witness

theorem exists_isModel_of_isThetaAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), (∀ x, p.up FS FT x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔ ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation k)) → ∀ f₀ φ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ φ f → ∃ Tm, p.IsModel ψ FS FT Tm ∧ (∀ O, IsOne O → Tm O = f₀) ∧ ∃ Φ : SB (Matrix Y Y' k), (∀ x, Φ.1 x = φ (p.up FS FT x)) ∧ Tm Φ = f := by
  classical
  intro D k _ _ _ _ p ψ hψ S T ΛS ΛT hS hT Y Y' _ _ _ _ FS FT hlat f₀ φ f hf₀ hφ hθ
  obtain ⟨⟨T₀, h₀⟩, hall⟩ := hθ
  have hf : f = T₀ φ := hall T₀ h₀

  have hNk : ∀ N : ℕ, 0 < N → (N : k) ≠ 0 := fun N hN h => by
    have h1 : prH p (N : D.host.E) = 0 := by rw [map_natCast]; exact h
    have h2 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    exact h2 ((map_eq_zero (prH p)).1 h1)
  obtain ⟨N, hN, hinv, hsupp⟩ := hφ.2
  have hN0 := hNk N hN
  have hA := lat_compact p FS FT hS hT
  have hAo := lat_open p FS FT hS hT
  generalize hAd : ((latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True).comap (upH p FS FT) : AddSubgroup _) = A at hA hAo
  have memA : ∀ x, x ∈ A ↔ p.up FS FT x ∈ (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) := fun x => by
    rw [← hAd]; rfl
  have hup_smul : ∀ x : Matrix Y Y' k, p.up FS FT (N • x) = N • p.up FS FT x := fun x => map_nsmul (upH p FS FT) N x
  have hNx : ∀ x : Matrix Y Y' k, (N : k) • x = N • x := fun x => Nat.cast_smul_eq_nsmul k N x

  let g : Matrix Y Y' k → ℂ := fun x => φ (p.up FS FT x)
  have hlc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hU : IsOpen ((fun y : Matrix Y Y' k => (N : k)⁻¹ • (y - x)) ⁻¹' (A : Set (Matrix Y Y' k))) :=
      hAo.preimage ((continuous_const_smul ((N : k)⁻¹)).comp (continuous_id.sub continuous_const))
    have hx : x ∈ ((fun y : Matrix Y Y' k => (N : k)⁻¹ • (y - x)) ⁻¹' (A : Set (Matrix Y Y' k))) := by
      simp only [Set.mem_preimage, sub_self, smul_zero]; exact A.zero_mem
    filter_upwards [hU.mem_nhds hx] with y hy
    have hy' : (N : k)⁻¹ • (y - x) ∈ A := hy
    have e1 : y = x + N • ((N : k)⁻¹ • (y - x)) := by
      rw [← hNx, smul_smul, mul_inv_cancel₀ hN0, one_smul, add_sub_cancel]
    change φ (p.up FS FT y) = φ (p.up FS FT x)
    rw [e1, up_add, hup_smul]
    exact hinv _ ((memA _).1 hy') (up_half p FS FT _) _
  have hcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (hA.image (continuous_const_smul (N : k)⁻¹)) fun x hx => ?_
    by_contra h
    apply hx
    have h1 := hsupp _ h
    rw [← hup_smul, ← memA] at h1
    refine ⟨N • x, h1, ?_⟩
    change (N : k)⁻¹ • (N • x) = x
    rw [← hNx, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  let Φ : SB (Matrix Y Y' k) := ⟨g, hlc, hcs⟩

  have hext : ∀ Ψ : SB (Matrix Y Y' k), IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) (ext p FS FT Ψ) :=
    ext_sb p FS FT hS hT
  refine ⟨T₀.comp (ext p FS FT), ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩, fun O hO => ?_, Φ, fun x => rfl, ?_⟩
  · exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ S T _ _ hS hT p.e p.split.1 (GlobalTheory.PlaceCoord.infPart_split p.split)
      _ hf₀ T₀ h₀ _ (hext Ψ)
  · refine Eq.trans (congrArg T₀ ?_) (h₀.trans _ (hext Ψ) _ (up_half p FS FT x))
    funext t
    rw [ext_apply, ext_apply, down_add, down_up, h]
    exact if_congr (half_add (up_half p FS FT x)).symm rfl rfl
  · refine Eq.trans (congrArg T₀ ?_) (h₀.modul _ (hext Ψ) _ hy)
    funext t
    rw [ext_apply, ext_apply, h]
    split_ifs with ht
    · rw [up_down p FS FT ht]
    · rw [mul_zero]
  · have e1 : ext p FS FT O = (1 : ℂ) • halfInd p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) := by
      funext t
      rw [one_smul, ext_apply, halfInd]
      by_cases ht : IsHalf p.e t
      · rw [if_pos ht, hO, Set.indicator_apply]
        refine if_congr ?_ rfl rfl
        rw [and_iff_left ht, ← up_down p FS FT ht, down_up, hlat]
        rfl
      · rw [if_neg ht, if_neg fun h => ht h.2]
    change T₀ (ext p FS FT O) = f₀
    rw [e1]
    exact h₀.vac
  · change T₀ (ext p FS FT Φ) = f
    rw [hf]
    congr 1
    funext t
    rw [ext_apply]
    split_ifs with ht
    · change φ (p.up FS FT (p.down FS FT t)) = φ t
      rw [up_down p FS FT ht]
    · by_contra h
      exact ht (hφ.1 t (Ne.symm h))

end GlobalTheory.LocMod.Witness
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMoveArgumentsLastRowVertexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_moveArguments_lastRow_vertex : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (F : Γ.Args → ℂ)
    (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    valuation k (gdet κ : k) = 1 → ∀ v ∈ symN k (Fin (topRank Γ (j + 1))) (Γ.m - 1 - (j + 1)), toFrame hs hj g = v * embX _ κ →
    ∀ (x : ColArgs Γ) (y : RowArgs Γ),
      flatTensor hs ψ ν (fun z => F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) z)) x y = flatTensor hs ψ ν F (colMove j κ x) y := by
  first | exact @GlobalTheory.TopLevelInv.FlatStep.flatTensor_moveArgs_mulSingle | exact GlobalTheory.TopLevelInv.FlatStep.flatTensor_moveArgs_mulSingle | (intros; apply GlobalTheory.TopLevelInv.FlatStep.flatTensor_moveArgs_mulSingle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorLocalIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

theorem pureTensor_oppArgs_local : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) (w : Pl D.host.E) (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid G t w).rank b.tgt)) (Fin ((locGrid G t w).rank b.src)) (Kw w) → ℂ) (x : ∀ i : Fin D.R.m, Mx D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank) (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank), (locGrid G t w).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ (oppArgs t B w x y) = (∏ i : Fin D.R.m, φ (.ex i D.R.m) (B.coord t w (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ ((x i).map fun a => cpt w (toEAf D a)))) * ∏ j : Fin D.R.m, φ (.theta D.R.m j) (B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ ((y j).map fun a => cpt w (toEAf D a))) := by
  intro D T L sc G t B w φ x y
  show ((GlobalTheory.SplitFlip.oppositePath D.R.m).map fun b => φ b (oppArgs t B w x y b)).prod = _
  simp only [GlobalTheory.SplitFlip.oppositePath, List.map_append, List.prod_append, List.map_reverse,
    List.prod_reverse, List.map_map]
  rw [← List.map_coe_finRange_eq_range, List.map_map, List.map_map, ← Fin.prod_univ_def, ← Fin.prod_univ_def]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_ <;> simp [oppArgs]

theorem flipFin_local_identity : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (Φ : ch.G.Datum) (e : AE D) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → (∀ x y, (∀ i, IsHalf e (x i)) → (∀ j, IsHalf e (y j)) → (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y)) → ∀ (n : locPl ch.G t → ℕ) (xw : ∀ w : locPl ch.G t, Fin (n w) → ℂ) (φw : ∀ w : locPl ch.G t, Fin (n w) → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ (w : locPl ch.G t) z, Tflip ch.W ch.S.B t Φ w.1 z = ∑ i, xw w i * (locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φw w i) z) → ∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ Fintype.piFinset (fun w => (Finset.univ : Finset (Fin (n w)))), (∏ w, xw w (a w)) * (∏ i : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (x i)) * ∏ j : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (y j) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch t Φ e τ φ hloc hfac n xw φw hexp x y
  by_cases hh : (∀ i, IsHalf e (x i)) ∧ ∀ j, IsHalf e (y j)
  · rw [hfac x y hh.1 hh.2, ← Finset.prod_coe_sort]
    simp_rw [hexp, pureTensor_oppArgs_local]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hh.1, hh.2, ↓reduceIte, Finset.prod_mul_distrib]
    rw [mul_assoc]
    congr 2 <;> exact Finset.prod_comm
  · rw [not_and_or] at hh
    rcases hh with hh | hh <;> simp only [not_forall] at hh <;> obtain ⟨k, hk⟩ := hh
    · trans (0 : ℂ)
      · rw [Finsupp.sum]
        refine Finset.sum_eq_zero fun d hd => ?_
        have h0 : (φ d).1 k (x k) = 0 := by
          by_contra hne
          exact hk (((hloc d hd).1 k).1.1 (x k) hne)
        apply mul_eq_zero_of_left
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) h0
      · symm
        refine Finset.sum_eq_zero fun a _ => ?_
        apply mul_eq_zero_of_left
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by dsimp only; exact if_neg hk)
    · trans (0 : ℂ)
      · rw [Finsupp.sum]
        refine Finset.sum_eq_zero fun d hd => ?_
        have h0 : (φ d).2 k (y k) = 0 := by
          by_contra hne
          exact hk (((hloc d hd).2 k).1.1 (y k) hne)
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) h0
      · symm
        refine Finset.sum_eq_zero fun a _ => ?_
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by dsimp only; exact if_neg hk)

end GlobalTheory.LocAsm
end

