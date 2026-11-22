import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0180
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0409
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0760
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0410
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0227
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabLPIsLabelActK
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SerSys.LabDepth

open GlobalTheory.WeilDeligne

section Transport

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime]
  (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (i : ℚ_[p] ≃+* w.adicCompletion F) (hi : Continuous i)
include hw hi

theorem norm_symm_le (z : w.adicCompletion F) (hz : ‖z‖ ≤ 1) : ‖i.symm z‖ ≤ 1 := by
  by_contra h
  push Not at h
  set t := i.symm z with ht
  have ht0 : t ≠ 0 := by rintro h0; rw [h0, norm_zero] at h; linarith
  have h1 : ‖t⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h
  have h2 : ‖t⁻¹‖ ≤ (p : ℝ) ^ (-1 : ℤ) := by
    have := (Padic.norm_le_pow_iff_norm_lt_pow_add_one t⁻¹ (-1)).2 (by simpa using h1)
    exact this
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h3 : ‖t⁻¹ / (p : ℚ_[p])‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p, div_le_one₀ (by have := (Fact.out : p.Prime).one_lt; positivity)]
    simpa using h2
  have h4 := GlobalTheory.TypeRec.Model.emb_le w p i.toRingHom hi _ h3
  have e : z⁻¹ = (p : w.adicCompletion F) * i.toRingHom (t⁻¹ / (p : ℚ_[p])) := by
    rw [map_div₀, map_inv₀, map_natCast]
    change z⁻¹ = (p : w.adicCompletion F) * ((i t)⁻¹ / p)
    rw [ht, RingEquiv.apply_symm_apply]
    have hpE : (p : w.adicCompletion F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    field_simp
  have h5 : ‖z⁻¹‖ < 1 := by
    rw [e, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h4) (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt w p hw)
  have hz0 : z ≠ 0 := by rintro rfl; simp [ht] at ht0
  rw [norm_inv] at h5
  have := (one_le_inv₀ (norm_pos_iff.2 hz0)).2 hz
  linarith

omit hw in

theorem norm_symm_lt (z : w.adicCompletion F) (hz : ‖z‖ < 1) : ‖i.symm z‖ < 1 := by
  by_contra h
  push Not at h
  set t := i.symm z with ht
  have ht0 : t ≠ 0 := by rintro h0; rw [h0, norm_zero] at h; linarith
  have h1 : ‖t⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ h
  have h4 := GlobalTheory.TypeRec.Model.emb_le w p i.toRingHom hi _ h1
  have e : i.toRingHom t⁻¹ = z⁻¹ := by
    rw [map_inv₀]; change (i t)⁻¹ = z⁻¹; rw [ht, RingEquiv.apply_symm_apply]
  rw [e, norm_inv] at h4
  have hz0 : z ≠ 0 := by rintro rfl; simp [ht] at ht0
  have := (one_lt_inv₀ (norm_pos_iff.2 hz0)).2 hz
  linarith

theorem exists_ker_red {n : ℕ} (u : GL (Fin n) (w.adicCompletion F))
    (hu : u ∈ GlobalTheory.SplitWeil.KOne (w.adicCompletion F) (Fin n)) :
    ∃ y : (GlobalTheory.GLp.red p n).ker, GlobalTheory.GLp.inc p n y = Matrix.GeneralLinearGroup.map i.symm.toRingHom u := by
  rw [← (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne w n).2, GlobalTheory.AdelicU.mem_princ_iff,
    GlobalTheory.AdelicU.mem_GLint_iff] at hu
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  have hM : ∀ a b, ‖i.symm (u.1 a b)‖ ≤ 1 := fun a b => norm_symm_le w p hw i hi _
    (Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h1 a b)))
  have hN : ∀ a b, ‖i.symm ((u⁻¹).1 a b)‖ ≤ 1 := fun a b => norm_symm_le w p hw i hi _
    (Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h2 a b)))
  let M : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of fun a b => ⟨i.symm (u.1 a b), hM a b⟩
  let N : Matrix (Fin n) (Fin n) ℤ_[p] := Matrix.of fun a b => ⟨i.symm ((u⁻¹).1 a b), hN a b⟩
  have hMm : M.map (PadicInt.Coe.ringHom (p := p)) = u.1.map i.symm := rfl
  have hNm : N.map (PadicInt.Coe.ringHom (p := p)) = (u⁻¹).1.map i.symm := rfl
  have hinj : Function.Injective (Matrix.map · (PadicInt.Coe.ringHom (p := p)) : Matrix (Fin n) (Fin n) ℤ_[p] → _) :=
    Matrix.map_injective Subtype.coe_injective
  have e1 : M * N = 1 := hinj (by
    simp only
    rw [Matrix.map_mul, hMm, hNm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← RingEquiv.coe_toRingHom i.symm, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
  have e2 : N * M = 1 := hinj (by
    simp only
    rw [Matrix.map_mul, hMm, hNm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← RingEquiv.coe_toRingHom i.symm, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one])
  let y : GL (Fin n) ℤ_[p] := ⟨M, N, e1, e2⟩
  have hy : GlobalTheory.GLp.red p n y = 1 := by
    refine Units.ext (Matrix.ext fun a b => ?_)
    change PadicInt.toZMod (M a b) = (1 : Matrix (Fin n) (Fin n) (ZMod p)) a b
    have h4 : M a b - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) a b ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      have h5 := norm_symm_lt w p i hi _ (Valued.toNormedField.norm_lt_one_iff.2 (h3 a b))
      convert h5 using 1
      rw [PadicInt.norm_def, PadicInt.coe_sub, Matrix.sub_apply, map_sub]
      congr 1
      by_cases hab : a = b
      · subst hab; simp; rfl
      · simp [Matrix.one_apply_ne hab]; rfl
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h4
    rw [h4]
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  exact ⟨⟨y, hy⟩, Units.ext rfl⟩

end Transport

theorem exists_pull (D : D7) (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (π : QRep (D.host.g k) n)
    (hπ : IrrSm π) (hfix : fixK1 π.ρ ≠ ⊥) :
    ∃ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)),
      Nonempty (π ≅ pull I k v σ) ∧
      GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin n)) ≠ ⊥ := by
  let _ := (I.i k v).toRingHom.toAlgebra
  have : ContinuousSMul ℚ_[D.host.g k] ((D.naut.plGw k v).adicCompletion D.host.E) :=
    continuousSMul_of_algebraMap _ _ (I.cont k v)
  let el : ℚ_[D.host.g k] ≃ₗ[ℚ_[D.host.g k]] (D.naut.plGw k v).adicCompletion D.host.E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) (I.i k v).bijective
  have hi : Continuous (I.i k v).symm := by
    refine el.toContinuousLinearEquiv.symm.continuous.congr fun y => (I.i k v).injective ?_
    exact (el.toContinuousLinearEquiv.apply_symm_apply y).trans ((I.i k v).apply_symm_apply y).symm
  have hc : Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) (I.i k v).symm.toRingHom) :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  have hg : ∀ g : GL (Fin n) ℚ_[D.host.g k], Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun a b => (I.i k v).symm_apply_apply _)
  refine ⟨⟨π, π.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom), fun x => (hπ.2 x).preimage hc,
    GlobalTheory.CuspRep.ParLaws.isIrreducible_comp ((GlobalTheory.GLp.Model.isIrrRep_iff _).1 hπ.1) _ fun g => ⟨_, hg g⟩⟩,
    ⟨Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ π) fun g => LinearMap.ext fun x => ?_)⟩, ?_⟩
  · change π.ρ g x = π.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g)) x
    rw [hg]
  · obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hfix
    refine (Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, hy0⟩
    obtain ⟨z, hz⟩ := exists_ker_red (D.naut.plGw k v) (D.host.g k) (D.naut.plGw_over k v) (I.i k v) (I.cont k v) u hu
    change π.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom u) y = y
    rw [← hz]
    have := (Submodule.mem_iInf _).1 hy z
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this

theorem tame_of_isTameWD {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x : WD h}
    (hx : GlobalTheory.LocLanglands.IsTameWD x) : x.tame := by
  obtain ⟨n, a, rfl, ha⟩ := hx
  refine (WD.tame_mk a).2 fun σ hσ => ha σ ⟨Wild_le_Ine hσ, fun y hy => ?_⟩
  have e : (σ : G E Ω) y - y = ((σ : G E Ω) y / y - 1) * y := by field_simp
  have h0 : 0 < A.valuation y := zero_lt_iff.mpr (by simpa using hy)
  rw [e, map_mul]
  exact mul_lt_of_lt_one_left h0 (hσ y hy)

end GlobalTheory.SerSys.LabDepth

open GlobalTheory.WeilDeligne GlobalTheory.SerSys.LabDepth in

theorem GlobalTheory.SerSys.inertiaCharpoly_isLabel_of_action : Green → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D) (L : ∀ k, LabelDatum (D.host.g k)), IsRc hL T I rc → GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.SerSys.LabTie D L → LabParam D L rc → ∀ k v (π : QRep (D.host.g k) D.R.r), IrrSm π → fixK1 π.ρ ≠ ⊥ → IsLabel D k (D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π)) ∧ ∀ y ∈ fixK1 π.ρ, actK π.ρ (D.ntypes.eSer k (D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π))) y = y := by
  intro hG hL D T I rc L hRc hLT hLab hP k v π hπ hfix
  let S : Sys (D.host.g k) := OfLabel.ofLabel (L k) (Bridge.five_le D k) hG
  have hSe : ∀ n f, S.e n f = eSerC (L k) n f := fun _ _ => rfl
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hfix
  obtain ⟨f, hf⟩ : ∃ f, actK π.ρ (S.e D.R.r f) y ≠ 0 := by
    obtain ⟨T', hT'⟩ := S.sum D.R.r
    by_contra hcon
    push Not at hcon
    apply hy0
    rw [← LabLoc.actK_one_of_mem π.ρ hy, ← hT', LabLoc.actK_finset_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun f _ => hcon f
  have hne : S.e D.R.r f ≠ 0 := fun e => hf (by rw [e]; simp [actK])
  obtain ⟨hm, hd, h0⟩ := S.label _ f hne
  have hine : D.naut.inePol (rc k v D.R.r π) (D.ntypes.tg k v) =
      ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (D.ntypes.teichC k x)).prod := by
    rw [← (hLab k).1]
    exact hP k v D.R.r π hπ f ⟨y, hy, hf⟩
  have hSet : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) :=
    .of_tameGenAt (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k)
      (D.naut.plGw_over k v)) (D.ntypes.tg_gen k v) (D.ntypes.teichC_inj k)
  have htame : (T.e _ (rc k v D.R.r π)).tame := by
    obtain ⟨σ, hiso, hσ⟩ := exists_pull D I k v π hπ hfix
    rw [hRc k v D.R.r σ π hiso]
    obtain ⟨a, ha, ε, -, hl⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
    refine tame_of_isTameWD ((hl.depth _).1 ?_)
    exact GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ).some.symm hσ
  have hlab : D.naut.items₂ k (D.naut.plGw k v) (rc k v D.R.r π) = f := by
    have e1 : (Formalism.CyclotomicNorms.rootsBar f).map (fun x => X - C (D.ntypes.teichC k x)) =
        ((Formalism.CyclotomicNorms.rootsBar f).map (D.ntypes.teichC k)).map (fun a => X - C a) := by
      rw [Multiset.map_map]; rfl
    rw [hLT k v, WD.lab_eq_iff_of_tame hSet htame, ← T.inePol _ _ _ (D.ntypes.tg_gen k v).1, hine, e1,
      roots_multiset_prod_X_sub_C]
    exact ⟨hm, rfl⟩
  refine ⟨hlab ▸ ⟨hm, hd, h0⟩, fun z hz => ?_⟩
  rw [hlab, (hLab k).2 f, ← hSe]
  refine actK_e_eq_self _ S (L k).teich (fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) ?_ (hP k v) D.R.r π hπ f hm h0 ?_ z hz
  · rw [(hLab k).1]
    exact fun x hx y hy e => D.ntypes.teichC_inj k x y hx hy e
  · rw [(hLab k).1]; exact hine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalPairingClassStableUnitriangularChange
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ClsStable

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E]

theorem h_smul_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_sum_left {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    {ι : Type} (s : Finset ι) (v : ι → V) (y : V) : H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := H.h_smul_left 0 0 y
    simpa using this
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, H.h_add_left, ih]

theorem h_sum_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    {ι : Type} (s : Finset ι) (v : ι → V) (x : V) : H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by
  rw [H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← H.h_herm]

theorem zhat_chg {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ)
    (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hg : GlobalTheory.LocOver.Chg f A g) (hg' : GlobalTheory.LocOver.Chg f' A' g') :
    H.Zhat g g' = A.transpose.map M.L.cj * H.Zhat f f' * A' := by
  ext a b
  simp only [Loc.HermSp.Zhat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  rw [hg a, hg' b, h_sum_left]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [H.h_smul_left, h_sum_right, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h_smul_right]
  ring

theorem intUni_mul {M : Loc.Model F E} {r : ℕ} {B A : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hB : IntUni M B) (hA : IntUni M A) : IntUni M (B * A) := by
  refine ⟨fun a b hab => ?_, fun a => ?_, fun a b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hB.1 a c h, zero_mul]
    · rw [hA.1 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hB.2.1, hA.2.1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hB.1 a c h, zero_mul]
      · rw [hA.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (hB.2.2 a c) (hA.2.2 c b)

theorem span_mul_mem {M : Loc.Model F E} {t x o : E} (hx : x ∈ Submodule.span M.L.O {t}) (ho : o ∈ M.L.O) :
    x * o ∈ Submodule.span M.L.O {t} ∧ o * x ∈ Submodule.span M.L.O {t} := by
  have h1 : (⟨o, ho⟩ : M.L.O) • x ∈ Submodule.span M.L.O {t} := Submodule.smul_mem _ _ hx
  have h2 : (⟨o, ho⟩ : M.L.O) • x = o * x := rfl
  rw [h2] at h1
  exact ⟨by rw [mul_comm]; exact h1, h1⟩

theorem zhat_mem_clsLoc_of_chg : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) → Chg f A g → Chg f' A' g' → H.Zhat f f' ∈ clsLoc M Y0 → H.Zhat g g' ∈ clsLoc M Y0 := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Y0 f f' g g' A A' hA hA' hint hg hg' hY
  obtain ⟨B, B', hB, hB', hBB, hZ⟩ := hY
  have hIA : IntUni M A := ⟨hA.1, hA.2, fun a b => (hint a b).1⟩
  have hIA' : IntUni M A' := ⟨hA'.1, hA'.2, fun a b => (hint a b).2.1⟩
  refine ⟨B * A, B' * A', intUni_mul hB hIA, intUni_mul hB' hIA', fun a b => ?_, ?_⟩
  · have e : (B * A) a b - (B' * A') a b =
        ∑ c, (B a c - B' a c) * A c b + ∑ c, B' a c * (A c b - A' c b) := by
      simp only [Matrix.mul_apply, ← Finset.sum_add_distrib]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [e]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => ?_) (Submodule.sum_mem _ fun c _ => ?_)
    · exact (span_mul_mem (hBB a c) (hIA.2.2 c b)).1
    · exact (span_mul_mem (hint c b).2.2 (hB'.2.2 a c)).2
  · rw [zhat_chg H r f f' g g' A A' hg hg', hZ, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.ClsStable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrincipalCongruenceMapCompletionSubOneValuedLtStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_map_completion_sub_one_valued_lt : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, ‖θ z‖ < 1 → Valued.v z < 1) → ∀ k ∈ (GlobalTheory.GLp.red g n).ker, ∀ a b : Fin n, Valued.v ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (((((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1 := by
  first | exact @GlobalTheory.GLp.inc_map_sub_one_valued_lt_one | exact GlobalTheory.GLp.inc_map_sub_one_valued_lt_one | (intros; apply GlobalTheory.GLp.inc_map_sub_one_valued_lt_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarCorankOnePairsTransStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarCorankOnePairs_trans : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' t'' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → t''.G ≠ 0 → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t'' = 1 → (Y.tO u u').scal t' t'' → (Y.tO u u').s0 t t'' = 1 ∧ (Y.tO u u').scal t t'' := by
  first | exact @GlobalTheory.ScalTrans.scalar_pair_trans | exact GlobalTheory.ScalTrans.scalar_pair_trans | (intros; apply GlobalTheory.ScalTrans.scalar_pair_trans <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitTrivialTranslateLocalComponentDisjointOrLeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTrivialTranslate_localComponent_disjoint_or_le : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))) (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → ℂ)), Function.Injective T → (∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)) → ∀ y : GAf L n, TrivOutside {s.v}ᶜ y → ∀ P : Submodule ℂ (GAf L n → ℂ), (∀ x : GAf L n, TrivOutside {s.v} x → ∀ f ∈ P, NG.rt L n x f ∈ P) → Disjoint (LinearMap.range ((NG.rt L n y).comp T)) P ∨ LinearMap.range ((NG.rt L n y).comp T) ≤ P := by
  first | exact @GlobalTheory.SlocDich.translate_dichotomy | exact GlobalTheory.SlocDich.translate_dichotomy | (intros; apply GlobalTheory.SlocDich.translate_dichotomy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SwxsOfSiegelWeil
section
namespace GlobalTheory.St

theorem swxs_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.VolStabS.MassDataS.SWXS :=
  fun h _ X => GlobalTheory.St.siegelWeil_volumes h _ _ _ (MassDataVolumesW.stepCM X) _ _ (MassDataVolumesW.stepHerm X)

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairsRowLatticeCountedViaEmbeddingsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termPairs_rowLattice_counted_via_embeddings : GlobalTheory.TypeAsm.PerRowC := by
  first | exact @GlobalTheory.TypeAsm.perRowC | exact GlobalTheory.TypeAsm.perRowC | (intros; apply GlobalTheory.TypeAsm.perRowC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumRationalClassesEqProdLocalSums
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass

theorem datum_wt_nonneg {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} (p : PlF D)
    (a b : LocNG.Datum (FP p)) : 0 ≤ LocNG.Datum.wt a b := by
  unfold LocNG.Datum.wt LocNG.volRel
  exact div_nonneg zero_le_one (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem tsum_classes_eq_prod_locSums : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP) (R : ∀ p, LocNG.Reps (FP p)) (V : ℝ), 0 ≤ V → BaseOK (Tu D u) (Tu D u') F F' P d0 → MassLaw F F' P d0 V → ∀ φ : ∀ p, LocNG.Datum (FP p) → ℝ≥0∞, (∀ p d d', LocNG.Datum.Rel d d' → φ p d = φ p d') → (∀ p d, (¬ ∃ τ, LocNG.IsTermOver (FP p) d τ) → φ p d = 0) → (∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), if (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (o.out p)) ∧ {p | o.out p ≠ d0 p}.Finite then (((stabY F F' o.out).encard : ℝ≥0∞))⁻¹ * ∏ p ∈ P, φ p (o.out p) else 0) = ENNReal.ofReal V * ∏ p ∈ P, ∑' d : (R p).RD, ENNReal.ofReal (LocNG.Datum.wt (d0 p) d.1) * φ p d.1 := by
  intro D Z FP u u' F F' P d0 R V hV hB hM φ hφ hφ0
  have hEq : ∀ p, Equivalence (LocNG.Datum.Rel (P := FP p)) := fun p => GlobalTheory.NonGenericLocalCheck.rel_equiv (FP p)
  let rep : ∀ p, LocNG.Datum (FP p) → (R p).RD := fun p y =>
    ⟨Classical.choose ((R p).hRD.2.1 y (Set.mem_univ y)), (Classical.choose_spec ((R p).hRD.2.1 y (Set.mem_univ y))).1⟩
  have hrep : ∀ p y, LocNG.Datum.Rel (rep p y).1 y := fun p y =>
    (Classical.choose_spec ((R p).hRD.2.1 y (Set.mem_univ y))).2
  have huniq : ∀ p y (a : (R p).RD), LocNG.Datum.Rel a.1 y → a = rep p y := fun p y a ha =>
    Subtype.ext ((R p).hRD.2.2 _ a.2 _ (rep p y).2 ((hEq p).trans ha ((hEq p).symm (hrep p y))))
  let ext : (∀ p : P, (R p.1).RD) → Dat Z FP := fun x p => if h : p ∈ P then (x ⟨p, h⟩).1 else d0 p
  have ext_in : ∀ x (p : P), ext x p.1 = (x p).1 := fun x p => by simp [ext, p.2]
  have ext_out : ∀ x p, p ∉ P → ext x p = d0 p := fun x p hp => by simp [ext, hp]
  let g : ∀ p : P, (R p.1).RD → ℝ≥0∞ := fun p d => ENNReal.ofReal (LocNG.Datum.wt (d0 p.1) d.1) * φ p.1 d.1

  have hR : ENNReal.ofReal V * ∏ p ∈ P, ∑' d : (R p).RD, ENNReal.ofReal (LocNG.Datum.wt (d0 p) d.1) * φ p d.1
      = ∑' x : (∀ p : P, (R p.1).RD), ENNReal.ofReal V * ∏ p : P, g p (x p) := by
    rw [ENNReal.tsum_mul_left, GlobalTheory.HL.tsum_pi_prod_ennreal g, ← Finset.prod_coe_sort P]

  rw [hR]
  let c : Quot (GRel (Z := Z) (FP := FP) F F') → ℝ≥0∞ := fun o =>
    (((stabY F F' o.out).encard : ℝ≥0∞))⁻¹ * ∏ p ∈ P, φ p (o.out p)

  have hx : ∀ x : (∀ p : P, (R p.1).RD), ENNReal.ofReal V * ∏ p : P, g p (x p)
      = ∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), if InGen (ext x) o.out then c o else 0 := by
    intro x
    have h1 : ENNReal.ofReal V * ∏ p : P, g p (x p) = massA F F' (ext x) * ∏ p : P, φ p.1 (x p).1 := by
      by_cases hT : ∀ p : P, ∃ τ, LocNG.IsTermOver (FP p.1) (x p).1 τ
      · have hTall : ∀ p, ∃ τ, LocNG.IsTermOver (FP p) (ext x p) τ := by
          intro p
          by_cases hp : p ∈ P
          · rw [ext_in x ⟨p, hp⟩]; exact hT ⟨p, hp⟩
          · rw [ext_out x p hp]; exact hB.2.2.2.1 p
        rw [hM (ext x) (ext_out x) hTall, ENNReal.ofReal_mul hV,
          ENNReal.ofReal_prod_of_nonneg (fun p _ => datum_wt_nonneg p _ _), ← Finset.prod_coe_sort P, mul_assoc,
          ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl (fun p _ => ?_)
        simp only [g, ext_in x p]
      · push_neg at hT
        obtain ⟨p, hp⟩ := hT
        have h0 : φ p.1 (x p).1 = 0 := hφ0 p.1 _ (by push_neg; exact hp)
        rw [Finset.prod_eq_zero (Finset.mem_univ p) (by simp [g, h0]),
          Finset.prod_eq_zero (Finset.mem_univ p) h0, mul_zero, mul_zero]
    rw [h1, massA, ← ENNReal.tsum_mul_right]
    refine tsum_congr (fun o => ?_)
    split_ifs with hI
    · simp only [c]
      rw [← Finset.prod_coe_sort P (fun p => φ p (o.out p))]
      congr 1
      refine Finset.prod_congr rfl (fun p _ => ?_)
      have := hI.1 p.1
      rw [ext_in x p] at this
      exact hφ p.1 _ _ this
    · exact zero_mul _
  rw [tsum_congr hx, ENNReal.tsum_comm]
  refine tsum_congr (fun o => ?_)
  let x0 : ∀ p : P, (R p.1).RD := fun p => rep p.1 (o.out p.1)
  have hfin : ∀ x, {p | o.out p ≠ ext x p} ⊆ {p | o.out p ≠ d0 p} ∪ (P : Set (PlF D)) ∧
      {p | o.out p ≠ d0 p} ⊆ {p | o.out p ≠ ext x p} ∪ (P : Set (PlF D)) := by
    intro x
    constructor
    · intro p hp
      by_cases hpP : p ∈ P
      · exact Or.inr hpP
      · left; simpa [Set.mem_setOf_eq, ext_out x p hpP] using hp
    · intro p hp
      by_cases hpP : p ∈ P
      · exact Or.inr hpP
      · left; simpa [Set.mem_setOf_eq, ext_out x p hpP] using hp
  rw [tsum_eq_single x0]
  · have hiff : InGen (ext x0) o.out ↔ ((∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (o.out p)) ∧ {p | o.out p ≠ d0 p}.Finite) := by
      constructor
      · rintro ⟨hr, hf⟩
        refine ⟨fun p hp => ?_, ((hf.union P.finite_toSet).subset (hfin x0).2)⟩
        have := hr p; rwa [ext_out x0 p hp] at this
      · rintro ⟨hr, hf⟩
        refine ⟨fun p => ?_, ((hf.union P.finite_toSet).subset (hfin x0).1)⟩
        by_cases hp : p ∈ P
        · rw [ext_in x0 ⟨p, hp⟩]; exact hrep p _
        · rw [ext_out x0 p hp]; exact hr p hp
    simp only [hiff, c]
  · intro x hx
    rw [if_neg]
    rintro ⟨hr, _⟩
    apply hx
    funext p
    have := hr p.1
    rw [ext_in x p] at this
    exact huniq p.1 _ (x p) this

end GlobalTheory.GenMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ValuationLtOneIffNormLtOnePadicCmCompletionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_lt_one_iff_norm_lt_one_padic_cmCompletion : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (g : ℕ) [Fact g.Prime] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (j : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i → Continuous j → ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z < 1 ↔ ‖j.symm (i z)‖ < 1 := by
  first | exact @GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous | exact GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous | (intros; apply GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous <;> assumption)
end

