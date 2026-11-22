import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0458
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0449
import Formalism.LocalToGlobal.Columns.RecLevelTop

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelReductionCriterion
section
noncomputable section

namespace GlobalTheory.PrinFrame

section Alg

open Matrix

variable {A : Type} [CommRing A] {n : ℕ}

theorem conj_single_mem (S : Subring A) (p : S) (hp : p * p = p) (γ : GL (Fin n) A)
    (h : ∀ i j, i ≠ j → ∀ a b, (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S) (i j a b : Fin n) :
    (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S := by
  by_cases hij : i = j
  · subst hij
    by_cases hl : ∃ l, l ≠ i
    · obtain ⟨l, hl⟩ := hl
      have hp' : (p : A) * p = p := congrArg Subtype.val hp
      have e1 : ∑ c, γ.1 l c * (γ⁻¹).1 c l = 1 := by
        have := congrFun (congrFun γ.mul_inv l) l
        rwa [Matrix.mul_apply, Matrix.one_apply_eq] at this
      have e2 : (p : A) * ((γ⁻¹).1 a i * γ.1 i b) =
          ∑ c, ((p : A) * ((γ⁻¹).1 a i * γ.1 l c)) * ((p : A) * ((γ⁻¹).1 c l * γ.1 i b)) := by
        rw [← mul_one ((p : A) * _), ← e1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        linear_combination (-((γ⁻¹).1 a i * γ.1 i b * γ.1 l c * (γ⁻¹).1 c l)) * hp'
      rw [e2]
      exact S.sum_mem fun c _ => S.mul_mem (h i l hl.symm a c) (h l i hl c b)
    · push Not at hl
      have e1 : (γ⁻¹).1 i i * γ.1 i i = 1 := by
        have := congrFun (congrFun γ.inv_mul i) i
        rwa [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i (fun c _ hc => absurd (hl c) hc)
          (fun hc => absurd (Finset.mem_univ i) hc)] at this
      rw [hl a, hl b, e1, mul_one]
      exact p.2
  · exact h i j hij a b

theorem red_conj_eq_one (S : Subring A) {k : Type} [CommRing k] (ρ : S →+* k) (p : S) (hρ : ρ p = 1) (γ : GL (Fin n) A)
    (h : ∀ i j a b, (p : A) * ((γ⁻¹).1 a i * γ.1 j b) ∈ S) (y y₀ : Matrix (Fin n) (Fin n) S)
    (hy : y₀.map S.subtype = γ.1 * y.map S.subtype * (γ⁻¹).1) (h1 : y.map ρ = 1) : y₀.map ρ = 1 := by
  have e0 : ∀ {B : Type} [CommRing B] (f : S →+* B) (z : Matrix (Fin n) (Fin n) S), (z - 1).map f = z.map f - 1 := by
    intro B _ f z
    rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)]
  have e1 : (y₀ - 1).map S.subtype = γ.1 * (y - 1).map S.subtype * (γ⁻¹).1 := by
    rw [e0, e0, hy, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv]
  have e2 : ∀ b a, ρ ((y - 1) b a) = 0 := fun b a => by
    have := congrFun (congrFun (e0 ρ y) b) a
    rwa [h1, sub_self] at this
  rw [← sub_eq_zero, ← e0]
  ext j i
  have e3 : p * (y₀ - 1) j i = ∑ a, ∑ b, (⟨_, h i j a b⟩ : S) * (y - 1) b a := by
    apply Subtype.ext
    have := congrFun (congrFun e1 j) i
    rw [Matrix.map_apply, Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Subring.subtype_apply] at this
    rw [Subring.coe_mul, this]
    simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have e4 := congrArg ρ e3
  rw [map_mul, hρ, one_mul] at e4
  simp only [map_sum, map_mul, e2, mul_zero, Finset.sum_const_zero] at e4
  exact e4

theorem transv_entry (S : Subring A) (p : S) (β β₀ : GL (Fin n) A) (i j : Fin n) (z : Matrix (Fin n) (Fin n) S)
    (h : (p : A) • (β.1 * z.map S.subtype * (β⁻¹).1) =
      (p : A) • (β₀.1 * (Matrix.transvection i j (1 : S)).map S.subtype * (β₀⁻¹).1)) (a b : Fin n) :
    (p : A) * (((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b) ∈ S := by
  have h2 := congrArg (fun M => (β⁻¹).1 * M * β.1) h
  have e0 : (Matrix.transvection i j (1 : S)).map S.subtype = 1 + Matrix.single i j (1 : A) := by
    rw [Matrix.transvection, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_single,
      map_one]
  have e1 : (β⁻¹).1 * (β.1 * z.map S.subtype * (β⁻¹).1) * β.1 = z.map S.subtype := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have e2 : (β⁻¹).1 * (β₀.1 * (1 + Matrix.single i j (1 : A)) * (β₀⁻¹).1) * β.1 =
      1 + ((β₀⁻¹ * β)⁻¹).1 * Matrix.single i j (1 : A) * (β₀⁻¹ * β).1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Units.inv_mul, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
  simp only [Matrix.mul_smul, Matrix.smul_mul] at h2
  rw [e0, e1, e2] at h2
  have h3 := congrFun (congrFun h2 a) b
  have e3 : (((β₀⁻¹ * β)⁻¹).1 * Matrix.single i j (1 : A) * (β₀⁻¹ * β).1) a b =
      ((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b := by
    generalize ((β₀⁻¹ * β)⁻¹).1 = M
    generalize (β₀⁻¹ * β).1 = N
    simp [Matrix.mul_apply, Matrix.single, ite_and]
  simp only [Matrix.smul_apply, Matrix.add_apply, e3, smul_eq_mul, Matrix.map_apply, Subring.subtype_apply, mul_add] at h3
  rw [← sub_eq_iff_eq_add'] at h3
  rw [← h3]
  refine S.sub_mem (S.mul_mem p.2 (z a b).2) (S.mul_mem p.2 ?_)
  rw [Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

end Alg

end GlobalTheory.PrinFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrinFrame

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem redFn_eq_one_of_le (V : HSp D) (β β₀ : GL (Fin V.rank) (Lev.EAf D))
    (h₀ : Formalism.L2.DIV.IsFrame β₀ (Formalism.L2.Herm.crdLat V V.L0))
    (hle : ∀ κ ∈ GfC V, finE V κ ∈ Formalism.L2.DIV.St β₀ → finE V κ ∈ Formalism.L2.DIV.St β)
    (P : Formalism.L2.DIV.Pl D.host.E) (hP : ¬ Formalism.IndefR.Lev.IsConjPl P P) (x : GL (Fin V.rank) (Lev.EAf D))
    (hx : x ∈ Formalism.L2.DIV.St β) (hx₀ : x ∈ Formalism.L2.DIV.St β₀) (h1 : redFn β P x = 1) : redFn β₀ P x = 1 := by
  obtain ⟨β₁, h₁⟩ := GlobalTheory.StdFrames.exists_base V
  obtain ⟨c, hc⟩ := GlobalTheory.StdFrames.isSD_one h₁
  have hB : IsBaseFrame V β₀ (Formalism.L2.Herm.crdLat V V.L0) (1 ^ c) := ⟨h₀, hc.2⟩
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt hP
  obtain ⟨p, hp, hpp, hres⟩ := GlobalTheory.ParahoricLift.exists_idem_int he
  have hoff : ∀ i j, i ≠ j → ∀ a b, (p : Lev.EAf D) * (((β₀⁻¹ * β)⁻¹).1 a i * (β₀⁻¹ * β).1 j b) ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro i j hij
    have hu' : p * (Matrix.transvection i j (1 : Formalism.L2.Herm.intAf D.host.F D.host.E)).det = p := by
      rw [Matrix.det_transvection_of_ne i j hij, mul_one]
    have hmm := GlobalTheory.ParahoricLift.conj_inv_part β₀ p p _ hu' hpp
    rw [hp] at hmm
    obtain ⟨κ, hs, hκ⟩ := GlobalTheory.ParahoricLift.split_lift_fin V he.1 _ _ hmm
    have hPI : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
    obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
    have hsf := GlobalTheory.LevSplit.supp_fin V (f := e + cA D e) hs
    rw [← hp] at hκ
    have hf : GlobalTheory.LevSplit.finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
      rw [RingHom.map_add, GlobalTheory.LevSplit.finSw_cA, hp]
    have hSt : finE V κ ∈ Formalism.L2.DIV.St β₀ :=
      GlobalTheory.ParahoricLift.mem_St_of_part D.sp.cm.sig V.gram _ β₀ hB.1 (GlobalTheory.ParahoricLift.hatL_selfDual hB) p p hpp
        (GlobalTheory.LevSplit.sigR_int p.2) _ hu' (finE V κ) (GlobalTheory.LevSplit.finE_mem_UA V κ) _ hf hsf hκ
    obtain ⟨z, hz⟩ := hle κ ((T3 P e _ hPI).2.2.1 κ hs) hSt
    rw [← hz] at hκ
    exact transv_entry _ p β β₀ i j z.1 hκ
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y₀, hy₀⟩ := hx₀
  rw [redFn_frGL] at h1
  rw [← hy₀, redFn_frGL]
  have e1 : intGL D.host.F D.host.E V.rank y₀ = (β₀⁻¹ * β) * intGL D.host.F D.host.E V.rank y * (β₀⁻¹ * β)⁻¹ := by
    have e2 : β₀ * intGL D.host.F D.host.E V.rank y₀ * β₀⁻¹ = β * intGL D.host.F D.host.E V.rank y * β⁻¹ := hy₀
    rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq] at e2
    rw [e2]
    group
  exact Units.ext (red_conj_eq_one _ (resS D.host.F P) p hres (β₀⁻¹ * β) (conj_single_mem _ p hpp _ hoff) y.1 y₀.1
    (congrArg Units.val e1) (congrArg Units.val h1))

theorem kset_iff_finE (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0))
    (κ : GA D (D.sp.Y 0)) : (iotaX X h κ).2 ∈ X.B.I.Kset ↔ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ I.Kset ↔ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
    intro I hI
    subst hI
    have hL : (Formalism.L2.SG.InstExistsPf.instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 :=
      Formalism.L2.SG.InstExistsPf.Lv_eq_map D
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx := GlobalTheory.FlagBasis.kset_iff (Formalism.L2.SG.InstExistsPf.instOf D) (β := β) (hL ▸ hβ) (Formalism.IndefR.RationalEmbedding.iota D κ).2
    generalize Lev.finE (D.sp.Y 0) κ = y at e2 ⊢
    subst e2
    exact hx
  exact key X.B.I h

theorem edgeSum_symEdge_one {k : Type} [CommRing k] {n : ℕ} (ρ l : ℕ) : edgeSum (symEdge ρ l) (1 : GL (Fin n) k) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · refine Matrix.one_apply_ne ?_
    rintro rfl
    unfold symEdge at h
    omega
  · rfl

theorem rowChi_eq_one : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), GlobalTheory.Core.Mi.IdE X → ∀ (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D), (∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St β) ↔ ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset)) → ∀ κ ∈ rowJ X h, (∀ PP ∈ Pg, redFn β PP (finE (D.sp.Y 0) κ) = 1) → rowChi X h κ = 1 := by
  intro D X h _ Pg hPg hIdem β hβ κ hκ hred
  have hnc := GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces Pg hPg hIdem
  have hψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1 := fun PP => by
    haveI := PP.isPrime
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero
    exact ⟨ψ, fun e => hψ (by rw [e]; rfl)⟩
  choose ψ0 hψ0 using hψ
  obtain ⟨β₀, h₀, hK⟩ := GlobalTheory.SeeConjRead.read_fin X h Pg hPg hnc ψ0 fun PP _ => hψ0 PP
  have hle : ∀ κ ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β₀ → finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β :=
    fun κ h1 h2 => ((hβ κ).2 ⟨(GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h κ).2 h1, (kset_iff_finE X h β₀ h₀ κ).2 h2⟩).2
  have hS₀ := ((hK κ).1.1 hκ.2).1
  have hS := hle κ ((GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h κ).1 hκ.1) hS₀
  refine ((hK κ).2 hκ.2).trans (Finset.prod_eq_one fun PP hPP => ?_)
  rw [redFn_eq_one_of_le (D.sp.Y 0) β β₀ h₀ hle PP (hnc PP hPP PP hPP) _ hS hS₀ (hred PP hPP), edgeSum_symEdge_one,
    AddChar.map_zero_eq_one]

end GlobalTheory.PrinFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepLinearRelationsPeriods
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSawStep

variable {D : D7}

theorem per_smul_right {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (φ : GA D B.A → ℂ) (b : ℂ) (f : GA D B.V → ℂ) :
    B.per ψ φ (b • f) = b * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem per_smul_left {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (a : ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ (a • φ) f = a * B.per ψ φ f := by
  simp only [BesLev.per, besPer, besFun, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x
  rw [← integral_const_mul]
  congr 1; funext n; ring

theorem trc_smul {V : HSp D} (e : GA D V →₀ ℂ) (b : ℂ) (f : GA D V → ℂ) : trc e (b • f) = b • trc e f := by
  funext g
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

theorem liftS_smul {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (b : ℂ) (G : GA D T → ℂ)
    (f : WO S T → ℂ) : liftS om ν 𝓕 (b • G) f = b • liftS om ν 𝓕 G f := by
  funext g
  simp only [liftS_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem rapidDec_smul {V : HSp D} (b : ℂ) (F : GA D V → ℂ) (hF : RapidDec V F) : RapidDec V (b • F) := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨fun γ hγ g => by simp only [Pi.smul_apply, h1 γ hγ g], h2.const_smul b, fun N => ?_⟩
  obtain ⟨C, hC⟩ := h3 N
  refine ⟨‖b‖ * C, fun g => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg b)

theorem contAut_zero (V : HSp D) : IsContAut V (fun _ => (0 : ℂ)) := ⟨fun _ _ _ => rfl, continuous_const⟩

theorem perF_smul {c : Comm D} (tt : Tup c) (n ρ : ℕ) (h : n + 2 * ρ + 2 = D.R.m) (φ : tt.Ch n → GA D (c.X n) → ℂ) (b : ℂ)
    (f : GA D (c.V n) → ℂ) : tt.perF n ρ h φ (b • f) = b * tt.perF n ρ h φ f := by
  simp only [Tup.perF, trc_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => per_smul_right _ _ _ _ _

theorem perF_comb (hPS : PerSum D) {c : Comm D} (hc : c.Is) (tt : Tup c) (n ρ : ℕ) (h : n + 2 * ρ + 2 = D.R.m) (k : ℂ)
    (co : c.Fr n →₀ ℂ) (φ : tt.Ch n → c.Fr n → GA D (c.X n) → ℂ) (hφ : ∀ β y, IsContAut (c.X n) (φ β y))
    (f : GA D (c.V n) → ℂ) (hf : IsContAut (c.V n) f) :
    tt.perF n ρ h (fun β => k • ∑ y' ∈ co.support, co y' • φ β y') f =
      k * ∑ y' ∈ co.support, co y' * tt.perF n ρ h (fun β => φ β y') f := by
  have e : ∀ β, (c.B n ρ h).per c.ψ (k • ∑ y' ∈ co.support, co y' • φ β y') (trc (tt.e n β) f) =
      k * ∑ y' ∈ co.support, co y' * (c.B n ρ h).per c.ψ (φ β y') (trc (tt.e n β) f) := by
    intro β
    have hT : IsContAut _ (trc (tt.e n β) f) :=
      (((GlobalTheory.T.besselPeriod_linear_and_translationCombination D c.ψ hc.std ρ (c.B n ρ h) (fun _ => 0) (contAut_zero _)).2 (tt.e n β) f hf).1)
    rw [per_smul_left]
    congr 1
    exact hPS c.ψ hc.std ρ (c.B n ρ h) (trc (tt.e n β) f) hT (c.Fr n) co.support co (fun y' => φ β y') (fun y' _ => hφ β y')
  simp only [Tup.perF, e]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.mul_sum]

set_option maxHeartbeats 2000000 in

theorem stepX_of_laws : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), DoubleStep D →
    RapidVal D → ValMove D → PerSum D → c.Is → (∀ s, (t s).Is) → (∀ s, (t s).LocFin) → ValX t → TwoX t → RdX t → StepX t := by
  intro hHC D c 𝒯 t hDS hRV hVM hPS hc ht hloc hVal hTwo hRd
  intro j σ h I _ s α ψ G hψ hvan y v
  obtain ⟨χ0, hχ0⟩ := hRd j (by omega)
  have hφ : ∀ i a, IsContAut (c.X j) ((t (s i)).rd j a (ψ i) y) := fun i a => (hχ0 (s i) (ψ i) (hψ i) a y).1
  have hspan : GlobalTheory.Core.Mi.ItSpans (c.M (j + 1)) (c.M (j + 1 + 1)) (c.It (j + 1)) := hc.span (j + 1) (by omega)
  simp only [Tup.per]
  refine GlobalTheory.T.period_linear_relation_density_of_unfolding_steps hHC D c 𝒯 t hc j (σ + 1) h I s (fun i => α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)))
    (fun i a => (t (s i)).rd j a (ψ i) y) (fun i => (t (s i)).io j ((t (s i)).io (j + 1) (G i))) ht hφ
    (c.V (j + 1 + 1)) (c.V (j + 1 + 1)) (c.par (j + 1 + 1)) (c.M (j + 1 + 1)) (c.It (j + 1)) hspan ?_ v
  intro P₁ P₂ v''
  have key : ∀ i, ((t (s i)).cI j * (t (s i)).cI (j + 1)) •
      ((t (s i)).io j ((t (s i)).io (j + 1) (G i))).1 (c.It j P₁ (c.It (j + 1) P₂ v'')) =
      liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 ((G i).1 v'') ((t (s i)).pt (j + 1) P₂))
        ((t (s i)).pt j P₁) := by
    intro i
    rw [(ht (s i)).io (j + 1) (by omega) (G i) P₂ v'', liftS_smul, (ht (s i)).io j (by omega) _ P₁ _, smul_smul, mul_comm]
  have e : ∀ i, α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)) * (t (s i)).perF j (σ + 1) h (fun a => (t (s i)).rd j a (ψ i) y)
      (((t (s i)).io j ((t (s i)).io (j + 1) (G i))).1 (c.It j P₁ (c.It (j + 1) P₂ v''))) =
      α i * (t (s i)).perF j (σ + 1) h (fun a => (t (s i)).rd j a (ψ i) y)
        (liftS ((t (s i)).om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
          (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 ((G i).1 v'') ((t (s i)).pt (j + 1) P₂))
          ((t (s i)).pt j P₁)) := by
    intro i
    rw [← key i, perF_smul, mul_assoc]
  rw [Finset.sum_congr rfl fun i _ => e i]
  have hR0 : ∀ i, RapidDec _ ((G i).1 v'') := by
    intro i
    obtain ⟨J, χ, hJ⟩ := (ht (s i)).CC (j + 1 + 1) (by omega)
    exact hRV c.θ hc.inf _ _ (c.M (j + 1 + 1)) J χ (G i).1 (hJ (G i).2) v''
  have hR1 : ∀ i, RapidDec _ (liftS ((t (s i)).om (j + 1)) (c.vol (j + 1 + 1)).μ (c.vol (j + 1 + 1)).𝓕 ((G i).1 v'')
      ((t (s i)).pt (j + 1) P₂)) := by
    intro i
    rw [(ht (s i)).io (j + 1) (by omega) (G i) P₂ v'']
    obtain ⟨J, χ, hJ⟩ := (ht (s i)).CC (j + 1) (by omega)
    exact rapidDec_smul _ _ (hRV c.θ hc.inf _ _ (c.M (j + 1)) J χ _ (hJ ((t (s i)).io (j + 1) (G i)).2) _)
  refine GlobalTheory.T.seeSaw_periods_linearRelations_doubleStep D c 𝒯 t hDS hc ht hloc j σ h P₁ P₂ I s α (fun i a => (t (s i)).rd j a (ψ i) y) (fun i => (G i).1 v'')
    hφ hR0 hR1 ?_
  intro a ha a' ha'
  obtain ⟨C, hC, hCe⟩ := hVal j σ h P₁ P₂ a ha a' ha'
  obtain ⟨co, hco⟩ := hTwo j (by omega) C hC y
  obtain ⟨sm, hsm⟩ := GlobalTheory.RealTransSm.rTrans_eq_map D c.θ (c.V (j + 1 + 1)) (c.par (j + 1 + 1)) (c.M (j + 1 + 1)) hc.inf a' ha'
  refine ⟨fun i => (t (s i)).cV j * (t (s i)).perF (j + 1 + 1) σ (idx_step h)
      ((t (s i)).two j (fun a => (t (s i)).rd j a ((t (s i)).S j (ψ i)) y) C) (rTrans a' ((G i).1 v'')),
    fun i => hCe (s i) (ψ i) (hψ i) y (G i) v'', ?_⟩
  obtain ⟨χ2, hχ2⟩ := hRd (j + 1 + 1) (by omega)
  have hψ'' : ∀ i, (t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i))) ∈ (t (s i)).Ram (j + 1 + 1) := fun i =>
    (ht (s i)).stabK (j + 1) (by omega) _ ((ht (s i)).stabK j (by omega) _ ((ht (s i)).stabS j (by omega) _ (hψ i)))
  have term : ∀ i, α i * ((t (s i)).cV j * (t (s i)).perF (j + 1 + 1) σ (idx_step h)
      ((t (s i)).two j (fun a => (t (s i)).rd j a ((t (s i)).S j (ψ i)) y) C) (rTrans a' ((G i).1 v''))) =
      ∑ y' ∈ co.support, co y' * (α i * ((t (s i)).cV j * (t (s i)).cK j * (t (s i)).cK (j + 1)) *
        (t (s i)).per (j + 1 + 1) σ (idx_step h) ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (G i) y' (sm v'')) := by
    intro i
    obtain ⟨J, χ, hJ⟩ := (ht (s i)).CC (j + 1 + 1) (by omega)
    have hw : rTrans a' ((G i).1 v'') = (G i).1 (sm v'') := (hsm J χ (G i).1 (hJ (G i).2) v'').symm
    have htwo : (t (s i)).two j (fun a => (t (s i)).rd j a ((t (s i)).S j (ψ i)) y) C = fun β =>
        ((t (s i)).cK j * (t (s i)).cK (j + 1)) • ∑ y' ∈ co.support, co y' •
          (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y' :=
      funext (hco (s i) _ ((ht (s i)).stabS j (by omega) _ (hψ i)))
    have hGw : RapidDec _ ((G i).1 (sm v'')) := hRV c.θ hc.inf _ _ (c.M (j + 1 + 1)) J χ (G i).1 (hJ (G i).2) _
    rw [hw, htwo, perF_comb hPS hc _ _ _ _ _ co _ (fun β y' => (hχ2 (s i) _ (hψ'' i) β y').1) _ ⟨hGw.1, hGw.2.1⟩]
    simp only [Tup.per, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y' _ => by ring
  rw [Finset.sum_congr rfl fun i _ => term i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun y' _ => ?_
  rw [← Finset.mul_sum, hvan y' (sm v''), mul_zero]

end GlobalTheory.SeeSawStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.LeftInvSect
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model
variable {D : D7} {n : ℕ}

theorem rat_mat {γ : G D n} (h : γ ∈ GF D n) :
    ∃ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) := by
  obtain ⟨x, -, hx⟩ := h
  exact ⟨x.1, (congrArg Units.val hx).symm⟩

theorem det_rat {γ : G D n} (h : γ ∈ GF D n) (a : GL (Fin n) (AE D)) (ha : blkA (mat γ) = a.1) :
    ∃ u : D.host.Eˣ, Matrix.GeneralLinearGroup.det a = Units.map (incA D).toMonoidHom u := by
  haveI : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))
  haveI : Nontrivial (AE D) := inferInstance
  obtain ⟨x, hx⟩ := rat_mat h
  have e : ((Matrix.GeneralLinearGroup.det a : (AE D)ˣ) : AE D) = incA D (blkA x).det := by
    rw [RingHom.map_det]
    change a.1.det = _
    rw [← ha, hx]; rfl
  have h0 : (blkA x).det ≠ 0 := fun h0 => Units.ne_zero _ (e.trans (by rw [h0, map_zero]))
  exact ⟨Units.mk0 _ h0, Units.ext e⟩

theorem siegelParabolicUnn_matrix_blockUpperTriangular {p : G D n} (hp : p ∈ P D n) : ∃ b d, mat p = blk4 (blkA (mat p)) b 0 d := by
  refine ⟨((mat p).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    ((mat p).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · exact lower_eq_zero hp i j
  · rfl

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : G D n) = 1 := rfl

theorem levi_mul_inv (a : GL (Fin n) (AE D)) :
    (blk4 a.1 0 0 (adj (a⁻¹).1) : Mx D (n + n) (n + n)) * blk4 (a⁻¹).1 0 0 (adj a.1) = 1 := by
  have h2 : (adj (a⁻¹).1 : Mx D n n) * adj a.1 = 1 := by rw [← adj_mul]; simp [adj_one]
  simp [submatrix_fromBlocks_mul, h2, block_matrix_one, -Matrix.coe_units_inv]

theorem exists_levi_unip {p : G D n} (hp : p ∈ P D n) (a : GL (Fin n) (AE D)) (ha' : blkA (mat p) = a.1) :
    ∃ (m u : G D n) (b : Mx D n n), p = m * u ∧ mat m = blk4 a.1 0 0 (adj (a⁻¹).1) ∧ mat u = blk4 1 b 0 1 := by
  obtain ⟨m, hm⟩ := exists_levi a
  obtain ⟨m', hm'⟩ := exists_levi a⁻¹
  obtain ⟨b, d, hb⟩ := siegelParabolicUnn_matrix_blockUpperTriangular hp
  rw [ha'] at hb
  rw [inv_inv] at hm'
  have hu : mat (m' * p) = blk4 1 ((a⁻¹).1 * b) 0 (adj a.1 * d) := by
    rw [mat_mul, hm', hb, submatrix_fromBlocks_mul]
    simp [-Matrix.coe_units_inv]
  have hd : (adj a.1 : Mx D n n) * d = 1 := by
    have h : adj (mat (m' * p)) * JR (AF D.host.F) (Jst D n) * mat (m' * p) = JR (AF D.host.F) (Jst D n) := (m' * p).2
    rw [JR_Jst, hu] at h
    generalize (adj a.1 : Mx D n n) * d = d' at h ⊢
    generalize (a⁻¹).1 * b = b' at h
    simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, adj_one, adj_zero, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, mul_neg,
      neg_mul, neg_zero] at h
    exact (blockMatrixTwoByTwoFin_injective h).2.1
  have hmm : m * m' = 1 := mat_inj (by rw [mat_mul, mat_one, hm, hm', levi_mul_inv])
  refine ⟨m, m' * p, (a⁻¹).1 * b, by rw [← mul_assoc, hmm, one_mul], hm, by rw [hu, hd]⟩

theorem exists_blkA {p : G D n} (hp : p ∈ P D n) : ∃ a : GL (Fin n) (AE D), blkA (mat p) = a.1 :=
  ⟨levi (D := D) (n := n) ⟨p, hp⟩, rfl⟩

theorem height_inv (hI : ∀ g : G D n, ∃ p ∈ P D n, ∃ k ∈ K D n, g = p * k) {H : G D n → ℝ≥0} (hH : IsHeight H)
    {γ : G D n} (hp : γ ∈ P D n) (a : GL (Fin n) (AE D)) (ha : blkA (mat γ) = a.1)
    (h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1) (g : G D n) : H (γ * g) = H g := by
  obtain ⟨p, hp', k, hk, rfl⟩ := hI g
  obtain ⟨c, hc⟩ := exists_blkA hp'
  have e : blkA (mat (γ * p)) = (a * c).1 := by rw [blkA_mul hp', ha, hc, Units.val_mul]
  rw [← mul_assoc, hH _ ((P D n).mul_mem hp hp') (a * c) e k hk, hH p hp' c hc k hk, map_mul, map_mul, h1, one_mul]

theorem leftInv_sect : ∀ (D : D7) (n : ℕ), (∀ g : GlobalTheory.StdUnn.G D n, ∃ p ∈ GlobalTheory.StdUnn.P D n, ∃ k ∈ GlobalTheory.StdUnn.K D n, g = p * k) → ∀ (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : GlobalTheory.StdUnn.G D n →* Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n)), IsHeckeChar D χ → GlobalTheory.StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ H : GlobalTheory.StdUnn.G D n → ℝ≥0, GlobalTheory.StdUnn.IsHeight H → ∀ (Φ : GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ V.rank n) (z : ℂ), GlobalTheory.AutomorphicL2Unitary.LeftInv (GlobalTheory.StdUnn.P D n ⊓ GlobalTheory.StdUnn.GF D n) (GlobalTheory.StdUnn.sect ω H Φ z) := by
  intro D n hI V ψ χ θ μ ω hχ hω H hH Φ z γ hγ g
  obtain ⟨hp, hr⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨a, ha⟩ := exists_blkA hp
  obtain ⟨u, hu⟩ := det_rat hr a ha
  have h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact absE_inclR u
  have h2 : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
    rw [hu]; exact hχ.2 u
  have hHe : H (γ * g) = H g := height_inv hI hH hp a ha h1 g
  have hW : (ω (γ * g) Φ).1 0 = (ω g Φ).1 0 := by
    obtain ⟨m, v, b, e, hm, hv⟩ := exists_levi_unip hp a ha
    have e' : ω (γ * g) Φ = ω m (ω v (ω g Φ)) := by
      rw [e, map_mul, map_mul]; rfl
    have z1 : ∀ a : Mx D n n, ((0 : Mx D V.rank n) ⬝ a : Mx D V.rank n) = 0 := fun a => Matrix.zero_mul a
    have z2 : StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
    rw [e', hω.levi m _ hm, h1, h2, z1, hω.unip v b hv, z2]
    simp [halfTr, npow]
  simp only [sect, hHe, hW]

end GlobalTheory.StdUnn.LeftInvSect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelSectionWeylElementEqSchrodingerIntegralStatement
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelSection_weylElement_eq_schrodingerIntegral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ w, IsWeyl A w → swSec A B omh ν 𝓨 f w = ∫ x, sch ψ A B ν 𝓨 f x ∂ν := by
  first | exact @GlobalTheory.Core.Rk.WeylValue.swSec_weyl | exact GlobalTheory.Core.Rk.WeylValue.swSec_weyl | (intros; apply GlobalTheory.Core.Rk.WeylValue.swSec_weyl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepLevelContainsUnitaryNearOneStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepLevel_contains_unitary_near_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (Q : Finset (HeightOneSpectrum (𝓞 E))), ∃ d : ℕ, ∀ z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), z ∈ Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ w ∉ Q, GlobalTheory.Mem.ColAd.locM w z = 1) → (∀ w ∈ Q, GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z - 1) ∧ GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z⁻¹ - 1)) → z ∈ S.U := by
  first | exact @GlobalTheory.LevelApprox.mem_U_of_near_one | exact GlobalTheory.LevelApprox.mem_U_of_near_one | (intros; apply GlobalTheory.LevelApprox.mem_U_of_near_one <;> assumption)
end

