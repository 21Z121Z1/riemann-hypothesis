import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTrigPolynomialAnnihilatingAdelicSchwartz
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0459
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardUnitaryFrameConjEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardUnitary_frameConj_eq : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ M : GL (Fin V.rank) (Lev.EAf D), M ∈ UA D.sp.cm V.gram → ∃ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 = M := by
  first | exact @GlobalTheory.FrameTransport.exists_frConj_eq | exact GlobalTheory.FrameTransport.exists_frConj_eq | (intros; apply GlobalTheory.FrameTransport.exists_frConj_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrigPolynomialIndicatorAwayFromPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.OffVTrig

variable {F : Type} [Field F] [NumberField F]

abbrev ev1 (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Af F := GlobalTheory.AdelicU.singleFin v 1

abbrev gv (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Af F := 1 - ev1 v

theorem finiteAdeleIndicatorAtPlace_mul_self (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : ev1 v * ev1 v = ev1 v := by
  rw [ev1, ← GlobalTheory.AdelicU.singleFin_mul, mul_one]

theorem finiteAdeleIndicatorAtPlace_mul_awayFromPlace (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : ev1 v * gv v = 0 := by
  rw [gv, mul_sub, mul_one, finiteAdeleIndicatorAtPlace_mul_self, sub_self]

variable {κ : Type} [Fintype κ]

def offV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (u : κ → Af F) : κ → Af F := fun i => gv v * u i

theorem continuous_offV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Continuous (offV (κ := κ) v) :=
  continuous_pi fun i => continuous_const.mul (continuous_apply i)

theorem vecFin_sub (u u' : κ → Af F) :
    GlobalTheory.FinTrig.vecFin (u - u') = GlobalTheory.FinTrig.vecFin u - GlobalTheory.FinTrig.vecFin u' := by
  funext i
  exact Prod.ext (show (0 : InfiniteAdeleRing F) = 0 - 0 by rw [sub_zero]) rfl

theorem exists_lev_subset (y : κ → Af F) (V : Set (κ → Af F)) (hV : IsOpen V) (hy : y ∈ V) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ {u | GlobalTheory.FinTrig.Lev d (u - y)} ⊆ V := by
  have h1 : (fun z : κ → Af F => y + z) ⁻¹' V ∈ nhds (0 : κ → Af F) :=
    (hV.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa using hy)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, _, t, ht, hsub⟩ := h1
  have hW : (⋂ i, t i) ∈ nhds (0 : Af F) := Filter.iInter_mem.mpr fun i => ht i
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun u hu => ?_⟩
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd0
  have hmem : ∀ i, u i - y i ∈ ⋂ j, t j := by
    intro i
    have e : u i - y i = algebraMap F (Af F) (algebraMap (𝓞 F) F d) *
        (algebraMap F (Af F) ((d : F)⁻¹) * (u i - y i)) := by
      rw [← mul_assoc, ← map_mul]
      change _ = algebraMap F (Af F) ((d : F) * (d : F)⁻¹) * _
      rw [mul_inv_cancel₀ hd', map_one, one_mul]
    rw [e]; exact hd _ (hu i)
  have : (fun z : κ → Af F => y + z) (u - y) ∈ V := hsub (fun i _ => Set.mem_iInter.mp (hmem i) i)
  simpa using this

def Freq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Set (κ → AF F) := {b | ∀ i, (b i).1 = 0 ∧ ev1 v * (b i).2 = 0}

theorem zero_mem_freq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : (0 : κ → AF F) ∈ Freq v := fun i =>
  ⟨rfl, show ev1 v * (0 : Af F) = 0 from mul_zero _⟩

theorem add_mem_freq {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {b b' : κ → AF F} (h : b ∈ Freq v) (h' : b' ∈ Freq v) :
    b + b' ∈ Freq v := fun i =>
  ⟨show (b i).1 + (b' i).1 = 0 by rw [(h i).1, (h' i).1, add_zero],
    show ev1 v * ((b i).2 + (b' i).2) = 0 by rw [mul_add, (h i).2, (h' i).2, add_zero]⟩

def TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : Submodule ℂ ((κ → AF F) → ℂ) :=
  Submodule.span ℂ (GlobalTheory.FinTrig.chi ψ '' (Freq v))

theorem chi_mem_TPv (ψ : AddChar (AF F) ℂ) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {b : κ → AF F} (hb : b ∈ Freq v) :
    GlobalTheory.FinTrig.chi ψ b ∈ TPv ψ v :=
  Submodule.subset_span ⟨b, hb, rfl⟩

theorem one_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : (1 : (κ → AF F) → ℂ) ∈ TPv ψ v := by
  rw [← GlobalTheory.FinTrig.chi_zero ψ]; exact chi_mem_TPv ψ (zero_mem_freq v)

theorem mul_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {f g : (κ → AF F) → ℂ}
    (hf : f ∈ TPv ψ v) (hg : g ∈ TPv ψ v) : f * g ∈ TPv ψ v := by
  have hle : TPv ψ v * TPv ψ v ≤ TPv (κ := κ) ψ v := by
    rw [TPv, Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ⟨q, hq, rfl⟩, b, ⟨q', hq', rfl⟩, rfl⟩
    exact ⟨q + q', add_mem_freq hq hq', (GlobalTheory.FinTrig.chi_mul ψ q q').symm⟩
  exact hle (Submodule.mul_mem_mul hf hg)

theorem prod_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {ι : Type} (t : Finset ι)
    (f : ι → (κ → AF F) → ℂ) (h : ∀ a ∈ t, f a ∈ TPv ψ v) : (∏ a ∈ t, f a) ∈ TPv ψ v :=
  Finset.prod_induction f (· ∈ TPv ψ v) (fun _ _ => mul_mem_TPv ψ v) (one_mem_TPv ψ v) h

theorem exists_of_mem_TPv (ψ : AddChar (AF F) ℂ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {P : (κ → AF F) → ℂ}
    (h : P ∈ TPv ψ v) :
    ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ q ∈ s, q ∈ Freq v) ∧
      ∀ x, P x = ∑ q ∈ s, c q * ψ (x ⬝ᵥ q) := by
  rw [TPv, Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, rfl⟩ := h
  refine ⟨l.support, l, fun q hq => (Finsupp.mem_supported ℂ l).1 hl hq, fun x => ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
  rfl

def killV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (q : κ → AF F) : κ → AF F := fun i => ((0 : InfiniteAdeleRing F), gv v * (q i).2)

theorem killV_mem (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (q : κ → AF F) : killV v q ∈ Freq v := fun i =>
  ⟨rfl, show ev1 v * (gv v * (q i).2) = 0 by rw [← mul_assoc, finiteAdeleIndicatorAtPlace_mul_awayFromPlace, zero_mul]⟩

theorem dot_killV (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (q x : κ → AF F) :
    x ⬝ᵥ killV v q = GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2)) ⬝ᵥ q := by
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => Prod.ext ?_ ?_
  · show (x i).1 * 0 = 0 * (q i).1
    rw [mul_zero, zero_mul]
  · show (x i).2 * (gv v * (q i).2) = (gv v * (x i).2) * (q i).2
    ring

end GlobalTheory.OffVTrig

namespace GlobalTheory.OffVTrig

theorem exists_offV_indicator_poly : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ K : Set (κ → Af F), IsCompact K → ∀ (y : κ → AF F) (V : Set (κ → Af F)), IsOpen V → (fun i => (y i).2) ∈ V →
    ∃ (A : Set (κ → Af F)) (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ),
      IsOpen A ∧ (fun i => (y i).2) ∈ A ∧ (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
      (∀ x z : κ → AF F, GlobalTheory.LatVac.liftV v 1 • z = z →
        ((fun i => ((x + z) i).2) ∈ A ↔ (fun i => (x i).2) ∈ A)) ∧
      (∀ x : κ → AF F, (fun i => (x i).2) ∈ A →
        (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) ∈ V) ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ K →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = A.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2) := by
  intro F _ _ κ _ v ψ hψ _ K hK y V hV hyV
  classical
  obtain ⟨d, -, hdV⟩ := exists_lev_subset (fun i => (y i).2) V hV hyV
  have hPc := continuous_offV (κ := κ) v
  have hAo : IsOpen {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} :=
    (GlobalTheory.FinTrig.isOpen_lev d (offV v (fun i => (y i).2))).preimage hPc
  set C := offV v '' K ∩ {z | GlobalTheory.FinTrig.Lev d (z - offV v (fun i => (y i).2))}ᶜ with hCdef
  have hC : IsCompact C :=
    (hK.image hPc).inter_right (GlobalTheory.FinTrig.isOpen_lev d (offV v (fun i => (y i).2))).isClosed_compl
  obtain ⟨t, htC, hcov⟩ := hC.elim_nhds_subcover (fun a => {z | GlobalTheory.FinTrig.Lev d (z - a)})
    (fun a _ => (GlobalTheory.FinTrig.isOpen_lev d a).mem_nhds
      (by simp only [Set.mem_setOf_eq, sub_self]; exact GlobalTheory.FinTrig.lev_zero d))
  have hsep : ∀ a ∈ C, ∃ q ∈ (GlobalTheory.FinTrig.Q0 : Set (κ → AF F)),
      ψ (GlobalTheory.FinTrig.vecFin (a - offV v (fun i => (y i).2)) ⬝ᵥ q) ≠ 1 ∧
      ∀ u, GlobalTheory.FinTrig.Lev d u → ψ (GlobalTheory.FinTrig.vecFin u ⬝ᵥ q) = 1 :=
    fun a ha => GlobalTheory.FinTrig.exists_sep ψ hψ d (a - offV v (fun i => (y i).2)) ha.2
  choose! q _ hq1 hq2 using hsep
  set c : (κ → Af F) → ℂ := fun a => ψ (GlobalTheory.FinTrig.vecFin (a - offV v (fun i => (y i).2)) ⬝ᵥ q a) with hc
  set φ : (κ → Af F) → (κ → AF F) → ℂ := fun a =>
    (1 - c a)⁻¹ • (ψ (-(GlobalTheory.FinTrig.vecFin (offV v (fun i => (y i).2)) ⬝ᵥ q a)) •
      GlobalTheory.FinTrig.chi ψ (killV v (q a)) - c a • 1) with hφ
  have hφx : ∀ a x, φ a x = (1 - c a)⁻¹ *
      (ψ (GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2) - offV v (fun i => (y i).2)) ⬝ᵥ q a) - c a) := by
    intro a x
    have e1 : ψ (-(GlobalTheory.FinTrig.vecFin (offV v (fun i => (y i).2)) ⬝ᵥ q a)) * ψ (x ⬝ᵥ killV v (q a)) =
        ψ (GlobalTheory.FinTrig.vecFin (offV v (fun i => (x i).2) - offV v (fun i => (y i).2)) ⬝ᵥ q a) := by
      rw [← AddChar.map_add_eq_mul, dot_killV, vecFin_sub, sub_dotProduct, neg_add_eq_sub]
    simp only [hφ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, GlobalTheory.FinTrig.chi, Pi.one_apply, mul_one]
    rw [e1]
  have hφmem : ∀ a ∈ t, φ a ∈ TPv ψ v := fun a _ =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (chi_mem_TPv ψ (killV_mem v (q a))))
      (Submodule.smul_mem _ _ (one_mem_TPv ψ v)))
  obtain ⟨s, cc, hs, hPs⟩ := exists_of_mem_TPv ψ v (prod_mem_TPv ψ v t φ hφmem)
  refine ⟨{u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))}, s, cc, hAo, ?_, ?_, ?_, ?_, ?_⟩
  · show GlobalTheory.FinTrig.Lev d (offV v (fun i => (y i).2) - offV v (fun i => (y i).2))
    rw [sub_self]; exact GlobalTheory.FinTrig.lev_zero d
  · intro b hb
    funext i
    exact Prod.ext (show (0 : InfiniteAdeleRing F) * (b i).1 = 0 from zero_mul _)
      (show ev1 v * (b i).2 = 0 from (hs b hb i).2)
  · intro x z hz
    have hz2 : ∀ i, gv v * (z i).2 = 0 := by
      intro i
      have h1 : ((GlobalTheory.LatVac.liftV v 1 • z) i).2 = ev1 v * (z i).2 := rfl
      rw [hz] at h1
      rw [h1, ← mul_assoc, mul_comm (gv v), finiteAdeleIndicatorAtPlace_mul_awayFromPlace, zero_mul]
    have e : offV v (fun i => ((x + z) i).2) = offV v (fun i => (x i).2) := by
      funext i
      show gv v * ((x i).2 + (z i).2) = gv v * (x i).2
      rw [mul_add, hz2 i, add_zero]
    show GlobalTheory.FinTrig.Lev d (offV v _ - _) ↔ GlobalTheory.FinTrig.Lev d (offV v _ - _)
    rw [e]
  · intro x hx
    apply hdV
    show GlobalTheory.FinTrig.Lev d (_ - _)
    have e : (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) - (fun i => (y i).2) =
        offV v (fun i => (x i).2) - offV v (fun i => (y i).2) := by
      funext i
      show (x i).2 + (ev1 v * (y i).2 - ev1 v * (x i).2) - (y i).2 = gv v * (x i).2 - gv v * (y i).2
      simp only [gv]; ring
    rw [e]; exact hx
  · intro x hxK
    rw [← hPs x, Finset.prod_apply]
    by_cases hxA : GlobalTheory.FinTrig.Lev d (offV v (fun i => (x i).2) - offV v (fun i => (y i).2))
    · rw [Set.indicator_of_mem (show (fun i => (x i).2) ∈
          {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} from hxA)]
      refine Finset.prod_eq_one fun a ha => ?_
      rw [hφx a x, hq2 a (htC a ha) _ hxA]
      have hne : 1 - c a ≠ 0 := sub_ne_zero.mpr (Ne.symm (hq1 a (htC a ha)))
      exact inv_mul_cancel₀ hne
    · rw [Set.indicator_of_notMem (show (fun i => (x i).2) ∉
          {u | GlobalTheory.FinTrig.Lev d (offV v u - offV v (fun i => (y i).2))} from hxA)]
      have hxC : offV v (fun i => (x i).2) ∈ C := ⟨⟨_, hxK, rfl⟩, hxA⟩
      obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.mp (hcov hxC)
      refine Finset.prod_eq_zero hat ?_
      rw [hφx a x]
      have e : offV v (fun i => (x i).2) - offV v (fun i => (y i).2) =
          (offV v (fun i => (x i).2) - a) + (a - offV v (fun i => (y i).2)) := (sub_add_sub_cancel _ _ _).symm
      rw [e, GlobalTheory.FinTrig.vecFin_add, add_dotProduct, AddChar.map_add_eq_mul, hq2 a (htC a hat) _ hxa, one_mul,
        sub_self, mul_zero]

end GlobalTheory.OffVTrig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCarryHyperbolicFamilyWittFrame
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.WittCarry

theorem exists_GF_carry_hyperbolic : ∀ {D : D7} {V : HSp D} (Φ : WittFrame V) {a : ℕ} (ha : a ≤ wittIndex V) (x x' : Fin a → V.V), LinearIndependent D.host.E (Sum.elim x x') → (∀ i j, V.hD (x i) (x j) = 0) → (∀ i j, V.hD (x' i) (x' j) = 0) → (∀ i j, V.hD (x i) (x' j) = if i = j then 1 else 0) → ∃ g : GF V, ∀ i, GlobalTheory.Cusp.ratAct D.sp.cm V g (x i) = Φ.e (Fin.castLE ha i) ∧ GlobalTheory.Cusp.ratAct D.sp.cm V g (x' i) = Φ.f (Fin.castLE ha i) := by
  intro D V Φ a ha x x' hli h1 h2 h3
  classical
  have hs : ∀ u w, star (V.hT u w) = V.hT w u := fun u w => V.herm.eq u w
  have hn : ∀ u, (∀ w, V.hT u w = 0) → u = 0 := fun u hu => V.nondeg.1 u hu
  have sw : ∀ u w, V.hD u w = star (V.hD w u) := fun u w => (hs u w).symm
  have hcast : ∀ i j : Fin a, (Fin.castLE ha i = Fin.castLE ha j) ↔ i = j :=
    fun i j => (Fin.castLE_injective ha).eq_iff
  let e' : Fin a → V.V := fun i => Φ.e (Fin.castLE ha i)
  let f' : Fin a → V.V := fun i => Φ.f (Fin.castLE ha i)
  have hli' : LinearIndependent D.host.E (Sum.elim e' f') := by
    refine LinearIndependent.of_pairwise_dual_eq_zero_one _
      (Sum.elim (fun i => V.hT (f' i)) (fun i => V.hT (e' i))) ?_ ?_
    · rintro (i | i) (j | j) hij
      · have : Fin.castLE ha j ≠ Fin.castLE ha i := fun h => hij (congrArg Sum.inl ((hcast j i).1 h).symm)
        exact (Φ.ef _ _).trans (if_neg this)
      · exact Φ.ff _ _
      · exact Φ.ee _ _
      · have : Fin.castLE ha i ≠ Fin.castLE ha j := fun h => hij (congrArg Sum.inr ((hcast i j).1 h))
        show V.hD (f' j) (e' i) = 0
        rw [sw]; show star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha j))) = 0
        rw [Φ.ef, if_neg this, star_zero]
    · rintro (i | i)
      · exact (Φ.ef _ _).trans (if_pos rfl)
      · show V.hD (f' i) (e' i) = 1
        rw [sw]; show star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha i))) = 1
        rw [Φ.ef, if_pos rfl, star_one]
  have hg : ∀ p q, V.hT (Sum.elim x x' p) (Sum.elim x x' q) = V.hT (Sum.elim e' f' p) (Sum.elim e' f' q) := by
    rintro (i | i) (j | j)
    · show V.hD (x j) (x i) = V.hD (e' j) (e' i)
      rw [h1, Φ.ee]
    · show V.hD (x' j) (x i) = V.hD (f' j) (e' i)
      rw [sw, sw (f' j)]
      show star (V.hD (x i) (x' j)) = star (V.hD (Φ.e (Fin.castLE ha i)) (Φ.f (Fin.castLE ha j)))
      rw [h3, Φ.ef]; simp only [hcast]
    · show V.hD (x j) (x' i) = V.hD (e' j) (f' i)
      show _ = V.hD (Φ.e (Fin.castLE ha j)) (Φ.f (Fin.castLE ha i))
      rw [h3, Φ.ef]; simp only [hcast]
    · show V.hD (x' j) (x' i) = V.hD (f' j) (f' i)
      rw [h2, Φ.ff]
  obtain ⟨g, hgB, hgv⟩ := GlobalTheory.LocOver.WittFrames.exists_isom_of_gram witt_extension_theorem V.hT hs hn _ _ hli hli' hg
  let M : Matrix (Fin V.rank) (Fin V.rank) D.host.E := LinearMap.toMatrix V.frame V.frame g.toLinearMap
  let N : Matrix (Fin V.rank) (Fin V.rank) D.host.E := LinearMap.toMatrix V.frame V.frame g.symm.toLinearMap
  have hMN : M * N = 1 := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one V.frame]; congr 1; ext y; simp
  have hNM : N * M = 1 := by
    rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one V.frame]; congr 1; ext y; simp
  let U : GL (Fin V.rank) D.host.E := ⟨M, N, hMN, hNM⟩
  have hrat : ∀ γ : GF V, γ.1 = U → GlobalTheory.Cusp.ratAct D.sp.cm V γ = g.toLinearMap := fun γ h => by
    show Matrix.toLin V.frame V.frame γ.1.1 = _
    rw [h]; exact Matrix.toLin_toMatrix _ _ _
  refine ⟨⟨U, ?_⟩, fun i => ?_⟩
  · show Formalism.UG.cT _ M * V.gram * M = V.gram
    funext i j
    have hexp : ∀ k, g (V.frame k) = ∑ l, M l k • V.frame l := fun k => by
      conv_lhs => rw [← V.frame.sum_repr (g (V.frame k))]
      simp [M, LinearMap.toMatrix_apply]
    rw [show V.gram i j = V.hT (V.frame i) (V.frame j) from rfl, ← hgB, hexp, hexp]
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_smulₛₗ,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    have hσ : ∀ z, (D.sp.cm.sig : D.host.E →+* D.host.E) z = star z := fun z => rfl
    simp only [hσ, starRingEnd_apply, HSpace.gram, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  · rw [hrat _ rfl]
    exact ⟨hgv (Sum.inl i), hgv (Sum.inr i)⟩

end GlobalTheory.WittCarry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTransferPosDef
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.DefTransfer

theorem sphOp_of_local : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (c : UA D.host.E V.rank ≃* GA D V),
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ c x ∈ GfC V ∧ SuppF V f (c x)) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, c x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ) (x : UA D.host.E V.rank),
      IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → x ∈ locU V.rank P →
      (DivAt V e (ϖ : D.host.E) d (c x) ↔ d.length = V.rank ∧ HasDiv (Ov D.host.E P) d (cLoc P x))) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (x y : UA D.host.E V.rank), x ∈ locU V.rank P →
      y ∈ locU V.rank P → HasDiv (Ov D.host.E P) d (cLoc P x) → HasDiv (Ov D.host.E P) d (cLoc P y) →
      ∃ k₁ ∈ KP V.rank P, ∃ k₂ ∈ KP V.rank P, y = k₁ * x * k₂) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) d R, GlobalTheory.Hk3.SphOp V P d R →
      (∀ γ ∈ R, c.symm γ ∈ locU V.rank P ∧ HasDiv (Ov D.host.E P) d (cLoc P (c.symm γ))) ∧
      ∀ x ∈ locU V.rank P, HasDiv (Ov D.host.E P) d (cLoc P x) →
        ∃! γ, γ ∈ R ∧ (c.symm γ)⁻¹ * x ∈ KP V.rank P := by
  intro D _ V c hloc hhyp hdiv hcart P d R hR
  obtain ⟨e, f, ϖ, α, -, hef, hϖ1, hϖ2, -, -, -, hαf, hαd, -, hrep⟩ := hR
  have hK : ∀ k, k ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ c.symm k ∈ KP V.rank P := by
    intro k
    constructor
    · rintro ⟨hk1, hk2⟩
      refine (hhyp P _).1 ?_
      rw [c.apply_symm_apply]
      exact ⟨hk1, e, f, hef, hk2⟩
    · intro hk
      have h1 := (hhyp P _).2 hk
      rw [c.apply_symm_apply] at h1
      have h2 := (hloc P e f hef _).1 hk.1
      rw [c.apply_symm_apply] at h2
      exact ⟨h1.1, h2.2⟩
  have hK1 : (1 : GA D V) ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := by
    refine (hK 1).2 ?_
    rw [map_one]
    exact ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _⟩
  have hKG : ∀ k, k ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} → k ∈ GfC V := fun k hk => hk.1.1
  obtain ⟨γ0, ⟨hγ0R, -⟩, -⟩ := hrep.2 α ⟨1, hK1, 1, hK1, by simp⟩
  obtain ⟨hγ0G, k₁, hk₁, k₂, hk₂, hγ0⟩ := hrep.1 γ0 hγ0R
  have hαG : α ∈ GfC V := by
    have : α = k₁⁻¹ * γ0 * k₂⁻¹ := by rw [hγ0]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hKG _ hk₁)) hγ0G) (Subgroup.inv_mem _ (hKG _ hk₂))
  have hαloc : c.symm α ∈ locU V.rank P :=
    (hloc P e f hef _).2 ⟨by rw [c.apply_symm_apply]; exact hαG, by rw [c.apply_symm_apply]; exact hαf⟩
  obtain ⟨-, hαdiv⟩ := (hdiv P e f ϖ d _ hef hϖ1 hϖ2 hαloc).1 (by rw [c.apply_symm_apply]; exact hαd)
  have hinv : ∀ x k₁ k₂, k₁ ∈ KP V.rank P → k₂ ∈ KP V.rank P → HasDiv (Ov D.host.E P) d (cLoc P x) →
      HasDiv (Ov D.host.E P) d (cLoc P (k₁ * x * k₂)) := by
    rintro x k₁ k₂ hk₁ hk₂ ⟨u, hu, a, ha, b, hb, h⟩
    refine ⟨u, hu, cLoc P k₁ * a, Subgroup.mul_mem _ hk₁.2 ha, b * cLoc P k₂, Subgroup.mul_mem _ hb hk₂.2, ?_⟩
    simp only [map_mul, Units.val_mul, h, Matrix.mul_assoc]
  refine ⟨fun γ hγ => ?_, fun x hx hxd => ?_⟩
  · obtain ⟨-, k₁, hk₁, k₂, hk₂, rfl⟩ := hrep.1 γ hγ
    have e1 : c.symm (k₁ * α * k₂) = c.symm k₁ * c.symm α * c.symm k₂ := by simp only [map_mul]
    rw [e1]
    have hk₁' := (hK _).1 hk₁
    have hk₂' := (hK _).1 hk₂
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₁'.1 hαloc) hk₂'.1, hinv _ _ _ hk₁' hk₂' hαdiv⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, hxe⟩ := hcart P d _ x hαloc hx hαdiv hxd
    have hcx : c x = c k₁ * α * c k₂ := by rw [hxe]; simp only [map_mul, c.apply_symm_apply]
    have hk₁' : c k₁ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := (hK _).2 (by rwa [c.symm_apply_apply])
    have hk₂' : c k₂ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} := (hK _).2 (by rwa [c.symm_apply_apply])
    have hconv : ∀ γ, γ⁻¹ * c x ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔ (c.symm γ)⁻¹ * x ∈ KP V.rank P := by
      intro γ
      rw [hK]
      simp only [map_mul, map_inv, c.symm_apply_apply]
    obtain ⟨γ, ⟨hγR, hγK⟩, huniq⟩ := hrep.2 (c x) ⟨_, hk₁', _, hk₂', hcx⟩
    exact ⟨γ, ⟨hγR, (hconv γ).1 hγK⟩, fun γ' hγ' => huniq γ' ⟨hγ'.1, (hconv γ').2 hγ'.2⟩⟩

theorem exists_isTransfer : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    IsInfFam θ → V.SigOK → V.IsPosDef → ∃ (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V), IsTransfer V θ j h₀ := by
  intro D _ V θ hθ hs hp
  obtain ⟨j, M, hM, hrat, hfin, hinf, hA, hform⟩ := GlobalTheory.T.exists_iso_definiteUnitary_adelicUnitaryGroup D V θ hθ hs hp
  obtain ⟨h₀, hh₀, hlat⟩ := GlobalTheory.T.exists_finite_unitary_point_selfDual_to_orthonormal D V M hM
  obtain ⟨hex, hloc⟩ := GlobalTheory.T.definiteUnitary_localPoints_transfer_iff D V j h₀ M hM hh₀ hfin hform hlat
  have hhyp := GlobalTheory.T.hyperspecial_stabilizer_transfer_conj_selfDual_lattice D V j h₀ M hM hh₀ hfin hform hlat hloc
  have hdiv := GlobalTheory.T.divAt_selfDual_lattice_iff_hasElementaryDivisors D V j h₀ M hM hh₀ hfin hform hlat
  refine ⟨j, h₀, hh₀, hrat, hfin, hinf, hA, fun P x => ?_, hhyp, ?_⟩
  · obtain ⟨e, f, hef⟩ := hex P
    constructor
    · intro hx
      obtain ⟨h1, h2⟩ := (hloc P e f hef x).1 hx
      exact ⟨h1, e, f, hef, h2⟩
    · rintro ⟨h1, e', f', hef', h2⟩
      exact (hloc P e' f' hef' x).2 ⟨h1, h2⟩
  · exact sphOp_of_local D V (cj j h₀) hloc hhyp hdiv (fun P d x y => GlobalTheory.T.mem_sameDoubleCoset_of_hasElementaryDivisors_definiteUnitary D V.rank P d x y)

end GlobalTheory.DefTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVolumeOneMeasureDefiniteOpenCompactStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_volumeOne_measure_definite_openCompact : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsDefiniteSpace V → IsOpenCompactLevel V K →
  ∃ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Links.IsMeasDef V K μ 𝓕 := by
  first | exact @GlobalTheory.DefiniteLevelMeasure.exists_isMeasDef_openCompact | exact GlobalTheory.DefiniteLevelMeasure.exists_isMeasDef_openCompact | (intros; apply GlobalTheory.DefiniteLevelMeasure.exists_isMeasDef_openCompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleModelsIsoMemIntegralOfOhEStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleModelsIso_mem_integral_of_OhE : ∀ {D : D7} (x : StandardLatticesGL3.AE D), x ∈ StandardLatticesGL3.OhE D → GlobalTheory.FrameTransport.adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE | exact GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE | (intros; apply GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumThetaFunctionDerivativeComplexStructurStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuum_thetaFunction_derivative_complex_structure : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ),
    IsStdChar D ψ (-1) → IsInfFam θ → IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
    ∀ x x' : WO S T, (∀ τ, compAt θ τ x' = cplxO (sS τ) (sT τ) (compAt θ τ x)) → ∀ w : WO S T, ∃ a : ℂ,
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x) f w) a 0 ∧
      HasDerivAt (fun t : ℝ => heisO ψ S T (realAd D.host.F t • x') f w) (Complex.I * a) 0 := by
  first | exact @GlobalTheory.FockLineJ.fock_line_J | exact GlobalTheory.FockLineJ.fock_line_J | (intros; apply GlobalTheory.FockLineJ.fock_line_J <;> assumption)
end

