import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedBaseChangeEqOfSatakeEq
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0338
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0686
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0185
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedBaseChangeEqOfSatakeEqStatement
section
open Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedBaseChange_eq_of_satake_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (α : Fin (n / 2) → ℂˣ) (α₀ : Fin (n / 2) → ℂ), (∀ (d : Fin n → ℤ) (t : Formalism.UG.GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → Formalism.UG.SatU ϖ q (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t) (fun i => (α i : ℂ)) = Formalism.UG.SatU ϖ q (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) t) α₀) → (GlobalTheory.LGrp.bcParam n α).map (fun a : ℂˣ => (a : ℂ)) = ubc n (Finset.univ.val.map α₀) := by
  first | exact @GlobalTheory.SatBcInj.bcParam_eq_ubc_of_satU_eq | exact GlobalTheory.SatBcInj.bcParam_eq_ubc_of_satU_eq | (intros; apply GlobalTheory.SatBcInj.bcParam_eq_ubc_of_satU_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedLocalPairActsOnVacuaByHeisenbergComb
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem locPair_extend_vac : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ φ : M →ₗ[ℂ] M, (∀ s, LocVac ρ s → LocVac ρ (φ s)) → ∃ B : Module.End ℂ M, (∀ x, B * ρ x = ρ x * B) ∧ ∀ s, LocVac ρ s → B s = φ s := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP φ hφ
  classical
  let V : Submodule ℂ M :=
    { carrier := {s | LocVac ρ s}
      add_mem' := by intro a b ha hb u hu; simp [ha u hu, hb u hu]
      zero_mem' := by intro u _; simp
      smul_mem' := by intro c a ha u hu; simp [ha u hu] }
  let T : (Matrix (Fin n') (Fin n) L →₀ V) →ₗ[ℂ] M := Finsupp.lsum ℂ (fun x => ρ x ∘ₗ V.subtype)
  let T' : (Matrix (Fin n') (Fin n) L →₀ V) →ₗ[ℂ] M := Finsupp.lsum ℂ (fun x => ρ x ∘ₗ φ ∘ₗ V.subtype)
  have hT : ∀ d, T d = d.sum fun x v => ρ x (v : M) := fun d => rfl
  have hT' : ∀ d, T' d = d.sum fun x v => ρ x (φ (v : M)) := fun d => rfl
  have hker : LinearMap.ker T ≤ LinearMap.ker T' := by
    intro d hd
    rw [LinearMap.mem_ker] at hd ⊢
    have key := GlobalTheory.T.vacuumTranslate_relation_map_preserving_vacua L ϖ σ q δ n n' JS JT ψ M ρ ω hP φ hφ (d.mapRange V.subtype (map_zero _))
      (fun x => by rw [Finsupp.mapRange_apply]; exact (d x).2)
    rw [Finsupp.sum_mapRange_index (fun x => map_zero _), Finsupp.sum_mapRange_index (fun x => by simp)] at key
    exact key hd
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hP.span, Submodule.span_le]
    rintro w ⟨x, s, hs, rfl⟩
    exact ⟨Finsupp.single x ⟨s, hs⟩, by rw [hT, Finsupp.sum_single_index (by simp)]⟩
  let B : Module.End ℂ M := (LinearMap.ker T).liftQ T' hker ∘ₗ (T.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hB : ∀ d, B (T d) = T' d := by
    intro d
    have : (T.quotKerEquivOfSurjective hsurj).symm (T d) = Submodule.Quotient.mk d := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [B, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  refine ⟨B, fun y => ?_, fun s hs => ?_⟩
  · let c : Matrix (Fin n') (Fin n) L → ℂ := fun x => ψ ((locH σ δ JS JT y x + σ (locH σ δ JS JT y x)) / 2)
    let Sh : (Matrix (Fin n') (Fin n) L →₀ V) →ₗ[ℂ] (Matrix (Fin n') (Fin n) L →₀ V) :=
      Finsupp.lsum ℂ (fun x => c x • Finsupp.lsingle (y + x))
    have h1 : ρ y ∘ₗ T = T ∘ₗ Sh := by
      apply Finsupp.lhom_ext
      intro x v
      simp only [LinearMap.comp_apply, Sh, T, Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply, map_smul]
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [← Module.End.mul_apply, hP.rho_mul]
      rfl
    have h2 : ρ y ∘ₗ T' = T' ∘ₗ Sh := by
      apply Finsupp.lhom_ext
      intro x v
      simp only [LinearMap.comp_apply, Sh, T', Finsupp.lsum_single, LinearMap.smul_apply, Finsupp.lsingle_apply, map_smul]
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
      rw [← Module.End.mul_apply, hP.rho_mul]
      rfl
    apply LinearMap.ext
    intro m
    obtain ⟨d, rfl⟩ := hsurj m
    have e1 := LinearMap.congr_fun h1 d
    have e2 := LinearMap.congr_fun h2 d
    simp only [LinearMap.comp_apply] at e1 e2
    rw [Module.End.mul_apply, Module.End.mul_apply, e1, hB, hB, e2]
  · have : T (Finsupp.single 0 ⟨s, hs⟩) = s := by
      rw [hT, Finsupp.sum_single_index (by simp), hP.rho_zero]; rfl
    calc B s = B (T (Finsupp.single 0 ⟨s, hs⟩)) := by rw [this]
      _ = φ s := by rw [hB, hT', Finsupp.sum_single_index (by simp), hP.rho_zero]; rfl

theorem locPair_act_vac_comb : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ p, ∃ c : Matrix (Fin n') (Fin n) L →₀ ℂ, ∀ s, LocVac ρ s → ω p s = c.sum fun x z => z • ρ x s := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP p
  classical
  by_cases h0 : ∃ s0, LocVac ρ s0 ∧ s0 ≠ 0
  swap
  · refine ⟨0, fun s hs => ?_⟩
    have : s = 0 := by by_contra h; exact h0 ⟨s, hs, h⟩
    subst this; simp
  obtain ⟨s0, hs0, hs0ne⟩ := h0

  let N : Subgroup (Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)) :=
    { carrier := {p | ∀ B : Module.End ℂ M, (∀ x, B * ρ x = ρ x * B) → ω p * B = B * ω p}
      one_mem' := by intro B _; simp
      mul_mem' := by
        intro a b ha hb B hB
        rw [map_mul, mul_assoc, hb B hB, ← mul_assoc, ha B hB, mul_assoc]
      inv_mem' := by
        intro a ha B hB
        have h1 : ω a⁻¹ * ω a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        have h2 : ω a * ω a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        calc ω a⁻¹ * B = ω a⁻¹ * B * (ω a * ω a⁻¹) := by rw [h2, mul_one]
          _ = ω a⁻¹ * (ω a * B) * ω a⁻¹ := by rw [ha B hB]; noncomm_ring
          _ = B * ω a⁻¹ := by rw [← mul_assoc, h1, one_mul] }
  have hN : N.Normal := by
    constructor
    intro a ha g B hB
    have h1 : ω g⁻¹ * ω g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : ω g * ω g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hB' : ∀ x, (ω g⁻¹ * B * ω g) * ρ x = ρ x * (ω g⁻¹ * B * ω g) := by
      intro x
      have hn := hP.norm g.1 g.2 x
      set y := (((g.2 : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x *
        (((g.1 : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
      have hn' : ω g * ρ x = ρ y * ω g := hn
      have hinv : ω g⁻¹ * ρ y = ρ x * ω g⁻¹ := by
        calc ω g⁻¹ * ρ y = ω g⁻¹ * ρ y * (ω g * ω g⁻¹) := by rw [h2, mul_one]
          _ = ω g⁻¹ * (ρ y * ω g) * ω g⁻¹ := by noncomm_ring
          _ = ω g⁻¹ * (ω g * ρ x) * ω g⁻¹ := by rw [hn']
          _ = (ω g⁻¹ * ω g) * ρ x * ω g⁻¹ := by noncomm_ring
          _ = ρ x * ω g⁻¹ := by rw [h1, one_mul]
      calc (ω g⁻¹ * B * ω g) * ρ x = ω g⁻¹ * B * (ω g * ρ x) := by noncomm_ring
        _ = ω g⁻¹ * (B * ρ y) * ω g := by rw [hn']; noncomm_ring
        _ = (ω g⁻¹ * ρ y) * B * ω g := by rw [hB y]; noncomm_ring
        _ = ρ x * (ω g⁻¹ * B * ω g) := by rw [hinv]; noncomm_ring
    have ha' := ha _ hB'
    calc ω (g * a * g⁻¹) * B = ω g * ω a * (ω g⁻¹ * B * ω g) * ω g⁻¹ := by
          rw [map_mul, map_mul]
          calc ω g * ω a * ω g⁻¹ * B = ω g * ω a * (ω g⁻¹ * B) * 1 := by noncomm_ring
            _ = _ := by rw [← h2]; noncomm_ring
      _ = ω g * (ω g⁻¹ * B * ω g) * ω a * ω g⁻¹ := by rw [mul_assoc (ω g) (ω a), ha']; noncomm_ring
      _ = (ω g * ω g⁻¹) * B * (ω g * ω a * ω g⁻¹) := by noncomm_ring
      _ = B * ω (g * a * g⁻¹) := by rw [h2, one_mul, map_mul, map_mul]

  have hInt : ∀ (g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L)) (h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)),
      (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
      (g, h) ∈ N := by
    intro g h hg hh B hB
    apply LinearMap.ext_on hP.span
    rintro w ⟨x, s, hs, rfl⟩
    have hBs : ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u (B s) = B s := by
      intro u hu
      have := congrArg (fun F => F s) (hB u)
      simp only [Module.End.mul_apply] at this
      rw [← this, hs u hu]
    have hn := hP.norm g h x
    have e1 := congrArg (fun F => F (B s)) hn
    have e2 := congrArg (fun F => F s) hn
    have e3 := congrArg (fun F => F s) (hB x)
    have e4 := congrArg (fun F => F s) (hB (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x *
        (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))
    simp only [Module.End.mul_apply] at e1 e2 e3 e4 ⊢
    rw [e3, e1, hP.fix g h hg hh _ hBs, e2, hP.fix g h hg hh _ hs, e4]
  have hTop : N = ⊤ := by
    have hS := GlobalTheory.T.normal_subgroup_containing_hyperspecial_eq_top_unramifiedUnitary L ϖ σ q n JS hP.unr hP.odd hP.intS hP.hermS (N.comap (MonoidHom.inl _ _)) (hN.comap _)
      (fun g hg => Subgroup.mem_comap.mpr (hInt g 1 hg (by simpa using (Formalism.UG.GLint (Fin n') (Formalism.UG.intL L)).one_mem)))
    have hT := GlobalTheory.T.normal_subgroup_containing_hyperspecial_eq_top_unramifiedUnitary L ϖ σ q n' JT hP.unr hP.odd hP.intT hP.hermT (N.comap (MonoidHom.inr _ _)) (hN.comap _)
      (fun h hh => Subgroup.mem_comap.mpr (hInt 1 h (by simpa using (Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)).one_mem) hh))
    rw [eq_top_iff]
    rintro ⟨g, h⟩ -
    have hg : (g, (1 : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L))) ∈ N := by
      have : g ∈ N.comap (MonoidHom.inl _ _) := by rw [hS]; trivial
      simpa using this
    have hh : ((1 : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L)), h) ∈ N := by
      have : h ∈ N.comap (MonoidHom.inr _ _) := by rw [hT]; trivial
      simpa using this
    have := N.mul_mem hg hh
    simpa using this
  have hpN : p ∈ N := by rw [hTop]; trivial

  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ M, f s0 = 1 := by
    have := (Module.forall_dual_apply_eq_zero_iff ℂ s0).not.mpr hs0ne
    push_neg at this
    obtain ⟨f, hf⟩ := this
    exact ⟨(f s0)⁻¹ • f, by simp [hf]⟩
  have hline : ∀ t, LocVac ρ t → ∀ m, LocVac ρ (f.smulRight t m) := by
    intro t ht m u hu
    simp [ht u hu]
  obtain ⟨B0, hB0, hB0v⟩ := locPair_extend_vac L ϖ σ q δ n n' JS JT ψ M ρ ω hP (f.smulRight s0) (fun m _ => hline s0 hs0 m)

  have hspan : ∀ m : M, ∃ c : Matrix (Fin n') (Fin n) L →₀ ℂ, B0 m = c.sum fun x z => z • ρ x s0 := by
    intro m
    have hm : m ∈ Submodule.span ℂ {w | ∃ x s, (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ u s = s) ∧ w = ρ x s} := by
      rw [hP.span]; trivial
    induction hm using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, s, hs, rfl⟩ := hw
      refine ⟨Finsupp.single x (f s), ?_⟩
      have := congrArg (fun F => F s) (hB0 x)
      simp only [Module.End.mul_apply] at this
      rw [this, hB0v s hs]
      simp
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨ca, hca⟩ := ha
      obtain ⟨cb, hcb⟩ := hb
      refine ⟨ca + cb, ?_⟩
      rw [map_add, hca, hcb, Finsupp.sum_add_index']
      · intro x; simp
      · intro x z z'; rw [add_smul]
    | smul a b _ hb =>
      obtain ⟨cb, hcb⟩ := hb
      refine ⟨a • cb, ?_⟩
      rw [map_smul, hcb, Finsupp.sum_smul_index' (h := fun x z => z • ρ x s0) (fun _ => zero_smul ℂ _), Finsupp.smul_sum]
      simp [Finsupp.sum, Finset.smul_sum, smul_smul]
  obtain ⟨c, hc⟩ := hspan (ω p s0)
  have hps0 : ω p s0 = c.sum fun x z => z • ρ x s0 := by
    have e := congrArg (fun F => F s0) (hpN B0 hB0)
    simp only [Module.End.mul_apply] at e
    rw [← hc, ← e, hB0v s0 hs0]
    simp [hf]
  refine ⟨c, fun s hs => ?_⟩
  obtain ⟨Bs, hBs, hBsv⟩ := locPair_extend_vac L ϖ σ q δ n n' JS JT ψ M ρ ω hP (f.smulRight s) (fun m _ => hline s hs m)
  have e1 : Bs s0 = s := by rw [hBsv s0 hs0]; simp [hf]
  have e := congrArg (fun F => F s0) (hpN Bs hBs)
  simp only [Module.End.mul_apply] at e
  rw [← e1, e, hps0, map_finsuppSum]
  refine Finsupp.sum_congr fun x _ => ?_
  have := congrArg (fun F => F s0) (hBs x)
  simp only [Module.End.mul_apply] at this
  rw [map_smul, this]

end GlobalTheory.Hk3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem weil_rep_equiv_of_charpoly_eq : ∀ (K Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (n m : ℕ) (a : WDRep h (Fin n → ℂ)) (b : WDRep h (Fin m → ℂ)), (∀ σ : Weil h, (a.ρ σ).charpoly = (b.ρ σ).charpoly) → ∃ e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin m → ℂ), ∀ σ z, e (a.ρ σ z) = b.ρ σ (e z) := by
  intro K Ω _ _ _ _ _ A v h n m a b hc
  have ha := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule a.ρ).1
    (GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho K Ω A v h n a)
  have hb := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule b.ρ).1
    (GlobalTheory.WeilDeligne.WDRep.isSemisimpleRepresentation_rho K Ω A v h m b)
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt ℂ (Weil h) _ _ a.ρ b.ρ ha hb hc
  exact ⟨e, fun σ z => LinearMap.congr_fun (he σ) z⟩

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ZeroEigensystemNotPassageOfFiniteTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zero_eigensystem_not_passage_of_finiteType : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ j (p : A3.fam3.base3.Ix), ¬ cxSys D.what₂.embLL ((A3.liftI j A3.A.μ0).HasRes3 (A3.fam3.tr3 j p.1)) 0 := by
  first | exact @GlobalTheory.ZeroPassage.zero_not_passage | exact GlobalTheory.ZeroPassage.zero_not_passage | (intros; apply GlobalTheory.ZeroPassage.zero_not_passage <;> assumption)
end

