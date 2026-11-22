import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1362
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1360
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
section
open scoped NNReal Pointwise
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.UnitaryVol

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h1 := h.2.2 (star v) (by simpa using hv)
  rw [star_star, hMv, dotProduct_zero] at h1
  simp at h1

theorem isHermND_map {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ}
    (hσ : ∀ x, σ (σ x) = x) (h : X.IsHerm σ B r s) : IsHermND σ (X.J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.map_apply, hσ]
    exact (h.herm j i).symm
  · have hJ : X.J.det ≠ 0 := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      intro hz
      apply det_ne_zero_of_isCartan (h.cartan w)
      rw [show X.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix X.J from rfl, ← RingHom.map_det, hz, map_zero]
    rw [show X.J.map σ = (σ : E →+* E).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 hJ

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  haveI := (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).to_subtype
  exact Function.Injective.countable
    (f := fun γ : ratU σ J => (⟨γ.1.1, Subgroup.mem_subgroupOf.1 γ.2⟩ :
      Set.range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))))
    fun γ γ' h => Subtype.val_injective (Subtype.val_injective (congrArg Subtype.val h :))

theorem measure_fundDom_lt_top (hP : GlobalTheory.Published.SiegelSetUnitary) {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ (J.map σ)) {μ : Measure (UA σ J)} [μ.IsHaarMeasure]
    {D : Set (UA σ J)} (hD : IsFundamentalDomain (ratU σ J) D μ) : μ D < ⊤ := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have heq : UG (cA σ) (incM F J) = HR (AF F) σ (J.map σ) := by
    have h := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ one_ne_zero
    rw [one_smul] at h
    exact h
  let e : UA σ J ≃* GAd σ (J.map σ) := MulEquiv.subgroupCongr heq
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  obtain ⟨S, hSc, hcov, -, hfin, -⟩ := GlobalTheory.SiegelSet.exists_cover hP hcm hJ
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ J) := ⟨by
    have h3 : (fun p : UA σ J × UA σ J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  have hH : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e he he'
  have h1 : μ (e ⁻¹' S) < ⊤ := by
    have h2 := hfin _ hH
    rwa [Measure.map_apply he.measurable hSc.measurableSet] at h2
  haveI := countable_ratU σ J
  haveI : MeasurableMul (UA σ J) :=
    ⟨fun g => (continuous_const.mul continuous_id).measurable, fun g => (continuous_id.mul continuous_const).measurable⟩
  haveI : MeasurableConstSMul (ratU σ J) (UA σ J) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun x : UA σ J => γ.1 * x).measurable⟩
  haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ := ⟨fun γ A _ => measure_preimage_mul μ γ.1 A⟩
  have hcov' : D ⊆ ⋃ γ : ratU σ J, γ • (e ⁻¹' S) ∩ D := by
    intro x hx
    obtain ⟨γ, hγ, s, hs, hxs⟩ := hcov (e x)
    obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
    have hr : e.symm γ ∈ ratU σ J := Subgroup.mem_subgroupOf.2 ⟨u, hu⟩
    refine Set.mem_iUnion.2 ⟨⟨e.symm γ, hr⟩, Set.mem_smul_set.2 ⟨e.symm s, show e (e.symm s) ∈ S by rw [MulEquiv.apply_symm_apply]; exact hs, ?_⟩, hx⟩
    change e.symm γ * e.symm s = x
    rw [← map_mul, ← hxs, MulEquiv.symm_apply_apply]
  calc μ D ≤ μ (⋃ γ : ratU σ J, γ • (e ⁻¹' S) ∩ D) := measure_mono hcov'
    _ ≤ ∑' γ : ratU σ J, μ (γ • (e ⁻¹' S) ∩ D) := measure_iUnion_le _
    _ = μ (e ⁻¹' S) := (hD.measure_eq_tsum _).symm
    _ < ⊤ := h1

theorem measure_dom_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W), GlobalTheory.Published.SiegelSetUnitary → IsTriple B G X om om' → G.M'.μ G.M'.dom < ⊤ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hP hT
  haveI := hT.geo.hM'.haar
  exact measure_fundDom_lt_top hP hT.base.cm
    (isHermND_map (GlobalTheory.SiegelSet.sigma_sigma hT.base.cm) hT.geo.hV') hT.geo.hM'.dom

end GlobalTheory.UnitaryVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmallSectionBallOfMulPowSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.MpDiv

theorem mem_Bl_of_mul_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N 0 → f * s ^ m ∈ P.Bl N m 2 → f ∈ P.Bl N 0 (2 * Real.exp (δ * N + C * m)) := by
  intro k _ X _ p D hX P s hs hs0 δ hδ
  obtain ⟨ρ, hρ, H⟩ := GlobalTheory.T.arith_global_maximum_principle_off_divisor k X p D hX P s hs hs0 δ hδ
  refine ⟨max 0 (-Real.log ρ), le_max_left _ _, fun N m f hf hfs => ?_⟩
  set C : ℝ := max 0 (-Real.log ρ) with hC
  have key := H N f (2 * Real.exp (C * m)) hf (fun σ y hy => ?_)
  · have e : Real.exp (δ * N) * (2 * Real.exp (C * m)) = 2 * Real.exp (δ * N + C * m) := by
      rw [Real.exp_add]; ring
    rwa [e] at key
  · obtain ⟨hp1, hp2⟩ := GlobalTheory.T.hermPair_pow_section_mem_and_norm_pow k X p P 0 1 s hs m
    have hm := (GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P N 0 _ _ f (s ^ m) hf hp1).2 σ y
    rw [hp2 σ y] at hm
    simp only [mul_zero, add_zero, mul_one, zero_add] at hm
    have h2 := hfs.2 σ y
    rw [hm] at h2
    have hn : 0 ≤ P.nu N 0 σ y f := by unfold Pair.nu; positivity
    have h1 : 1 ≤ Real.exp C * P.nu 0 1 σ y s := by
      have : Real.exp (-Real.log ρ) ≤ Real.exp C := Real.exp_le_exp.2 (le_max_right _ _)
      rw [Real.exp_neg, Real.exp_log hρ] at this
      calc (1 : ℝ) = ρ⁻¹ * ρ := (inv_mul_cancel₀ hρ.ne').symm
        _ ≤ Real.exp C * P.nu 0 1 σ y s :=
          mul_le_mul this hy hρ.le (Real.exp_pos _).le
    have h3 : 1 ≤ Real.exp (C * m) * P.nu 0 1 σ y s ^ m := by
      rw [mul_comm C, Real.exp_nat_mul, ← mul_pow]
      exact one_le_pow₀ h1
    calc P.nu N 0 σ y f ≤ P.nu N 0 σ y f * (Real.exp (C * m) * P.nu 0 1 σ y s ^ m) :=
          le_mul_of_one_le_right hn h3
      _ = Real.exp (C * m) * (P.nu N 0 σ y f * P.nu 0 1 σ y s ^ m) := by ring
      _ ≤ Real.exp (C * m) * 2 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = 2 * Real.exp (C * m) := mul_comm _ _

end GlobalTheory.VolBr.MpDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit

noncomputable section
namespace GlobalTheory.GJReg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def chiS (ν : kˣ →* ℂˣ) (s : ℂ) (g : GL (Fin n) k) : ℂ := (ν (gdet g) : ℂ) * apow (gdet g) s

theorem chiS_mul (ν : kˣ →* ℂˣ) (s : ℂ) (g h : GL (Fin n) k) : chiS ν s (g * h) = chiS ν s g * chiS ν s h := by
  simp only [chiS, gdet_mul, map_mul, Units.val_mul, apow_mul]; ring

@[simp] theorem chiS_one (ν : kˣ →* ℂˣ) (s : ℂ) : chiS ν s (1 : GL (Fin n) k) = 1 := by
  simp [chiS, gdet]

theorem chiS_inv_mul (ν : kˣ →* ℂˣ) (s : ℂ) (g : GL (Fin n) k) : chiS ν s g⁻¹ * chiS ν s g = 1 := by
  rw [← chiS_mul, inv_mul_cancel, chiS_one]

theorem chiS_of_mem_KO {ν : kˣ →* ℂˣ} (hν : IsUnram ν) (s : ℂ) {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    chiS ν s g = 1 := by
  have hv := valuation_gdet_of_mem_KO hg
  simp [chiS, hν _ hv, apow_of_valuation_eq_one hv]

def latInd (g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k → ℂ := fun X =>
  (intM k (Fin n) (Fin n)).indicator 1 (X * (g⁻¹ : GL (Fin n) k).val)

theorem latInd_mem_SB (g : GL (Fin n) k) : latInd g ∈ SB (Matrix (Fin n) (Fin n) k) :=
  restrict_mem_SB (P' := g.val) (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    indicator_intM_mem_SB

theorem mul_left_mem_SB (g : GL (Fin n) k) {φ : Matrix (Fin n) (Fin n) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin n) (Fin n) k)) : (fun X => φ (g.val * X)) ∈ SB (Matrix (Fin n) (Fin n) k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have c1 : Continuous fun X : Matrix (Fin n) (Fin n) k => g.val * X := continuous_const.matrix_mul continuous_id
  have c2 : Continuous fun X : Matrix (Fin n) (Fin n) k => (g⁻¹).val * X := continuous_const.matrix_mul continuous_id
  have e : Topology.IsClosedEmbedding fun X : Matrix (Fin n) (Fin n) k => g.val * X :=
    Function.LeftInverse.isClosedEmbedding (f := fun X => (g⁻¹).val * X)
      (fun X => by simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul])
      c2 c1
  exact ⟨hφ.1.comp_continuous c1, hφ.2.comp_isClosedEmbedding e⟩

theorem mul_right_mem_SB (g : GL (Fin n) k) {φ : Matrix (Fin n) (Fin n) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin n) (Fin n) k)) : (fun X => φ (X * g.val)) ∈ SB (Matrix (Fin n) (Fin n) k) :=
  restrict_mem_SB (P' := (g⁻¹).val) (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hφ

variable (k n) in

def kInd : Matrix (Fin n) (Fin n) k → ℂ := {X | ∃ g ∈ KO k (Fin n), g.val = X}.indicator 1

def gjZ [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (s : ℂ) (φ : Matrix (Fin n) (Fin n) k → ℂ) : ℂ :=
  ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) s ∂(haarVol (KO k (Fin n)))

end GlobalTheory.GJReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiProdCompInvTranspose
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.InvTransposeProd

open Matrix GlobalTheory.TypeTame
open scoped TensorProduct

variable {k : Type} [Field k] {h n : ℕ} {d : Fin h → ℕ}

def revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) : (Σ a : Fin h, Fin (d (Fin.rev a))) ≃ Fin n :=
  (Equiv.sigmaCongrLeft (β := fun b => Fin (d b)) Fin.revPerm).trans e

theorem revPlace_apply (e : (Σ a, Fin (d a)) ≃ Fin n) (a : Fin h) (i : Fin (d (Fin.rev a))) :
    revPlace e ⟨a, i⟩ = e ⟨Fin.rev a, i⟩ := rfl

theorem blk_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) (x : Fin n) :
    blk e x = Fin.rev (blk (revPlace e) x) := by
  obtain ⟨⟨a, i⟩, rfl⟩ := (revPlace e).surjective x
  rw [blk_apply, revPlace_apply, blk_apply]

theorem mem_parab_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) {q : GL (Fin n) k} (hq : q ∈ parab k e) :
    invTranspose n q ∈ parab k (revPlace e) := by
  refine mem_parab.2 fun i j hij => ?_
  rw [invTranspose_val, Matrix.transpose_apply]
  refine mem_parab.1 (inv_mem hq) j i ?_
  rw [blk_revPlace e i, blk_revPlace e j]
  exact Fin.rev_lt_rev.2 hij

theorem mem_parab_of_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) {p : GL (Fin n) k}
    (hp : p ∈ parab k (revPlace e)) : invTranspose n p ∈ parab k e := by
  refine mem_parab.2 fun i j hij => ?_
  rw [invTranspose_val, Matrix.transpose_apply]
  refine mem_parab.1 (inv_mem hp) j i ?_
  rw [blk_revPlace e i, blk_revPlace e j] at hij
  exact Fin.rev_lt_rev.1 hij

theorem leviProj_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) (q : parab k e)
    (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)) (b : Fin h) :
    leviProj k (revPlace e) ⟨invTranspose n q, hq⟩ b =
      invTranspose (d (Fin.rev b)) (leviProj k e q (Fin.rev b)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invTranspose_val, Matrix.transpose_apply, ← Pi.inv_apply, ← map_inv, leviProj_apply, leviProj_apply]
  rfl

theorem det_invTranspose (m : ℕ) (g : GL (Fin m) k) :
    GeneralLinearGroup.det (invTranspose m g) = (GeneralLinearGroup.det g)⁻¹ := by
  ext
  rw [GeneralLinearGroup.val_det_apply, invTranspose_val, Matrix.det_transpose, ← GeneralLinearGroup.val_det_apply,
    map_inv]

omit [Field k] in
theorem modExp_rev (b : Fin h) :
    modExp (fun a => Fin (d (Fin.rev a))) b = -modExp (fun a => Fin (d a)) (Fin.rev b) := by
  unfold modExp
  simp only [Fintype.card_fin, Finset.sum_filter]
  have h1 : (∑ c : Fin h, if b < c then (d (Fin.rev c) : ℤ) else 0) =
      ∑ c : Fin h, if c < Fin.rev b then (d c : ℤ) else 0 :=
    Fintype.sum_equiv Fin.revPerm _ _ fun c => by simp [Fin.rev_lt_rev]
  have h2 : (∑ c : Fin h, if c < b then (d (Fin.rev c) : ℤ) else 0) =
      ∑ c : Fin h, if Fin.rev b < c then (d c : ℤ) else 0 :=
    Fintype.sum_equiv Fin.revPerm _ _ fun c => by simp [Fin.rev_lt_rev]
  rw [h1, h2]
  ring

section Local

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deltaHalf_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) (q : parab k e)
    (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)) :
    deltaHalf k (fun a => Fin (d (Fin.rev a))) (leviProj k (revPlace e) ⟨invTranspose n q, hq⟩) =
      deltaHalf k (fun a => Fin (d a)) (leviProj k e q) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Fintype.prod_equiv Fin.revPerm _ _ fun b => ?_
  rw [leviProj_revPlace e q hq b, det_invTranspose, modExp_rev]
  simp only [Int.cast_neg, neg_div, absPow_neg, MonoidHom.inv_apply, map_inv, inv_inv, Fin.revPerm_apply]
  rfl

variable (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def revTensor : (⨂[ℂ] a, X a) ≃ₗ[ℂ] ⨂[ℂ] a, X (Fin.rev a) :=
  PiTensorProduct.reindex ℂ X Fin.revPerm

theorem revTensor_tprod (z : ∀ a, X a) :
    revTensor X (PiTensorProduct.tprod ℂ z) = PiTensorProduct.tprod ℂ fun a => z (Fin.rev a) :=
  PiTensorProduct.reindex_tprod _ _

variable {X}

def revRep (π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))) :
    Representation ℂ (Levi k fun a => Fin (d (Fin.rev a))) (⨂[ℂ] a, X a) where
  toFun g := (revTensor X).symm.toLinearMap ∘ₗ piTensor π' g ∘ₗ (revTensor X).toLinearMap
  map_one' := by ext; simp
  map_mul' g g' := by ext; simp

def revRepEquiv (π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))) :
    (revRep π').Equiv (piTensor π') :=
  Representation.Equiv.mk (revTensor X) fun g => LinearMap.ext fun v => by
    simp [revRep]

theorem revRep_leviProj (e : (Σ a, Fin (d a)) ≃ Fin n)
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (q : parab k e)
    (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)) :
    revRep (fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))))
        (leviProj k (revPlace e) ⟨invTranspose n q, hq⟩) = piTensor π (leviProj k e q) := by
  have key : (piTensor fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))))
        (leviProj k (revPlace e) ⟨invTranspose n q, hq⟩) ∘ₗ (revTensor X).toLinearMap =
      (revTensor X).toLinearMap ∘ₗ piTensor π (leviProj k e q) := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun z => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      revTensor_tprod, piTensor_tprod]
    congr 1
  refine LinearMap.ext fun v => ?_
  show (revTensor X).symm _ = _
  rw [(revTensor X).symm_apply_eq]
  exact LinearMap.congr_fun key v

end Local

theorem multiProd_comp_invTranspose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h n : ℕ) (d : Fin h → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : (Σ a, Fin (d (Fin.rev a))) ≃ Fin n) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (π a)) → Nonempty (Representation.Equiv ((multiProd e π).comp (GlobalTheory.TypeTame.invTranspose n)) (multiProd e' fun a => ((π (Fin.rev a)).comp (GlobalTheory.TypeTame.invTranspose (d (Fin.rev a))) : Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))))) := by
  intro k _ _ _ _ h n d e e' X _ _ π _
  set π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a)) :=
    fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))) with hπ'
  have key : ∀ (q : parab k e) (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)),
      ((twist (revRep π') (deltaHalf k _)).comp (leviProj k (revPlace e))) ⟨invTranspose n q, hq⟩ =
        ((twist (piTensor π) (deltaHalf k _)).comp (leviProj k e)) q := by
    intro q hq
    refine LinearMap.ext fun v => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, twist_apply, twist_apply, deltaHalf_revPlace e q hq,
      hπ', revRep_leviProj e π q hq]
  obtain ⟨A⟩ : Nonempty ((parInd (revPlace e) (revRep π')).Equiv
      ((multiProd e π).comp (invTranspose n))) := by
    refine Relabel.smInd_equiv_comp (P := parab k (revPlace e)) (Q := parab k e)
      (σ := (twist (revRep π') (deltaHalf k _)).comp (leviProj k (revPlace e)))
      (τ := (twist (piTensor π) (deltaHalf k _)).comp (leviProj k e))
      (invTranspose n) (invTranspose n) (continuous_invTranspose n) (continuous_invTranspose n)
      (invTranspose_invTranspose n) (invTranspose_invTranspose n)
      (fun q => ⟨⟨_, mem_parab_revPlace e q.2⟩, rfl, key q _⟩) (fun p => ?_)
    have hp : invTranspose n (invTranspose n (p : GL (Fin n) k)) ∈ parab k (revPlace e) := by
      rw [invTranspose_invTranspose]
      exact p.2
    refine ⟨⟨_, mem_parab_of_revPlace e p.2⟩, rfl, ?_⟩
    refine (key ⟨_, mem_parab_of_revPlace e p.2⟩ hp).symm.trans ?_
    exact congrArg _ (Subtype.ext (invTranspose_invTranspose n (p : GL (Fin n) k)))
  obtain ⟨B⟩ := GlobalTheory.T.product_representation_reorder_equiv k h n (fun a => d (Fin.rev a)) (revPlace e) e' (fun a => X (Fin.rev a)) π'
  exact ⟨A.symm.trans ((parIndEquiv (revPlace e) (revRepEquiv π')).trans B)⟩

end GlobalTheory.InvTransposeProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitUnitaryGroupIsoGl
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.EulerTw
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.GamInert

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

omit [IsCMField E] in

theorem gl_ext_pLoc {x y : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)}
    (h : ∀ w, GeneralLinearGroup.map (pLoc E w) x = GeneralLinearGroup.map (pLoc E w) y) : x = y := by
  refine Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun w => ?_))
  exact congrArg (fun z : GL (Fin n) (w.adicCompletion E) => z i j) (h w)

omit [IsCMField E] in
theorem pLoc_idem (T : Finset (Pl E)) (w : Pl E) : pLoc E w (idem E T) = if w ∈ T then 1 else 0 := rfl

theorem pLoc_prjG (T : Finset (Pl E)) (w : Pl E) (x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    GeneralLinearGroup.map (pLoc E w) (prjG E n T x) =
      if w ∈ T then GeneralLinearGroup.map (pLoc E w) x else 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pLoc E w (idem E T * x i j + (1 - idem E T) * (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = _
  rw [map_add, map_mul, map_mul, map_sub, map_one, pLoc_idem]
  split_ifs with hw
  · rw [one_mul, sub_self, zero_mul, add_zero]; rfl
  · rw [zero_mul, sub_zero, zero_add, one_mul, Units.val_one, Matrix.one_apply, Matrix.one_apply, apply_ite (pLoc E w),
      map_one, map_zero]

omit [IsCMField E] in

theorem continuous_comp_pLoc (w : Pl E) :
    Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) :=
  Continuous.units_map _ (continuous_id.matrix_map
    (RestrictedProduct.continuous_eval (R := fun v : Pl E => v.adicCompletion E) w))

theorem orb_eq {u : Pl E} (hu : ¬ IsSplitAt u) : orb E u = {u} := by
  have h : cPl E u = u := (GlobalTheory.ConjAtPlace.conjSrc_eq_iff u).2 hu
  rw [orb, h]
  simp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : Pl E), ¬ IsSplitAt u → ∃ e : GlobalTheory.EulerTw.Gam E n u ≃ₜ* GLw n u, ∀ g, e g = GeneralLinearGroup.map (pLoc E u) g.1 := by
  intro E _ _ _ n u hu
  have ho := orb_eq E hu
  have hmem : ∀ x : GLw n u, locGL E n u x ∈ Gam E n u := fun x =>
    ⟨locGL E n u x, gl_ext_pLoc E n fun w => by
      rw [pLoc_prjG, ho]
      split_ifs with hw
      · rfl
      · rw [pLoc_locGL_of_ne (by simpa using hw)]⟩
  refine ⟨{ toFun := fun g => GeneralLinearGroup.map (pLoc E u) g.1
            invFun := fun x => ⟨locGL E n u x, hmem x⟩
            left_inv := ?_
            right_inv := fun x => pLoc_locGL u x
            map_mul' := fun g h => map_mul (GeneralLinearGroup.map (pLoc E u)) g.1 h.1
            continuous_toFun := (continuous_comp_pLoc E n u).comp continuous_subtype_val
            continuous_invFun := (GlobalTheory.CuspRep.CuspSub.continuous_locGL u).subtype_mk hmem }, fun g => rfl⟩
  rintro ⟨g, x, rfl⟩
  refine Subtype.ext (gl_ext_pLoc E n fun w => ?_)
  by_cases hw : w = u
  · subst hw
    exact pLoc_locGL _ _
  · change GeneralLinearGroup.map (pLoc E w) (locGL E n u _) = GeneralLinearGroup.map (pLoc E w) (prjG E n (orb E u) x)
    rw [pLoc_locGL_of_ne hw, pLoc_prjG, ho, if_neg (by simpa using hw)]

end GlobalTheory.EulerTw.GamInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSquareLinearFactorOfPencilLineDiscriminantNeZStatement
section
open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_square_linear_factor_of_pencilLineDiscriminant_ne_zero : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (s : Fin D → Fin N → K) (a b : Fin N → K), 1 ≤ δ → (GlobalTheory.PencilDisc.line s a b f).natDegree ≤ δ → (GlobalTheory.PencilDisc.line s a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join s b) f → GlobalTheory.PencilDisc.disc δ s a b f ≠ 0 → GlobalTheory.HSChoice.NoSquare (GlobalTheory.HSChoice.spec s f) := by
  first | exact @GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero | exact GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero | (intros; apply GlobalTheory.PencilDisc.noSquare_spec_of_disc_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSph

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def latAt {d : ℕ} (W : Spc F E d) (v : Pl F) : AddSubgroup (Fin d → AE F E) :=
  AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
    ∃ y ∈ W.L, z = a • fun i => inclR (F := F) (AF F) (y i)}

def KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : Set (UA σ W.J) :=
  {h | h ∈ UAt σ W (evFin F v) ∧ ∀ z ∈ latAt W v, mat h *ᵥ z ∈ latAt W v ∧ mat h⁻¹ *ᵥ z ∈ latAt W v}

theorem one_mem_KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) : (1 : UA σ W.J) ∈ KAt σ W v := by
  refine ⟨?_, fun z hz => ?_⟩
  · intro u _
    show u • (mat (1 : UA σ W.J) - 1) = 0
    simp [mat]
  · simp [mat, hz]

end GlobalTheory.InertSph
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralRestrictedProductEqProdStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_restrictedProduct_eq_prod : ∀ (ι G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : ι → Type) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)] [∀ i, T2Space (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (δ : G) (f : ∀ i, H i → ℂ), (∀ i, Continuous (p i)) → (∀ x y : G, (∀ i, p i x = p i y) → x = y) → (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ C : ∀ i, Set (H i), (∀ i, IsCompact (C i)) → (∀ᶠ i in cofinite, C i = KH i) → IsCompact {x : G | ∀ i, p i x ∈ C i}) → (∀ i, IsCompact (KH i : Set (H i))) → (∀ i, ∀ a ∈ twCent (MonoidHom.id (H i)) (p i δ), ∀ b ∈ twCent (MonoidHom.id (H i)) (p i δ), a * b = b * a) → (∀ i (x : H i), twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ∧ (twCent (MonoidHom.id (H i)) (p i δ) ⊓ (KH i).map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id (H i)) (p i δ))) ≠ 0) → (∀ i (x : H i), (rStab fun k : KH i => f i ((x * k)⁻¹ * p i δ * (x * k))).index ≠ 0) → (∀ i, {q : DoubleCoset.Quotient (twCent (MonoidHom.id (H i)) (p i δ) : Set (H i)) (KH i : Set (H i)) | ∃ k ∈ KH i, f i ((Quotient.out q * k)⁻¹ * p i δ * (Quotient.out q * k)) ≠ 0}.Finite) → (∀ᶠ i in cofinite, p i δ ∈ KH i ∧ f i = (KH i : Set (H i)).indicator 1 ∧ (∀ g : H i, g⁻¹ * p i δ * g ∈ KH i → ∃ t ∈ twCent (MonoidHom.id (H i)) (p i δ), t⁻¹ * g ∈ KH i) ∧ cptPart (twCent (MonoidHom.id (H i)) (p i δ)) ≤ KH i) → twOrb (MonoidHom.id G) K δ (fun x => ∏ᶠ i, f i (p i x)) = ∏ᶠ i, twOrb (MonoidHom.id (H i)) (KH i) (p i δ) (f i) := by
  first | exact @GlobalTheory.RestrProd.twOrb_restrProd | exact GlobalTheory.RestrProd.twOrb_restrProd | (intros; apply GlobalTheory.RestrProd.twOrb_restrProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralUnitIndicatorEventuallyOneClassStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_unitIndicator_eventually_oneClass : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ∀ γ : UL n w, γ.1.val.charpoly = atPl w P → (twOrb (MonoidHom.id _) (KL n w) γ ((KL n w : Set (UL n w)).indicator 1) = if ∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w then 1 else 0) ∧ kapSign n w (atPl w P) γ.1 = 1 ∧ ∀ Q₁ : (w.adicCompletion E)[X], Q₁ ∣ atPl w P → (∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w) → kapSign n w Q₁ γ.1 = 1 := by
  first | exact @GlobalTheory.BCT.OrbUnit.orbUnit_ae | exact GlobalTheory.BCT.OrbUnit.orbUnit_ae | (intros; apply GlobalTheory.BCT.OrbUnit.orbUnit_ae <;> assumption)
end

