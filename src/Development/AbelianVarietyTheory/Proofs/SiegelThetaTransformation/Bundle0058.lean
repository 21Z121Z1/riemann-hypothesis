import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0057
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixed
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnnihilationCreationPeriodCoordinatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilation_creation_periodCoordinates : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℝ Φ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w)) → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Fin S.rank → Fin C.g → ℂ), u = zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) → ∀ w, IsRealPt w → annih (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u + I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)) ∧ crea (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (2 * ((-(π * ∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k))) * Φ (C.zOf (C.xB B) w) + (1 / 2 : ℂ) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u - I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)))) := by
  first | exact @GlobalTheory.Ker.annih_crea_coord | exact GlobalTheory.Ker.annih_crea_coord | (intros; apply GlobalTheory.Ker.annih_crea_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaLevelDataFormsSystem
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.RecSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem EF_swap (hs : IsSympl X bas) (u v : Fin r → E) : EF X u v = -EF X v u := by
  rw [EF_crd hs u v, EF_crd hs v u, neg_neg, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eq_zero_of_EF (hs : IsSympl X bas) (u : Fin r → E) (h : ∀ v, EF X u v = 0) : u = 0 := by
  have hc : crd X bas u = 0 := by
    funext j
    rcases j with i | i
    · have h1 := h (vecQ X bas (Pi.single (Sum.inr i) 1))
      rw [EF_crd hs, crd_vecQ hs] at h1
      simpa [Pi.single_apply] using h1
    · have h1 := h (vecQ X bas (Pi.single (Sum.inl i) 1))
      rw [EF_crd hs, crd_vecQ hs] at h1
      simpa [Pi.single_apply] using h1
  rw [← vecQ_crd X bas u, hc]
  exact vecQ_zero X bas

theorem EFBil_nondegenerate (hs : IsSympl X bas) :
    LinearMap.BilinForm.Nondegenerate (EFBil X) := by
  refine ⟨fun u hu => eq_zero_of_EF hs u fun v => hu v, fun u hu => eq_zero_of_EF hs u fun v => ?_⟩
  have h0 : EF X v u = 0 := hu v
  rw [EF_swap hs, h0, neg_zero]

theorem selfD_int {L : Lt E r} (h : SelfD X L) : (L.restrictScalars ℤ).FG ∧
    LinearMap.BilinForm.dualSubmodule (EFBil X) (L.restrictScalars ℤ) = L.restrictScalars ℤ := by
  refine ⟨h.1.restrictScalars, ?_⟩
  ext x
  rw [LinearMap.BilinForm.mem_dualSubmodule, Submodule.restrictScalars_mem, h.2 x]
  constructor
  · intro H y hy
    obtain ⟨k, hk⟩ := Submodule.mem_one.1 (H y hy)
    exact ⟨k, hk.symm.trans (eq_intCast _ k)⟩
  · intro H y hy
    obtain ⟨k, hk⟩ := H y hy
    exact Submodule.mem_one.2 ⟨k, (eq_intCast _ k).trans hk.symm⟩

theorem tail_le (hs : IsSympl X bas) (hn : 4 * (Module.finrank ℚ E * r) + 4 ≤ n)
    (𝓛 : Set (Lt E r)) (h𝓛 : ∀ L ∈ 𝓛, SelfD X L) {L : Lt E r} (hL : L ∈ 𝓛) :
    Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} =>
      (L'.1.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2)) ∧
    ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L},
      (L'.1.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2) ≤ 0.65 := by
  classical
  have hρ : Module.finrank ℚ (Fin r → E) = Module.finrank ℚ E * r := by
    rw [Module.finrank_pi_fintype]
    simp [mul_comm]
  have hsw := EF_swap (X := X) hs
  have hB := EFBil_nondegenerate hs
  have hrefl : (EFBil X).IsRefl := fun x y hxy => by
    have h0 : EF X x y = 0 := hxy
    show EF X y x = 0
    rw [hsw, h0, neg_zero]
  have hlr : ∀ x y, EFBil X x y = EFBil X y x ∨ EFBil X x y = -EFBil X y x :=
    fun x y => Or.inr (show EF X x y = -EF X y x from hsw x y)
  obtain ⟨hLfg, hLd⟩ := selfD_int (h𝓛 L hL)
  have key := card_selfDual_le (EFBil X) hB hrefl hlr _ hLfg hLd
  let f : {L' // L' ∈ 𝓛 ∧ L' ≠ L} → ℕ := fun L' => L'.1.toAddSubgroup.relIndex L.toAddSubgroup
  let G : {L' // L' ∈ 𝓛 ∧ L' ≠ L} → Submodule ℤ (Fin r → E) := fun L' => L'.1.restrictScalars ℤ
  have hGinj : Function.Injective G := fun a b hab =>
    Subtype.ext (Submodule.restrictScalars_injective ℤ _ _ hab)
  have hGmem : ∀ i, (G i).FG ∧ LinearMap.BilinForm.dualSubmodule (EFBil X) (G i) = G i ∧
      (G i).toAddSubgroup.relIndex (L.restrictScalars ℤ).toAddSubgroup = f i := fun i =>
    ⟨(selfD_int (h𝓛 i.1 i.2.1)).1, (selfD_int (h𝓛 i.1 i.2.1)).2, rfl⟩
  have h2 : ∀ i, 2 ≤ f i := by
    intro i
    obtain ⟨hne, h1⟩ := (key 1 le_rfl).2.2 (G i) (hGmem i).1 (hGmem i).2.1
    have hfi : f i ≠ 1 := fun h1' => i.2.2 (Submodule.restrictScalars_injective ℤ _ _ (h1 h1'))
    have : f i ≠ 0 := hne
    omega
  have hc : ∀ m, {i | f i = m}.Finite ∧ {i | f i = m}.ncard ≤ m ^ (2 * Module.finrank ℚ (Fin r → E)) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have he : {i | f i = 0} = ∅ := Set.eq_empty_of_forall_notMem fun i hi => by
        have := h2 i
        simp only [Set.mem_ofPred_eq] at hi
        omega
      simp [he]
    · have hsub : ∀ i ∈ {i | f i = m}, G i ∈ {L' : Submodule ℤ (Fin r → E) | L'.FG ∧
          LinearMap.BilinForm.dualSubmodule (EFBil X) L' = L' ∧ L'.toAddSubgroup.relIndex (L.restrictScalars ℤ).toAddSubgroup = m} :=
        fun i hi => ⟨(hGmem i).1, (hGmem i).2.1, (hGmem i).2.2.trans hi⟩
      have hfin' := (key m hm).1
      refine ⟨(hfin'.preimage hGinj.injOn).subset fun i hi => hsub i hi, ?_⟩
      exact (Set.ncard_le_ncard_of_injOn G hsub hGinj.injOn hfin').trans (key m hm).2.1
  have hρn : 4 * Module.finrank ℚ (Fin r → E) + 4 ≤ n := by rw [hρ]; exact hn
  let c : {L' // L' ∈ 𝓛 ∧ L' ≠ L} → ℂ := fun i => (((f i : ℝ) ^ (-(n : ℝ) / 2) : ℝ) : ℂ)
  have hnorm : ∀ i, ‖c i‖ = (f i : ℝ) ^ (-(n : ℝ) / 2) := fun i =>
    Complex.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have res := tail_sum_lt_one f _ n hρn h2 hc c fun i => (hnorm i).le
  simp only [hnorm] at res
  exact res

theorem norm_eq_one_of_ip {φ : TF n g} (hφ : IsSB φ) (h1 : SW.ip φ φ = 1) {c : ℂ}
    (h : SW.ip (c • φ) (c • φ) = 1) : ‖c‖ = 1 := by
  have hc := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) φ φ hφ hφ).2.2.2.1
  have hF := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) φ _ hφ hc).2.2.1
  have hsm := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) _ _ hF hF).2.2.2.2.2.1 (c * conj c)
  have e : (fun x => (c • φ) x * conj ((c • φ) x)) = (c * conj c) • (φ * fun x => conj (φ x)) := by
    funext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, map_mul]
    ring
  have h1' : haar (φ * fun x => conj (φ x)) = 1 := h1
  unfold SW.ip at h
  rw [e, hsm, h1', mul_one, Complex.mul_conj] at h
  have h2 : ‖c‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact_mod_cast h
  nlinarith [norm_nonneg c]

end GlobalTheory.SW.RecSys

namespace GlobalTheory.SW

open RecSys

theorem isSystem_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ μ : GL (Fin r) E → Lt E r → ℂ, (∀ γ ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx γ (v₀ L) = (μ γ L * (D.lam k : ℂˣ)) • v₀ (mapL γ L)) → IsSystem X bas idx M D.grp D.lats (D.phi bas hn v₀) μ := by
  intro E _ _ _ r X g bas idx n hs hn2 hnE D hn M hM0 hMm v₀ hv₀ μ hμ
  obtain ⟨-, -, hgrp, hlats, hlam, -, -⟩ := GlobalTheory.T.level_structure_properties E r X g bas idx n hs hn2 D hn
  have T4 := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀
  have T5 := GlobalTheory.T.thetaTestFunction_norm_and_overlap_bound E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀
  have hfinQ : Finite (𝓞 E ⧸ D.𝔪) := D.𝔪.finiteQuotientOfFreeOfNeBot D.ne_bot
  have hfinM : Finite (Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) :=
    inferInstanceAs (Finite (Fin r → Fin r → 𝓞 E ⧸ D.𝔪))
  have hcard : 0 < Nat.card D.J := Nat.card_pos
  refine
    { un := fun γ hγ => ((hgrp γ).1 hγ).1
      lat := fun L hL => ⟨hL.1.1, (hlats L hL).2.1⟩
      stab := fun γ hγ L hL => ((hlats L hL).2.2.2 γ hγ).1
      sb := fun L hL Λ hΛ => (T4 L hL Λ hΛ).1
      norm := ⟨(Nat.card D.J : ℝ), by exact_mod_cast hcard,
        fun L hL Λ hΛ => by rw [(T5 L hL Λ hΛ).1, Complex.ofReal_natCast],
        fun L L' => (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2), 0.65,
        by norm_num, fun L hL L' hL' Λ hΛ => (T5 L hL Λ hΛ).2 L' hL',
        fun L hL => RecSys.tail_le hs hnE D.lats (fun L' hL' => hL'.1) hL⟩
      mu := fun γ hγ L hL => ?_
      supp := fun γ hγ hγ' L hL L' hL' Λ hΛ =>
        GlobalTheory.T.thetaTestFunction_overlap_eq_zero_outside_level E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀ γ hγ hγ' L hL L' hL' Λ hΛ
      cusp := fun ξ hξ hξ0 L hL Λ hΛ =>
        GlobalTheory.T.thetaTestFunction_no_coinvariants_isotropic E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀ ξ hξ hξ0 L hL Λ hΛ
      adm := fun L hL L' hL' => GlobalTheory.T.admissible_doubledHermitianThetaFamily E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀ L hL L' hL' }
  obtain ⟨hun, k, hkJ, hred⟩ := (hgrp γ).1 hγ
  have hmem := ((hlats L hL).2.2.2 γ hγ).1
  have hrel := hμ γ hγ L hL ⟨k, hkJ⟩ hred
  have hvac := hv₀ L hL
  have hvac' := hv₀ _ hmem
  have hip : SW.ip ((μ γ L * ((D.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)) • v₀ (mapL γ L))
      ((μ γ L * ((D.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)) • v₀ (mapL γ L)) = 1 := by
    rw [← hrel, ((wG_laws E r X g bas idx n hs hn2 γ hun (v₀ L) hvac.1).2.2.1 (v₀ L) hvac.1).1]
    exact hvac.2.1
  have htn := RecSys.norm_eq_one_of_ip hvac'.1 hvac'.2.1 hip
  have hl := hlam ⟨k, hkJ⟩
  refine ⟨?_, fun Λ hΛ => ?_⟩
  · rw [norm_mul, hl, mul_one] at htn
    exact htn
  · rw [(T4 L hL Λ hΛ).2.2.2 γ hγ ⟨k, hkJ⟩ hred _ htn hrel, mul_inv_cancel_right₀ (Units.ne_zero _)]

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsLatticeVacuumIffSignedRationalFixedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLatticeVacuum_iff_signedRational_fixed : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∀ (M : ℕ), ∀ Λ ∈ Vset D.host.E S.rank M, ∀ L : Lt D.host.E T.rank, SelfD C.X L → ∀ f, C.IsTh f → (IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f ↔ ∀ y ∈ tens Λ L, epsW C.X w y • C.rho (finW S T y) f = f) := by
  first | exact @GlobalTheory.Ker.SignVac.isLatVac_iff | exact GlobalTheory.Ker.SignVac.isLatVac_iff | (intros; apply GlobalTheory.Ker.SignVac.isLatVac_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SectionsReadAsTranslatesAtScaledPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem reads_isUUOver_isVtOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (N : ℕ), Odd N → ∀ θ, A.Reads 1 y.s θ → (∀ a₁ a₂ : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a₁ = (2 : ℕ) • u) → (∃ u ∈ L, (N ^ 2 : ℕ) • a₂ = (2 : ℕ) • u) → ∀ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)), IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (A.ex (pv X idx x a₁)) (A.ex (pv X idx x a₂)) F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a₂)) (fock X bas idx x 1 (pv X idx x ((N : E) • a₁)) θ) ((N : ℂ) • z))) ∧ ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) → ∀ (t : (ptO Xo y.x) ⟶ Xo.univ.t.G) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), IsVtOver Xo.univ.t.G Xo.univ.t.PP N (fun t' => t' = A.ex (pv X idx x a)) y.s t F → A.Reads ((N : ℤ) ^ 2) F (fun z => fock X bas idx x 1 (pv X idx x ((N : E) • a)) θ ((N : ℂ) • z)) := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL N hN θ hθ
  have hpv : ∀ (n : ℕ) (a : Fin r → E), pv X idx x ((n : E) • a) = (n : ℂ) • pv X idx x a := by
    intro n a
    rw [(hx_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx).2.2.2.2.1]
    funext j
    simp
  have hfk : ∀ (φ : (Fin g → ℂ) → ℂ) (a : Fin r → E),
      Dict.fock X bas idx x (N ^ 2) (pv X idx x a) (fun z => φ ((N : ℂ) • z)) =
        fun z => Dict.fock X bas idx x 1 (pv X idx x ((N : E) • a)) φ ((N : ℂ) • z) := by
    intro φ a
    rw [hpv]
    exact (fock_laws E r X g bas idx 0 hs ⟨0, rfl⟩ x hx 1 φ).2.2.1 N _
  obtain ⟨Φ, he, -, hlat, -, -, hrd, hf⟩ := GlobalTheory.Dict.AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hχ : ∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1 := fun a ha =>
    (GlobalTheory.AnVal.chi_eq_sign E H Dw l Xo c y g _ e Φ a ha).1
  have htw : ∀ α₀ α s₁, α₀.IsGen → IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ →
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α
        (LB.pullGen Xo.univ.t.PP.L _ _ α₀ (snd (ptO Xo y.x) Xo.univ.t.G).left) →
      IsTwistPull Xo.univ.t.G Xo.univ.t.PP.L (mulT Xo.univ.t.G (ptO Xo y.x) N)
        (snd (ptO Xo y.x) Xo.univ.t.G ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α y.s s₁ →
      A.Reads ((N : ℤ) ^ 2) s₁ (fun z => θ ((N : ℂ) • z)) := by
    intro α₀ α s₁ hg hn hc ht
    exact (hrd _ _ _).1
      (GlobalTheory.T.normalisedPullbackMulN_reads_theta _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr N α₀ α y.s s₁ θ hg hn hc ht ((hrd _ _ _).2 hθ))
  have hsy : ∀ a : Fin r → E, (∃ u ∈ L, (N ^ 2 : ℕ) • a = (2 : ℕ) • u) →
      ∀ U : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x),
      SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) (A.ex (pv X idx x a)) U →
      ∀ (s s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (φ : (Fin g → ℂ) → ℂ),
      IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) U s s' →
      A.Reads ((N : ℤ) ^ 2) s (fun z => φ ((N : ℂ) • z)) →
      A.Reads ((N : ℤ) ^ 2) s'
        (fun z => Dict.fock X bas idx x 1 (pv X idx x ((N : E) • a)) φ ((N : ℂ) • z)) := by
    rintro a ⟨u, hu, hau⟩ U hU s s' φ hA hs'
    have h2 : ((N ^ 2 : ℕ) : ℂ) • pv X idx x a = (2 : ℂ) • pv X idx x u := by
      have h3 := hpv 2 u
      rw [← hpv, Nat.cast_smul_eq_nsmul, hau, ← Nat.cast_smul_eq_nsmul E, h3]
      norm_num
    rw [← he] at hU
    have h4 := GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation _ Xo.univ.t.G Xo.univ.t.PP y.x g Φ.toAnFr hχ ((N : ℤ) ^ 2) (N ^ 2) U
      (pv X idx x a) (pv X idx x u) s s' _ hN.pow ((hlat _).2 ⟨u, hu, rfl⟩) h2 hU hA ((hrd _ _ _).2 hs')
    have h5 := hf (N ^ 2) (pv X idx x a) (fun z => φ ((N : ℂ) • z))
    rw [Nat.cast_pow, hfk] at h5
    rw [h5] at h4
    exact (hrd _ _ _).1 h4
  refine ⟨?_, ?_⟩
  · rintro a₁ a₂ h₁ h₂ F ⟨α₀, α, s₁, s₂, U₁, U₂, hg, hn, hc, ht, hU₁, hA₁, hU₂, hA₂⟩
    exact hsy a₂ h₂ U₂ hU₂ s₂ F _ hA₂ (hsy a₁ h₁ U₁ hU₁ s₁ s₂ _ hA₁ (htw α₀ α s₁ hg hn hc ht))
  · rintro a h t F ⟨t', α₀, α, s₁, U, -, rfl, hg, hn, hc, ht, hU, hA⟩
    exact hsy a h U hU s₁ F _ hA (htw α₀ α s₁ hg hn hc ht)

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattices_at_level : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∀ (M : ℕ) (h : GA D S) (Λ : Lt D.host.E S.rank), 0 < M → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → Λ ∈ Vset D.host.E S.rank M) ∧ ∀ (Lv : SW.Level C.X) (g : GA D T) (L : Lt D.host.E T.rank), L.FG → IsMov (fmt T g) C.X.Λ L → SelfD C.X L ∧ (TrivAt T (C.under Lv) g → L ∈ Lv.lats) ∧ C.under Lv ≠ ⊥ ∧ (L ∈ Lv.lats → ∃ g' ∈ GfC T, TrivAt T (C.under Lv) g' ∧ IsMov (fmt T g') C.X.Λ L) := by
  first | exact @GlobalTheory.Ker.MovLev.mov_mem_lattices | exact GlobalTheory.Ker.MovLev.mov_mem_lattices | (intros; apply GlobalTheory.Ker.MovLev.mov_mem_lattices <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionSpaceHeisenbergLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_space_heisenberg_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), C.IsTh 0 ∧ (∀ f f', C.IsTh f → C.IsTh f' → C.IsTh (f + f') ∧ ((∀ w, IsRealPt w → f w = f' w) → f = f')) ∧ ∀ f, C.IsTh f → (∀ a : ℂ, C.IsTh (a • f)) ∧ (∀ w, C.IsTh (C.rho w f)) ∧ (∀ w w', C.rho w (C.rho w' f) = C.ψ (symplOH S T w w') • C.rho (w + w') f) ∧ (∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) w, IsRealPt w → C.rho (finW S T y) f w = cexp (π * I * (EFR C.X (C.realPt w) (embR C.X y) : ℝ)) * f (w - (ratW T S yᵀ - finW S T y))) ∧ (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, C.IsTh fun w => f (actO S T γ γ' w)) ∧ ∃ N : ℕ, 0 < N ∧ ∀ u ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ), C.rho (N • u) f = f := by
  first | exact @GlobalTheory.ThetaSpace.theta_space_laws | exact GlobalTheory.ThetaSpace.theta_space_laws | (intros; apply GlobalTheory.ThetaSpace.theta_space_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesLowerRowsZeroEqFreeLowerRowsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_lowerRowsZero_eq_freeLowerRows : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 : Ideal (𝓞 E)), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ Λ ∈ Vset E n M, ∀ P ∈ Harm.rowHighest ℂ k k', ∃ Λ' ∈ Vset E n M, ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ L ∈ D.lats, ∀ x ∈ X.dom, thP X hr bas idx (D.phi bas hn v₀ L Λ) P x = thP X hr bas idx (phiF bas D 𝔐 hn v₀ L Λ') P' x := by
  first | exact @GlobalTheory.Dict.DiagFree.thP_phi_eq_thP_phiF | exact GlobalTheory.Dict.DiagFree.thP_phi_eq_thP_phiF | (intros; apply GlobalTheory.Dict.DiagFree.thP_phi_eq_thP_phiF <;> assumption)
end

