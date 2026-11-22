import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AllHypothesesInhabited
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero GlobalTheory.ThetaMean GlobalTheory.SiegelFormula.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SiegelWeilMiddle.Model

variable {D : D7}

abbrev iso9 (D : D7) : HSp D := Examples₂.lorentzSpace (E := D.host.E) Examples₂.star_isIntegral

theorem wittIndex_eq_one (D : D7) : Formalism.MainNotions.SchurIrreducible.wittIdx (iso9 D) = 1 := by
  have h1 : Formalism.MainNotions.SchurIrreducible.wittIdx (iso9 D) ≤ 1 :=
    (GlobalTheory.WittSignature.wittIdx_le_signature D.host.E (iso9 D) (Examples₂.lorentzSpace_signature_ok _) D.host.φ₀
      (D.sp.cm.cmUnram.2.1 D.host.φ₀)).2
  let v : Fin (8 + 1) → D.host.E := Pi.single 0 1 + Pi.single 8 1
  have hv : v ≠ 0 := fun h => by simpa [v] using congrFun h 0
  have h0 : Examples₂.diagForm (E := D.host.E) (8 + 1) Examples₂.negLast v v = 0 := by
    simp [Examples₂.diagForm_apply, v, Fin.sum_univ_succ, Examples₂.sgn, Examples₂.negLast, Pi.single_apply]
  have h2 : 1 ≤ Formalism.MainNotions.SchurIrreducible.wittIdx (iso9 D) := le_csSup (bddAbove_witt _)
    ⟨Submodule.span D.host.E {(v : (iso9 D).V)}, finrank_span_singleton hv, by
      intro x hx y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
      change Examples₂.diagForm (E := D.host.E) (8 + 1) Examples₂.negLast (a • v) (b • v) = 0
      simp [h0]⟩
  omega

theorem range_inhabited (D : D7) :
    (∃ A B : HSp D, 0 < Formalism.MainNotions.SchurIrreducible.wittIdx B ∧ A.rank < B.rank ∧ B.rank ≤ 2 * A.rank ∧
      A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) ∧
    (∃ A B : HSp D, B.rank = 2 * A.rank ∧ A.rank < B.rank ∧ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) :=
  ⟨⟨pos D 5, iso9 D, by rw [wittIndex_eq_one]; decide, show 5 < 8 + 1 by decide, show 8 + 1 ≤ 2 * 5 by decide,
    by rw [wittIndex_eq_one]; exact show 5 + 1 < 8 + 1 by decide⟩,
   ⟨pos D 1, pos D 2, rfl, show 1 < 2 by decide, by rw [wittIdx_pos]; exact show 1 + 0 < 2 by decide⟩⟩

theorem split_excluded (A V : HSp D) (h : V.rank = A.rank) :
    ¬ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx (dblSp V) < (dblSp V).rank := by
  rw [wittIdx_dblSp]
  change ¬ A.rank + V.rank < V.rank + V.rank
  omega

theorem hypotheses_inhabited (H : GlobalTheory.Published.WeilRepresentationUnitaryPair) (D : D7) :
    ∃ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle)
      (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (a : GL (Fin A.rank) (AE D))
      (μ : Measure (WO A B)) (𝓨 : Set (WO A B)) (ν : Measure (GA D B)),
      0 < Formalism.MainNotions.SchurIrreducible.wittIdx B ∧ A.rank < B.rank ∧ B.rank ≤ 2 * A.rank ∧ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank ∧
        IsWeilDatumO ψ (dblSp A) B 1 χB ω ∧ IsMaj A a ∧ IsCovolOne (ratL B A) μ 𝓨 ∧ ν.IsHaarMeasure ∧
        (∃ f, IsThetaFunO ψ (dblSp A) B f ∧ f ≠ 0) ∧ ∃ f, IsThetaFunO ψ (dblSp A) B f ∧ IsKFinVec ω (Khat A a) f := by
  obtain ⟨A, B, h0, h1, h2, h3⟩ := (range_inhabited D).1
  obtain ⟨m, ψ, χ, ω, f, μ, 𝓨, hm, hω, hf, hf0, hμ⟩ := data_exist H A B
  obtain ⟨a, ha⟩ := exists_isMaj A
  exact ⟨ψ, A, B, χ, ω, a, μ, 𝓨, m, h0, h1, h2, h3, hω, ha, hμ, hm, ⟨f, hf, hf0⟩,
    0, GlobalTheory.ThetaMean.Model.zero_vec ψ _ B ω _⟩

theorem conclusion_zero (A B : HSp D) (h : A.rank < B.rank)
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))
    (a : GL (Fin A.rank) (AE D)) (μ : Measure (WO A B)) (𝓨 : Set (WO A B)) (ν : Measure (GA D B)) :
    Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 0) (sZero A B)) (sZero A B) (thetaMean ω ν 0) := by
  simpa only [if_pos h, one_smul] using GlobalTheory.ThetaMean.Model.conclusion_zero A B ω a μ 𝓨 ν

theorem integrable_of_weil (H : GlobalTheory.Published.WeilSiegelFormulaUnitary) {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D}
    (h1 : A.rank < B.rank) (h2 : B.rank ≤ 2 * A.rank) (h3 : A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) {χ ω f}
    (hω : IsWeilDatumO ψ (dblSp A) B 1 χ ω) (hf : IsThetaFunO ψ (dblSp A) B f) (ν : Measure (GA D B)) [ν.IsHaarMeasure]
    (g : GA D (dblSp A)) : Integrable (AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO ω g h f) (autMeasure B ν) :=
  ((H D A B ν inferInstance (GlobalTheory.Published.one_le_of_range h1 h2) (.inr h3)).2 ψ χ ω hω f hf).1 g

theorem conclusion_of_aniso (H : GlobalTheory.Published.SiegelWeilAnisotropicUnitary) {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D}
    (h1 : A.rank < B.rank) (h2 : B.rank ≤ 2 * A.rank) (hB : IsAniso B) {χ ω f}
    (hω : IsWeilDatumO ψ (dblSp A) B 1 χ ω) {a : GL (Fin A.rank) (AE D)} (ha : IsMaj A a)
    (hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a)) {μ : Measure (WO A B)} {𝓨 : Set (WO A B)}
    (hμ : IsCovolOne (ratL B A) μ 𝓨) (ν : Measure (GA D B)) [ν.IsHaarMeasure]
    (hf : IsThetaFunO ψ (dblSp A) B f) (hK : IsKFinVec ω (Khat A a) f) :
    Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 f) (sZero A B)) (sZero A B) (thetaMean ω ν f) := by
  have hA := GlobalTheory.Published.one_le_of_range h1 h2
  simpa only [if_pos h1, one_smul] using
    (H D ψ A B hA (hA.trans h1.le) hB χ ω hω a ha hI μ 𝓨 hμ ν inferInstance f hf hK).2

theorem weilPair : GlobalTheory.Published.WeilRepresentationUnitaryPair := fun D ψ S T χS χT hψ h1 h2 h3 h4 =>
  GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT
    ((GlobalTheory.WeilParts.exists_isEtaTilde_unramified D).imp fun _ h => h) h1 h2 h3 h4

theorem all_hypotheses_inhabited (D : D7) (A B : HSp D) :
    ∃ (ψ : AddChar (AF D.host.F) ℂ) (χB : (AE D)ˣ →* Circle)
      (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (a : GL (Fin A.rank) (AE D))
      (θ : InfFam D) (sS : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.RealMat (dblSp A)) (sB : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.RealMat B)
      (μ : Measure (WO A B)) (𝓨 : Set (WO A B)) (ν : Measure (GA D B)) (f : WO (dblSp A) B → ℂ),
      IsWeilDatumO ψ (dblSp A) B 1 χB ω ∧ IsMaj A a ∧ HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) ∧ IsInfFam θ ∧
        (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) ∧ (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) ∧
        (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
          sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) ∧
        IsCovolOne (ratL B A) μ 𝓨 ∧ ν.IsHaarMeasure ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec ψ θ (dblSp A) B sS sB f ∧ f ≠ 0 := by
  obtain ⟨m, ψ, χ, ω, -, μ, 𝓨, hm, hω, -, -, hμ⟩ := data_exist weilPair A B
  obtain ⟨θ, hθ⟩ := hω.std.2.1
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ)
      (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  obtain ⟨a, ha, hfr⟩ := GlobalTheory.Core.Rk.MajFrame.exists_maj_cart D θ A (s A) hθ (hs A)
  obtain ⟨h1, h2⟩ := GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl D θ A (s A) a hθ (hs A) hfr
  obtain ⟨f, hf, f0⟩ := GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua.exists_isVac_ne_zero hω.std hθ h1 (hs B)
  refine ⟨ψ, χ, ω, a, θ, _, s B, μ, 𝓨, m, f, hω, ha, GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha, hθ, h1, hs B, h2, hμ, hm,
    ⟨hf.1, 1, fun l hl => ?_⟩, f0⟩
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
  exact hf.2 p.1 p.2

end GlobalTheory.SiegelWeilMiddle.Model

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisPoleLEZeroOfLt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis.SimplePoleModel

open GlobalTheory.Eis

theorem resEta_one_two_mul (D : D7) (k : ℕ) : ResEta D 1 (2 * k) :=
  ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun η h x => by
    rw [pow_mul, pow_two, GlobalTheory.VolHeckeCompare.IsEta_mul_self h x, one_pow]; rfl⟩

open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem hypotheses_hold (D : D7) (V : HSp D) (k : ℕ) (s₁ : ℂ) :
    ∃ (a : GL (Fin V.rank) (AE D)) (φ : GA D (dblSp V) → ℂ), IsMaj V a ∧
      HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) ∧ IsHeckeChar D 1 ∧ ResEta D 1 (2 * k) ∧
      φ ∈ degPS V a 1 s₁ ∧ ∀ g, φ g ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_isMaj V
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  refine ⟨a, sph V a s₁, ha, hI, ⟨continuous_const, fun _ => rfl⟩, resEta_one_two_mul D k, sph_mem hI s₁, fun g => ?_⟩
  simp only [sph, npow_eq_exp (hgtH_pos _)]
  exact Complex.exp_ne_zero _

theorem poleLE_succ {h : ℂ → ℂ} {s₀ : ℂ} {k : ℕ} (a : PoleLE h s₀ k) : PoleLE h s₀ (k + 1) :=
  a.imp fun _ b => ⟨b.1, le_trans (by exact_mod_cast (by omega : (-((k + 1 : ℕ) : ℤ)) ≤ -(k : ℤ))) b.2⟩

theorem eisPoleLE_zero_of_lt {D : D7} {V : HSp D} {a : GL (Fin V.rank) (AE D)}
    (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a)) {μ : (AE D)ˣ →* Circle} {b : ℕ} (hμ : IsHeckeChar D μ)
    {s₁ : ℂ} {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s₁) (hb : 2 * V.rank < b) :
    EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 0 := by
  have h1 := (sphConv D V a hI).isEisFamily_flat hI hφ hμ
  refine (eisValueAt_iff_eisPoleLE.1 (h1.eisValueAt h1.analyticOnNhd_flat ?_)).1
  have : (2 * V.rank : ℝ) < b := by exact_mod_cast hb
  simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re]
  linarith

theorem simplePole_iff : Published.SiegelEisensteinSimplePole ↔
    ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a →
    ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
    ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ →
      V.rank < b → b ≤ 2 * V.rank → EisPoleLE V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1 := by
  refine ⟨fun h D V a ha μ b hμ hb s₁ φ hφ h1 h2 => h D V (by omega) a ha (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha)
    μ b hμ hb s₁ φ hφ h1, fun h D V _ a ha hI μ b hμ hb s₁ φ hφ h1 => ?_⟩
  rcases le_or_gt b (2 * V.rank) with h2 | h2
  · exact h D V a ha μ b hμ hb s₁ φ hφ h1 h2
  · have := eisPoleLE_zero_of_lt hI hμ hφ h2
    exact ⟨this.1, fun g => poleLE_succ (this.2 g)⟩

theorem eisRegularAt_one (hc : Published.SiegelEisensteinContinuation) (hp : Published.SiegelEisensteinSimplePole)
    {D : D7} {V : HSp D} (h0 : 0 < V.rank) {a : GL (Fin V.rank) (AE D)} (ha : IsMaj V a)
    {μ : (AE D)ˣ →* Circle} {b : ℕ} (hμ : IsHeckeChar D μ) (hb : ResEta D μ b)
    {s₁ : ℂ} {φ : GA D (dblSp V) → ℂ} (hφ : φ ∈ degPS V a μ s₁) (hab : V.rank < b) :
    EisRegularAt V (flat V a φ s₁) (((b : ℂ) - V.rank) / 2) 1 :=
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  let ⟨_, h⟩ := (hc D V h0 a ha hI μ b hμ hb s₁ φ hφ).2 (((b : ℂ) - V.rank) / 2)
  h.of_poleLE (hp D V h0 a ha hI μ b hμ hb s₁ φ hφ hab)

end GlobalTheory.Eis.SimplePoleModel

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.ExistsNotEisContinues
section
noncomputable section

open scoped ComplexConjugate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Filter Topology Set Metric MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis.ContModel

theorem hypotheses_inhabited (n b : ℕ) (s₁ : ℂ) :
    ∃ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (μ : (AE D)ˣ →* Circle) (φ : GA D (dblSp V) → ℂ),
      V.rank = n ∧ IsMaj V a ∧ HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) ∧ IsHeckeChar D μ ∧ ResEta D μ (2 * b) ∧
        φ ∈ degPS V a μ s₁ ∧ ∀ g, φ g ≠ 0 := by
  obtain ⟨D⟩ := GlobalTheory.Mem.nonempty_record
  obtain ⟨V, a, -, -, -, -, h1, h2, -⟩ := DblModel.hypotheses_inhabited D n 0
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a h2
  refine ⟨D, V, a, 1, sph V a s₁, h1, h2, hI, ⟨continuous_const, fun _ => rfl⟩, DblModel.resEta_one D b,
    sph_mem hI s₁, fun g => ?_⟩
  rw [sph, npow_eq_exp (hgtH_pos _)]
  exact Complex.exp_ne_zero _

variable {D : D7} {V : HSp D} {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : GA D (dblSp V) → ℂ}

theorem isEisFamily_flat (ha : IsMaj V a) (hμ : IsHeckeChar D μ) (hφ : φ ∈ degPS V a μ s₁) :
    IsEisFamily V (flat V a φ s₁) :=
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  (sphConv D V a hI).isEisFamily_flat hI hφ hμ

theorem eisCont_right (ha : IsMaj V a) (hμ : IsHeckeChar D μ) (hφ : φ ∈ degPS V a μ s₁) :
    (∀ s ∈ rightOf (V.rank / 2), eisCont V (flat V a φ s₁) s = eis V (flat V a φ s₁ s)) ∧
    (∀ g, DifferentiableOn ℂ (eisCont V (flat V a φ s₁) · g) (rightOf (V.rank / 2))) ∧
    ContinuousOn (fun x : ℂ × GA D (dblSp V) => eisCont V (flat V a φ s₁) x.1 x.2) (rightOf (V.rank / 2) ×ˢ univ) := by
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  have h := isEisFamily_flat ha hμ hφ
  have e : ∀ s ∈ rightOf (V.rank / 2), eisCont V (flat V a φ s₁) s = eis V (flat V a φ s₁ s) := fun s hs =>
    (h.eisValueAt h.analyticOnNhd_flat hs).eisCont_eq
  refine ⟨e, fun g => (h.analyticOnNhd_flat g).differentiableOn.congr fun s hs => congrFun (e s hs) g, ?_⟩
  exact ((sphConv D V a hI).continuousOn_eis hI (continuous_flat hI hφ).continuousOn
    fun s _ => flat_mem hI hφ s).congr fun x hx => congrFun (e _ hx.1) _

theorem one_le_eisCont_sph (ha : IsMaj V a) {σ : ℝ} (hσ : (V.rank : ℝ) / 2 < σ) :
    1 ≤ (eisCont V (flat V a (sph V a σ) σ) σ 1).re := by
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  rw [(eisCont_right (μ := 1) ha ⟨continuous_const, fun _ => rfl⟩ (sph_mem hI σ)).1 σ (by simpa using hσ)]
  simpa only [flatH_self] using ((sphConv_iff hI).1 (sphConv D V a hI)).2 σ hσ

theorem iff_reduced : Published.SiegelEisensteinContinuation ↔
    ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a →
      ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
      ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ →
        (∀ g, Continues (eisSer V (flat V a φ s₁) g)) ∧ ∀ s₀, ∃ k, EisRegularAt V (flat V a φ s₁) s₀ k :=
  ⟨fun h D V h0 a ha μ b hμ hb s₁ φ hφ =>
    let h' := h D V h0 a ha (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha) μ b hμ hb s₁ φ hφ
    ⟨h'.1.2, h'.2⟩,
  fun h D V h0 a ha _ μ b hμ hb s₁ φ hφ =>
    let h' := h D V h0 a ha μ b hμ hb s₁ φ hφ
    ⟨⟨isEisFamily_flat ha hμ hφ, h'.1⟩, h'.2⟩⟩

theorem modGrowth_eis (hP : Published.SiegelEisensteinContinuation) (h0 : 0 < V.rank) (ha : IsMaj V a) {b : ℕ}
    (hμ : IsHeckeChar D μ) (hb : ResEta D μ b) (hφ : φ ∈ degPS V a μ s₁) (hs : (V.rank : ℝ) / 2 < s₁.re) :
    Grow.ModGrowth (dblSp V) (eis V φ) := by
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  obtain ⟨k, hk⟩ := (hP D V h0 a ha hI μ b hμ hb s₁ φ hφ).2 s₁
  have hv := (sphConv D V a hI).eisValueAt_flat hI hφ hμ hs
  obtain ⟨r, hr, -, -, C, N, h⟩ := hk.of_eisValueAt hv
  exact ⟨C, N, fun g => hv.eisCont_eq ▸ h s₁ (mem_ball_self hr) g⟩

theorem exists_not_eisContinues (V : HSp D) : ∃ Φ, IsEisFamily V Φ ∧
    (∀ g, AnalyticOnNhd ℂ (eisSer V Φ g) (rightOf 0)) ∧ ¬ EisContinues V Φ := by
  obtain ⟨Φ, h1, h2, -⟩ := Model.exists_family V Measure.haar fun s => Complex.exp s⁻¹
  have e : ∀ g, eisSer V Φ g = fun s => Complex.exp s⁻¹ := fun g => funext fun s => h1 s g
  have hA : AnalyticOnNhd ℂ (fun s : ℂ => Complex.exp s⁻¹) (rightOf 0) := fun s hs =>
    (analyticAt_id.inv (by rintro (rfl : s = 0); simp at hs)).cexp
  refine ⟨Φ, h2.1, fun g => e g ▸ hA, fun h => ?_⟩
  have h3 : (0 : ℂ) ∈ contDom fun s : ℂ => Complex.exp s⁻¹ := by
    rw [(continues_iff hA).1 (e 1 ▸ h.2 1)]; trivial
  obtain ⟨k, hk⟩ := meromorphicOn_cont _ 0 h3
  have hl : Tendsto (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    exact (Complex.continuous_ofReal.tendsto' 0 0 rfl).comp tendsto_inv_atTop_zero
  have h4 := (hk.continuousAt.tendsto.comp hl).norm
  have h5 : Tendsto (fun t : ℝ => Real.exp t / t ^ k) atTop atTop := Real.tendsto_exp_div_pow_atTop k
  refine not_tendsto_atTop_of_tendsto_nhds h4 (h5.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
  have h6 := eqOn_cont hA (x := ((t⁻¹ : ℝ) : ℂ)) (by simpa using ht)
  simp only [Function.comp, h6, sub_zero, smul_eq_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp]
  simp [abs_of_pos ht, div_eq_inv_mul]

end GlobalTheory.Eis.ContModel

end
end

