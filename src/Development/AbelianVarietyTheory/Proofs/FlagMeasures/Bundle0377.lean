import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0373
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0350
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0364
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0310
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0188
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0369
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0271
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0145
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0375
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0376
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicIteratedIntegrabilityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_convolution_anisotropic : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), 1 < A.rank → IsAniso A → ∀ μ 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ → ∀ ν 𝓝, IsUnitN B d.eM ν 𝓝 → ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) → ∀ (Φ : X.Sch L A) φ F, IsAutFun A φ → IsAutFun B F → d.Conv Wl.ψ (omZ Wl L A Φ) μ 𝓕 ν 𝓝 s φ F := by
  first | exact @GlobalTheory.Per.FJConv.conv_of_isAniso | exact GlobalTheory.Per.FJConv.conv_of_isAniso | (intros; apply GlobalTheory.Per.FJConv.conv_of_isAniso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselEnergyNormalisedFrameChangeStatement
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselEnergy_normalised_frame_change : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Bs : B.RealPlaceData k r L.Wp L.Wq) (cN : ℝ) (F : B.Mat k r → (L.Wq →L[ℂ] L.Wp)), 1 ≤ k → IsStdOf L μsec Bs → IsRatioN k r cN → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → ∫⁻ p : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') p * Formalism.MainNotions.S.hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))) = ENNReal.ofReal (lamN L cN ^ 4 / D.GamLev k r ‖cStd / L.c‖⁻¹ 1 0) * B.normSq Bs (conjF (cStd / L.c) F) := by
  first | exact @GlobalTheory.ThA.energy_change_of_frame | exact GlobalTheory.ThA.energy_change_of_frame | (intros; apply GlobalTheory.ThA.energy_change_of_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BoundedEquivariantMapSmoothContinuousSeminormBouStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedEquivariantMap_smooth_continuous_seminorm_bound : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (T : H → Mat k r → Wp), IsURepOn (GG k r) σ → IsHaarOn (GG k r) μG → (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x) + T u' (Matrix.of x)) → (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) → (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H, AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) → (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG] fun x => T u (Matrix.of x * y)) → ∃ (C : ℝ) (Ws : List (List (Mat k r))), (∀ ws ∈ Ws, ∀ X ∈ ws, InLieHpk k r X) ∧ ∀ u : H, IsSmoothVec σ u → ∃ f : Mat k r → Wp, ContinuousOn f (GG k r) ∧ (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] (fun x => T u (Matrix.of x)) ∧ ‖f 1‖ ≤ C * (Ws.map fun ws => ‖dsigW σ ws u‖).sum := by
  first | exact @GlobalTheory.SgInf.reg_main | exact GlobalTheory.SgInf.reg_main | (intros; apply GlobalTheory.SgInf.reg_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardExactGramIntegralFrameClassesLeStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_exactGramIntegralFrameClasses_le : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (Z : GramM D) (s : ℕ) (De Q : ℝ), 1 ≤ s → s ≤ D.R.k → SubOK D (L0X D Λ (lf D F0)) P s De → QOK D u u' Z Q → (cntCl (ExSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P) (TEqv D Λ (lf D F0)) : ℝ≥0∞) ≤ ENNReal.ofReal (frB D s (NT D u) De Q) := by
  first | exact @GlobalTheory.LoopC.FrEx.cntCl_ExSet_le | exact GlobalTheory.LoopC.FrEx.cntCl_ExSet_le | (intros; apply GlobalTheory.LoopC.FrEx.cntCl_ExSet_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardStabilizerInnerDatumRowDoubleCoset
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StabCnt
open Formalism.L2.SG.Pf

variable {D : D7} {T T' : D.host.E}

theorem mul_mem_isometriesFixingBothFrames {F : LFlag (VS D) D.R.rS T} {F' : LFlag (VS D) D.R.rS T'} {h k : GV D} (hh : h ∈ H0 F F')
    (hk : k ∈ H0 F F') : h * k ∈ H0 F F' :=
  ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hh.1 hk.1, fun a => by rw [le_mul_app, hk.2.1 a, hh.2.1 a],
    fun a => by rw [le_mul_app, hk.2.2 a, hh.2.2 a]⟩

theorem principalPolarisation_exists_unique_section (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') : (1 : GV D) ∈ H0 F F' :=
  ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun _ => rfl, fun _ => rfl⟩

theorem nlam_iff_nrat {F0 : LFlag (VS D) D.R.rS T} {lam : LV D} {b : GV D} (hb : b ∈ Aut0 F0 lam) :
    b ∈ NLam lam F0 ↔ b ∈ NRat F0 :=
  ⟨fun h => ⟨h.1.1, h.2.1, h.2.2⟩, fun h => ⟨⟨h.1, hb.2⟩, h.2.1, h.2.2⟩⟩

section Corr

variable {F0 F : LFlag (VS D) D.R.rS T} {F0' F' : LFlag (VS D) D.R.rS T'} {γ g : GV D}

theorem s_adapt (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hg : Adapt g F0 F) (hg' : Adapt g (mapLF γ F0') F')
    {b₁ b₂ n n' : GV D} (hb1 : Adapt b₁ F0 F0) (hb2 : Adapt b₂ F0' F0') (hn : n ∈ NRat F0) (hn' : n' ∈ NRat F0')
    (he : b₁ * γ * b₂⁻¹ = n * γ * n') :
    Adapt (g * n⁻¹ * b₁ * g⁻¹) F F ∧ Adapt (g * n⁻¹ * b₁ * g⁻¹) F' F' ∧
      g * n⁻¹ * b₁ * g⁻¹ = (g * γ) * (n' * b₂) * (g * γ)⁻¹ := by
  have e1 : n⁻¹ * b₁ = γ * n' * b₂ * γ⁻¹ := by
    calc n⁻¹ * b₁ = n⁻¹ * (b₁ * γ * b₂⁻¹) * b₂ * γ⁻¹ := by group
      _ = n⁻¹ * (n * γ * n') * b₂ * γ⁻¹ := by rw [he]
      _ = γ * n' * b₂ * γ⁻¹ := by group
  have hseq : g * n⁻¹ * b₁ * g⁻¹ = (g * γ) * (n' * b₂) * (g * γ)⁻¹ := by
    calc g * n⁻¹ * b₁ * g⁻¹ = g * (n⁻¹ * b₁) * g⁻¹ := by group
      _ = g * (γ * n' * b₂ * γ⁻¹) * g⁻¹ := by rw [e1]
      _ = (g * γ) * (n' * b₂) * (g * γ)⁻¹ := by group
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  refine ⟨adapt_mul (adapt_inv hg) (adapt_mul hb1 (adapt_mul (adapt_nrat (nrat_inv hn)) hg)), ?_, hseq⟩
  rw [hseq]
  exact adapt_mul (adapt_inv hG) (adapt_mul (adapt_mul hb2 (adapt_nrat hn')) hG)

theorem cong_mod {A0 A : LFlag (VS D) D.R.rS T} {a s μ n b : GV D} (ha : Adapt a A0 A) (hs : Adapt s A A)
    (hμ : μ ∈ NRat A) (hn : n ∈ NRat A0) (hb : Adapt b A0 A0) (hseq : s = a * (n * b) * a⁻¹) :
    ∀ x ∈ orth (VS D) (Xsp A), (s * μ⁻¹) x - (a * b * a⁻¹) x ∈ Xsp A := by
  intro x hx
  have e : (s * μ⁻¹) x - (a * b * a⁻¹) x = s (μ⁻¹ x - x) + a (n (b (a⁻¹ x)) - b (a⁻¹ x)) := by
    rw [hseq]
    simp only [le_mul_app, map_sub]
    abel
  rw [e]
  refine add_mem (mem_of_map_eq (adapt_xsp hs) ((nrat_inv hμ).2.2 x hx)) ?_
  refine mem_of_map_eq (adapt_xsp ha) (hn.2.2 _ ?_)
  exact mem_of_map_eq (adapt_orth hb) (symm_mem_of_map_eq (adapt_orth ha) hx)

variable (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hg : Adapt g F0 F) (hg' : Adapt g (mapLF γ F0') F')
  (hI : ∀ s, Adapt s F F → Adapt s F' F' → ∃! h, h ∈ H0 F F' ∧ h⁻¹ * s ∈ NRat F ∧ h⁻¹ * s ∈ NRat F')
include hγ hg hg'

include hI in
theorem corr_exists {lam lam' : LV D} {b : GV D × GV D} (hb : InB F0 F0' lam lam' γ b) :
    ∃ h, Corr F0 F F0' F' γ g b h := by
  obtain ⟨⟨n, hn, n', hn', he⟩, -⟩ := hb.2.2
  obtain ⟨hs1, hs2, -⟩ := s_adapt hγ hg hg' hb.1.1 hb.2.1.1 hn hn' he
  obtain ⟨h, ⟨hh, h1, h2⟩, -⟩ := hI _ hs1 hs2
  exact ⟨h, hh, n, hn, n', hn', he, h1, h2⟩

include hI in
theorem corr_unique {b : GV D × GV D} (hb1 : Adapt b.1 F0 F0) (hb2 : Adapt b.2 F0' F0') {h k : GV D}
    (hh : Corr F0 F F0' F' γ g b h) (hk : Corr F0 F F0' F' γ g b k) : h = k := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hk0, m, hm, m', hm', he2, k1, k2⟩ := hk
  obtain ⟨hs1, hs2, hseq⟩ := s_adapt hγ hg hg' hb1 hb2 hn hn' he
  obtain ⟨-, -, hteq⟩ := s_adapt hγ hg hg' hb1 hb2 hm hm' he2
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  have tF : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F := by
    have e : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) = (g * b.1⁻¹) * (m * n⁻¹) * (g * b.1⁻¹)⁻¹ := by group
    rw [e]; exact nrat_conj (adapt_mul (adapt_inv hb1) hg) (nrat_mul hm (nrat_inv hn))
  have tF' : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) ∈ NRat F' := by
    have e : (g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) =
        ((g * γ) * b.2⁻¹) * (m'⁻¹ * n') * ((g * γ) * b.2⁻¹)⁻¹ := by rw [hseq, hteq]; group
    rw [e]; exact nrat_conj (adapt_mul (adapt_inv hb2) hG) (nrat_mul (nrat_inv hm') hn')
  obtain ⟨x, -, hu⟩ := hI _ hs1 hs2
  have ek : k⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) = (k⁻¹ * (g * m⁻¹ * b.1 * g⁻¹)) * ((g * m⁻¹ * b.1 * g⁻¹)⁻¹ * (g * n⁻¹ * b.1 * g⁻¹)) := by group
  rw [hu h ⟨hh0, h1, h2⟩, hu k ⟨hk0, by rw [ek]; exact nrat_mul k1 tF, by rw [ek]; exact nrat_mul k2 tF'⟩]

theorem corr_mul {lam lam' : LV D} {b c : GV D × GV D} (hb : InB F0 F0' lam lam' γ b)
    (hc : InB F0 F0' lam lam' γ c) {h k : GV D} (hh : Corr F0 F F0' F' γ g b h)
    (hk : Corr F0 F F0' F' γ g c k) : Corr F0 F F0' F' γ g (b * c) (h * k) := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hk0, m, hm, m', hm', hec, k1, k2⟩ := hk
  have hk1 := (frameAdaptedIsometry_of_fixing_both_frames hk0).1
  have hk2 := (frameAdaptedIsometry_of_fixing_both_frames hk0).2
  refine ⟨mul_mem_isometriesFixingBothFrames hh0 hk0, b.1 * m * b.1⁻¹ * n, nrat_mul (nrat_conj hb.1.1 hm) hn,
    n' * (b.2 * m' * b.2⁻¹), nrat_mul hn' (nrat_conj hb.2.1.1 hm'), ?_, ?_, ?_⟩
  · show b.1 * c.1 * γ * (b.2 * c.2)⁻¹ = _
    calc b.1 * c.1 * γ * (b.2 * c.2)⁻¹ = b.1 * (c.1 * γ * c.2⁻¹) * b.2⁻¹ := by group
      _ = b.1 * (m * γ * m') * b.2⁻¹ := by rw [hec]
      _ = b.1 * m * b.1⁻¹ * (b.1 * γ * b.2⁻¹) * (b.2 * m' * b.2⁻¹) := by group
      _ = b.1 * m * b.1⁻¹ * (n * γ * n') * (b.2 * m' * b.2⁻¹) := by rw [he]
      _ = _ := by group
  · have e : (h * k)⁻¹ * (g * (b.1 * m * b.1⁻¹ * n)⁻¹ * (b * c).1 * g⁻¹) =
        (k⁻¹ * (h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹)) * k⁻¹⁻¹) * (k⁻¹ * (g * m⁻¹ * c.1 * g⁻¹)) := by
      show _ = _; simp only [Prod.fst_mul]; group
    rw [e]; exact nrat_mul (nrat_conj (adapt_inv hk1) h1) k1
  · have e : (h * k)⁻¹ * (g * (b.1 * m * b.1⁻¹ * n)⁻¹ * (b * c).1 * g⁻¹) =
        (k⁻¹ * (h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹)) * k⁻¹⁻¹) * (k⁻¹ * (g * m⁻¹ * c.1 * g⁻¹)) := by
      show _ = _; simp only [Prod.fst_mul]; group
    rw [e]; exact nrat_mul (nrat_conj (adapt_inv hk2) h2) k2

theorem corr_stab {lam lam' Λ : LV D} (hγl : Formalism.HermitianLatticesTheory.gmap γ lam' = lam) (hΛ : Λ = Formalism.HermitianLatticesTheory.gmap g lam)
    {b : GV D × GV D} (hb : InB F0 F0' lam lam' γ b) {h : GV D} (hh : Corr F0 F F0' F' γ g b h) :
    h ∈ stabL F F' Λ := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hs1, hs2, hseq⟩ := s_adapt hγ hg hg' hb.1.1 hb.2.1.1 hn hn' he
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  have hh' : h = (g * n⁻¹ * b.1 * g⁻¹) * (h⁻¹ * (g * n⁻¹ * b.1 * g⁻¹))⁻¹ := by group
  refine ⟨hh0, (GlobalTheory.T.innerDatum_stable_iff_identifications_compatible D T T' F0 F F0' F' lam lam' Λ γ g h b.1 b.2 hγ hγl hg hg' hΛ hb.1 hb.2.1 hh0
    ?_ ?_).2 hb.2.2.2⟩
  · intro x hx
    rw [hh']
    exact cong_mod hg hs1 h1 (nrat_inv hn) hb.1.1 (by group) x hx
  · intro x hx
    rw [hh', show g * γ * b.2 * γ⁻¹ * g⁻¹ = (g * γ) * b.2 * (g * γ)⁻¹ by group]
    exact cong_mod hG hs2 h2 hn' hb.2.1.1 hseq x hx

include hI in
theorem corr_ker {lam lam' : LV D} {b : GV D × GV D} (hb : InB F0 F0' lam lam' γ b) {h : GV D}
    (hh : Corr F0 F F0' F' γ g b h) : h = 1 ↔ b.1 ∈ NLam lam F0 ∧ b.2 ∈ NLam lam' F0' := by
  obtain ⟨hh0, n, hn, n', hn', he, h1, h2⟩ := hh
  obtain ⟨hs1, hs2, hseq⟩ := s_adapt hγ hg hg' hb.1.1 hb.2.1.1 hn hn' he
  have hG : Adapt (g * γ) F0' F' := adapt_mul (adapt_mapLF hγ) hg'
  rw [nlam_iff_nrat hb.1, nlam_iff_nrat hb.2.1]
  constructor
  · rintro rfl
    rw [inv_one, one_mul] at h1 h2
    constructor
    · have c := nrat_conj (adapt_inv hg) h1
      have e : g⁻¹ * (g * n⁻¹ * b.1 * g⁻¹) * g⁻¹⁻¹ = n⁻¹ * b.1 := by group
      rw [e] at c
      have := nrat_mul hn c
      rwa [mul_inv_cancel_left] at this
    · rw [hseq] at h2
      have c := nrat_conj (adapt_inv hG) h2
      have e : (g * γ)⁻¹ * ((g * γ) * (n' * b.2) * (g * γ)⁻¹) * (g * γ)⁻¹⁻¹ = n' * b.2 := by group
      rw [e] at c
      have := nrat_mul (nrat_inv hn') c
      rwa [inv_mul_cancel_left] at this
  · rintro ⟨c1, c2⟩
    have sF : g * n⁻¹ * b.1 * g⁻¹ ∈ NRat F := by
      have e : g * n⁻¹ * b.1 * g⁻¹ = g * (n⁻¹ * b.1) * g⁻¹ := by group
      rw [e]; exact nrat_conj hg (nrat_mul (nrat_inv hn) c1)
    have sF' : g * n⁻¹ * b.1 * g⁻¹ ∈ NRat F' := by
      rw [hseq]; exact nrat_conj hG (nrat_mul hn' c2)
    obtain ⟨x, -, hu⟩ := hI _ hs1 hs2
    rw [hu h ⟨hh0, h1, h2⟩, hu 1 ⟨principalPolarisation_exists_unique_section F F', by rwa [inv_one, one_mul], by rwa [inv_one, one_mul]⟩]

end Corr

theorem card_of_hom {G : Type*} [Group G] {B : Subgroup (G × G)} {N N' : Subgroup G} (φ : B →* G) (S : Set G)
    (hR : ∀ h, h ∈ φ.range ↔ h ∈ S) (hK : ∀ b : B, φ b = 1 ↔ (b : G × G).1 ∈ N ∧ (b : G × G).2 ∈ N') :
    Nat.card S = (N.prod N').relIndex B := by
  have hker : φ.ker = (N.prod N').subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_prod, hK]
  have e1 : Nat.card S = Nat.card φ.range :=
    Nat.card_congr (Equiv.subtypeEquivRight fun h => (hR h).symm)
  rw [e1, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, Subgroup.relIndex, ← hker]
  rfl

theorem stab_card : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → ∀ (B : Subgroup (GV D × GV D)) (N N' : Subgroup (GV D)), (∀ b, b ∈ B ↔ b.1 ∈ Aut0 (lf D (X.Fu u)) t.lam ∧ b.2 ∈ Aut0 (lf D (X.Fu u')) t.lam' ∧ KeyEq (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lin (b.1 * t.lin * b.2⁻¹)) → (N : Set (GV D)) = NLam t.lam (lf D (X.Fu u)) → (N' : Set (GV D)) = NLam t.lam' (lf D (X.Fu u')) → Nat.card (stabL F F' Λ) = (N.prod N').relIndex B := by
  intro D X Y u u' F F' w hZ hG t Λ hTG B N N' hB hN hN'
  obtain ⟨g, hg, hg', hΛ⟩ := hTG
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hγl : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have hg2 : Adapt g (mapLF t.lin (lf D (X.Fu u'))) F' := hg'
  have hI := GlobalTheory.T.existsUnique_isometryFixingBothFrames_of_frameAdapted D X Y u u' F F' w hZ hG
  have hB' : ∀ b, b ∈ B ↔ InB (lf D (X.Fu u)) (lf D (X.Fu u')) t.lam t.lam' t.lin b := hB
  have hf : ∀ b : B, ∃ h, Corr (lf D (X.Fu u)) F (lf D (X.Fu u')) F' t.lin g (b : GV D × GV D) h :=
    fun b => corr_exists hγ hg hg2 hI ((hB' b).1 b.2)
  let f : B → GV D := fun b => Classical.choose (hf b)
  have hfs : ∀ b : B, Corr (lf D (X.Fu u)) F (lf D (X.Fu u')) F' t.lin g (b : GV D × GV D) (f b) :=
    fun b => Classical.choose_spec (hf b)
  have hAd : ∀ b : B, Adapt (b : GV D × GV D).1 (lf D (X.Fu u)) (lf D (X.Fu u)) ∧
      Adapt (b : GV D × GV D).2 (lf D (X.Fu u')) (lf D (X.Fu u')) :=
    fun b => ⟨((hB' b).1 b.2).1.1, ((hB' b).1 b.2).2.1.1⟩
  let φ : B →* GV D := MonoidHom.mk' f fun b c =>
    corr_unique hγ hg hg2 hI (hAd (b * c)).1 (hAd (b * c)).2 (hfs (b * c))
      (corr_mul hγ hg hg2 ((hB' b).1 b.2) ((hB' c).1 c.2) (hfs b) (hfs c))
  refine card_of_hom φ _ (fun h => ⟨?_, fun hh => ?_⟩) (fun b => ?_)
  · rintro ⟨b, rfl⟩
    exact corr_stab hγ hg hg2 hγl hΛ ((hB' b).1 b.2) (hfs b)
  · have hrow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 _ t.mem
    have hrow' : IsRowLat D (X.Fu u') t.lam' := (Y.rowsOK u').1 _ t.mem'
    obtain ⟨b, hbB, hbC⟩ := GlobalTheory.T.innerDatumStabiliser_from_adapted_pair D _ _ (lf D (X.Fu u)) F (lf D (X.Fu u')) F' t.lam t.lam' Λ t.lin g h
      hγ hγl hg hg2 hΛ (fun σ hσ hL => GlobalTheory.T.row_lattices_same_inner_differ_by_rational_unipotent D _ (X.Fu u) t.lam t.lam σ hrow hrow hσ hL)
      (fun σ hσ hL => GlobalTheory.T.row_lattices_same_inner_differ_by_rational_unipotent D _ (X.Fu u') t.lam' t.lam' σ hrow' hrow' hσ hL) hh
    refine ⟨⟨b, (hB' b).2 hbB⟩, ?_⟩
    exact corr_unique hγ hg hg2 hI hbB.1.1 hbB.2.1.1 (hfs _) hbC
  · have hK := corr_ker hγ hg hg2 hI ((hB' b).1 b.2) (hfs b)
    show f b = 1 ↔ _
    rw [hK]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · show _ ∈ (N : Set (GV D)); rw [hN]; exact h1
      · show _ ∈ (N' : Set (GV D)); rw [hN']; exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have : (b : GV D × GV D).1 ∈ (N : Set (GV D)) := h1
        rwa [hN] at this
      · have : (b : GV D × GV D).2 ∈ (N' : Set (GV D)) := h2
        rwa [hN'] at this

end GlobalTheory.StabCnt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorIsCuspForm
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.RowCusp

theorem level_comp_Re (B : RowsAut) (k : B.I.Gf) (hk : k ∈ B.I.Kg B.g) (hg : 1 ≤ B.g) :
    (B.R (1, k)).comp B.Re = B.Re := by
  obtain ⟨hR1, hRmul, hRnorm, -, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B

  have hπ1 : (fun a : B.I.Gf => B.R (1, a)) 1 = 1 := hR1
  have hπmul : ∀ a b : B.I.Gf, (fun a : B.I.Gf => B.R (1, a)) (a * b) =
      (fun a : B.I.Gf => B.R (1, a)) a * (fun a : B.I.Gf => B.R (1, a)) b := by
    intro a b
    have hab : ((1 : B.I.Ginf), a * b) = ((1 : B.I.Ginf), a) * (1, b) := by
      simp [Prod.mk_mul_mk]
    simp only
    rw [hab, hRmul]
  have hadj : ∀ (a : B.I.Gf) (u v : B.I.L2 B.μf B.fund),
      ⟪u, B.R (1, a) v⟫_ℂ = ⟪B.R (1, a⁻¹) u, v⟫_ℂ :=
    GlobalTheory.IdemProj.inner_rep (fun a : B.I.Gf => B.R (1, a)) hπ1 hπmul (fun a v => hRnorm _ v)

  have hone : (1 : B.I.Gf) ∈ B.I.Kg B.g := by
    refine ⟨?_, fun y _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    · show ((1 : B.I.Gf) : GL (Fin B.I.n) (TensorProduct B.I.F B.I.E (Af B.I.F))) ∈ Formalism.UG.stabGL B.I.Lf
      simpa using (Formalism.UG.stabGL B.I.Lf).one_mem
    · simp [AutInst.fmat]
  have he : ∀ x, B.e (k * x) = B.e x := by
    intro x
    have h' := B.e_adm.2.2.2.2.2.1 x k hk 1 hone
    rwa [mul_one] at h'
  refine ContinuousLinearMap.ext (fun y => ext_inner_left ℂ (fun x => ?_))
  rw [ContinuousLinearMap.comp_apply, hadj, B.Re_spec.2, B.Re_spec.2]
  have hshift : ∀ g, B.e g * ⟪B.R (1, k⁻¹) x, B.R (1, g) y⟫_ℂ =
      (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) (k * g) := by
    intro g
    simp only
    rw [he, ← inv_inv k, ← hadj, inv_inv, ← ContinuousLinearMap.mul_apply, ← hπmul]
  calc ∫ g, B.e g * ⟪B.R (1, k⁻¹) x, B.R (1, g) y⟫_ℂ ∂B.μf
      = ∫ g, (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) (k * g) ∂B.μf := by
        congr 1
        funext g
        exact hshift g
    _ = ∫ g, B.e g * ⟪x, B.R (1, g) y⟫_ℂ ∂B.μf :=
        integral_mul_left_eq_self (μ := B.μf) (fun g => B.e g * ⟪x, B.R (1, g) y⟫_ℂ) k

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d) (hn : 1 ≤ B.I.n)
    (hh : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) (hl : LocDec B h) :
    Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hcont, hbound, hmaj⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl

  have hgap : ∀ v, rkR (B.I.ε v) = 0 ∨
      8 * Real.sqrt (rkR (B.I.ε v)) * (0 + 4 * B.I.n * rkR (B.I.ε v)) < h := by
    intro v
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with hq | hq
    · exact Or.inl hq
    · right
      have hqR : (0 : ℝ) < (rkR (B.I.ε v) : ℝ) := by exact_mod_cast hq
      have hnR : (1 : ℝ) ≤ (B.I.n : ℝ) := by exact_mod_cast hn
      have hsq : (0 : ℝ) < Real.sqrt (rkR (B.I.ε v) : ℝ) := Real.sqrt_pos.mpr hqR
      have hpow : ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) =
          (rkR (B.I.ε v) : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) := by
        rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hqR, Real.rpow_one,
          Real.sqrt_eq_rpow]
      have hv := hh v
      rw [hpow] at hv
      have hpos : 0 < (B.I.n : ℝ) * (rkR (B.I.ε v) : ℝ) * Real.sqrt (rkR (B.I.ε v) : ℝ) := by
        positivity
      nlinarith
  have hint : Integrable (majPh B d h) (muInf B.I) := by
    simpa using hmaj 0 le_rfl hgap
  exact hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

theorem row_isCuspFn : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → ∀ T, B.I.IsRConv B.μf B.fund B.R (phe B d) T → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) := by
  intro hSL B d h hd hg hh hl hH T hT A hA
  rcases Nat.eq_zero_or_pos B.I.n with hn0 | hnpos
  ·
    intro W hW
    exfalso
    apply hW.1
    rw [Submodule.eq_bot_iff]
    intro x _
    funext i
    exact absurd i.2 (by omega)
  have hn : 1 ≤ B.I.n := hnpos

  obtain ⟨A₀, hA₀, hAeq⟩ := Submodule.mem_map.mp hA
  have hAc : A = B.Re.comp A₀ := hAeq.symm
  have hA₀' : ∀ g : B.I.Ginf, A₀.comp (B.σs g) = (B.R (g, 1)).comp A₀ := hA₀
  have hcomm : ∀ g : B.I.Ginf, B.Re.comp (B.R (g, 1)) = (B.R (g, 1)).comp B.Re :=
    (GlobalTheory.IdemProj.re_orth_proj B).2.1
  have hAS : A ∈ B.I.HomS B.σs B.μf B.fund B.R := by
    show ∀ g : B.I.Ginf, A.comp (B.σs g) = (B.R (g, 1)).comp A
    intro g
    rw [hAc, ContinuousLinearMap.comp_assoc, hA₀' g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]

  have hfix : ∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w) := by
    intro k hk
    rw [hAc]
    exact congrArg (fun L : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => L (A₀ (B.tens B.w)))
      (level_comp_Re B k hk hg)
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_continuousRep_bounded_evaluation_rows hSL B d hd hn hg
  obtain ⟨f, hf, hfb⟩ := hC A hAS hfix

  have hTy : T (A (B.tens B.w)) = A (B.tens B.w) :=
    ((GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hn hh hl)).2.2.2 T hT).2.1 A hA
  exact (GlobalTheory.T.cuspidal_of_convolution_fixed_moderate_growth B d h hd (GlobalTheory.T.integral_discreteSeries_unipotent_vanishes hSL B d h hd hl hh) hl hH T hT (A (B.tens B.w)) f
    (C * ‖A (B.tens B.w)‖) hTy hf (fun x => (hfb x).trans_eq (by ring))).2

end GlobalTheory.RowCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicCorrectionLevelCharacter
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem GlobalTheory.St.G.level_char_match : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (Λ : Submodule (OAd F E) (Fin n → E ⊗[F] Ad F)) (Fr : AdFrame cm.sig J Λ (gp 0 * gp 1) k) (h0 : UPts cm.sig J (Ad F)), (∀ x, (h0⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) → ∃ h1 : UPts cm.sig J (Ad F), (∀ x, (h1⁻¹).1.1 *ᵥ x ∈ hat F S.Lb ↔ x ∈ Λ) ∧ ∀ y : UPts cm.sig J (Ad F), (Fr.InK y.1 ↔ ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U) ∧ ∀ hy : ((h1⁻¹ * y * h1 : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U, Fr.chi y.1 = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl hsplT hdeg Λ Fr h0 hh0
  obtain ⟨Fr', hFr'⟩ := GlobalTheory.T.transport_frame_along_unitary_adelic F E n cm.sig J Λ (hat F S.Lb) (gp 0 * gp 1) k h0 hh0 Fr
  obtain ⟨κ, hκ, hκU⟩ := GlobalTheory.T.adelicFrameLevel_conj_formLevel_with_characters F E cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl hsplT hdeg Fr'
  refine ⟨h0 * κ, ?_, ?_⟩
  · intro x
    have hκi : (κ⁻¹ : UPts cm.sig J (Ad F)).1 ∈ stabGL (hat F S.Lb) := by
      simpa using (stabGL (hat F S.Lb)).inv_mem hκ
    have e : ((h0 * κ)⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ x = (κ⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ ((h0⁻¹ : UPts cm.sig J (Ad F)).1.1 *ᵥ x) := by
      rw [_root_.mul_inv_rev]; simp [Matrix.mulVec_mulVec]
    rw [e, ← hκi _, hh0]
  · intro y
    have e : ((h0 * κ)⁻¹ * y * (h0 * κ) : UPts cm.sig J (Ad F)) = κ⁻¹ * (h0⁻¹ * y * h0) * κ := by group
    obtain ⟨h1, h2⟩ := hFr' y
    obtain ⟨h3, h4⟩ := hκU (h0⁻¹ * y * h0)
    refine ⟨?_, ?_⟩
    · rw [h1, h3, e]
    · intro hy
      rw [h2]
      have hy' : ((κ⁻¹ * (h0⁻¹ * y * h0) * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U := by rw [← e]; exact hy
      rw [h4 hy']
      have hx : (⟨_, hy'⟩ : S.U) = ⟨_, hy⟩ := Subtype.ext (congrArg (fun z : UPts cm.sig J (Ad F) => z.1) e.symm)
      rw [hx]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousRepresentativeBoundedEvaluationStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousRepresentative_bounded_evaluation : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.I.n → 1 ≤ B.g → ∃ C : ℝ, ∀ A ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w)) → ∃ f : B.I.GA → ℂ, IsContRep B (A (B.tens B.w)) f ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖A (B.tens B.w)‖ := by
  first | exact @GlobalTheory.EvalBound.exists_contRep_bound_of_isKTypeOf | exact GlobalTheory.EvalBound.exists_contRep_bound_of_isKTypeOf | (intros; apply GlobalTheory.EvalBound.exists_contRep_bound_of_isKTypeOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreGramNumberNullAndCutoffIntegralBoundStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_gramNumber_null_and_cutoff_integral_bound : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yv k r z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR k r β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  first | exact @GlobalTheory.Amp.FibNf.fibre_bound | exact GlobalTheory.Amp.FibNf.fibre_bound | (intros; apply GlobalTheory.Amp.FibNf.fibre_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentGramNullAndFibreVolumeNormalFormStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotent_gramNull_and_fibreVolume_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → 1 ≤ j → j + 2 ≤ k → ∀ De : ℝ, DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yj k r hj z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR0 k r j β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset0 k r hj z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y) := by
  first | exact @GlobalTheory.Amp.FibreNormal.fibre_volume | exact GlobalTheory.Amp.FibreNormal.fibre_volume | (intros; apply GlobalTheory.Amp.FibreNormal.fibre_volume <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePhStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelB' : KernelB := by
  first | exact @GlobalTheory.KernelExpansion.kernelB | exact GlobalTheory.KernelExpansion.kernelB | (intros; apply GlobalTheory.KernelExpansion.kernelB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.JExistsAll
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem jExists_all : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), JExists D F := by
  intro D F X u wt hw
  obtain ⟨J, hJ, -⟩ := GlobalTheory.T.exists_equivariant_unitary_coefficientMap_onto D X u (F u) wt hw
  exact ⟨J, hJ⟩

end GlobalTheory
end

