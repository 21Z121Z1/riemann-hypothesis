import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0560
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0495
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0558
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsValueFixedLevelPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0553
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0477
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0500
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0541
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0545
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0561

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaAtMoveLat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacMove
variable {D : D7}

theorem mt_mul₀ (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mt_one₀ (V : HSp D) : mt V 1 = 1 := rfl

theorem mt_mul_inv (V : HSp D) (g : GA D V) (y : Fin V.rank → AE D) : mt V g *ᵥ (mt V g⁻¹ *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.one_mulVec]

theorem mulVec_mem_idAt {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) {P : Pl D → Prop} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ idAt D P) (i : Fin n) : (A *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : Lat S} {P : Pl D → Prop} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  have e := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  rw [mt_mul_inv] at e
  exact e.symm

theorem mulVec_mem_latA {S : HSp D} {g : GA D S} {L M : Lat S} {P : Pl D → Prop} (h : Moves S g L M P)
    {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) : mt S g *ᵥ z ∈ latA S M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact GlobalTheory.FinPl.MovedVac.smul_mem_latA ha ((h y' (GlobalTheory.FinPl.FrameLat.latV_supp hy'm)).1 hy'm)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem actO_eq (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g h u = HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹) := rfl

theorem actO_mem_latO {S T : HSp D} {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : Pl D → Prop} {g : GA D S} {h : GA D T}
    (hg : Moves S g Λ M P) (hh : Moves T h Λ' M' P) {u : WO S T}
    (hu : u ∈ latO S T (Λ : Set _) (Λ' : Set _) P) : actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T Λ Λ' hΛ hΛ' P] at hu
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M M' hM hM' P]
  obtain ⟨hmx, hmap⟩ := hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [actO_eq, Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : mt S g⁻¹ *ᵥ y ∈ latV S Λ P :=
      (moves_inv hg y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    exact mulVec_mem_latA hh (hmap _ h1)

theorem mem_latO_iff_actO {S T : HSp D} {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : Pl D → Prop} {g : GA D S} {h : GA D T}
    (hg : Moves S g Λ M P) (hh : Moves T h Λ' M' P) (u : WO S T) :
    u ∈ latO S T (Λ : Set _) (Λ' : Set _) P ↔ actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  refine ⟨actO_mem_latO hΛ hM hΛ' hM' hg hh, fun hu => ?_⟩
  have := actO_mem_latO hM hΛ hM' hΛ' (moves_inv hg) (moves_inv hh) hu
  rwa [GlobalTheory.SplitHecke.actO_inv_actO] at this

end GlobalTheory.VacMove

namespace GlobalTheory.VacMove

theorem isThetaAt_moveLat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Λ M : Lat S) (Λ' M' : Lat T), IsSelfDualC S Λ → IsSelfDualC S M → IsSelfDualC T Λ' → IsSelfDualC T M' → ∀ b ∈ GfC S, ∀ b' ∈ GfC T, Moves S b Λ M (fun _ => True) → Moves T b' Λ' M' (fun _ => True) → ∀ e Φ f₀ f, e * e = e → infPart D e = 0 → IsThetaFunO ψ S T f₀ → IsThetaFunO ψ S T f → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀) (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) (om (b, b') f) := by
  intro D ψ S T χS χT om hW Λ M Λ' M' hΛ hM hΛ' hM' b _ b' _ hb hb' e Φ f₀ f hee hinf hf₀ _ hf
  have key := mem_latO_iff_actO hΛ hM hΛ' hM' hb hb'
  have key' := mem_latO_iff_actO hM hΛ hM' hΛ' (moves_inv hb) (moves_inv hb')
  have omm : ∀ p q (X : WO S T → ℂ), om p (om q X) = om (p * q) X := fun p q X => by
    rw [map_mul]; rfl
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hf
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T Λ Λ' hΛ hΛ' e hee hinf f₀ hf₀ T₀ hT₀
  refine ⟨⟨_, GlobalTheory.SplitMove.isPlaceModel_move₂ hW key hT₀ th0⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T M M' hM hM' e hee hinf _
    (hW.om_pres _ _ hf₀) T' hT'
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW key' hT' th1
  have ev : om (b⁻¹, b'⁻¹) (om (b, b') f₀) = f₀ := by
    rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
  rw [ev] at pm
  have hf' : f = om (b⁻¹, b'⁻¹) (T' fun t => Φ (actO S T b⁻¹ b'⁻¹ t)) := hall _ pm
  rw [hf', omm, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one]; rfl

end GlobalTheory.VacMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumExistsAtLevelPrimePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.LastSeeSawDatum

section Helpers

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem comb_apply' {S T : HSp D} (c : WO S T →₀ ℂ) (g : WO S T → ℂ) (u : WO S T) :
    comb ψ S T c g u = ∑ x ∈ c.support, c x * (ψ (symplOH S T u x) * g (u + x)) := by
  simp only [comb, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul]

theorem isThetaFunO_add' {S T : HSp D} {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) where
  quasi γ w := by simp only [Pi.add_apply]; rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hUo', hU'⟩ := hg.level
    refine ⟨U ⊓ U', hUo.inter hUo', fun u hu hi => ?_⟩
    funext w
    have h1 := congrFun (hU u hu.1 hi) w
    have h2 := congrFun (hU' u hu.2 hi) w
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w)

theorem heisO_smul' {S T : HSp D} (u : WO S T) (r : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (r • f) = r • heisO ψ S T u f := by
  funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring

theorem heisO_add' {S T : HSp D} (u : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := by
  funext w; simp only [heisO, Pi.add_apply]; ring

theorem heisO_zero' {S T : HSp D} (u : WO S T) : heisO ψ S T u (0 : WO S T → ℂ) = 0 := by
  funext w; simp only [heisO, Pi.zero_apply, mul_zero]

theorem isThetaFunO_zero' (S T : HSp D) : IsThetaFunO ψ S T (0 : WO S T → ℂ) where
  quasi γ w := by simp only [Pi.zero_apply, mul_zero]
  level := ⟨⊤, isOpen_univ, fun u _ _ => heisO_zero' u⟩
  cont := continuous_const
  smooth k L hL hfin w := by simp only [Pi.zero_apply]; exact contDiff_const

theorem isThetaFunO_smul' {S T : HSp D} (r : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (r • f) where
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    exact ⟨U, hUo, fun u hu hi => by rw [heisO_smul', hU u hu hi]⟩
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := by
    simp only [Pi.smul_apply, smul_eq_mul]; exact contDiff_const.mul (hf.smooth k L hL hfin w)

variable {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop}

theorem vac_zero : Vac ψ S T LS LT P 0 :=
  ⟨isThetaFunO_zero' S T, fun u _ => heisO_zero' _, fun e _ u _ _ => heisO_zero' _⟩

theorem vac_add {f g : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) (hg : Vac ψ S T LS LT P g) :
    Vac ψ S T LS LT P (f + g) :=
  ⟨isThetaFunO_add' hf.1 hg.1, fun u hu => by rw [heisO_add', hf.2.1 u hu, hg.2.1 u hu],
    fun e he u hu hu' => by rw [heisO_add', hf.2.2 e he u hu hu', hg.2.2 e he u hu hu']⟩

theorem vac_smul (r : ℂ) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT P (r • f) :=
  ⟨isThetaFunO_smul' r hf.1, fun u hu => by rw [heisO_smul', hf.2.1 u hu],
    fun e he u hu hu' => by rw [heisO_smul', hf.2.2 e he u hu hu']⟩

theorem vac_sum {ι : Type} (s : Finset ι) (r : ι → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ i ∈ s, Vac ψ S T LS LT P (f i)) : Vac ψ S T LS LT P (∑ i ∈ s, r i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (vac_zero : Vac ψ S T LS LT P 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact vac_add (vac_smul _ (h a (Finset.mem_insert_self a s))) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem comb_smul_fun (c : WO S T →₀ ℂ) (r : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (r • f) = r • comb ψ S T c f := by
  funext u
  simp only [comb_apply', Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem comb_sum_fun {ι : Type} (c : WO S T →₀ ℂ) (s : Finset ι) (r : ι → ℂ) (f : ι → WO S T → ℂ) :
    comb ψ S T c (∑ i ∈ s, r i • f i) = ∑ i ∈ s, r i • comb ψ S T c (f i) := by
  funext u
  simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring

theorem comb_swap {A S X : HSp D} (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ) (G : WO A S → WO S X → ℂ)
    (u : WO A S) (x : WO S X) :
    comb ψ S X c' (fun x' => comb ψ A S c (fun u' => G u' x') u) x =
      comb ψ A S c (fun u' => comb ψ S X c' (G u') x) u := by
  simp only [comb_apply', Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Helpers

theorem lastDatum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k] (Ψ : Matrix n n' k → ℂ) (LA : Lat A) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (c : WO A S →₀ ℂ) (c' : WO S X →₀ ℂ), CombAt (· = p.v) c → CombAt (· = p.v) c' → (∀ f₀, Vac ψ A S LA LS (· = p.v) f₀ → Over ψ α β LA LS f₀ Ψ (comb ψ A S c f₀)) → (∀ f₀, Vac ψ S X LS LX (· = p.v) f₀ → Over ψ β γ₀ LS LX f₀ (phiOne (ε • Q) (lastPair q Λ)) (comb ψ S X c' f₀)) → ∃ (e : WO A S →₀ ℂ) (e' : WO S X →₀ ℂ), CombAt (· = p.v) e ∧ CombAt (· = p.v) e' ∧ ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → BiVacAt ψ LA LS LX (· = p.v) (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) ∧ lastBi o o'' τ Ξ Φ₂ = biComb ψ A S X c c' (biComb ψ A S X e e' (lastBi o o'' τ Ξ Φ₂)) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hIC n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  obtain ⟨ε, hε⟩ := GlobalTheory.T.lastSeesaw_datum_eq_lattice_pair_over_vacuum D k p q ψ hψ hU χ hχ hIC n n' n'' V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  refine ⟨ε, ?_⟩
  intro α α₀ β γ γ₀ hα hγ Q Λ _ Ψ LA LS LT LX hLA hLS hLT hLX hβQ hγΛ c c' hc hc' hcv hcv'
  obtain ⟨e, he, heP⟩ := GlobalTheory.T.splitPlaceDatum_carried_back_to_baseVacuum D k p n n' ψ hψ hU A S α β LA LS hLA hLS Ψ c hc hcv
  obtain ⟨e', he', heP'⟩ := GlobalTheory.T.splitPlaceDatum_carried_back_to_baseVacuum D k p (n'' ⊕ Fin 1) n ψ hψ hU S X β γ₀ LS LX hLS hLX _ c' hc' hcv'
  refine ⟨e, e', he, he', ?_⟩
  intro L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂
  have ha : charInd (resChar χ hχ q) Q ≠ 0 := by
    intro h
    have hev : Q.ev 0 = 0 := by
      unfold Pair.ev
      rw [dif_pos Q.lat.zero_mem]
      exact map_zero Q.fn
    have h0 := congrFun h 0
    simp only [charInd, vecInd, hev, neg_zero, AddChar.map_zero_eq_one, Q.lat.zero_mem, if_true, mul_one,
      Pi.zero_apply] at h0
    exact one_ne_zero h0
  have hA : ∀ y : WO L S, Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u => Ξ ((o.resS S).symm (u, y)))) ∧
      comb ψ A S c (comb ψ A S e (fun u => Ξ ((o.resS S).symm (u, y)))) = fun u => Ξ ((o.resS S).symm (u, y)) := by
    intro y
    obtain ⟨g, hg⟩ := GlobalTheory.T.sliceAlongLine_datum_over_vacuum_splitPlace D k p n n' ψ hψ hU V₀ A L S o ζ hζ α α₀ β hα Ψ _ ha LA LS hLA hLS L₁ L₂ f₁ Ξ hΞ y
    exact heP g _ hg
  have hcol : ∀ x, (fun u => lastBi o o'' τ Ξ Φ₂ u x) =
      Φ₂ (o''.resT S x).1 • fun u => Ξ ((o.resS S).symm (u, kap τ S (o''.resT S x).2)) := by
    intro x; funext u; rfl
  have hAc : ∀ x, Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u => lastBi o o'' τ Ξ Φ₂ u x)) ∧
      comb ψ A S c (comb ψ A S e (fun u => lastBi o o'' τ Ξ Φ₂ u x)) = fun u => lastBi o o'' τ Ξ Φ₂ u x := by
    intro x
    rw [hcol x, comb_smul_fun, comb_smul_fun]
    exact ⟨vac_smul _ (hA _).1, by rw [(hA _).2]⟩
  have hX : ∀ u, Vac ψ S X LS LX (· = p.v) (comb ψ S X e' (lastBi o o'' τ Ξ Φ₂ u)) ∧
      comb ψ S X c' (comb ψ S X e' (lastBi o o'' τ Ξ Φ₂ u)) = lastBi o o'' τ Ξ Φ₂ u := by
    intro u
    obtain ⟨g, hg⟩ := hε α α₀ β γ γ₀ hα hγ Q Λ Ψ LS LT LX hLS hLT hLX hβQ hγΛ L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂ u
    exact heP' g _ hg
  generalize lastBi o o'' τ Ξ Φ₂ = C at hAc hX ⊢
  refine ⟨⟨fun x => ?_, fun u => ?_⟩, ?_⟩
  · have e1 : (fun u' => comb ψ S X e' (C u') x) =
        ∑ j ∈ e'.support, (e' j * ψ (symplOH S X x j)) • fun u' => C u' (x + j) := by
      funext u'
      simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    show Vac ψ A S LA LS (· = p.v) (comb ψ A S e (fun u' => comb ψ S X e' (C u') x))
    rw [e1, comb_sum_fun]
    exact vac_sum _ _ _ fun j _ => (hAc (x + j)).1
  · have e2 : (fun x => comb ψ A S e (fun u' => comb ψ S X e' (C u') x) u) =
        ∑ i ∈ e.support, (e i * ψ (symplOH A S u i)) • comb ψ S X e' (C (u + i)) := by
      funext x
      simp only [comb_apply', Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    show Vac ψ S X LS LX (· = p.v) (fun x => comb ψ A S e (fun u' => comb ψ S X e' (C u') x) u)
    rw [e2]
    exact vac_sum _ _ _ fun i _ => (hX (u + i)).1
  · funext u x
    have hsw : ∀ u', comb ψ S X c' (fun x' => comb ψ A S e (fun u'' => comb ψ S X e' (C u'') x') u') x =
        comb ψ A S e (fun u'' => C u'' x) u' := by
      intro u'
      have h1 := comb_swap (ψ := ψ) e c' (fun u'' x' => comb ψ S X e' (C u'') x') u' x
      beta_reduce at h1
      rw [h1]
      congr 1
      funext u''
      exact congrFun (hX u'').2 x
    show C u x = comb ψ A S c (fun u' => comb ψ S X c' (fun x' => comb ψ A S e (fun u'' => comb ψ S X e' (C u'') x') u') x) u
    simp only [hsw]
    exact (congrFun (hAc x).2 u).symm

end GlobalTheory.LastSeeSawDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepsKernelEqSumCouplingCosets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QPl.LastPt

set_option maxHeartbeats 4000000 in

theorem kernel_eq_sum : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), c.Is → v.Is → ∀ (h : Q.s + 2 * 0 + 2 = D.R.m), c.Lz.rank = 1 → (v.τ Q.s h)ᴴ * ((c.bes Q.s 0 h).L.gram * v.τ Q.s h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram → ∀ s₁ : StepBF c.ψ (c.B Q.s 0 h) (c.J Q.s 0 h), s₁.χW = χ Q.s → ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N Q.s) (v.N (Q.s + 1)) (· = Q.q.v) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (Q.s + 1)) v.NT (· = Q.q.v) Ψ₂ → ∀ α (S : Finset ((Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂)), Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) ⊆ ↑S → ∀ (d₁ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X Q.s) (c.X (Q.s + 1)) →₀ ℂ) (d₂ : (Q.X (Q.s + 1) → Q.k) ⧸ box (Q.X (Q.s + 1)) Q.c₂ → WO (c.X (Q.s + 1)) (c.X (Q.s + 1 + 1)) →₀ ℂ), (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX Q.s (Nat.le_succ _)) (Q.FX (Q.s + 1) le_rfl) (d₁ yb) (Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb)) → (∀ yb, (ofSplit Q.q).IsCombAt c.ψ (Q.FX (Q.s + 1) le_rfl) Q.FM (d₂ yb) (Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb)) → c.lst Q.s h (v.τ Q.s h) s₁ (∑ g ∈ (Q.εL Q.s α).support, Q.εL Q.s α g • s₁.om (g, 1) (comb c.ψ _ _ (Q.eL Q.s) Ψ₁)) (comb c.ψ _ _ Q.eLT Ψ₂) = ∑ yb ∈ S, biComb c.ψ _ _ _ (d₁ yb) (d₂ yb) (c.lst Q.s h (v.τ Q.s h) s₁ Ψ₁ Ψ₂) := by
  intro D c v χ Q hc hv h hr hτ s₁ hχ X₁ X₂ h₁ h₂ α S hS d₁ d₂ hd₁ hd₂
  classical
  have hs := Q.hs
  have hsc : Q.sc Q.s ≠ 0 := Q.sc_ne Q.s
  obtain ⟨T₁, hT₁, hX₁⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Q.k Q.q Q.unit _ _ _ _ (Q.FY Q.s (0 + 1) (by omega)) (Q.FY (Q.s + 1) 0 rfl) c.ψ Q.ψk
    hc.std Q.char Q.cond _ _ (hv.sd Q.s (by omega)) (hv.sd (Q.s + 1) (by omega)) (Q.latY _ _ _) (Q.latY _ _ _)).2 X₁ h₁
  obtain ⟨T₂, hT₂, hX₂⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Q.k Q.q Q.unit _ _ _ _ (Q.FY (Q.s + 1) 0 rfl) Q.FT c.ψ Q.ψk
    hc.std Q.char Q.cond _ _ (hv.sd (Q.s + 1) (by omega)) hv.sdT (Q.latY _ _ _) Q.latT).2 X₂ h₂
  obtain ⟨F₀, hF₀⟩ := ((GlobalTheory.LocMod.normalFrames_exist D Q.k (ofSplit Q.q) _ 0 (Q.sc Q.s) hsc).1 (c.B Q.s 0 h)
    (Q.FX Q.s (by omega))).1
  have hjac := Q.jac Q.s 0 h 0 (by omega)
  obtain ⟨U₁, hU₁, hfl⟩ := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D) Q.k (ofSplit Q.q) Q.ν Q.unitVol.1
    c.ψ Q.ψk Q.char 0 (c.B Q.s 0 h) (c.J Q.s 0 h) s₁ (Q.sc Q.s) hsc _ _ 0 (Q.FX Q.s (by omega)) F₀
    (Q.FY Q.s (0 + 1) (by omega)) (Q.FX (Q.s + 1) le_rfl) (Q.FY (Q.s + 1) 0 rfl) hF₀ (Q.bes Q.s 0 h (0 + 1) (by omega)) hjac T₁ hT₁
  obtain ⟨U₂, hU₂, hres, hext⟩ := GlobalTheory.LevelLast.splitLocalPlace_isModel_wittExtendByZero_rankZero (ofSplit Q.q) c.ψ (c.jac Q.s 0 h).d (Q.FX (Q.s + 1) le_rfl)
    (Q.FY (Q.s + 1) 0 rfl) Q.FT hjac.2.1 T₂ hT₂
  let Φ₁ : SB _ := ⟨_, Q.reg.1 Q.s 0 rfl⟩
  let Φα : SB (Matrix (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1)) Q.k) :=
    ⟨om (Q.T.mu (Q.s + 1)) (Q.rep Q.s 0 rfl α) 1 (Q.T.Phi Q.s 0 rfl), om_mem_SB _ _ _ (Q.reg.1 Q.s 0 rfl)⟩
  let Φ₂ : SB _ := ⟨_, Q.reg.2.1⟩
  let O₁ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1) ⊕ Fin 0) (Q.X Q.s ⊕ Fin (0 + 1))⟩
  let O₂ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Q.Z (Q.X (Q.s + 1) ⊕ Fin 0)⟩
  let O₁' : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1)) (Q.X Q.s ⊕ Unit)⟩
  let O₂' : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) Q.Z (Q.X (Q.s + 1))⟩
  let Ψα : SB _ := ⟨_, ((GlobalTheory.LocFlat.flat_SB_onto Q.k Q.ψk Q.ν Q.cond.continuous Q.unitVol.1 _ _ 0 (0 + 1) le_rfl).1
    le_rfl).1 _ Φα.2⟩
  obtain ⟨Y₂, hY₂⟩ := hres Φ₂
  have a₁ : comb c.ψ _ _ (Q.eL Q.s) X₁ = T₁ Φ₁ := by
    rw [← hX₁ O₁ rfl]
    exact ((Q.eL_at Q.s 0 rfl).2 T₁ hT₁ O₁ Φ₁ rfl rfl).symm
  have a₂ : comb c.ψ _ _ Q.eLT X₂ = T₂ Φ₂ := by
    rw [← hX₂ O₂ rfl]
    exact (Q.eLT_at.2 T₂ hT₂ O₂ Φ₂ rfl rfl).symm
  have a₃ := GlobalTheory.T.exchangeCombination_moves_lastStepDatum_to_chart D c v χ Q hc h s₁ hχ α T₁ hT₁ Φ₁ Φα rfl rfl
  have b₁ : flatBF s₁ (T₁ Φα) = U₁ Ψα := hfl Φα Ψα rfl
  have b₁' : flatBF s₁ (T₁ O₁) = U₁ O₁' := hfl O₁ O₁' (by
    have := (GlobalTheory.LocFlat.flat_contr_intIndicator Q.k Q.ψk Q.ν Q.cond Q.unitVol (Q.X (Q.s + 1)) (Q.X Q.s) Unit 0 (0 + 1)).1
    rw [if_neg (by omega)] at this
    exact this.symm)
  have b₂ := hext Φ₂ Y₂ hY₂
  have b₂' := hext O₂ O₂' fun x => by
    have hx : (∀ r q, x r q ∈ 𝒪[Q.k]) ↔
        ∀ r (q : Q.X (Q.s + 1) ⊕ Fin 0), (fromCols x 0) r q ∈ 𝒪[Q.k] := by
      refine ⟨fun hx r q => ?_, fun hx r q => hx r (Sum.inl q)⟩
      rcases q with q | q
      · exact hx r q
      · exact q.elim0
    simp only [O₂, O₂', Set.indicator_apply, Set.mem_setOf_eq, hx]
  rw [a₁, a₂, a₃, ← hX₁ O₁ rfl, ← hX₂ O₂ rfl]
  unfold Comm.lst
  rw [b₁, b₁', b₂, b₂']
  obtain ⟨Λ, hΛ, hK⟩ := GlobalTheory.T.splitPlace_doubleStep_kernel_localModels D Q.k (ofSplit Q.q) Q.ν Q.unitVol.1 c.ψ hc.std Q.ψk Q.char 0 (c.B Q.s 0 h) (c.X (Q.s + 1))
    (c.X (Q.s + 1 + 1)) c.T c.Lz (c.oT (Q.s + 1 + 1) h) (v.τ Q.s h) hr hτ (Q.sc Q.s) Q.z₀ hsc (Q.tau h) _ _ _
    (Q.FX Q.s (by omega)) F₀ (Q.FX (Q.s + 1) le_rfl) Q.FT Q.FM hF₀ Q.last U₁ U₂ hU₁ hU₂
  obtain ⟨Ξ, hΞ, hΞK⟩ := hK Ψα Y₂
  obtain ⟨Ξ', hΞ', hΞ'K⟩ := hK O₁' O₂'
  have hv1 : valuation Q.k (-1 : Q.k) = 1 := by simp
  haveI := Q.unitVol.1
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.X (Q.s + 1)) (n' := Q.X Q.s)
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Q.k) (n := Q.Z ⊕ Unit) (n' := Q.X (Q.s + 1))
  let P₁ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.X (Q.s + 1)) (Q.X Q.s)⟩
  let P₂ : SB _ := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB (k := Q.k) (Q.Z ⊕ Unit) (Q.X (Q.s + 1))⟩
  let E₁ := fun yb => (⟨_, (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).1⟩ : SB _)
  let E₂ := fun yb => (⟨_, (GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat D c v χ Q α yb).2⟩ : SB _)
  let E := fun yb => (⟨fun q => (E₁ yb).1 q.1 * (E₂ yb).1 q.2, GlobalTheory.FinPl.Comm.prod_mem_SB (E₁ yb).2 (E₂ yb).2 (s := id)
    continuous_fst continuous_snd continuous_id fun _ => rfl⟩ :
      SB (Matrix (Q.X (Q.s + 1)) (Q.X Q.s) Q.k × Matrix (Q.Z ⊕ Unit) (Q.X (Q.s + 1)) Q.k))
  have hsum : Ξ = ∑ yb ∈ S, E yb := Subtype.ext (funext fun q => by
    have e : (fun y => Ψα.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = Q.T.Psi (Q.rep Q.s 0 rfl α) q.1 :=
      funext fun y => GlobalTheory.LevelLast.flCol_one _ _ _ _
    rw [hΞ q, hY₂, e, (GlobalTheory.Couple.psi_eq_sum_coupIdx Q.k Q.s Q.X Q.Z Q.T Q.A Q.c₁ Q.c₂ Q.adapt Q.ψk Q.cond.continuous Q.ν (-1) S hS
      _ ((Q.rep_bij Q.s 0 rfl).mapsTo (Set.mem_univ α)) q.1).2, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun yb _ => mul_left_comm _ _ _)
  have hone : ∀ q, Ξ'.1 q = P₁.1 q.1 * P₂.1 q.2 := fun q => by
    have e : (fun y => O₁'.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        P₁.1 q.1 * cosetInd (box _ (1 : Q.kˣ)) (Submodule.Quotient.mk 0) y :=
      funext fun y => GlobalTheory.LastTwoSteps.intInd_fromCols q.1 y
    rw [hΞ' q, e, GlobalTheory.LastTwoSteps.hat_const_mul, GlobalTheory.LastTwoSteps.hat_int Q.cond Q.unitVol hv1]
    simp only [P₂, O₂']
    rw [GlobalTheory.LastTwoSteps.intInd_rows q.2]
    ring
  refine Eq.trans (funext hΞK) ?_
  show Λ Ξ = _
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun yb _ => ?_
  refine ((GlobalTheory.T.heisenbergCombination_twoVariableModel_and_lineExtension D Q.k (ofSplit Q.q) c.ψ _ _ _).1 _ _ _ _ _ _ Λ (d₁ yb) (d₂ yb) (E₁ yb) P₁ (E₂ yb) P₂ (E yb) Ξ' hΛ
    (hd₁ yb) (hd₂ yb) rfl rfl (fun _ => rfl) hone).trans ?_
  exact congrArg _ (funext hΞ'K).symm

end GlobalTheory.QPl.LastPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Fam.goodBF_of_normalFrames : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), ∀ j ρ h, GlobalTheory.FinPl.GoodBF (commOf (pk W) u (mkGeo m b₀)).ψ ((commOf (pk W) u (mkGeo m b₀)).B j ρ h) ((commOf (pk W) u (mkGeo m b₀)).J j ρ h) (N₁ j) (M₁ j ρ h) (N₁ (j + 1)) ((commOf (pk W) u (mkGeo m b₀)).x (j + 1)).L (PP.under (𝓞 D.host.F)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hgram hτ hNT hζ hSD hgP htP hdisj hPre hOrth hbas FY sc hNF N₁ M₁ hN₁ hFY hM₁ hcore PP hP j ρ h
  have hx : ∀ j, j ≤ D.R.m → (a.x j).Is := fun j hj => hIs.x j hj
  exact ⟨GlobalTheory.FinPl.TamePlaces.tame D _, hN₁ j (by omega), hM₁ j ρ h, hN₁ (j + 1) (by omega), (hIs.x (j + 1) (by omega)).sd,
    GlobalTheory.T.besselLattice_splits_along_witt_normalFrames _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.fourierJacobiLattice_splits_at_normalFrame_place _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.besselPeriodCharacter_primitive_normalFrames _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.besselToJacobiMap_carries_normalFrameLines _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.normalFrame_place_yZero_primitive_in_hom_lattice _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneCosetBesselToFourierJacobi
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem oneCosetBF : ∀ D : D7, GlobalTheory.FinPl.OneCosetBF D := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf
  refine ⟨GlobalTheory.T.besselToJacobi_flatMap_vacuum_at_goodPlace D ψ ρ B J s LV LV₀ LW LW₀ v hG 𝔉 h𝔉 f hf, ?_⟩
  intro h hh hne
  obtain ⟨n, hnN, hnG, t, ht, htG, γ, hγ, κ, hκ, rfl⟩ :=
    GlobalTheory.T.iwasawa_decomposition_selfDual_wittSplit_at_place D J.W J.W₀ ρ J.d LW LW₀ v hG.tame hG.sdW hG.sdW₀ hG.monoW h hh
  have h1 := GlobalTheory.T.besselToJacobiFlatMap_support_reduces_to_torus D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf n hnN hnG t γ hγ κ hκ hne
  have hinv := GlobalTheory.T.inv_diag_torus_integral_besselJacobi_unramified D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hrat := GlobalTheory.T.torusEntryRatio_integral_at_unramified_place D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hlast := GlobalTheory.T.lastDiagonalEntry_torus_integral_of_flatMap_ne_zero D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG h1
  have hint := GlobalTheory.T.diagonalAdelic_entries_congr_one_of_ratios_at_place D ρ v t ht hinv hrat hlast
  have hK := GlobalTheory.T.wittLeviDiagonal_mem_latticeStabilizer_of_units D J.W J.W₀ ρ J.d LW LW₀ v hG.sdW hG.monoW t ht htG (fun i => ⟨hint i, hinv i⟩)
  refine ⟨n * J.d.emb0 γ, ?_, ?_, J.d.levi t * κ, GlobalTheory.T.inLatticeStabilizerAtPlaces_mul_of_mem D J.W LW (· = v) _ _ hK hκ, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right ⟨γ, rfl⟩)
  · exact Subgroup.mul_mem _ hnG (GlobalTheory.T.emb0_mem_grpAt_of_mem_grpAt D J.W J.W₀ ρ J.d (· = v) γ hγ)
  · rw [mul_assoc n (J.d.levi t), ← J.d.wittHyperbolic_anisotropic_commute_levi γ t]
    simp only [mul_assoc]

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwistStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_of_unity_theta_twist : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ t, ∃ ζ : ℕ → ℂ, (∀ j, ∃ n : ℕ, 0 < n ∧ ζ j ^ n = 1) ∧ (∀ j, j + 1 < D.R.m → f.g.b j ∈ GfC _ → f.g.b (j + 1) ∈ GfC _ → ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, ∀ g, IsThetaFunO (pk W).ψ _ _ g → (pk W).ωY t j (a * f.g.b j, a' * f.g.b (j + 1)) g = ζ j • (pk W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) g) ∧ (∀ j h g, IsThetaFunO (pk W).ψ _ _ g → omT (pk W) t j h (f.g.b (j + 1), f.g.bT) g = ζ (j + 1) • omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) g) ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ (pk W).toLevCh.mu t j ^ n = (pk W).toLevCh.mu W.P.A3.A.μ0 j ^ n := by
  first | exact @GlobalTheory.TupRoot.weil_tuple_root | exact GlobalTheory.TupRoot.weil_tuple_root | (intros; apply GlobalTheory.TupRoot.weil_tuple_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepFinitelyManyCellsUniformProoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceDoubleStepFinitelyManyCellsUniform_proof : ∀ D : D7, FinOne D := by
  first | exact @GlobalTheory.QPl.FinOneProof.finOne | exact GlobalTheory.QPl.FinOneProof.finOne | (intros; apply GlobalTheory.QPl.FinOneProof.finOne <;> assumption)
end

