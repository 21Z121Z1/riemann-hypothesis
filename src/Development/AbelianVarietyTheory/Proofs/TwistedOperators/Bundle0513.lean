import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0352
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0325
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0319
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerSpanKFiniteTensors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0502
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0503
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesSmoothModerateGrowthDeriv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.PoinDer

variable {D : D7}

theorem termBound (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v : ∀ τ, M.H τ) (hv : KDecay M v) (b : ∀ τ, M.H τ)
    (hb : ∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : GA D V, ‖coef θ M K v b x‖ ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ :=
  GlobalTheory.T.norm_levelIndicatorCoefficientTest_le_decay D θ hθ V S M K v hv b hb

theorem sumBound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ →
    ∀ (𝔪 : Ideal (𝓞 D.host.E)) (c : GA D V), ∃ (C₀ : ℝ) (A : ℕ), ∀ (u : GA D V → ℝ) (C : ℝ), (∀ x, 0 ≤ u x) →
    (∀ x, Lev.finE V x ∉ congLev D.sp.cm V.gram Λ 𝔪 → u x = 0) →
    (∀ x, u x ≤ C * ∏ τ, ((1 + hsn (cmp θ τ x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) → ∀ g : GA D V,
    Summable (fun γ : GQ V => u (c * (γ : GA D V) * g)) ∧ ∑' γ : GQ V, u (c * (γ : GA D V) * g) ≤ C * C₀ * height V g ^ A :=
  GlobalTheory.T.coefficientPoincareSeries_summable_majorant

theorem termDeriv (hHC : GlobalTheory.Published.HarishChandraModules) (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ)
    (τ : D.what₂.Tau) (hb : b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (x : GA D V) :
    HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s))
      (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 :=
  GlobalTheory.T.hasDerivAt_levelIndicatorCoefficientTest_oneParam D hHC θ hθ V S M K v b τ hb X hX x

theorem onePDecay (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (N : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : GA D V) (t : ℝ), |t| < 1 →
      ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤ L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ :=
  GlobalTheory.T.decayWeight_oneParamTranslate_le_const_mul D θ hθ V τ X hX N

theorem finE_mul_oneP (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (x : GA D V) (t : ℝ) :
    Lev.finE V (x * oneP θ V τ X t) = Lev.finE V x := by
  have h : finHom V (oneP θ V τ X t) = 1 := GlobalTheory.PointAtPlaceHom.atTau_mem V τ _
  show (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) (x * oneP θ V τ X t) = (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) x
  rw [map_mul, MonoidHom.comp_apply (Formalism.UG.bc (Lev.swapAE D)) (finHom V) (oneP θ V τ X t), h, map_one, mul_one]

theorem poin_smooth_growth_deriv : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ UnifModGrowth V θ (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (w : M.H τ) = dRep (M.rep τ) X (a τ) → (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ' => Function.update a τ w τ') = Rder θ V τ X (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  intro hHC D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c a
  obtain ⟨C₀, A, hB⟩ := sumBound D θ hθ V Λ hΛ 𝔪 c
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hK

  have hsum : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∃ C : ℝ, ∀ g,
      Summable (fun γ : GQ V => ‖coef θ M K v b (c * (γ : GA D V) * g)‖) ∧
      ∑' γ : GQ V, ‖coef θ M K v b (c * (γ : GA D V) * g)‖ ≤ C * height V g ^ A := by
    intro b hb
    obtain ⟨C, hC0, hC⟩ := termBound θ hθ M K v hv b hb
    refine ⟨C * C₀, fun g => ?_⟩
    refine hB (fun x => ‖coef θ M K v b x‖) C (fun _ => norm_nonneg _) (fun x hx => ?_) hC g
    simp only [coef, if_neg hx, norm_zero]
  have grow : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ModGrowthExp V A (poin θ M K v c b) := by
    intro b hb
    obtain ⟨C, hC⟩ := hsum b hb
    exact ⟨C, fun g => (norm_tsum_le_tsum_norm (hC g).1).trans (hC g).2⟩

  have der : ∀ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∀ τ, ∀ X ∈ lieAt V τ, ∀ g,
      HasDerivAt (fun t : ℝ => poin θ M K v c b (g * oneP θ V τ X t))
        (poin θ M K v c (Function.update b τ (dRep (M.rep τ) X (b τ))) g) 0 := by
    intro b hb τ X hX g
    set b' := Function.update b τ (dRep (M.rep τ) X (b τ)) with hb'd
    have hb' : ∀ τ', b' τ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ' := by
      intro τ'
      by_cases h : τ' = τ
      · subst h
        rw [hb'd, Function.update_self]
        exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M τ' hX (hb τ')
      · rw [hb'd, Function.update_of_ne h]
        exact hb τ'
    obtain ⟨C', hC'0, hC'⟩ := termBound θ hθ M K v hv b' hb'
    obtain ⟨L, hL0, hL⟩ := onePDecay θ hθ V τ hX (2 * V.rank ^ 2 + 1)
    set u : GA D V → ℝ := fun x => if Lev.finE V x ∈ K then C' * L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ else 0
      with hu
    have hprod : ∀ x : GA D V, 0 ≤ ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x =>
      Finset.prod_nonneg fun τ' _ => inv_nonneg.2 (pow_nonneg (by unfold hsn; positivity) _)
    have hu0 : ∀ x, 0 ≤ u x := fun x => by
      simp only [hu]; split_ifs
      · exact mul_nonneg (mul_nonneg hC'0 hL0) (hprod x)
      · exact le_rfl
    have huK : ∀ x, Lev.finE V x ∉ K → u x = 0 := fun x hx => by simp only [hu, if_neg hx]
    have huC : ∀ x, u x ≤ (C' * L) * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹ := fun x => by
      simp only [hu]; split_ifs
      · exact le_rfl
      · exact mul_nonneg (mul_nonneg hC'0 hL0) (hprod x)
    have hbd : ∀ (x : GA D V) (y : ℝ), y ∈ Set.Ioo (-1 : ℝ) 1 → ‖coef θ M K v b' (x * oneP θ V τ X y)‖ ≤ u x := by
      intro x y hy
      by_cases hx : Lev.finE V x ∈ K
      · have h1 := hC' (x * oneP θ V τ X y)
        have h2 := hL x y (abs_lt.2 ⟨hy.1, hy.2⟩)
        simp only [hu, if_pos hx]
        calc _ ≤ _ := h1
          _ ≤ C' * (L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ (2 * V.rank ^ 2 + 1))⁻¹) := mul_le_mul_of_nonneg_left h2 hC'0
          _ = _ := by ring
      · have : coef θ M K v b' (x * oneP θ V τ X y) = 0 := by
          simp only [coef, finE_mul_oneP, if_neg hx]
        rw [this, norm_zero]
        exact hu0 x
    have hS := (hB u (C' * L) hu0 huK huC g).1
    obtain ⟨Cb, hCb⟩ := hsum b hb
    have key := hasDerivAt_tsum_of_isPreconnected (g := fun (γ : GQ V) (s : ℝ) => coef θ M K v b (c * (γ : GA D V) * g * oneP θ V τ X s))
      (g' := fun (γ : GQ V) (s : ℝ) => coef θ M K v b' (c * (γ : GA D V) * g * oneP θ V τ X s)) (t := Set.Ioo (-1 : ℝ) 1)
      (y₀ := 0) (y := 0) hS isOpen_Ioo isPreconnected_Ioo
      (fun γ y _ => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun x => termDeriv hHC θ hθ M K v b τ (hb τ) hX x) _ y)
      (fun γ y hy => hbd _ y hy) (by norm_num)
      (by simpa [GlobalTheory.Mem.Lift.oneP_zero hθ] using (hCb g).1.of_norm) (by norm_num)
    simp only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
    refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [poin, mul_assoc]
  refine ⟨?_, ⟨A, fun l hl => ?_⟩, ?_⟩
  ·
    refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ V
      {φ | ∃ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) ∧ φ = poin θ M K v c b} ?_ ?_ _ ⟨_, fun τ => (a τ).2, rfl⟩
    · rintro φ ⟨b, hb, rfl⟩
      exact (((GlobalTheory.T.coefficientPoincareSeries_isAutomorphic D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c).1 fun τ => ⟨b τ, hb τ⟩).1).cont
    · rintro φ ⟨b, hb, rfl⟩ τ X hX
      refine ⟨_, ⟨Function.update b τ (dRep (M.rep τ) X (b τ)), fun τ' => ?_, rfl⟩, der b hb τ X hX⟩
      by_cases h : τ' = τ
      · subst h
        rw [Function.update_self]
        exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M τ' hX (hb τ')
      · rw [Function.update_of_ne h]
        exact hb τ'
  ·
    have claim : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
        ∃ b : ∀ τ, M.H τ, (∀ τ, b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) ∧
          l.foldr (fun p f => Rder θ V p.1 p.2 f) (poin θ M K v c fun τ => a τ) = poin θ M K v c b := by
      intro l
      induction l with
      | nil => exact fun _ => ⟨fun τ => a τ, fun τ => (a τ).2, rfl⟩
      | cons p l ih =>
        intro hl'
        obtain ⟨b, hb, e⟩ := ih fun q hq => hl' q (List.mem_cons_of_mem _ hq)
        have hX : p.2 ∈ lieAt V p.1 := hl' p List.mem_cons_self
        refine ⟨Function.update b p.1 (dRep (M.rep p.1) p.2 (b p.1)), fun τ' => ?_, ?_⟩
        · by_cases h : τ' = p.1
          · rw [h, Function.update_self]
            exact GlobalTheory.GKUnif.dRep_mem_kFin hHC M p.1 hX (hb p.1)
          · rw [Function.update_of_ne h]
            exact hb τ'
        · rw [List.foldr_cons, e]
          funext g
          exact (der b hb p.1 p.2 hX g).deriv
    obtain ⟨b, hb, e⟩ := claim l hl
    rw [e]
    exact grow b hb
  ·
    intro τ X hX w hw
    funext g
    have e : (fun τ' => (Function.update a τ w τ' : M.H τ')) =
        Function.update (fun τ' => (a τ' : M.H τ')) τ (dRep (M.rep τ) X (a τ)) := by
      funext τ'
      by_cases h : τ' = τ
      · subst h
        simp [hw]
      · simp [Function.update_of_ne h]
    rw [e]
    exact ((der (fun τ' => a τ') (fun τ' => (a τ').2) τ X hX g).deriv).symm

end GlobalTheory.PoinDer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.StdFrames
open scoped TensorProduct

namespace GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type}

def edgeOf : Arrow T → GlobalTheory.SplitFlip.Edge
  | .right i j => .ex i j
  | .down _ i j => .theta i j
  | _ => .ex 0 0

def IsGridArrow (m : ℕ) (t : T) (a : Arrow T) : Prop :=
  (∃ i j, i < m ∧ j ≤ m ∧ a = .right i j) ∨ ∃ i j, i ≤ m ∧ j < m ∧ a = .down t i j

variable {X Y : Node}

def OnGrid (m : ℕ) (t : T) (p : Path T X Y) : Prop := ∀ a ∈ p.arrows, IsGridArrow m t a

def edges (p : Path T X Y) : List GlobalTheory.SplitFlip.Edge := p.arrows.map edgeOf

section Grid

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def vacOf {W : G.Weil} (ρ : RealMatch W) : ∀ a : Arrow T, Sch G a
  | .right i j => ρ.vX i j
  | .down _ i j => ρ.vT i j
  | _ => 0

def locArg (B : Frames G) (t : T) (w : Pl D.host.E) : ∀ a : Arrow T, WO (G.pS a.pair) (G.pT a.pair) →
    Matrix (Fin ((locGrid G t w).rank (edgeOf a).tgt)) (Fin ((locGrid G t w).rank (edgeOf a).src)) (Kw w)
  | .right i j, x => if h : i < D.R.m ∧ j ≤ D.R.m then
      B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨h.1.le, h.2⟩ ⟨h.1, h.2⟩ (x.map fun c => cpt w (toEAf D c)) else 0
  | .down _ i j, x => if h : i ≤ D.R.m ∧ j < D.R.m then
      B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨h.1, h.2⟩ ⟨h.1, h.2.le⟩ (x.map fun c => cpt w (toEAf D c)) else 0
  | .coreUp _, _ => 0
  | .coreDown _, _ => 0
  | .col _ _, _ => 0

abbrev ArgT (G : GridData L sc) (p : Path T X Y) : Type := p.Fam fun a => WO (G.pS a.pair) (G.pT a.pair)

def castArg {t : T} {w : Pl D.host.E} {e₁ e₂ : GlobalTheory.SplitFlip.Edge} (h : e₁ = e₂)
    (y : Matrix (Fin ((locGrid G t w).rank e₁.tgt)) (Fin ((locGrid G t w).rank e₁.src)) (Kw w)) :
    Matrix (Fin ((locGrid G t w).rank e₂.tgt)) (Fin ((locGrid G t w).rank e₂.src)) (Kw w) := h ▸ y

def argAt (B : Frames G) (t : T) (w : Pl D.host.E) (a : Arrow T) (x : WO (G.pS a.pair) (G.pT a.pair)) (e : GlobalTheory.SplitFlip.Edge)
    (d : Matrix (Fin ((locGrid G t w).rank e.tgt)) (Fin ((locGrid G t w).rank e.src)) (Kw w)) :
    Matrix (Fin ((locGrid G t w).rank e.tgt)) (Fin ((locGrid G t w).rank e.src)) (Kw w) :=
  if h : edgeOf a = e then castArg h (locArg B t w a x) else d

noncomputable def pathArgs (B : Frames G) (t : T) (w : Pl D.host.E) : ∀ {Y : Node} (p : Path T X Y), ArgT G p → (locGrid G t w).Args
  | _, .nil, _ => 0
  | _, .snoc a p, x => fun e => argAt B t w a x.2 e (pathArgs B t w p x.1 e)

noncomputable def famProd : ∀ {Y : Node} (p : Path T X Y), PureT G p → ArgT G p → ℂ
  | _, .nil, _, _ => 1
  | _, .snoc _ p, d, x => famProd p d.1 x.1 * d.2 x.2

noncomputable def HalfAll (e : AE D) : ∀ {Y : Node} (p : Path T X Y), ArgT G p → Prop
  | _, .nil, _ => True
  | _, .snoc _ p, x => HalfAll e p x.1 ∧ IsHalf e x.2

noncomputable def VecAll {W : G.Weil} (ρ : RealMatch W) (e : AE D) : ∀ {Y : Node} (p : Path T X Y), PureT G p → PureT G p → Prop
  | _, .nil, _, _ => True
  | _, .snoc a p, φ, f => VecAll ρ e p φ.1 f.1 ∧ IsLocVec W a.pair e (vacOf ρ a) φ.2 f.2

def RepFin {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) (p : Path T X Y) (τ : TotT G p)
    (Tl : ∀ w, (locGrid G t w).Args → ℂ) : Prop :=
  ∃ e, IsIdemSum e (locPl G t) ∧ ∃ φ : PureT G p → PureT G p, (∀ d ∈ τ.support, VecAll ρ e p (φ d) d) ∧
    ∀ x : ArgT G p, HalfAll e p x → (τ.sum fun d c => c * famProd p (φ d) x) = ∏ w ∈ locPl G t, Tl w (pathArgs B t w p x)

variable (G) in

abbrev PolE : Type := ∀ e : GlobalTheory.SplitFlip.Edge, PolF D (G.V (.grid e.src.1 e.src.2)).rank (G.V (.grid e.tgt.1 e.tgt.2)).rank

def polOf (P : PolE G) : ∀ a : Arrow T, PolF D (G.pT a.pair).rank (G.pS a.pair).rank
  | .right i j => P (.ex i j)
  | .down _ i j => P (.theta i j)
  | .coreUp _ => 0
  | .coreDown _ => 0
  | .col _ _ => 0

noncomputable def restrictPol (P : PolE G) : ∀ {Y : Node} (p : Path T X Y), PolT G p
  | _, .nil => ()
  | _, .snoc a p => (restrictPol P p, polOf P a)

def tensE (W : G.Weil) (p : Path T X Y) (Q : PolE G →₀ ℂ) (τ : TotT G p) : TotT G p :=
  tensT W (Q.mapDomain fun P => restrictPol P p) τ

def toOpp (P : PolE G) : GlobalTheory.RowClaim.PolRow G × GlobalTheory.RowClaim.PolDown G :=
  (fun i => P (.ex i D.R.m), fun j => P (.theta D.R.m j))

end Grid

end GlobalTheory.FlipRun

namespace GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.ChiGrid GlobalTheory.FunObj

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem range_snd_rel (ρ : RealMatch W) (i j : ℕ) :
    LinearMap.range ((LinearMap.snd ℂ _ _).comp (ρ.rel i j).subtype) = ⊤ := by
  refine LinearMap.range_eq_top.2 fun b => ?_
  obtain ⟨a, h⟩ := ρ.onto_small i j b
  exact ⟨⟨(a, b), h⟩, rfl⟩

def matchLin (ρ : RealMatch W) (i j : ℕ) : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j) →ₗ[ℂ]
    PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) :=
  (LinearMap.fst ℂ _ _).comp ((ρ.rel i j).subtype.comp
    (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose)

theorem matchLin_mem (ρ : RealMatch W) (i j : ℕ) (b : PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)) :
    (matchLin ρ i j b, b) ∈ ρ.rel i j := by
  have h := LinearMap.congr_fun (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose_spec b
  set g := (LinearMap.exists_rightInverse_of_surjective _ (range_snd_rel ρ i j)).choose
  have e : ((g b : PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j))) = (matchLin ρ i j b, b) :=
    Prod.ext rfl h
  exact e ▸ (g b).2

def flipPol (ρ : RealMatch W) (i j : ℕ) (P : PolE G) : PolE G →₀ ℂ :=
  (toTens_surjective (matchLin ρ i j (P (.theta i j) ⊗ₜ P (.ex i j)))).choose.sum fun q c =>
    Finsupp.single (Function.update (Function.update P (.ex i (j + 1)) q.1.2) (.theta (i + 1) j) q.2) c

def flipPolE (ρ : RealMatch W) (i j : ℕ) (Q : PolE G →₀ ℂ) : PolE G →₀ ℂ := Q.sum fun P c => c • flipPol ρ i j P

def flipsPolE (ρ : RealMatch W) (l : List (ℕ × ℕ)) (Q : PolE G →₀ ℂ) : PolE G →₀ ℂ :=
  l.foldl (fun Q x => flipPolE ρ x.1 x.2 Q) Q

def IsCuspListed (θ : InfFam D) (X : Node) (F : Fn G X) : Prop :=
  IsAutFunSm θ (G.V X) F ∧ IsCuspFun (G.V X) F ∧ G.IsListed θ X F

def CuspStep (W : G.Weil) (M : Vol G) (ρ : RealMatch W) (t : T) : Prop :=
  ∀ a : Arrow T, IsGridArrow D.R.m t a → ∀ e, IsIdemSum e (locPl G t) → ∀ φ f, IsLocVec W a.pair e (vacOf ρ a) φ f →
    ∀ (Q : PolF D (G.pT a.pair).rank (G.pS a.pair).rank) (F : Fn G a.src), IsCuspListed W.θ a.src F →
      LiftConv W M a (W.fock a.pair f Q) F ∧ IsCuspListed W.θ a.tgt (liftA W M a (W.fock a.pair f Q) F)

end GlobalTheory.FlipRun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def PeriodsOnLine (ch : Choice R) : Prop :=
  ∃ ell : PolCol ch.G × PolRow ch.G → ℂ, ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
    IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
      ∃ κ : ℂ, ∀ P, defPer t ch.S.toGridChoice M P d (colFn ch a) (formTop ch t y) = κ * ell P

def RealLine (ch : Choice R) : Prop :=
  ∃ ell : PolCol ch.G × PolRow ch.G → ℂ, ell ≠ 0 ∧
    (∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M →
      ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y, ∃ K : ℂ, ∀ σ : PolCol ch.G × PolRow ch.G →₀ ℂ,
        defTot t ch.S.toGridChoice M σ τ (colFn ch a) (formTop ch t y) = (σ.sum fun P c => c * ell P) * K) ∧
    ∀ z : ℂ, ∃ σ : PolCol ch.G × PolRow ch.G →₀ ℂ, (z = 0 → σ = 0) ∧ (σ.sum fun P c => c * ell P) = z

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem sum_sum_line {P D' : Type} (σ : P →₀ ℂ) (τ : D' →₀ ℂ) (f : P → D' → ℂ) (ell : P → ℂ)
    (κ : D' → ℂ) (h : ∀ d ∈ τ.support, ∀ p, f p d = κ d * ell p) :
    (σ.sum fun p c => τ.sum fun d c' => c * c' * f p d) =
      (σ.sum fun p c => c * ell p) * τ.sum fun d c' => c' * κ d := by
  rw [Finsupp.sum_mul]
  refine Finsupp.sum_congr fun p _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun d hd => ?_
  rw [h d hd p]
  ring

theorem realLine_of_periodsOnLine (ch : Choice R) (h : PeriodsOnLine ch) : RealLine ch := by
  obtain ⟨ell₀, h₀⟩ := h
  classical
  let ell : PolCol ch.G × PolRow ch.G → ℂ := if ell₀ = 0 then fun _ => 1 else ell₀
  have hne : ell ≠ 0 := by
    by_cases e : ell₀ = 0
    · simp only [ell, e, if_true]
      intro h1
      have := congrFun h1 (Classical.arbitrary _)
      simp at this
    · simpa [ell, e] using e
  have hline : ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
        ∃ κ : ℂ, ∀ P, defPer t ch.S.toGridChoice M P d (colFn ch a) (formTop ch t y) = κ * ell P := by
    intro t a hS β hβ M hM τ hτ d hd y
    obtain ⟨κ, hκ⟩ := h₀ t a hS β hβ M hM τ hτ d hd y
    by_cases e : ell₀ = 0
    · refine ⟨0, fun P => ?_⟩
      rw [hκ P, e]
      simp
    · exact ⟨κ, fun P => by simp only [ell, e, if_false]; exact hκ P⟩
  refine ⟨ell, hne, fun t a hS β hβ M hM τ hτ y => ?_, fun z => ?_⟩
  · choose κ hκ using hline t a hS β hβ M hM τ hτ
    let κ' : PureDat ch.G t → ℂ := fun d => if hd : d ∈ τ.support then κ d hd y else 0
    refine ⟨τ.sum fun d c' => c' * κ' d, fun σ => ?_⟩
    refine sum_sum_line σ τ _ ell κ' fun d hd P => ?_
    simp only [κ', dif_pos hd]
    exact hκ d hd y P
  · obtain ⟨P₀, hP₀⟩ := Function.ne_iff.1 hne
    refine ⟨Finsupp.single P₀ (z / ell P₀), fun hz => by simp [hz], ?_⟩
    rw [Finsupp.sum_single_index (zero_mul _)]
    exact div_mul_cancel₀ z hP₀

theorem big_mono {Q Q' : ChP} (h : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), Q ch → Q' ch) (hQ : Big Q) : Big Q' := by
  obtain ⟨CF0, hC⟩ := hQ
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hC ε CF hCF
  exact ⟨x₀, fun D large₂ he hx' Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => h ch (hx D large₂ he hx' Γ Pl0 T A Ks R F hS ch hch hsc)⟩

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinerSpanKFiniteTensorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Chain GlobalTheory.Chain.IoLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaIntertwiner_span_kFiniteTensors : ∀ (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) (D : D7) (k : Fin D.R.m) (a b : ℕ),
    a = k → b = (k : ℕ) + 1 → ∀ (V W : HSp D) (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) b))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ), IsStepWeil k ψ V W ω → IsVacVec ψ θ M M' f →
    ∀ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, IsItW θ M M' ω (ptOf ψ θ M M' f) It →
    ∃ (h : KSm M) (h' : KSm M'), LinearMap.range (inclK h) ≤ Submodule.span ℂ {x | ∃ φ y, It φ (inclK h' y) = x} := by
  first | exact @GlobalTheory.Chain.KFinOnto.itW_onto_kFin | exact GlobalTheory.Chain.KFinOnto.itW_onto_kFin | (intros; apply GlobalTheory.Chain.KFinOnto.itW_onto_kFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaIntertwinersProportionalOfDiscreteSerieStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realThetaIntertwiners_proportional_of_discreteSeries : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.Chain.ItLine D := by
  first | exact @GlobalTheory.Chain.RealLine.itLine_of_discreteSeries | exact GlobalTheory.Chain.RealLine.itLine_of_discreteSeries | (intros; apply GlobalTheory.Chain.RealLine.itLine_of_discreteSeries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeChangeOfLatticeLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_changeOfLattice_laws : ∀ D : D7, ReLatLaw D := by
  first | exact @GlobalTheory.ReLatPf.reLatLaw_holds | exact GlobalTheory.ReLatPf.reLatLaw_holds | (intros; apply GlobalTheory.ReLatPf.reLatLaw_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StableFockSpanContainsRowHighestPolynomialsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableFockSpan_contains_rowHighestPolynomials : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → T.rank ≤ S.rank → ∀ B₀, C.IsB B₀ → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, (∀ τ, (BS τ)ᴴ * BS τ = 1) → ∀ f, C.IsTh f → C.IsFock B₀ f → f ≠ 0 → ∀ (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ = C.X.p0) → (∀ τ, q τ = C.q0) → ∀ (pt : MvPolynomial (FVar D T.rank S.rank) ℂ → WO S T → ℂ) (U : Submodule ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ)), (∀ P, pt P = pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B₀) BS B₀ f P) → Formalism.IndefR.Datum.delta p q ap am ∈ U → (∀ h ∈ GinfC S, ∀ P ∈ U, ∃ P' ∈ U, om (h, 1) (pt P) = pt P') → C.IsB (revB C.X.p0 B₀) ∧ C.sB (revB C.X.p0 B₀) = C.sB B₀ ∧ ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (Q₀ : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q₀ ∈ Harm.rowHighest ℂ c c' ∧ C.fvec (revB C.X.p0 B₀) f Q₀ = pt (Formalism.IndefR.Datum.delta p q ap am) ∧ pt (Formalism.IndefR.Datum.delta p q ap am) ≠ 0 ∧ ∀ Q, C.toH Q ∈ Harm.rowHighest ℂ c c' → ∃ P ∈ U, C.fvec (revB C.X.p0 B₀) f Q = pt P := by
  first | exact @GlobalTheory.AdSpan.StableFock.fockSpan_rowHighest | exact GlobalTheory.AdSpan.StableFock.fockSpan_rowHighest | (intros; apply GlobalTheory.AdSpan.StableFock.fockSpan_rowHighest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProjectionIntertwinesLevelLiftsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaProjection_intertwines_levelLifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i t g κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ → ∀ y y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e y (h * (finHom _).rangeRestrict κ)) → R.thG i t y' = R.gW i (sg0 D A) g (R.thG i t y) := by
  first | exact @GlobalTheory.ThetaProjEquiv.thG_intertwines_core | exact GlobalTheory.ThetaProjEquiv.thG_intertwines_core | (intros; apply GlobalTheory.ThetaProjEquiv.thG_intertwines_core <;> assumption)
end

