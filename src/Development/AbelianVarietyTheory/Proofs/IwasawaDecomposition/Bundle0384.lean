import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepFamilyBounded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0227
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSpacesOfOver
section
noncomputable section

namespace GlobalTheory.Mem.HostFrames

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top NumberField

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def SignFrame (S : HSpace E) : Prop :=
  (∃ neg : Fin S.rank → Bool, ∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then (Examples₂.sgn (neg a) : E) else 0) ∧
    S.L0 = Submodule.span (𝓞 E) (Set.range S.frame)

def UnitFrame (S : HSpace E) : Prop :=
  (∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0) ∧ S.L0 = Submodule.span (𝓞 E) (Set.range S.frame)

theorem UnitFrame.signFrame {S : HSpace E} (h : UnitFrame S) : SignFrame S :=
  ⟨⟨fun _ => false, fun a b => by rw [h.1]; simp [Examples₂.sgn]⟩, h.2⟩

variable (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))

theorem signFrame_stdSpace (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) : SignFrame (Examples₂.stdSpace hstar N neg p q) :=
  ⟨⟨neg, Examples₂.stdSpace_gram_apply hstar N neg p q⟩, rfl⟩

theorem unitFrame_stdSpace (N p q : ℕ) : UnitFrame (Examples₂.stdSpace hstar N (fun _ => false) p q) :=
  ⟨fun a b => (Examples₂.stdSpace_gram_apply hstar N (fun _ => false) p q a b).trans (by simp [Examples₂.sgn]; rfl), rfl⟩

theorem SignFrame.gram_eq {S : HSpace E} (h : SignFrame S) (F : Type) [Field F] [Algebra F E] :
    ∃ d : Fin S.rank → F, (∀ a, d a = 1 ∨ d a = -1) ∧ S.gram = Matrix.diagonal fun a => algebraMap F E (d a) := by
  obtain ⟨neg, hn⟩ := h.1
  refine ⟨fun a => Examples₂.sgn (neg a), fun a => by cases hh : neg a <;> simp [Examples₂.sgn, hh], ?_⟩
  ext a b
  rw [HSpace.gram, hn, Matrix.diagonal_apply, Examples₂.map_sgn]

end Coord

section Diag

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {S : Spaces R F E}

theorem signFrame_Y (h : DiagSpaces S) (j : ℕ) : SignFrame (S.Y j) := by
  obtain ⟨hs, -, -, hY, -, -⟩ := h
  rw [hY]; exact signFrame_stdSpace hs _ _ _ _

theorem signFrame_V (h : DiagSpaces S) (j : ℕ) : SignFrame (S.V j) := by
  obtain ⟨hs, -, -, -, -, hV⟩ := h
  rw [hV]; exact signFrame_stdSpace hs _ _ _ _

theorem signFrame_W_of_one_le_of_le (h : DiagSpaces S) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) : SignFrame (S.W j) := by
  obtain ⟨hs, -, -, -, hW, -⟩ := h
  rw [hW j h1 h2]; exact signFrame_stdSpace hs _ _ _ _

theorem unitFrame_X' (h : DiagSpaces S) : UnitFrame S.X' := by
  obtain ⟨hs, -, hX, -, -, -⟩ := h
  rw [hX]; exact unitFrame_stdSpace hs _ _ _

theorem unitFrame_X (h : DiagSpaces S) (j : ℕ) : UnitFrame (S.X j) := by
  obtain ⟨hs, hX, -, -, -, -⟩ := h
  rw [hX]; exact unitFrame_stdSpace hs _ _ _

theorem unitFrame_V (h : DiagSpaces S) {j : ℕ} (hn : S.Vneg j = false) : UnitFrame (S.V j) ∧ (S.V j).IsPosDef := by
  obtain ⟨hs, -, -, -, -, hV⟩ := h
  rw [hV, hn]; exact ⟨unitFrame_stdSpace hs _ _ _, fun _ => rfl⟩

def setW0 (S : Spaces R F E) (Z : HSpace E) (hZ : Z.SigOK) : Spaces R F E :=
  { S with
    W := fun j => match j with
      | 0 => Z
      | j + 1 => S.W (j + 1)
    W_sig := fun j => match j with
      | 0 => hZ
      | j + 1 => S.W_sig (j + 1)
    W_rank := fun j h1 h2 => match j, h1, h2 with
      | j + 1, h1, h2 => S.W_rank (j + 1) h1 h2
    W_sigval := fun j h1 h2 => match j, h1, h2 with
      | j + 1, h1, h2 => S.W_sigval (j + 1) h1 h2
    baseSpace_isometric_graded := fun j h1 h2 => match j, h1, h2 with
      | j + 1, h1, h2 => S.baseSpace_isometric_graded (j + 1) h1 h2 }

theorem diagSpaces_setW0 (h : DiagSpaces S) (Z : HSpace E) (hZ : Z.SigOK) :
    DiagSpaces (setW0 S Z hZ) ∧ (setW0 S Z hZ).W 0 = Z := by
  obtain ⟨hs, h1, h2, h3, h4, h5⟩ := h
  refine ⟨⟨hs, h1, h2, h3, fun j a b => ?_, h5⟩, rfl⟩
  match j, a, b with
  | j + 1, a, b => exact h4 (j + 1) a b

end Diag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem diagSpaces_of_over {K : Ctx} {B : Pre} (h : K.Over B) : DiagSpaces B.sp := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, hd⟩ := h
  exact hd

theorem val_of_over {K : Ctx} {B : Pre} (h : K.Over B) :
    RankVal K.s B.R ∧ ∃ bT, ∀ u, HCVal K.s K.cD K.ch B.host (fun τ : Tau B.R => (τ : B.R.GG)) (B.hcW u) bT := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, hd⟩ := h
  exact ⟨K.ok.rank, _, K.ok.hc⟩

theorem frames_of_over (K : Ctx) (X : Stages) (h : K.Over X.B.toPre) :
    X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧
    (∀ i, SignFrame (Wc X.toD7 i) ∧ SignFrame (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧
    (∀ j, SignFrame (X.toD7.sp.Y j) ∧ SignFrame (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → SignFrame (X.toD7.sp.W j))) ∧
    SignFrame X.toD7.sp.X' ∧
    (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧
      (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧
    ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧
      X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame)) := by
  have hd : DiagSpaces X.toD7.sp := diagSpaces_of_over h
  have hV : ∀ i : Fin X.toD7.R.m, X.toD7.sp.Vneg ((i : ℕ) + 1) = false := fun i => X.B.V_pos _ (by omega) i.2
  exact ⟨rfl, fun i => ⟨signFrame_W_of_one_le_of_le hd (by omega) i.2, signFrame_V hd _⟩, fun i => (unitFrame_V hd (hV i)).2,
    fun j => ⟨signFrame_Y hd j, signFrame_V hd j, signFrame_W_of_one_le_of_le hd⟩, (unitFrame_X' hd).signFrame,
    fun i => (unitFrame_V hd (hV i)).1, unitFrame_X' hd⟩

theorem size_le (eps c : ℝ) (A : ℕ) (he : 0 < eps) (he' : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (y : ℝ),
    s.eps = eps → x0 ≤ s.x → RankVal s R → 402 * (A : ℝ) + 2 ≤ y → c * s.L * (R.N R.m : ℝ) ^ A ≤ (⌈s.x ^ y⌉₊ : ℝ) := by
  obtain ⟨x1, h1⟩ := rank_basic_bounds eps he he'
  refine ⟨max x1 c, fun s R y hs hx hR hy => ?_⟩
  obtain ⟨-, -, -, -, -, hL, hL1, -, -, -, -, -, -, -, hN, -, -⟩ := h1 s R hs ((le_max_left _ _).trans hx) hR
  have hc : c ≤ s.x := (le_max_right _ _).trans hx
  have hx1 : 1 ≤ s.x := s.one_lt_alt.le
  have hx0 : 0 < s.x := by linarith
  have a1 : (R.N R.m : ℝ) ^ A ≤ s.x ^ (402 * (A : ℝ)) := by
    rw [Real.rpow_mul hx0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hN A
  have a2 : c * s.L ≤ s.x * s.x := mul_le_mul hc hL (by linarith) hx0.le
  calc c * s.L * (R.N R.m : ℝ) ^ A ≤ s.x * s.x * s.x ^ (402 * (A : ℝ)) :=
        mul_le_mul a2 a1 (by positivity) (by positivity)
    _ = s.x ^ (402 * (A : ℝ) + 2) := by rw [Real.rpow_add hx0, Real.rpow_two]; ring
    _ ≤ s.x ^ y := Real.rpow_le_rpow_of_exponent_le hx1 hy
    _ ≤ _ := Nat.le_ceil _

theorem gaps_ev (c : ℝ) (A : ℕ) : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → ∃ h Δ : ℕ,
    c * K.s.L * (X.toD7.R.N X.toD7.R.m : ℝ) ^ A ≤ h ∧ c * K.s.L * (X.toD7.R.N X.toD7.R.m : ℝ) ^ A ≤ Δ ∧ 1 ≤ K.s.L ∧
    ∀ u τ, (∀ j, (X.toD7.hcW u τ).e j - (X.toD7.hcW u τ).b j = h) ∧
      (∀ (j : Fin X.toD7.R.m) (hj : j.1 + 1 < X.toD7.R.m), (X.toD7.hcW u τ).b ⟨j.1 + 1, hj⟩ - (X.toD7.hcW u τ).e j = h) ∧
      ∀ i : Fin (X.toD7.R.k - 1), (X.toD7.hcW u τ).v i = ((X.toD7.R.k - 2 - i.1 : ℕ) : ℚ) * (4 * Δ) := by
  refine ⟨1, one_pos, fun eps C8 he _ he' _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ =>
    ⟨402 * A + 2, fun cD hcD => ⟨402 * A + 2, fun ch hch => ?_⟩⟩⟩⟩
  obtain ⟨x0, h0⟩ := size_le eps c A he he'
  refine ⟨x0, fun K _ k1 k2 k3 k4 X hX => ?_⟩
  obtain ⟨hR, bT, hH⟩ := val_of_over hX
  refine ⟨⌈K.s.x ^ K.ch⌉₊, Delv K.s K.cD, h0 _ _ _ k3 k4 hR (k2 ▸ hch), h0 _ _ _ k3 k4 hR (k1 ▸ hcD),
    Real.one_le_rpow K.s.one_lt_alt.le K.s.eps_pos.le, fun u τ => ?_⟩
  obtain ⟨hv, -, ⟨b1, hb, -⟩, -⟩ := hH u
  refine ⟨fun j => ?_, fun j hj => ?_, hv τ⟩
  · have := (hb τ j).2
    show (X.B.hcW u τ).e j - (X.B.hcW u τ).b j = _
    rw [this]
    simp only [h0v]; push_cast; ring
  · have e1 := (hb τ j).2
    have e2 := (hb τ j).1
    have e3 := (hb τ ⟨j.1 + 1, hj⟩).1
    refine (congrArg₂ (· - ·) e3 (e1.trans (congrArg (· + _) e2))).trans ?_
    simp only [h0v]; push_cast; ring

end GlobalTheory.Mem.HostFrames

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNodeGapGeRankPow
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top Filter

namespace GlobalTheory.Mem.Top.NodeGap

theorem rank_le {s : Scale} {R : Ranks} (h : RankVal s R) (hx : 4 ≤ s.x) : (R.r : ℝ) ≤ s.x ^ 6 := by
  have h1 : (R.k : ℝ) ≤ 2 * s.x ^ (9 / 2 + 10 * s.eps) := h.2.2.1.2
  have h2 : s.x ^ (9 / 2 + 10 * s.eps) ≤ s.x ^ 5 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by have := s.eps_lt; push_cast; linarith)
  have h3 : R.r ≤ 2 * R.k := by have := R.m_add_three_le_k; unfold Ranks.r; omega
  have h4 : (R.r : ℝ) ≤ 2 * R.k := by exact_mod_cast h3
  have h5 : (0 : ℝ) < s.x ^ 5 := by positivity
  calc (R.r : ℝ) ≤ 4 * s.x ^ 5 := by linarith
    _ ≤ s.x * s.x ^ 5 := by gcongr
    _ = s.x ^ 6 := by ring

theorem le_m {s : Scale} {R : Ranks} (h : RankVal s R) {M : ℕ} (hx : (M : ℝ) ^ 4 ≤ s.x) : M ≤ R.m := by
  have h1 : Real.sqrt (s.x * s.delta1) ≤ (R.m : ℝ) := h.2.1.1
  have hx0 : 0 < s.x := by linarith [s.one_lt_alt]
  have h2 : (M : ℝ) ^ 2 ≤ s.x * s.delta1 := by
    have e : s.x * s.delta1 = s.x ^ (1 - s.eps / 8) := by
      unfold Scale.delta1
      rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
    have h3 : s.x ^ ((1 : ℝ) / 2) ≤ s.x ^ (1 - s.eps / 8) :=
      Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by have := s.eps_lt; linarith)
    rw [e]
    refine le_trans ?_ h3
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by rw [← pow_mul]; exact hx)
  have h4 : (M : ℝ) ≤ R.m := (Real.le_sqrt_of_sq_le h2).trans h1
  exact_mod_cast h4

theorem b_eq (K : Ctx) (u : K.P.Word) (τ : Tau K.P.R) :
    ∃ b1 : ℤ, ∀ j : Fin K.P.R.m, (K.P.hcW u τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h0v K.s K.ch : ℚ) ∧
      (K.P.hcW u τ).e j = (K.P.hcW u τ).b j + (h0v K.s K.ch : ℚ) / 2 := by
  obtain ⟨b1, h, -⟩ := (K.ok.hc u).2.2.1
  exact ⟨b1 τ, h τ⟩

theorem eventually_nodeGap_ge_rank_pow (A : ℝ) (N M : ℕ) : Ev fun K => M ≤ K.P.R.m ∧ A * (K.P.R.r : ℝ) ^ N ≤ (h0v K.s K.ch : ℝ) := by
  refine ⟨1, one_pos, fun eps C8 _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨6 * N + 1, fun ch hch =>
    ⟨max (max 4 A) ((M : ℝ) ^ 4), fun K _ _ h3 _ hx => ?_⟩⟩⟩⟩⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx4, hxA⟩, hxM⟩ := hx
  refine ⟨le_m K.ok.rank hxM, ?_⟩
  have h1 := rank_le K.ok.rank hx4
  have h2 : K.s.x ^ (6 * N + 1) ≤ K.s.x ^ K.ch := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le K.s.one_lt_alt.le (by rw [h3]; push_cast; exact hch)
  have h5 : K.s.x ^ K.ch ≤ (⌈K.s.x ^ K.ch⌉₊ : ℝ) := Nat.le_ceil _
  have h6 : (0 : ℝ) ≤ (⌈K.s.x ^ K.ch⌉₊ : ℝ) := Nat.cast_nonneg _
  calc A * (K.P.R.r : ℝ) ^ N ≤ K.s.x * (K.s.x ^ 6) ^ N := by gcongr
    _ = K.s.x ^ (6 * N + 1) := by ring
    _ ≤ (h0v K.s K.ch : ℝ) := by unfold h0v; push_cast; linarith

theorem ev_nodes (A : ℝ) (N M : ℕ) : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → M ≤ X.toD7.R.m ∧
    ∃ h : ℕ, A * (X.toD7.R.r : ℝ) ^ N ≤ (h : ℝ) ∧ ∀ τ, ∃ b1 : ℤ, ∀ j : Fin X.toD7.R.m,
      (X.toD7.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ) ∧ (X.toD7.hc τ).e j = (X.toD7.hc τ).b j + (h : ℚ) / 2 := by
  obtain ⟨a, ha, hp⟩ := eventually_nodeGap_ge_rank_pow A N M
  refine ⟨a, ha, fun e C8 he hle h52 h8 => ?_⟩
  obtain ⟨K0, hK⟩ := hp e C8 he hle h52 h8
  refine ⟨K0, fun C hC hC8 hL => ?_⟩
  obtain ⟨a1, ha1⟩ := hK C hC hC8 hL
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  refine ⟨a3, fun K h1 h2 h3 h4 hx X hO => ?_⟩
  obtain ⟨g1, g2⟩ := ha3 K h1 h2 h3 h4 hx
  have key : ∀ B : Pre, K.Over B → M ≤ B.R.m ∧
      ∃ h : ℕ, A * (B.R.r : ℝ) ^ N ≤ (h : ℝ) ∧ ∀ τ, ∃ b1 : ℤ, ∀ j : Fin B.R.m,
        (B.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ) ∧ (B.hc τ).e j = (B.hc τ).b j + (h : ℚ) / 2 := by
    rintro B ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩
    exact ⟨g1, _, g2, fun τ => b_eq K K.P.u₀ τ⟩
  exact key _ hO

end GlobalTheory.Mem.Top.NodeGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientLinearLiftDoubleCosetOperators
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLiftN

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem unif_ne_zero {s : SplitPlace L} {ϖ : s.v.adicCompletion (maximalRealSubfield L)}
    (hϖ : IsUnif L s.v ϖ) : ϖ ≠ 0 := by
  rintro rfl
  have : Valued.v (0 : s.v.adicCompletion (maximalRealSubfield L)) = WithZero.exp (-1 : ℤ) := hϖ
  rw [map_zero] at this
  exact WithZero.exp_ne_zero this.symm

theorem tSet_subset_of_unif (n : ℕ) (s : SplitPlace L) (ϖ ϖ' : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hϖ : IsUnif L s.v ϖ) (hϖ' : IsUnif L s.v ϖ') : tSet L n s ϖ k ⊆ tSet L n s ϖ' k := by
  rintro x ⟨hx, a, ha, b, hb, e⟩
  have h0 := unif_ne_zero hϖ'
  have h0' := unif_ne_zero hϖ
  set u := ϖ / ϖ' with hu
  have hu0 : u ≠ 0 := div_ne_zero h0' h0
  have hv : Valued.v u = 1 := by
    rw [hu, map_div₀]
    have e1 : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have e2 : Valued.v ϖ' = WithZero.exp (-1 : ℤ) := hϖ'
    rw [e1, e2, div_self WithZero.exp_ne_zero]
  have hvi : Valued.v u⁻¹ = 1 := by rw [map_inv₀, hv, inv_one]
  let c : Fin n → s.v.adicCompletion (maximalRealSubfield L) := fun i => if (i : ℕ) < k then u else 1
  let c' : Fin n → s.v.adicCompletion (maximalRealSubfield L) := fun i => if (i : ℕ) < k then u⁻¹ else 1
  have hcc : (fun i => c i * c' i) = fun _ => 1 := by
    funext i; simp only [c, c']; split_ifs <;> simp [hu0]
  have hcc' : (fun i => c' i * c i) = fun _ => 1 := by
    funext i; simp only [c, c']; split_ifs <;> simp [hu0]
  let dm : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    ⟨Matrix.diagonal c, Matrix.diagonal c', by rw [Matrix.diagonal_mul_diagonal, hcc, Matrix.diagonal_one],
      by rw [Matrix.diagonal_mul_diagonal, hcc', Matrix.diagonal_one]⟩
  have hI : ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z ≤ 1 →
      z ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun z hz =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ s.v).2 hz
  have hdm : dm ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    rw [GlobalTheory.HeckeStdFacts.mem_GLint_iff]
    refine ⟨fun i j => hI _ ?_, fun i j => hI _ ?_⟩
    · show Valued.v (Matrix.diagonal c i j) ≤ 1
      rw [Matrix.diagonal_apply]
      split_ifs
      · simp only [c]; split_ifs
        · rw [hv]
        · rw [map_one]
      · rw [map_zero]; exact zero_le'
    · show Valued.v (Matrix.diagonal c' i j) ≤ 1
      rw [Matrix.diagonal_apply]
      split_ifs
      · simp only [c']; split_ifs
        · rw [hvi]
        · rw [map_one]
      · rw [map_zero]; exact zero_le'
  have hdiag : Formalism.UG.diagJ n ϖ k = Formalism.UG.diagJ n ϖ' k * (dm : Matrix (Fin n) (Fin n) _) := by
    show _ = _ * Matrix.diagonal c
    rw [Formalism.UG.diagJ, Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [c]
    split_ifs
    · rw [hu]; field_simp
    · rw [one_mul]
  refine ⟨hx, a, ha, dm * b, mul_mem hdm hb, ?_⟩
  rw [e, Units.val_mul, hdiag]
  simp only [Matrix.mul_assoc]

theorem tSet_eq_of_unif (n : ℕ) (s : SplitPlace L) (ϖ ϖ' : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hϖ : IsUnif L s.v ϖ) (hϖ' : IsUnif L s.v ϖ') : tSet L n s ϖ k = tSet L n s ϖ' k :=
  Set.Subset.antisymm (tSet_subset_of_unif n s ϖ ϖ' k hϖ hϖ') (tSet_subset_of_unif n s ϖ' ϖ k hϖ' hϖ)

theorem tN_eq_of_conj (D : D7) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf D.host.E n))
    (v : PlE D.host) (s s' : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E))
    (ϖ' : s'.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ) (hc : IsConjPl D.host v s.w)
    (hc' : IsConjPl D.host v s'.w) (hu : IsUnif D.host.E s.v ϖ) (hu' : IsUnif D.host.E s'.v ϖ') (f : GAf D.host.E n → W) :
    NG.tN J s ϖ k f = NG.tN J s' ϖ' k f := by
  have hw : s.w = s'.w := GlobalTheory.TwSys.ResidualCompare.isConjPl_unique hc hc'
  obtain rfl := GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq _ s s' hw
  unfold NG.tN
  rw [tSet_eq_of_unif n s ϖ ϖ' k hu hu']

end GlobalTheory.HeckeLiftN

namespace GlobalTheory.HeckeLiftN

theorem heckeLift (D : D7) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) :
    HeckeStdPlain → GenHyp M C.Q → MtInput D M tup C.Q → HeckeLift0 (mt0 M) C.Q := by
  intro hP hG hI j w v k h1 h2 hg
  classical
  by_cases hex : ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ
  swap
  · exact ⟨0, fun s ϖ hc hu _ => absurd ⟨s, ϖ, hc, hu⟩ hex⟩
  obtain ⟨s0, ϖ0, hc0, hu0⟩ := hex
  obtain ⟨B, hB, hBs⟩ := hG w j h1 h2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hj' : j' < D.R.m := by omega
  set Mw := M (D.what₂.muTw w) (j' + 1) h1 h2 with hMw
  have hrat : ∀ x, ∃ x', Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x') =
      NG.tN Mw.J s0 ϖ0 k (Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) :=
    fun x => hI.rat w ⟨j', hj'⟩ v k s0 ϖ0 hg hc0 hu0 x
  obtain ⟨-, Plin, -, -⟩ := hP D.host.E D.R.nV Mw.wt Mw.J Mw.χ B Mw.J_open hB s0 ϖ0 k (hBs v k s0 hg hc0) hu0
    hg.2.2.2.2.1 hg.2.2.2.2.2
  have hTS : ∀ y, Mw.real y ∈ NG.TypeSp Mw.wt.ρ Mw.J Mw.χ := fun y => by
    rw [← Mw.real_range]; exact LinearMap.mem_range_self _ y
  have hRJ : Function.Injective fun x => Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x) :=
    Mw.real_inj.comp (Formalism.L2.jMt_injective _ _)
  have htN0 : NG.tN Mw.J s0 ϖ0 k (0 : GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
    have := Plin (0 : GAf D.host.E D.R.nV → Mw.wt.W) (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    rw [one_smul, add_zero, one_smul] at this
    simpa using this
  let T0 : D.what₂.MtL (D.what₂.muTw w) (j' + 1) → D.what₂.MtL (D.what₂.muTw w) (j' + 1) := fun x => (hrat x).choose
  have hT0 : ∀ x, Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 x)) =
      NG.tN Mw.J s0 ϖ0 k (Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) := fun x => (hrat x).choose_spec
  have hadd : ∀ x y, T0 (x + y) = T0 x + T0 y := by
    intro x y
    apply hRJ
    show Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 (x + y))) =
      Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 x + T0 y))
    have := Plin _ (hTS (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) _ (hTS (D.what₂.jMt (D.what₂.muTw w) (j' + 1) y)) 1
    rw [one_smul, one_smul] at this
    rw [hT0, map_add, map_add, map_add, map_add, hT0, hT0, this]
  have hsmul : ∀ (a : D.what₂.LL) x, T0 (a • x) = a • T0 x := by
    intro a x
    apply hRJ
    show Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 (a • x))) =
      Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (a • T0 x))
    have := Plin _ (hTS (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) 0 (Submodule.zero_mem _) (D.what₂.embLL a)
    rw [add_zero, htN0, add_zero] at this
    rw [hT0]
    simp only [LinearMap.map_smulₛₗ, RingHom.id_apply]
    rw [hT0, this]
  let T : Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) (j' + 1)) :=
    { toFun := T0
      map_add' := hadd
      map_smul' := hsmul }
  refine ⟨T, fun s ϖ hc hu x => ?_⟩
  show Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 x)) =
    NG.tN Mw.J s ϖ k (Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x))
  rw [hT0]
  exact tN_eq_of_conj D Mw.J v s0 s ϖ0 ϖ k hc0 hc hu0 hu _

end GlobalTheory.HeckeLiftN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjReferenceChartIndexStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_referenceChartIndex : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ b : Idx I.sel (I.tup a) (I.idx a) i, ∃ (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i)
      (x : ∀ w : (B.primes X).vGs, GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ w.1.asIdeal)),
      (i + 1 = B.R.m → ∀ w, x w = 1) ∧
      (∀ g : GLG B.fields.E (B.R.N i) (B.primes X).vGs, g ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp ↔
        (fun w => x w * g w * (x w)⁻¹) ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp) ∧
      ∀ (g : ↥(levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp) (g0 : ↥(levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp),
        (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) →
        (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).chr g = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).chr g0 := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch.idx_match | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch.idx_match | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch.idx_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepFamilyBoundedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_rep_family_bounded : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE),
    GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ c1 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c1 l j).1 ≤ (b0 l j).1) →
      ∃ rho : RhoFam D T, (∀ i σ b, Continuous fun g =>
          ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) ∧
        ∀ i σ b, (∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ D.what₂.isot j σ ≠ ⊥) → D.nd.goodRow σ →
        ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
        ∀ (φ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ),
          (∀ z : ℤ_[T.l i], φ (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
            algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i])) →
          (∀ x : ↥D.LL0, ι (φ ((if b then T.emb0 i else T.emb0b i) x)) = embLL0 D x) →
          IsRepOf D (T.l i) ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
            (mapRep (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))) (rho i σ b)) := by
  first | exact @GlobalTheory.HeightCounting.RowRhoInt.rho_rows | exact GlobalTheory.HeightCounting.RowRhoInt.rho_rows | (intros; apply GlobalTheory.HeightCounting.RowRhoInt.rho_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulMemOfSpan
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Full

theorem exists_nsmul_mem_of_span {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (x : V) (hx : x ∈ Submodule.span K (L : Set V)) :
    ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegerMultiple.main
  | exact _root_.GlobalTheory.NatMulIntegerMultiple.main
  | (apply _root_.GlobalTheory.NatMulIntegerMultiple.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegerMultiple.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegerMultiple.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegerMultiple.main ..)

theorem dgam_pos_and_full : ∀ D : D7, (∀ u, 0 < (D.mem u).C.DGam) ∧
    ∀ u (x : (D.div.Nu u).V), ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ DV.MramL D u := by
  intro D
  refine ⟨fun u => (D.mem u).C.DGam_pos, fun u x => ?_⟩
  obtain ⟨n, hn, h⟩ := exists_nsmul_mem_of_span ((D.fm u).lat 0).L (D.nuIn u x)
    (by rw [((D.fm u).lat_good 0).2.2]; trivial)
  refine ⟨n, hn, ?_⟩
  show D.nuIn u (n • x) ∈ ((D.fm u).lat 0).L
  rw [map_nsmul]
  exact h

end GlobalTheory.Mem.Full
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceOfIsSplitPlaceCmField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.SplitPlaceOf

theorem exists_splitPlace : ∀ (D : D7) (P : PlE D.host), IsSplitPl D.host P →
    ∃ s : SplitPlace D.host.E, s.w = P :=
  fun D P hP => GlobalTheory.RowUnitProof.exists_splitPlace_eq D P hP

end GlobalTheory.HeightCounting.SplitPlaceOf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFactsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeDoubleCosetOperators_standardFacts : HeckeStdPlain := by
  first | exact @GlobalTheory.HeckeStdFacts.heckeStdPlain | exact GlobalTheory.HeckeStdFacts.heckeStdPlain | (intros; apply GlobalTheory.HeckeStdFacts.heckeStdPlain <;> assumption)
end

