import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf

variable {D : D7}

def gramQ (W : HSp D) {ρ : ℕ} (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) : Matrix (Fin ρ) (Fin ρ) D.host.E :=
  xᴴ ⬝ (W.gram ⬝ x)

def Orb (W : HSp D) {ρ : ℕ} (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) : Set (Matrix (Fin W.rank) (Fin ρ) D.host.E) :=
  {x | LinearIndependent D.host.E x.transpose ∧ gramQ W x = gramQ W x₀}

def Rgrp (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) : Subgroup (GA D W) where
  carrier := {r | ∃ u ∈ UX D ρ, mt W r ⬝ x = x ⬝ u.1}
  one_mem' := ⟨1, one_mem _, by rw [mt_one, Matrix.one_mul, Units.val_one, Matrix.mul_one]⟩
  mul_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨v, hv, hb⟩
    exact ⟨u * v, mul_mem hu hv, by
      rw [mt_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Units.val_mul, Matrix.mul_assoc]⟩
  inv_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    have h : mt W a⁻¹ ⬝ (x ⬝ u.1) = x := by rw [← ha, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    calc mt W a⁻¹ ⬝ x = mt W a⁻¹ ⬝ (x ⬝ u.1) ⬝ (u⁻¹).1 := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = x ⬝ (u⁻¹).1 := by rw [h]

section Source

variable (ψ : AddChar (AF D.host.F) ℂ) {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (W : HSp D)

def Nfix (j : Fin ρ) : Subgroup (GA D V) :=
  flagN d ⊓ ⨅ i : {i : Fin ρ // i ≤ j}, fixer V (d.jX.submatrix id fun _ : Fin 1 => i.1)

def term (v : VolM D W.rank ρ) (Ψ : WO V W → ℂ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E) : ℂ :=
  d.mixS W ψ v.μ v.𝓕 Ψ (rat x) 0

structure IsTh (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ) : Prop where
  cont : Continuous fun n : flagN d => Th n.1
  left : ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ n ∈ flagN d, Th (γ * n) = Th n
  cen : ∀ c, ∀ n ∈ flagN d, Th (d.nC c * n) = star (ψ (d.qS W c (rat x₀))) * Th n
  dep : ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), a j = 1 → (∀ i, j < i → a i = 0) → gramQ W x₀ *ᵥ a = 0 →
    ∃ (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V) (u : GA D V) (c : ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u ∧ u ∈ Nfix d j ∧ c ≠ 1 ∧
      ∀ n ∈ flagN d, ∀ n' ∈ flagN d, Th (n * u * n') = c * Th (n * n')

def IsBase (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) : Prop :=
  LinearIndependent D.host.E x₀.transpose ∧
    ∀ u ∈ UX D ρ, adj u.1 ⬝ ((rat (gramQ W x₀) : Mx D ρ ρ) ⬝ u.1) = rat (gramQ W x₀)

def flFun (v : VolM D W.rank ρ) (Th : GA D V → ℂ) (x : Mx D W.rank ρ) (Ψ : WO V W → ℂ) (u : UX D ρ)
    (b : Mx D ρ V₀.rank) : ℂ :=
  Th (d.nB b * d.levi u.1) * d.mixS W ψ v.μ v.𝓕 Ψ (x ⬝ u.1.1) (x ⬝ b)

def fl (v : VolM D W.rank ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (Th : GA D V → ℂ) (x : Mx D W.rank ρ)
    (Ψ : WO V W → ℂ) : ℂ :=
  ∫ u, (∫ b in vb.𝓕, flFun ψ d W v Th x Ψ u b ∂vb.μ) ∂vU.ν

end Source

def kerBF {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) (φ : GA D B.A → ℂ)
    (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ) (h : GA D J.W) : ℂ :=
  G h * ∫ h₀ in B.vA.𝓕, φ h₀ * flatBF s (s.om (embA B.d B.o h₀, h) Φ) 0 ∂B.vA.μ

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.LinkSimil
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.StCheck

open GlobalTheory.Size (posSp)
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem jointCont (D : D7) : JointCont D := fun _ _ _ _ _ _ h _ hf => GlobalTheory.ThetaJointCont.continuous_om_oriented h hf

theorem quasiFam_of_weil {S L : HSp D} {χS χL} {om : Om S L} (hom : IsWeilDatumO ψ S L χS χL om) {f : WO S L → ℂ}
    (hf : IsThetaFunO ψ S L f) {φ : GA D S → ℂ} (hφ : IsContAut S φ) :
    IsQuasiFam ψ S L fun h w => star (φ h) * om (h, 1) f w := by
  refine ⟨fun h γ w => ?_, ?_, fun γ hγ h w => ?_⟩
  · rw [(hom.om_pres _ f hf).quasi]; ring
  · exact (hφ.2.comp continuous_fst).star.mul ((jointCont D ψ S L χS χL om hom f hf).comp
      (f := fun p : GA D S × WO S L => ((p.1, (1 : GA D L)), p.2))
      ((continuous_fst.prodMk continuous_const).prodMk continuous_snd))
  · have h1 := GlobalTheory.MixPer.Check.om_rat hom hγ (one_mem _) (hom.om_pres (h, 1) f hf)
      (fun u => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std (hom.om_pres (h, 1) f hf) u) (w ⬝ mt S γ)
    rw [actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one, ← Module.End.mul_apply, ← map_mul,
      Prod.mk_mul_mk, mul_one] at h1
    rw [hφ.1 γ hγ, h1]

theorem exists_quasiFam (D : D7) (m : ℕ) (hW : ∀ ψ, IsStdChar D ψ (-1) →
    ∃ χS χL om, IsWeilDatumO ψ (posSp D m) (posSp D 1) χS χL om) :
    ∃ (ψ : AddChar (AF D.host.F) ℂ) (Y : GA D (posSp D m) → WO (posSp D m) (posSp D 1) → ℂ),
      IsStdChar D ψ (-1) ∧ IsQuasiFam ψ _ _ Y ∧ Y 1 ≠ 0 := by
  obtain ⟨ψ, θ, μ, 𝓕, U, f, hψ, -, hm, hU, hf, h0, -⟩ := GlobalTheory.Size.exists_theta_posSp D m 1
  obtain ⟨χS, χL, om, hom⟩ := hW ψ hψ
  have hf' : IsThetaFunO ψ _ _ f := GlobalTheory.Size.isTheta_iff_level.2 ⟨U, hU, hf⟩
  refine ⟨ψ, _, hψ, quasiFam_of_weil hom hf' (φ := fun _ => 1) ⟨fun _ _ _ => rfl, continuous_const⟩, fun h => h0 ?_⟩
  have e : f = 0 := by
    funext w
    have := congrFun h w
    rw [show ((1 : GA D (posSp D m)), (1 : GA D (posSp D 1))) = 1 from rfl, map_one] at this
    simpa using this
  rw [e]; simp [GlobalTheory.Ker.ipO]

theorem trace_inverseGram_conj_smul_eq {R : Type} [CommRing R] {m n : ℕ} (c : R) (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin m) (Fin n) R)
    (g : Matrix (Fin n) (Fin n) R) (y : Matrix (Fin n) (Fin m) R) :
    (a ⬝ (b ⬝ ((c • g) ⬝ y))).trace = c * (a ⬝ (b ⬝ (g ⬝ y))).trace := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]

set_option maxHeartbeats 1600000 in

theorem hO_ofAdj (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (c : D.host.E)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = c • L'.gram) (x y : WO S L') :
    hO L S (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ x))
      (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ y)) =
      incA D (c / (D.host.xi0 * star D.host.xi0)) * hO S L' y x := by
  have h : adj (rat τ : Mx D L.rank L'.rank) ⬝ (gA L ⬝ (rat τ : Mx D L.rank L'.rank)) = incA D c • gA L' := by
    rw [gA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]; exact congrArg rat hτ
  rw [hO_eq_trace, hO_eq_trace, ofAdj, ofAdj]
  simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel, trace_smul, smul_eq_mul]
  rw [trace_mul_comm (rat τ : Mx D L.rank L'.rank), Matrix.mul_assoc y, trace_mul_comm y]
  simp only [Matrix.mul_assoc]
  rw [cancel₃ h]
  have h0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have h1 : incA D (c / (D.host.xi0 * star D.host.xi0)) =
      incA D (-D.host.xi0⁻¹) * (cA D (incA D (-D.host.xi0⁻¹)) * incA D c) := by
    rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, ← map_mul]
    congr 1
    rw [star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    field_simp
  have h2 := trace_inverseGram_conj_smul_eq (R := AE D) (incA D c) (giA S) (adj x) (gA L') y
  rw [h1, mul_assoc, mul_assoc]
  exact congrArg (fun t => incA D (-D.host.xi0⁻¹) * (cA D (incA D (-D.host.xi0⁻¹)) * t)) h2

theorem normSq_xi_ne_zero : D.host.xi0 * star D.host.xi0 ≠ 0 :=
  mul_ne_zero (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (star_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))

theorem sympl_link (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = (D.host.xi0 * star D.host.xi0) • L'.gram) (x y : WO S L') :
    symplOH L S (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ x)) (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ y)) =
      -symplOH S L' x y := by
  rw [symplOH_eq, hO_ofAdj L L' S τ _ hτ, div_self normSq_xi_ne_zero, map_one, one_mul, ← symplOH_eq, symplOH_skew]

theorem sympl_last (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = (-(D.host.xi0 * star D.host.xi0)) • L'.gram) (x y : WO S L') :
    symplOH L S (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ x)) (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ y)) =
      symplOH S L' x y := by
  rw [symplOH_eq, hO_ofAdj L L' S τ _ hτ, neg_div, div_self normSq_xi_ne_zero, map_neg, map_one, neg_one_mul, map_neg,
    ← symplOH_eq, symplOH_skew, neg_neg]

theorem mt_inv_ofAdj (L W : HSp D) (n : GA D W) (z : Mx D L.rank W.rank) :
    mt W n⁻¹ ⬝ ofAdj L W z = ofAdj L W (z ⬝ mt W n) := by
  simp only [ofAdj, mt_inv, adj_mul, Matrix.mul_smul, Matrix.mul_assoc, gA_giA_cancel]

theorem incAdj_eq {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (L : HSp D) (y : Mx D L.rank ρ) :
    d.incAdj L y = ofAdj L W (y ⬝ d.pX) := by
  simp only [ofAdj, d.incAdj_apply, d.incY_apply, d.pX_eq, adj_mul, adj_adj, adj_gA, Matrix.mul_smul, Matrix.mul_assoc,
    giA_gA_cancel]

theorem projection_mul_ofAdjoint {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (L : HSp D) (z : Mx D L.rank W.rank) :
    d.p0 ⬝ ofAdj L W z = ofAdj L W₀ (z ⬝ d.j0) := by
  simp only [ofAdj, d.p0_eq, adj_mul, Matrix.mul_smul, Matrix.mul_assoc, gA_giA_cancel]

theorem tau_zEll {ρ σ : ℕ} {B : BesLev D σ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') :
    (rat l.τ : Mx D B.L.rank L'.rank) ⬝ zEll L' ρ ζ' = yZero B.L ρ B.ζ := by
  rw [zEll, Matrix.mul_vecMulVec, ← ratV_mulVec, l.map, yZero, zEll, ← Matrix.neg_vecMulVec]
  congr 1
  funext i; exact map_neg (incA D) _

theorem link_point {ρ σ : ℕ} {B : BesLev D σ} {L' W W₀ : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')
    (d : HypDec W W₀ ρ) (n : GA D W) : ptT d B.L (yZero B.L ρ B.ζ) n = l.κ W₀ (ptS d L' (zEll L' ρ ζ') n) := by
  rw [ptT, incAdj_eq, mt_inv_ofAdj, projection_mul_ofAdjoint, Link.κ, ptS, d.extX_apply, ← tau_zEll l]
  simp only [Matrix.mul_assoc]

theorem link_centre {ρ σ : ℕ} {B : BesLev D σ} {L' W W₀ : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')
    (hτ : l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram)
    (d : HypDec W W₀ ρ) (n : GA D W) : cenT d B.L (yZero B.L ρ B.ζ) n = -cenS d L' (zEll L' ρ ζ') n := by
  rw [cenT, incAdj_eq, mt_inv_ofAdj, cenS, d.extX_apply, ← tau_zEll l, ← sympl_link B.L L' W l.τ hτ]
  simp only [Matrix.mul_assoc]

theorem link_simil {σ : ℕ} {B : BesLev D σ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (h : IsLineVec L' ζ')
    (l : Link B L' ζ') : l.τᴴ ⬝ (B.L.gram ⬝ l.τ) = (D.host.xi0 * star D.host.xi0) • L'.gram := by
  have e : star ζ' ⬝ᵥ (l.τᴴ ⬝ (B.L.gram ⬝ l.τ)) *ᵥ ζ' =
      star ζ' ⬝ᵥ ((D.host.xi0 * star D.host.xi0) • L'.gram) *ᵥ ζ' := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.star_mulVec, ← Matrix.mulVec_mulVec, l.map, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← l.norm, star_neg, Matrix.mulVec_neg, neg_dotProduct_neg]
  have hu : Unique (Fin L'.rank) := by rw [h.1]; infer_instance
  have h2 := h.2
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at e h2
  funext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  have a : star ζ' default ≠ 0 := left_ne_zero_of_mul h2
  have b : ζ' default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
  have c := mul_left_cancel₀ a e
  have c' := mul_right_cancel₀ b c
  exact c'

example (D : D7) : ∃ τ : Matrix (Fin 1) (Fin 1) D.host.E,
    τᴴ ⬝ ((show Matrix (Fin 1) (Fin 1) D.host.E from (diagSp D 1 ![true] 0 1).gram) ⬝ τ) =
      (-(D.host.xi0 * star D.host.xi0)) • (show Matrix (Fin 1) (Fin 1) D.host.E from (diagSp D 1 ![false] 1 0).gram) := by
  refine ⟨D.host.xi0 • 1, ?_⟩
  rw [diagSp_gram, diagSp_gram]
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [Examples₂.sgn, mul_comm]

end GlobalTheory.Unf.StCheck

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.FinPl

variable {D : D7}

section Ops

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def formAt (β : Frame p S n) (P : Pair k n) (φ₀ : GA D S → ℂ) : Form k n (GA D S → ℂ) :=
  fun P₁ => β.rep (Classical.epsilon fun g : GL n k => g • P = P₁) φ₀

def sOp (β : Frame p S n) (P : Pair k n) (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (φ₀ : GA D S → ℂ) : GA D S → ℂ :=
  dia ε (FFStar q χ (formAt β P φ₀)) P

def diaAt (β : Frame p S n) (P : Pair k n) (s : 𝓀[k]ˣ) (φ₀ : GA D S → ℂ) : GA D S → ℂ := dia s (formAt β P φ₀) P

def Frame.IsLatMoved (β : Frame p S n) (g : GA D S) (L : Lat S) (Λ : Submodule 𝒪[k] (n → k)) : Prop :=
  ∀ x : n → k, x ∈ Λ ↔ mt S g⁻¹ *ᵥ (fun i => p.sec ((β.b *ᵥ x) i)) ∈ latV S L (· = p.v)

end Ops

def UnrAt {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (s : Step ψ V V₀ W W₀ ρ σ) (v : Pl D) : Prop :=
  CharUnramAt D s.χV v ∧ CharUnramAt D s.χW v

def FlatLaws (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (P : Pl D → Prop),
    (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J), IsFlatBF s P (flatBF s)) ∧
    ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), IsFlatFB s P (flatFB s)

def OneCosetBF (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V)
    (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v →
    ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f →
      Vac ψ B.V₀ J.W₀ LV₀ LW₀ (· = v) (𝔉 f) ∧
      ∀ h ∈ grpAt J.W (· = v), 𝔉 (s.om (1, h) f) ≠ 0 →
        ∃ r ∈ jacGrp J.d, r ∈ grpAt J.W (· = v) ∧ ∃ κ, InK J.W LW (· = v) κ ∧ h = r * κ

def OrbitSplit (D : D7) : Prop :=
  ∀ (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (v : Pl D), Tame D v → IsSelfDualC B.V₀ L₀ → SplitCore B L₀ v →
    ∀ γ ∈ grpAt B.V₀ (· = v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = v) →
        mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = v)) →
      ∃ a ∈ grpAt B.A (· = v), ∃ κ, InK B.V₀ L₀ (· = v) κ ∧ γ = B.o.emb (a, 1) * κ

def OrbitGlued (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (σ : ℕ) (B : BesLev D σ) (L₀ : Lat B.V₀) (β : Frame p B.A n)
    (β₀ : Frame p B.V₀ (n ⊕ Fin 1)) (P : Pair k n), IsSelfDualC B.V₀ L₀ → GluedCore B L₀ q β β₀ P →
    ∀ γ ∈ grpAt B.V₀ (· = p.v), (∀ a : AE D, a • ratV (vecB B.o B.ζ) ∈ latA B.V₀ L₀ (· = p.v) →
        mt B.V₀ γ⁻¹ *ᵥ (a • ratV (vecB B.o B.ζ)) ∈ latA B.V₀ L₀ (· = p.v)) →
      (∃ a ∈ grpAt B.A (· = p.v), ∃ κ, InK B.V₀ L₀ (· = p.v) κ ∧ γ = B.o.emb (a, 1) * κ) ∨
      ∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsLattice k),
        β₀.IsLatMoved γ L₀ (lastKer Λ) ∨ β₀.IsLatMoved γ L₀ (lastPair q Λ).lat

def SourceGlued (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ₀ : AddChar k Circle)
    (hχ : HasConductor χ₀ 1) (χ : AddChar 𝓀[k] ℂ), χ = resChar χ₀ hχ q →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ →
    CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om →
    CharUnramAt D χS p.v → CharUnramAt D χT p.v →
    ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ →
    ∀ (P P₁ : Pair k n') (Λ : Submodule 𝒪[k] (n → k)) [Λ.IsLattice k],
      (∃ c : ℂ, ∀ (LS : Lat S) (LT : Lat T) (f₀ Ξ : WO S T → ℂ) (Ξ' : Pair k n → WO S T → ℂ),
        Over ψ α₀ β LS LT f₀ (latInd (gluedS q 1 P.ker P.vec) Λ) Ξ →
        (∀ Q ∈ withLat Λ, Over ψ α₀ β LS LT f₀ (tensCol (phiOne P₁ Q) (charInd χ Q)) (Ξ' Q)) →
        ∀ φ, IsRam α φ → liftA o om vA (φ P) Ξ = c • ∑ Q ∈ withLat Λ, liftA o om vA (FFStar q χ φ P₁) (Ξ' Q)) ∧
      ∀ (LS : Lat S) (LT : Lat T) (f₀ Ξ : WO S T → ℂ) (a : (n → k) → ℂ),
        (Over ψ α₀ β LS LT f₀ (tensCol (latInd P.lat Λ) a) Ξ ∨ Over ψ α₀ β LS LT f₀ (tensCol (latInd P.ker Λ) a) Ξ) →
        ∀ φ, IsRam α φ → liftA o om vA (φ P) Ξ = 0

def Contraction (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ →
    ∃ ε : k, (ε = 1 ∨ ε = -1) ∧
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
      (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
      (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
      (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'')
      (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ →
      ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀)
        (f₁ Ξ₁ Ξ₁' : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ Ξ₂' : WO J.W₀ B'.V₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (Ψ₂ : Matrix n'' n k → ℂ)
        (a a' b b' : (n → k) → ℂ), a ∈ SB (n → k) → a' ∈ SB (n → k) → b ∈ SB (n → k) → b' ∈ SB (n → k) →
        Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ₁ → Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a') Ξ₁' →
        Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ₂ → Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b') Ξ₂' →
        ∀ φ, IsContAut B.A φ →
          (∫ η, (∫ y, a' y * (χ (ε * (η ⬝ᵥ y)) : ℂ) ∂μ) * b' η ∂μ) • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ =
            (∫ η, (∫ y, a y * (χ (ε * (η ⬝ᵥ y)) : ℂ) ∂μ) * b η ∂μ) • hand0 s₁ s₂ l vL φ Ξ₁' Ξ₂'

def VertexGlued (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ →
    ∃ ε : 𝓀[k]ˣ, (ε = 1 ∨ ε = -1) ∧
    ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
      (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
      (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), UnrAt s₁ p.v → UnrAt s₂ p.v →
      ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'')
        (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ →
      ∀ (P P₁ : Pair k n') (Q : Pair k n),
        (∀ R : Pair k n'', ∃ c : ℂ, ∀ (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀)
          (f₁ Ξ₁ Ξ₁' : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ Ξ₂' : WO J.W₀ B'.V₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (latInd (gluedS q 1 P.ker P.vec) Q.lat) Ξ₁ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P₁ Q) (vecInd Q.lat)) Ξ₁' →
          Over ψ β γ₀ L₂' L₃ f₂ (latInd Q.lat (gluedS q 1 R.ker R.vec)) Ξ₂ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow (phiOne Q R) (dualInd Q.lat)) Ξ₂' →
          ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ =
            c • hand0 s₁ s₂ l vL (dia ε (FFStar q (resChar χ hχ q) φ) P₁) Ξ₁' Ξ₂') ∧
        ∀ (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k] (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀)
          (f₁ Ξ₁ : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ : WO J.W₀ B'.V₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (latInd (gluedS q 1 P.ker P.vec) Q.lat) Ξ₁ →
          (Over ψ β γ₀ L₂' L₃ f₂ (latInd Q.lat (lastKer Λ)) Ξ₂ ∨ Over ψ β γ₀ L₂' L₃ f₂ (latInd Q.lat (lastPair q Λ).lat) Ξ₂) →
          ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = 0

def Commutation (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (q : Unif k) (χ₀ : AddChar k Circle)
    (hχ : HasConductor χ₀ 1) (χ : AddChar 𝓀[k] ℂ), χ = resChar χ₀ hχ q → ∀ (ε : 𝓀[k]ˣ) (ψ : AddChar (AF D.host.F) ℂ)
    (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B')
    (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), UnrAt s₁ p.v → UnrAt s₂ p.v →
    ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'')
      (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ →
    ∀ (P : Pair k n') (Q : Pair k n) (R : Pair k n''), ∃ c : ℂ, c ≠ 0 ∧
      ∀ (L₁ : Lat B.V₀) (L₂ L₂' : Lat J.W₀) (L₃ : Lat B'.V₀) (f₁ Ξ₁ : WO B.V₀ J.W₀ → ℂ) (f₂ Ξ₂ : WO J.W₀ B'.V₀ → ℂ),
        Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P Q) (vecInd Q.lat)) Ξ₁ →
        Over ψ β γ₀ L₂' L₃ f₂ (tensRow (phiOne Q R) (dualInd Q.lat)) Ξ₂ →
        ∀ φ₀, RamAt α P φ₀ → RamAt γ R (hand0 s₁ s₂ l vL φ₀ Ξ₁ Ξ₂) ∧
          (∀ s, hand0 s₁ s₂ l vL (diaAt α P s φ₀) Ξ₁ Ξ₂ = diaAt γ R s (hand0 s₁ s₂ l vL φ₀ Ξ₁ Ξ₂)) ∧
          hand0 s₁ s₂ l vL (sOp α P q χ ε φ₀) Ξ₁ Ξ₂ = c • sOp γ R q χ ε (hand0 s₁ s₂ l vL φ₀ Ξ₁ Ξ₂)

def LastGlued (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ₀ : AddChar k Circle)
    (hχ : HasConductor χ₀ 1) (χ : AddChar 𝓀[k] ℂ), χ = resChar χ₀ hχ q →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (T : HSp D) (B : BesLev D 0) (t : Last ψ T B), UnrAt t.s p.v →
    CharUnramAt D t.χS p.v → CharUnramAt D t.χT p.v → ExtUnramAt D p.v →
    ∀ o : OrthDec B.V B.A B.L, (∀ a, o.emb (a, 1) = embA B.d B.o a) →
    ∀ (α : Frame p B.A n') (α₀ : Frame p B.V (n' ⊕ Fin 1)) (β : Frame p t.J.W n), IsSumFrame o B.ζ α α₀ →
    ∀ (P P₁ : Pair k n') (Q : Pair k n), ∃ c : ℂ,
      ∀ (L₁ : Lat B.V) (L₂ L₂' : Lat t.J.W) (L₃ : Lat T) (f₁ Φ₁ Φ₁' : WO B.V t.J.W → ℂ) (Φ₂ : WO t.J.W T → ℂ),
        Over ψ α₀ β L₁ L₂ f₁ (latInd (gluedS q 1 P.ker P.vec) Q.lat) Φ₁ →
        Over ψ α₀ β L₁ L₂ f₁ (tensCol (phiOne P₁ Q) (charInd χ Q)) Φ₁' →
        IsSelfDualC t.J.W L₂' → IsSelfDualC T L₃ → β.IsLat L₂' Q.lat → Vac ψ t.J.W T L₂' L₃ (· = p.v) Φ₂ →
        ∀ φ, IsRam α φ → ∀ F, IsContAut T F → t.Q (φ P) Φ₁ Φ₂ F = c * t.Q (FFStar q χ φ P₁) Φ₁' Φ₂ F

def RamBijective (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ₀ : AddChar k Circle)
    (hχ : HasConductor χ₀ 1) (χ : AddChar 𝓀[k] ℂ), χ = resChar χ₀ hχ q → ∀ (ε : 𝓀[k]ˣ) (S : HSp D)
    (β : Frame p S n) (P : Pair k n),
      Set.BijOn (sOp β P q χ ε) {φ₀ | RamAt β P φ₀} {φ₀ | RamAt β P φ₀} ∧
      (∀ φ, IsRam β φ → IsRam β (dia ε (FFStar q χ φ)) ∧ sOp β P q χ ε (φ P) = dia ε (FFStar q χ φ) P) ∧
      ∃ c c' : GL n k →₀ ℂ, (∀ φ₀, sOp β P q χ ε φ₀ = c.sum fun g a => a • β.rep g φ₀) ∧
        ∀ φ₀, RamAt β P φ₀ → sOp β P q χ ε (c'.sum fun g a => a • β.rep g φ₀) = φ₀ ∧
          RamAt β P (c'.sum fun g a => a • β.rep g φ₀)

def OverBasic (D : D7) : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ),
    IsStdChar D ψ (-1) → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T),
    IsSelfDualC S LS → IsSelfDualC T LT → ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ →
      (∀ Ψ ∈ SB (Matrix n n' k), ∃! f, Over ψ α β LS LT f₀ Ψ f) ∧
      (∀ Ψ f, Over ψ α β LS LT f₀ Ψ f → IsThetaFunO ψ S T f ∧
        ∀ (MS : Lat S) (MT : Lat T) (P : Pl D → Prop), ¬ P p.v → Vac ψ S T MS MT P f₀ → Vac ψ S T MS MT P f) ∧
      (p.UnitAA → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT →
        Over ψ α β LS LT f₀ (latInd ΛS ΛT) f₀)

def PlacesToAdeles (D : D7) : Prop :=
  ∀ (S : HSp D) (L : Lat S) (P : Pl D → Prop), IsSelfDualC S L →
    ∀ R : Subgroup (GA D S), ∀ h : GA D S,
      (∀ v, P v → ∃ hv ∈ grpAt S (· = v), ∃ h' ∈ grpOff S (· = v), h = hv * h' ∧
        ∃ r ∈ R, r ∈ grpAt S (· = v) ∧ ∃ κ, InK S L (· = v) κ ∧ hv = r * κ) →
      ∃ r ∈ R, r ∈ grpAt S P ∧ ∃ g ∈ grpOff S P, ∃ κ, InK S L P κ ∧ h = r * g * κ

end GlobalTheory.FinPl

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.FB

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ}

def x0 (B : BesLev D σ) : Mx D B.V.rank (σ + 1) := xLast B.d (vecB B.o B.ζ)

def zl (B : BesLev D σ) : Mx D B.L.rank (σ + 1) := zEll B.L (σ + 1) B.ζ

def orb (B : BesLev D σ) : Set (Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E) :=
  {x | LinearIndependent D.host.E x.transpose ∧
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat x : Mx D B.V.rank (σ + 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zl B)}

def Quasi (ψ : AddChar (AF D.host.F) ℂ) (S L : HSp D) (y : WO S L → ℂ) : Prop :=
  (∀ γ w, y (ratW L S γ + w) = ψ (-(symplOH S L (ratW L S γ) w)) * y w) ∧ Continuous y

def RQ (B : BesLev D σ) : Subgroup (GQ B.V) := (besGrp B.d B.o).subgroupOf (GQ B.V)

abbrev Cos (B : BesLev D σ) : Type := GQ B.V ⧸ RQ B

def rep {B : BesLev D σ} (q : Cos B) : GA D B.V := ((q.out : GQ B.V) : GA D B.V)⁻¹

def th (J : JacLev D (σ + 1)) (ψ : AddChar (AF D.host.F) ℂ) (B : BesLev D σ) (y : WO J.W₀ B.L → ℂ) (n : GA D J.W) : ℂ :=
  star (jacS ψ J.d B.L (zl B) n y 0) * star (psiFlag ψ J.d n)

variable {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B)

def term (Ψ : WO J.W B.V → ℂ) (x : Mx D B.V.rank (σ + 1)) : WO J.W₀ B.V → ℂ := J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ x

def kerN (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) : ℂ :=
  ∫ n in J.vN.𝓝, th J ψ B y n.1 * s.om (n.1, 1) Ψ 0 ∂J.vN.ν

def bFun (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) (x : Mx D B.V.rank (σ + 1)) (b : Mx D (σ + 1) J.W₀.rank) : ℂ :=
  term s Ψ x (x ⬝ b) * star (y (zl B ⬝ b))

def bTerm (vB : VolM D (σ + 1) J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) (x : Mx D B.V.rank (σ + 1)) : ℂ :=
  ∫ b in vB.𝓕, bFun s y Ψ x b ∂vB.μ

def uFun (vB : VolM D (σ + 1) J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) (x : Mx D B.V.rank (σ + 1))
    (u : UX D (σ + 1)) : ℂ :=
  star (psiUni ψ u.1) * bTerm s vB y (s.om (J.d.levi u.1, 1) Ψ) x

def tFlat (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ) : ℂ :=
  contractT B.o J.W₀ vL.μ vL.𝓕 (flatFB s Ψ) y 0

def unfF (vL : VolM D B.L.rank J.W₀.rank) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (G : GA D B.V → ℂ) (Φ : WO J.W B.V → ℂ)
    (h : GA D B.V) : ℂ :=
  G h * handFB s vL Y (flatFB s (s.om (1, h) Φ)) 1

theorem quasi_of_fam {S L : HSp D} {Y : GA D S → WO S L → ℂ} (hY : IsQuasiFam ψ S L Y) (h : GA D S) : Quasi ψ S L (Y h) :=
  ⟨hY.quasi h, hY.cont.comp (Continuous.prodMk_right h)⟩

end GlobalTheory.Unf.FB

end
end

