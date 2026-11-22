import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0025
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0697
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundHolomorphicFrameChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0688
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0681
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0691
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0690
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0708
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0692
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0709

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaxSimplicialCellMultiplicityLtTopOfIsPolyFan
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section
namespace GlobalTheory.PolFan

namespace MultBound
variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  {X₁ : Type} [AddCommGroup X₁] [Module O X₁] {m : ℕ}

theorem cellMult_map {Y : Type} [AddCommGroup Y] [Module O Y] (f : balForms bar X ≃ₗ[ℤ] balForms bar Y)
    (δ : Fin m → balForms bar X) : cellMult bar (fun i => f (δ i)) = cellMult bar δ := by
  unfold cellMult
  have hs : (Submodule.span ℤ (Set.range δ)).map (f : balForms bar X →ₗ[ℤ] balForms bar Y) =
      Submodule.span ℤ (Set.range fun i => f (δ i)) := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  let g := Submodule.Quotient.equiv _ _ f hs
  symm
  refine Nat.card_congr (g.toEquiv.subtypeEquiv fun x => ?_)
  simp only [Submodule.mem_torsion_iff]
  refine exists_congr fun a => ?_
  rw [Submonoid.smul_def, Submonoid.smul_def]
  change _ ↔ (a : ℤ) • g x = 0
  rw [← map_smul, LinearEquiv.map_eq_zero_iff]

theorem cellMult_le_of_finite (T : Set (balForms bar X)) (hT : T.Finite) :
    ∃ C : ℕ, ∀ (m : ℕ) (δ : Fin m → balForms bar X), (∀ i, δ i ∈ T) → cellMult bar δ ≤ C := by
  classical
  let F : Set (balForms bar X) → ℕ := fun s => Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ Submodule.span ℤ s))
  refine ⟨hT.toFinset.powerset.sup fun s => F ↑s, fun m δ hδ => ?_⟩
  have hr : Set.range δ ⊆ T := Set.range_subset_iff.2 hδ
  have e : Set.range δ = ↑((hT.subset hr).toFinset) := by simp
  have hmem : (hT.subset hr).toFinset ∈ hT.toFinset.powerset :=
    Finset.mem_powerset.2 (Set.Finite.toFinset_subset_toFinset.2 hr)
  show F (Set.range δ) ≤ _
  rw [e]
  exact Finset.le_sup_of_le hmem le_rfl

theorem zsmul_cancel {g : ℤ} (hg : g ≠ 0) {u w : balForms bar X} (h : g • u = g • w) : u = w :=
  Subtype.ext (LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ (congrArg Subtype.val h) a b
    simp only [Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hg this)

theorem prim_eq_of_smul {β β' : balForms bar X} (hβ : IsPrim bar β) (hβ' : IsPrim bar β') {p q : ℕ} (hp : 0 < p)
    (h : p • β = q • β') : β = β' := by
  have hd0 : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left _ hp
  obtain ⟨p', q', hcop, hp', hq'⟩ := Nat.exists_coprime p q
  have h' : (p' : ℤ) • β = (q' : ℤ) • β' := by
    refine zsmul_cancel (g := (Nat.gcd p q : ℤ)) (by exact_mod_cast hd0.ne') ?_
    rw [smul_smul, smul_smul, ← Nat.cast_mul, ← Nat.cast_mul, mul_comm, ← hp', mul_comm, ← hq', natCast_zsmul,
      natCast_zsmul]
    exact h
  have hb : ((Nat.gcd p' q' : ℕ) : ℤ) = p' * Nat.gcdA p' q' + q' * Nat.gcdB p' q' := Nat.gcd_eq_gcd_ab p' q'
  rw [hcop, Nat.cast_one] at hb
  set A := Nat.gcdA p' q'
  set B := Nat.gcdB p' q'
  set x : balForms bar X := B • β + A • β'
  have e1 : β = q' • x := by
    rw [← natCast_zsmul, smul_add, smul_smul, smul_smul,
      show ((q' : ℤ) * A) • β' = (A * p') • β by rw [mul_comm, ← smul_smul, ← h', smul_smul], ← add_smul]
    conv_lhs => rw [← one_smul ℤ β]
    congr 1
    rw [hb]; ring
  have e2 : β' = p' • x := by
    rw [← natCast_zsmul, smul_add, smul_smul, smul_smul,
      show ((p' : ℤ) * B) • β = (B * q') • β' by rw [mul_comm, ← smul_smul, h', smul_smul], ← add_smul]
    conv_lhs => rw [← one_smul ℤ β']
    congr 1
    rw [hb]; ring
  have h1 := hβ _ _ e1
  have h2 := hβ' _ _ e2
  rw [e1, e2, h1, h2]

theorem transport [Module.Finite O X] [Module.Finite O X₁] (e : X ≃ₗ[O] X₁) {δ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar φ δ) (hl : LinearIndependent ℤ δ) (hp : ∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X₁)) :
    ∃ h' : IsCell bar φ (fun i => pull e.toLinearMap (δ i)), LinearIndependent ℤ (fun i => pull e.toLinearMap (δ i)) ∧
      (∀ i, IsPrim bar (⟨_, h'.mem i⟩ : balForms bar X)) ∧
      cellMult bar (fun i => (⟨pull e.toLinearMap (δ i), h'.mem i⟩ : balForms bar X)) =
        cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X₁)) := by
  have h' : IsCell bar φ (fun i => pull e.toLinearMap (δ i)) :=
    ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
      IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩
  have e0 : ∀ i, (pullBalEquiv bar e) ⟨δ i, h.mem i⟩ = ⟨pull e.toLinearMap (δ i), h'.mem i⟩ := fun i => rfl
  have hfam : (fun i => (pullBalEquiv bar e) ⟨δ i, h.mem i⟩) =
      fun i => (⟨pull e.toLinearMap (δ i), h'.mem i⟩ : balForms bar X) := funext e0
  refine ⟨h', ?_, fun i k β' hk => ?_, by rw [← hfam]; exact cellMult_map _ _⟩
  · let P : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X :=
      { toFun := pull e.toLinearMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact hl.map' P (LinearMap.ker_eq_bot.2 fun a b hab => by
      rw [← pull_symm_pull e a, ← pull_symm_pull e b]; exact congrArg _ hab)
  · exact hp i k _ (by rw [← (pullBalEquiv bar e).symm_apply_apply ⟨δ i, h.mem i⟩, e0, hk, map_nsmul])

theorem perModule [Module.Finite O X] (hF : IsPolyFanOn bar φ X)
    (hpsd : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone bar X) :
    ∃ C : ℕ, ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ), LinearIndependent ℤ δ →
      (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) → cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) ≤ C := by
  classical
  obtain ⟨S, hS, hcov⟩ := hF.finite
  let T : Set (balForms bar X) :=
    {β | IsPrim bar β ∧ ∃ γ : balForms bar X, γ.1 ∈ S ∧ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a • β = b • γ}
  have hT : T.Finite := by
    have hS' : {γ : balForms bar X | γ.1 ∈ S}.Finite := hS.preimage Subtype.val_injective.injOn
    choose! f hf using fun β (hβ : β ∈ T) => hβ.2
    refine Set.Finite.of_injOn (f := f) (fun β hβ => (hf β hβ).1) (fun β hβ β' hβ' hff => ?_) hS'
    obtain ⟨-, a, b, ha, hb, h1⟩ := hf β hβ
    obtain ⟨-, a', b', ha', hb', h2⟩ := hf β' hβ'
    rw [hff] at h1
    refine prim_eq_of_smul hβ.1 hβ'.1 (p := b' * a) (q := b * a') (by positivity) ?_
    rw [mul_smul, h1, mul_smul, h2, smul_comm]
  obtain ⟨C, hC⟩ := cellMult_le_of_finite T hT
  refine ⟨C, fun m δ h hl hp => ?_⟩
  have hB : toReal (∑ i, δ i) ∈ psdCone bar X := hpsd _ (Submodule.sum_mem _ fun i _ => h.mem i) fun y => by
    simp only [LinearMap.sum_apply]; exact Finset.sum_nonneg fun i _ => h.nonneg i y
  obtain ⟨e, n, γ, c, hγ, hγS, hc, hrel⟩ := hcov _ hB
  obtain ⟨h', hl', hp', hm⟩ := transport e h hl hp
  rw [← hm]
  refine hC m _ fun i => ⟨hp' i, ?_⟩
  have hrel' : ∑ i, toReal (pull e.toLinearMap (δ i)) = ∑ j, c j • toReal (γ j) := by
    rw [← hrel]; ext a b; simp [LinearMap.sum_apply]
  obtain ⟨j, a, b, ha, hb, hab⟩ := GlobalTheory.T.cellGenerator_on_ray_of_linIndep_subcell O bar φ X m n _ γ c h' hγ hl' hc hrel' i
  exact ⟨⟨γ j, hγ.mem j⟩, hγS j, a, b, ha, hb, Subtype.ext (by simpa using hab)⟩

end MultBound

open MultBound in

theorem maxMult_lt_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ : InvFun (𝓞 E)), IsPolyFan H.bar q φ → maxMult H.bar q φ < ⊤ := by
  intro E _ _ _ H q φ hφ
  obtain ⟨n, Y, hY⟩ := GlobalTheory.T.finitely_many_iso_classes_projective_numberField E q
  have hb : ∀ k : Fin n, ∃ C : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
      [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Nonempty (X ≃ₗ[𝓞 E] Y k) → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
      LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
      cellMult H.bar (fun i => (⟨δ i, h.mem i⟩ : balForms H.bar X)) ≤ C := by
    intro k
    by_cases hk : ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X)
      (_ : Module.Projective (𝓞 E) X), Module.finrank (𝓞 E) X ≤ q ∧ Nonempty (X ≃ₗ[𝓞 E] Y k)
    · obtain ⟨X, _, _, _, _, hX, ⟨e⟩⟩ := hk
      haveI : Module.Finite (𝓞 E) (Y k) := Module.Finite.equiv e
      haveI : Module.Projective (𝓞 E) (Y k) := Module.Projective.of_equiv e
      have hYr : Module.finrank (𝓞 E) (Y k) ≤ q := e.finrank_eq ▸ hX
      obtain ⟨C, hC⟩ := perModule (hφ (Y k) hYr) (GlobalTheory.T.intBilinFormToReal_mem_balancedPsdCone E H (Y k))
      refine ⟨C, fun X' _ _ _ _ _ he' m δ h hl hp => ?_⟩
      obtain ⟨e'⟩ := he'
      obtain ⟨h', hl', hp', hc⟩ := transport e'.symm h hl hp
      rw [← hc]
      exact hC m _ h' hl' hp'
    · exact ⟨0, fun X _ _ _ _ hX he => (hk ⟨X, _, _, inferInstance, inferInstance, hX, he⟩).elim⟩
  choose C hC using hb
  refine lt_of_le_of_lt (b := ((Finset.univ.sup C : ℕ) : ℕ∞)) ?_ (ENat.coe_lt_top _)
  unfold maxMult
  refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun hX =>
    iSup_le fun m => iSup_le fun δ => iSup_le fun h => iSup_le fun hl => iSup_le fun hp => ?_
  obtain ⟨k, he⟩ := hY X hX
  exact_mod_cast (hC k X hX he m δ h hl hp).trans (Finset.le_sup (Finset.mem_univ k))

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
section
noncomputable section

open MvPolynomial Matrix NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder

namespace GlobalTheory.PointChern

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def coordOf {H : Host E} {Dw : Datum H} {n : ℕ} (e : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (w : ReciprocityTheory.L2DbarEstimates.V n) : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ :=
  fun τ i j => w (e.symm (τ, i, j))

def InDom {H : Host E} {Dw : Datum H} (z : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) : Prop :=
  ∀ τ, (1 - (z τ)ᴴ * z τ).PosDef

theorem mult_of_mem {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : Dw.mult τ = Dw.p := by
  simp [Datum.mult, h]

theorem mult_of_not_mem {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : ¬ τ (H.rt : E) = H.rt0) :
    Dw.mult τ = Dw.q := by
  simp [Datum.mult, h]

open Classical in

def modelGram (H : Host E) (Dw : Datum H) (z : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) :
    GlobalTheory.FlagBundle.Mat Dw.mult ℂ := fun τ =>
  if h : τ (H.rt : E) = H.rt0 then
    reindex (finCongr (mult_of_mem Dw h).symm) (finCongr (mult_of_mem Dw h).symm)
      (1 - (z ⟨τ, h⟩).map (starRingEnd ℂ) * (z ⟨τ, h⟩)ᵀ)⁻¹
  else if h' : conjEmb τ (H.rt : E) = H.rt0 then
    reindex (finCongr (mult_of_not_mem Dw h).symm) (finCongr (mult_of_not_mem Dw h).symm)
      (1 - (z ⟨conjEmb τ, h'⟩)ᴴ * z ⟨conjEmb τ, h'⟩)⁻¹
  else 1

def relPoly {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  ∑ a ∈ Finset.range (k + 1), C ((-1 : ℝ) ^ (k - a)) * X (τ.1, a) * X (conjEmb τ.1, k - a)

end GlobalTheory.PointChern
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundCongrGermGramStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordGoodGrowthBound_congr_germ_gram : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (c : ℝ) (N : ℕ) (G G' : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n), G =ᶠ[nhds v] G' → GlobalTheory.GoodMetric.GoodBound S c N G v → GlobalTheory.GoodMetric.GoodBound S c N G' v := by
  first | exact @GlobalTheory.GoodMetric.goodBound_congr_nhds | exact GlobalTheory.GoodMetric.goodBound_congr_nhds | (intros; apply GlobalTheory.GoodMetric.goodBound_congr_nhds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundHolomorphicFrameChangeStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordGoodGrowthBound_holomorphic_frameChange : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (S : Finset (Fin n)) (c : ℝ) (N : ℕ) (B : ℝ), ∃ c' : ℝ, ∀ (G₀ P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n), ‖v‖ < 1 → (G₀ v).det ≠ 0 → (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) → (∀ i k, ContDiffAt ℝ 2 (fun u => P u i k) v) → (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar P u η = 0) → IsUnit (P v).det → (∀ i k, ‖P v i k‖ ≤ B) → (∀ i k, ‖(P v)⁻¹ i k‖ ≤ B) → (∀ a i k, ‖GlobalTheory.HermFrame.mdel P v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) → (∀ a b i k, ‖GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel P u (GlobalTheory.GoodMetric.coordVec b)) v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) → GlobalTheory.GoodMetric.GoodBound S c N G₀ v → (P v * G₀ v * (P v)ᴴ).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => (P u * G₀ u * (P u)ᴴ) i k) v) ∧ GlobalTheory.GoodMetric.GoodBound S c' N (fun u => P u * G₀ u * (P u)ᴴ) v := by
  first | exact @GlobalTheory.GoodMetric.FrameChange.goodBound_changeFrame | exact GlobalTheory.GoodMetric.FrameChange.goodBound_changeFrame | (intros; apply GlobalTheory.GoodMetric.FrameChange.goodBound_changeFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodsPolyGrowthOfBoundedCoisotropic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerGrowth

theorem differentiableOn_matrix_det_of_entries_normedSpace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B) :
    DifferentiableOn ℂ (fun b => (A b).det) B := by
  simp only [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul ?_ _
  have key : ∀ t : Finset (Fin d), DifferentiableOn ℂ (fun b => ∏ i ∈ t, A b (σ i) i) B := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).mul ih
  exact key _

theorem differentiableOn_matrix_inv_apply_of_entries {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B)
    (hd : ∀ b ∈ B, (A b).det ≠ 0) (i j : Fin d) :
    DifferentiableOn ℂ (fun b => (A b)⁻¹ i j) B := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((differentiableOn_matrix_det_of_entries_normedSpace hA).inv hd).mul (differentiableOn_matrix_det_of_entries_normedSpace fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableOn_const _
  · exact hA _ _

theorem lam_polyGrowth_of_coisotropic : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), DifferentiableOn ℂ lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → (∀ w ∈ W, ∃ C : ℝ, ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → ‖∑ j, (w j : ℂ) • lam s j‖ ≤ C) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a g r lam M W hd hs hW hb
  by_cases hne : (logDom n a).Nonempty
  swap
  · exact ⟨0, 0, fun s hs' => absurd ⟨s, hs'⟩ hne⟩
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨hli0, hsp0, Hm0, hH0, hP0, hM0⟩ := hs s0 hs0
  obtain ⟨hMa, hMd, hr⟩ := GlobalTheory.T.hermForm_periods_alternating_nondeg_rank_eq_two_mul g r (lam s0) M Hm0 hli0 hsp0 hH0 hP0 hM0
  obtain ⟨d, e, f, heW, hee, hfe, hsp⟩ := GlobalTheory.T.exists_lagrangian_dual_pair_in_coisotropic r M W hMa hMd hW
  obtain ⟨hli, hrd⟩ := GlobalTheory.T.isotropicDual_family_linearIndependent_rank_eq_two_mul r d M e f hee hfe hsp
  obtain rfl : d = g := by omega
  obtain ⟨E, hE⟩ : ∃ E : (Fin n → ℂ) → Fin d → Fin d → ℂ, E = fun s i => ∑ m, (e i m : ℂ) • lam s m := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : (Fin n → ℂ) → Fin d → Fin d → ℂ, F = fun s j => ∑ m, (f j m : ℂ) • lam s m := ⟨_, rfl⟩
  obtain ⟨Em, hEm⟩ : ∃ Em : (Fin n → ℂ) → Matrix (Fin d) (Fin d) ℂ, Em = fun s => Matrix.of fun k i => E s i k :=
    ⟨_, rfl⟩
  obtain ⟨Fm, hFm⟩ : ∃ Fm : (Fin n → ℂ) → Matrix (Fin d) (Fin d) ℂ, Fm = fun s => Matrix.of fun k j => F s j k :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : (Fin n → ℂ) → Fin d → Fin d → ℂ, τ = fun s i j => ((Em s)⁻¹ * Fm s) i j := ⟨_, rfl⟩
  have hlinE : LinearIndependent ℝ e := hli.comp Sum.inl Sum.inl_injective

  have hpt : ∀ s ∈ logDom n a, (Em s).det ≠ 0 ∧ (∀ j, F s j = ∑ i, τ s i j • E s i) ∧
      (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) ∧
      ∀ i j, τ s i j - τ s j i = ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ) := by
    intro s hs'
    obtain ⟨hli1, -, Hm, hH, hP, hMs⟩ := hs s hs'
    have h6 := GlobalTheory.T.hermForm_im_real_combination_eq_dotProduct d r (lam s) M Hm hMs
    have hEE : ∀ i j, (hermForm Hm (E s i) (E s j)).im = 0 := fun i j => by
      rw [hE]; exact (h6 _ _).trans (hee i j)
    have hFE : ∀ i j, (hermForm Hm (F s i) (E s j)).im = if i = j then 1 else 0 := fun i j => by
      rw [hE, hF]; exact (h6 _ _).trans (hfe i j)
    have hFF : ∀ i j, (hermForm Hm (F s i) (F s j)).im = f i ⬝ᵥ M *ᵥ f j := fun i j => by
      rw [hF]; exact h6 _ _
    have hEli : LinearIndependent ℝ (E s) := by
      rw [hE]; exact GlobalTheory.T.linearIndependent_real_combinations_of_independent d r d (lam s) e hli1 hlinE
    have hdet : (Em s).det ≠ 0 := by rw [hEm]; exact GlobalTheory.T.det_ne_zero_of_real_independent_isotropic_hermitian d Hm (E s) hP hEli hEE
    have hFt : ∀ j, F s j = ∑ i, τ s i j • E s i := by
      intro j
      have hm := Matrix.mul_nonsing_inv_cancel_left (Em s) (Fm s) (Ne.isUnit hdet)
      funext k
      have := congrFun (congrFun hm k) j
      have hEmk : ∀ k i, Em s k i = E s i k := fun k i => by simp [hEm]
      have hFmk : ∀ k i, Fm s k i = F s i k := fun k i => by simp [hFm]
      rw [Matrix.mul_apply] at this
      simp only [hEmk, hFmk] at this
      rw [hτ]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    obtain ⟨h4a, h4b⟩ := GlobalTheory.T.riemann_relations_period_matrix_hermitian d d Hm (E s) (F s) (τ s) hH hP hFt hEE hFE
    exact ⟨hdet, hFt, h4a, fun i j => (h4b i j).trans (by rw [hFF])⟩

  have hlam : ∀ m k, DifferentiableOn ℂ (fun s => lam s m k) (logDom n a) := fun m k =>
    differentiableOn_pi.1 (differentiableOn_pi.1 hd m) k
  have hEmd : ∀ k i, DifferentiableOn ℂ (fun s => Em s k i) (logDom n a) := fun k i => by
    simp only [hEm, hE, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun m _ => (hlam m k).const_mul _
  have hFmd : ∀ k i, DifferentiableOn ℂ (fun s => Fm s k i) (logDom n a) := fun k i => by
    simp only [hFm, hF, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun m _ => (hlam m k).const_mul _
  have hτd : DifferentiableOn ℂ τ (logDom n a) := by
    refine differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => ?_
    simp only [hτ, Matrix.mul_apply]
    exact DifferentiableOn.fun_sum fun l _ =>
      (differentiableOn_matrix_inv_apply_of_entries hEmd (fun s hs' => (hpt s hs').1) i l).mul (hFmd l j)
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.periodMatrix_polynomialGrowth_puncturedPolydisc n a d τ (fun i j => ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ)) hτd (fun s hs' => (hpt s hs').2.2.1)
    (fun s hs' => (hpt s hs').2.2.2)
  set R : Set (Fin n → ℂ) := {s | s ∈ logDom n a ∧ ‖logExp a s‖ ≤ 1 / 2 ∧
    ∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi} with hR
  have hEb : ∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C := fun i => by
    obtain ⟨C, hC⟩ := hb (e i) (heW i)
    exact ⟨C, fun s hs' => by rw [hE]; exact hC s hs'.1 hs'.2.1⟩
  have h9 := GlobalTheory.T.polynomial_growth_matrix_mul_bounded_vectors n d d R τ E ⟨C, k, fun s hs' => hC s hs'.1 hs'.2.1 hs'.2.2⟩ hEb
  obtain ⟨C', k', h8⟩ := GlobalTheory.T.polynomial_growth_of_spanning_combinations n d r (Fin d ⊕ Fin d) R lam (Sum.elim e f) hsp (fun i => by
    rcases i with i | j
    · obtain ⟨C, hC⟩ := hEb i
      exact ⟨C, 0, fun s hs' => by simpa [hE] using hC s hs'⟩
    · obtain ⟨C, k, hC⟩ := h9 j
      refine ⟨C, k, fun s hs' => ?_⟩
      have := (hpt s hs'.1).2.1 j
      simp only [hF] at this
      simp only [Sum.elim_inr]
      rw [this]
      exact hC s hs')
  exact ⟨C', k', fun s hs' h1 h2 => h8 s ⟨hs', h1, h2⟩⟩

end GlobalTheory.ShFam.Hor.LogCh.PerGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationLineBundleUnifIso
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SquareOfGeneric

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CechPic

section Pt

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem pull_one_eq_zero (L : RigLB G) {T : Over S} :
    pull (1 : T ⟶ G).left (cls L.L L.isLB) = 0 := by
  have a := (cls_eq_zero_iff (pull_isLB L.isLB (eSec G))).2 ⟨L.rig, L.rigGen⟩
  rw [cls_pull L.isLB] at a
  rw [Hom.one_def, Over.comp_left, pull_comp]
  change pull _ (pull (eSec G) _) = 0
  rw [a, map_zero]

theorem pull_inv (L : RigLB G) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]))
    (hs : s.IsGen) {T : Over S} (x : T ⟶ G) :
    pull x⁻¹.left (cls L.L L.isLB) = pull x.left (cls L.L L.isLB) := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb L.isLB _ _)).2 ⟨s, hs⟩
  rw [cls_linComb L.isLB, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pull_id, one_smul, neg_smul] at e
  have e' : pull (ι[G]).left (cls L.L L.isLB) = cls L.L L.isLB := by
    rw [← sub_eq_zero, sub_eq_add_neg]; exact e
  rw [Hom.inv_def, Over.comp_left, pull_comp, e']

theorem lam_self [IsCommMonObj G] (L : RigLB G) (hΘ : ∃ t : LB.Gen (Theta G L.L), t.IsGen)
    (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : s.IsGen)
    {T : Over S} (x : T ⟶ G) :
    lam (cls L.L L.isLB) x x = 2 • pull x.left (cls L.L L.isLB) := by
  have h := lam_mul_left L.isLB hΘ x⁻¹ x x
  rw [inv_mul_cancel, lam_one_left] at h
  have h2 : lam (cls L.L L.isLB) x⁻¹ x = - pull x⁻¹.left (cls L.L L.isLB) - pull x.left (cls L.L L.isLB) := by
    simp only [lam, inv_mul_cancel, pull_one_eq_zero]; abel
  calc lam (cls L.L L.isLB) x x
      = (lam (cls L.L L.isLB) x⁻¹ x + lam (cls L.L L.isLB) x x) - lam (cls L.L L.isLB) x⁻¹ x := by abel
    _ = 2 • pull x.left (cls L.L L.isLB) := by rw [← h, h2, pull_inv L s hs]; abel

theorem lam_pull_fst {S' : Scheme.{0}} (f : S' ⟶ S) (c : Pic G.left) {T : Over S'}
    (x y : T ⟶ (Over.pullback f).obj G) :
    lam (CechPic.pull (pullback.fst G.hom f) c) x y =
      lam c (pushPt (isGrpPullback_pullback G f).1.w x) (pushPt (isGrpPullback_pullback G f).1.w y) := by
  have h := isGrpPullback_pullback G f
  have e1 : (x * y).left ≫ pullback.fst G.hom f = (pushPt h.1.w x * pushPt h.1.w y).left :=
    congrArg (fun z => z.left) (map_mul (pushHom h T) x y)
  have e0 : (1 : T ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (map_one (pushHom h T))
  simp only [lam, ← pull_comp, e1, e0]
  rfl

end Pt

end GlobalTheory.SquareOfGeneric

namespace GlobalTheory.SquareOfGeneric

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CechPic

theorem diag_lam_eq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
    (U : Unif (maximalIdeal R) D A G) (L : LB ((Over.pullback (jK R)).obj G).left) (hL : L.IsLB)
    (eL : LBIso L (U.LG.L.pull (pullback.fst G.hom (jK R))))
    (h : (abelian₂ ((Over.pullback (jK R)).obj G) L).IsLB) :
    CechPic.pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G))).left
        (cls _ h) = 2 • CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L U.LG.isLB) := by
  have e₁ : cls _ h = lam (cls L hL) (fst _ _) (snd _ _) := cls_cube_two hL _ _ h
  have e₂ : cls L hL = CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L U.LG.isLB) :=
    (cls_eq_iff hL (pull_isLB U.LG.isLB _)).2 eL
  rw [e₁, pull_lam, lift_fst, lift_snd, e₂, lam_pull_fst,
    lam_self U.LG ⟨U.cubG.t, U.cubG.isGen⟩ U.symG U.symG_gen]
  rfl

end GlobalTheory.SquareOfGeneric

open GlobalTheory.CechPic MonoidalCategory CartesianMonoidalCategory MonObj in
theorem GlobalTheory.squares_iso_of_lam_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (L L' : LB ((Over.pullback (jK R)).obj G).left), L.IsLB → L'.IsLB → LBIso L (U.LG.L.pull (pullback.fst G.hom (jK R))) → LBIso L' (U'.LG.L.pull (pullback.fst G.hom (jK R))) → LBIso (abelian₂ ((Over.pullback (jK R)).obj G) L) (abelian₂ ((Over.pullback (jK R)).obj G) L') → LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) := by
  intro R _ _ _ hR G _ _ hG D D' A A' U U' L L' hL hL' eL eL' eΛ
  have hΛ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL' _ _)).2 eΛ
  have key := congrArg (CechPic.pull (lift (𝟙 ((Over.pullback (jK R)).obj G))
    (𝟙 ((Over.pullback (jK R)).obj G))).left) hΛ
  have k₁ := GlobalTheory.SquareOfGeneric.diag_lam_eq R G D A U L hL eL (LB.isLB_linComb hL _ _)
  have k₂ := GlobalTheory.SquareOfGeneric.diag_lam_eq R G D' A' U' L' hL' eL' (LB.isLB_linComb hL' _ _)
  replace key := k₁.symm.trans (key.trans k₂)
  refine GlobalTheory.T.lineBundleIso_of_generic_iso_normal_local_base R hR.1 hR.2.1 G.left G.hom (eSec G) hG.smooth hG.quasiCompact
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected)
    (Over.w η[G]) _ _ (LB.isLB_linComb U'.LG.isLB _ _) (LB.isLB_linComb U.LG.isLB _ _) ?_
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb U'.LG.isLB _ _) _) (pull_isLB (LB.isLB_linComb U.LG.isLB _ _) _)).1 ?_
  rw [cls_pull (LB.isLB_linComb U'.LG.isLB _ _), cls_pull (LB.isLB_linComb U.LG.isLB _ _),
    cls_linComb U'.LG.isLB, cls_linComb U.LG.isLB]
  simp only [Fin.sum_univ_one, pull_id, map_zsmul]
  rw [two_zsmul, two_zsmul, ← two_nsmul, ← two_nsmul]
  exact key.symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyhedralPolarisationFaceCutIsCellStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyhedralPolarisation_face_cut_isCell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X], IsPolyFanOn H.bar ψ X → Dominates H.bar X → ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i)) := by
  first | exact @GlobalTheory.PolFan.FaceCutCell.isCell_comp | exact GlobalTheory.PolFan.FaceCutCell.isCell_comp | (intros; apply GlobalTheory.PolFan.FaceCutCell.isCell_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PuncturedPolydiscSumNegLogEqAndGeLogTwoStatement
section
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (∑ i : Fin a, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp (Fin.castLE ha i)) = (∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) / (2 * Real.pi)) ∧ (0 < a → Real.log 2 ≤ ∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) := by
  first | exact @GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo.tlog_sum_eq_and_log_two_le | exact GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo.tlog_sum_eq_and_log_two_le | (intros; apply GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo.tlog_sum_eq_and_log_two_le <;> assumption)
end

