import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0632
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0654
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0657

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparisonStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_pullback_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (W : ValuationSubring ℂ) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Y : Model Xo c (c.V W).subtype)
    (bV : 𝓞 c.F →+* c.V W), (∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (χZ : Sp R ⟶ Z.X) (χY : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo.XF c), Out.jK R ≫ χZ = y ≫ Z.j → Out.jK R ≫ χY = y ≫ Y.j →
      ∃ (t : SAB H (Sp R)) (m₁ : SABMap t Z.t χZ) (m₂ : SABMap t Y.t χY),
        ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Z.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
          g ≫ m₁.φ = g₁ ≫ Z.m.φ → g₁ ≫ Z.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ → g₁ ≫ Z.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom →
          g ≫ m₂.φ = g₂ ≫ Y.m.φ := by
  first | exact @GlobalTheory.TriplesAlong.main | exact GlobalTheory.TriplesAlong.main | (intros; apply GlobalTheory.TriplesAlong.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Defs

variable {O : Type} [CommRing O] (bar : O → O) (q : ℕ)

def InRCone {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) :
    Prop :=
  ∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ toReal β = ∑ i, c i • toReal (γ i)

def genRank {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) : ℕ :=
  Module.finrank ℤ (Submodule.span ℤ (Set.range γ))

def IsCarrierDim (ψ lab : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
      lab.evalZ β = ((sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
        genRank γ = k} : ℕ) : ℝ)

def IsBaryStage (ψ lab φ : InvFun O) (i : ℕ) : Prop :=
  IsPolyFan bar q φ ∧ Subordinate bar q φ ψ ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ →
      ∃ (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X),
        IsCell bar φ (Fin.append v u) ∧ IsCell bar ψ v ∧ (∀ j, InRCone (Fin.append v u) (γ j)) ∧
        Function.Injective (fun j => lab.evalZ (u j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u j)) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ i) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β → (i : ℝ) < lab.evalZ β) ∧
        ∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0

def IsCentreSet (ψ w : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
      ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) →
        w.evalZ β = 1 → w.evalZ β' = 1 → InRCone γ β → InRCone γ β' → β = β'

def IsFaceCut {X : Type} [AddCommGroup X] {m m' : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) : Prop :=
  (∀ j, 0 ≤ h (γ j)) ∧ ∀ j, h (γ j) = 0 ↔ j ∈ Set.range s

def IsStarOf (ψ w ψ' : InvFun O) : Prop :=
  (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
      (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell bar ψ' γ) ∧
  (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
      ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ →
        ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
          IsCell bar ψ' (Fin.cons β₀ fun j => γ (s j))) ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X), IsCell bar ψ' γ' →
      (∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) ∧ ∀ j, InRCone γ (γ' j)) ∨
      ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
        (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ ∧ β₀ ∈ balForms bar X ∧ (∀ y, 0 ≤ β₀ y y) ∧
        w.evalZ β₀ = 1 ∧ InRCone γ β₀ ∧ IsFaceCut γ s h ∧ 0 < h β₀ ∧
        ∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)

end Defs

section Basic

variable {O : Type} [CommRing O] {bar : O → O} {q : ℕ}

theorem inRCone_self {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (j : Fin m) :
    InRCone γ (γ j) :=
  ⟨Pi.single j 1, fun i => by by_cases h : i = j <;> simp [Pi.single_apply, h], by
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]
    simp⟩

example : InRCone ![mulForm] ((2 : ℤ) • mulForm) ∧ ¬ InRCone ![mulForm] (-mulForm) := by
  refine ⟨⟨![2], fun i => by fin_cases i; norm_num, LinearMap.ext₂ fun a b => by simp⟩, ?_⟩
  rintro ⟨c, hc, h⟩
  have := LinearMap.congr_fun₂ h 1 1
  simp at this
  linarith [hc 0]

example (ψ : InvFun O) : IsCentreSet bar q ψ (zeroFun O) := fun X _ _ _ _ _ =>
  ⟨fun β _ _ => Or.inl (zeroFun_evalZ β), fun β _ _ h => by simp at h, fun _ _ _ β _ _ _ _ _ h => by simp at h⟩

example : IsFaceCut ![mulForm] (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin 1)
    (LinearMap.applyₗ 1 ∘ₗ LinearMap.applyₗ 1) := by
  refine ⟨fun j => by simp, fun j => ?_⟩
  simp

theorem isBaryStage_start {ψ lab : InvFun O} (hψ : IsPolyFan bar q ψ) {N : ℕ}
    (hN : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N) :
    IsBaryStage bar q ψ lab ψ N := by
  refine ⟨hψ, Subordinate.refl ψ, fun X _ _ _ _ hX m γ hγ => ?_⟩
  have e : Fin.append γ (Fin.elim0 : Fin 0 → LinearMap.BilinForm ℤ X) = γ := by
    funext i; simp [Fin.append_elim0]
  refine ⟨m, 0, γ, Fin.elim0, by rw [e]; exact hγ, hγ, fun j => by rw [e]; exact inRCone_self γ j,
    fun i => i.elim0, fun i => i.elim0, fun β hβ hp _ => hN X hX β hβ hp, fun β _ _ h h' => (h' (e ▸ h)).elim,
    fun d c _ => funext fun i => i.elim0⟩

example : IsBaryStage id 1 (InvFun.minVal ℤ) (zeroFun ℤ) (InvFun.minVal ℤ) 0 :=
  isBaryStage_start isPolyFan_minVal_one fun _ _ _ _ _ _ β _ _ => by simp

end Basic

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLBLatLBAndTrAdd
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
open GlobalTheory.GradedPieces GlobalTheory.Points GlobalTheory.LieMet

namespace GlobalTheory.LocM.LatGr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B}

theorem tan_of_flagAt {k : Type} [Field k] {x : Sp k ⟶ Z.X} {u : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u) :
    ∀ σ i, IsTanAtG (Y Z.i).t (x ≫ Z.π) (u σ i) := by
  obtain ⟨a, φ, -, hf, -⟩ := h
  exact fun σ i => (hf.1 σ i).1

theorem linInd_of_flagAt {k : Type} [Field k] {x : Sp k ⟶ Z.X} {u : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u)
    (σ : E →+* ℂ) : LinearIndependent k fun i => tanOf (tan_of_flagAt h σ i) := by
  obtain ⟨a, φ, -, hf, -⟩ := id h
  have e : GlobalTheory.DRFlag.up (Dw := Dw) (fun σ i => tanOf (tan_of_flagAt h σ i)) = u :=
    funext fun σ => funext fun i => left_tanOf _
  have hf' : LocM.IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (x ≫ Z.π)
      (GlobalTheory.DRFlag.up (Dw := Dw) (fun σ i => tanOf (tan_of_flagAt h σ i))) := by
    rw [e]
    exact hf
  exact ((GlobalTheory.DRFlag.isFrame_up_iff (φ.comp (Z.alg a)) _).1 hf' σ).1

theorem exists_diag_frames (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {k : Type} [Field k]
    {x : Sp k ⟶ Z.X} {u u' : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u) (h' : Z.FlagAt x u') :
    ∃ d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k, ∀ σ,
      Diag (fun i => tanOf (tan_of_flagAt h' σ i)) (fun i => tanOf (tan_of_flagAt h σ i)) (d σ) := by
  choose d hd using fun σ => exists_diag_of_flagAt Z hty h h' σ (tan_of_flagAt h σ) (tan_of_flagAt h' σ)
    (linInd_of_flagAt h' σ)
  exact ⟨d, hd⟩

theorem diag_ne_zero {k M : Type} [Field k] [AddCommGroup M] [Module k M] {m : ℕ} {p q : Fin m → M}
    {d : Fin m → k} (hd : Diag p q d) (hp : LinearIndependent k p) (hq : LinearIndependent k q) (a : Fin m) :
    d a ≠ 0 := by
  obtain ⟨d', h'⟩ := hd.symm hq
  have e := congrFun ((hd.trans h').unique hp (Diag.refl p)) a
  intro h0
  simp only [h0, mul_zero] at e
  exact zero_ne_one e

variable (hex : ∀ (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ),
  ∃ a : Γ(Z.X, q.U ⊓ q'.U)ˣ, q.IsTr q' e a.val)
include hex

theorem valR_tr (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) {k : Type} [Field k]
    (x : Sp k ⟶ Z.X) {u u' : Vecs Dw (Y Z.i).t k} (hu : q.FrameAt x u) (hu' : q'.FrameAt x u')
    (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k)
    (hd : ∀ σ, Diag (fun i => tanOf (tan_of_flagAt hu'.2.1 σ i)) (fun i => tanOf (tan_of_flagAt hu.2.1 σ i)) (d σ)) :
    valR x _ (q.tr q' e).val = ∏ σ, ∏ i, d σ i ^ e σ i :=
  LatChart.isTr_tr (hex q q' e) k x u u' d hu hu' fun σ => (diagAt_iff _ _ _).2 (hd σ)

theorem valR_res_tr (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) {k : Type} [Field k]
    (x : Sp k ⟶ Z.X) {V : Z.X.Opens} (hV : V ≤ q.U ⊓ q'.U) (h : ⊤ ≤ x ⁻¹ᵁ V) {u u' : Vecs Dw (Y Z.i).t k}
    (hu : q.FrameAt x u) (hu' : q'.FrameAt x u') (d : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → k)
    (hd : ∀ σ, Diag (fun i => tanOf (tan_of_flagAt hu'.2.1 σ i)) (fun i => tanOf (tan_of_flagAt hu.2.1 σ i)) (d σ)) :
    valR x V (res hV (q.tr q' e)).val = ∏ σ, ∏ i, d σ i ^ e σ i :=
  (valR_res x hV h _).trans (valR_tr hex q q' e x hu hu' d hd)

variable (hL : HasLatFlags Z L)
include hL

theorem isLB_latLB (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : (latLB Z L e).IsLB := by
  refine ⟨top_unique fun z _ => Opens.mem_iSup.2 (hL.2 z), fun q => ?_, fun q q' q'' => ?_⟩
  · refine Units.ext (fn_ext Z fun k _ x h ho => ?_)
    obtain ⟨u, hu⟩ := q.exists_frameAt h ho
    refine (valR_res_tr hex q q e x _ h hu hu (fun _ _ => 1) fun σ => Diag.refl _).trans ?_
    simp only [one_zpow, Finset.prod_const_one]
    exact (valR_one x _ h).symm
  · refine Units.ext (fn_ext Z fun k _ x h ho => (valR_mul x _ h _ _).trans ?_)
    obtain ⟨u, hu⟩ := q.exists_frameAt (le_preimage_mono x (inf_le_left.trans inf_le_left) h) ho
    obtain ⟨u', hu'⟩ := q'.exists_frameAt (le_preimage_mono x (inf_le_left.trans inf_le_right) h) ho
    obtain ⟨u'', hu''⟩ := q''.exists_frameAt (le_preimage_mono x inf_le_right h) ho
    obtain ⟨d₁, hd₁⟩ := exists_diag_frames hL.1 hu.2.1 hu'.2.1
    obtain ⟨d₂, hd₂⟩ := exists_diag_frames hL.1 hu'.2.1 hu''.2.1
    refine (congrArg₂ (· * ·) (valR_res_tr hex q q' e x _ h hu hu' d₁ hd₁)
      (valR_res_tr hex q' q'' e x _ h hu' hu'' d₂ hd₂)).trans
      (.trans ?_ (valR_res_tr hex q q'' e x _ h hu hu'' _ fun σ => (hd₂ σ).trans (hd₁ σ)).symm)
    simp only [mul_zpow, Finset.prod_mul_distrib]

theorem tr_add (q q' : LatChart Z L) (e e' : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) :
    q.tr q' (e + e') = q.tr q' e * q.tr q' e' := by
  refine Units.ext (fn_ext Z fun k _ x h ho => ?_)
  obtain ⟨u, hu⟩ := q.exists_frameAt (le_preimage_mono x inf_le_left h) ho
  obtain ⟨u', hu'⟩ := q'.exists_frameAt (le_preimage_mono x inf_le_right h) ho
  obtain ⟨d, hd⟩ := exists_diag_frames hL.1 hu.2.1 hu'.2.1
  rw [Units.val_mul, valR_mul x _ h, valR_tr hex q q' _ x hu hu' d hd, valR_tr hex q q' e x hu hu' d hd,
    valR_tr hex q q' e' x hu hu' d hd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact zpow_add₀ (diag_ne_zero (hd σ) (linInd_of_flagAt hu'.2.1 σ) (linInd_of_flagAt hu.2.1 σ) i) _ _

end GlobalTheory.LocM.LatGr

open GlobalTheory.LocM.LatGr in

theorem GlobalTheory.LocM.LatGr.isLB_latLB_and_tr_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ),
    p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z B : Mdl Y i₀) (L : Lat B),
    HasLatFlags Z L → (∀ (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ),
      ∃ a : Γ(Z.X, q.U ⊓ q'.U)ˣ, q.IsTr q' e a.val) →
    (∀ e, (latLB Z L e).IsLB) ∧ ∀ (q q' : LatChart Z L) (e e' : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ),
      q.tr q' (e + e') = q.tr q' e * q.tr q' e' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL hex => ⟨fun e => isLB_latLB hex hL e, fun q q' e e' => tr_add hex hL q q' e e'⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisOfClosedBall
section
set_option autoImplicit false

namespace GlobalTheory.LatticeBasisClosedBall

theorem exists_real_coords {g : ℕ} (lam : Fin (2 * g) → Fin g → ℂ) (hli : LinearIndependent ℝ lam)
    (w : Fin g → ℂ) : ∃ c : Fin (2 * g) → ℝ, ∑ j, c j • lam j = w := by
  have hdim : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hspan : Submodule.span ℝ (Set.range lam) = ⊤ := hli.span_eq_top_of_card_eq_finrank' hdim
  have hw : w ∈ Submodule.span ℝ (Set.range lam) := hspan ▸ Submodule.mem_top
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw

theorem isLatBasis_of_closedBall : ∀ {g : ℕ} (H : AddSubgroup (Fin g → ℂ)) (lam : Fin (2 * g) → Fin g → ℂ)
    (R : ℝ), LinearIndependent ℝ lam → (∀ j : Fin (2 * g), lam j ∈ H) → ∑ j : Fin (2 * g), ‖lam j‖ ≤ R →
    (∀ w ∈ Metric.closedBall (0 : Fin g → ℂ) R, w ∈ H →
      ∃ m : Fin (2 * g) → ℤ, w = ∑ j : Fin (2 * g), m j • lam j) →
    GlobalTheory.ShFam.Hor.LogCh.IsLatBasis (↑H : Set (Fin g → ℂ)) lam := by
  intro g H lam R hli hmem hR hball
  have hint : ∀ m : Fin (2 * g) → ℤ, ∑ j, m j • lam j ∈ H := fun m =>
    H.sum_mem fun j _ => H.zsmul_mem (hmem j) (m j)
  refine ⟨hli, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · obtain ⟨c, hc⟩ := exists_real_coords lam hli w
    have hsplit : w - ∑ j, ⌊c j⌋ • lam j = ∑ j, Int.fract (c j) • lam j := by
      rw [← hc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Int.fract, sub_smul, Int.cast_smul_eq_zsmul]
    have hH : w - ∑ j, ⌊c j⌋ • lam j ∈ H := H.sub_mem hw (hint _)
    have hnorm : w - ∑ j, ⌊c j⌋ • lam j ∈ Metric.closedBall (0 : Fin g → ℂ) R := by
      rw [mem_closedBall_zero_iff, hsplit]
      refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_) hR)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    obtain ⟨m, hm⟩ := hball _ hnorm hH
    refine ⟨fun j => m j + ⌊c j⌋, ?_⟩
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← hm, sub_add_cancel]
  · rintro ⟨m, rfl⟩
    exact hint m

end GlobalTheory.LatticeBasisClosedBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPoint
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TraitProper

open GlobalTheory.ArcProper in

theorem isProper_of_lift_genericPoint : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp R) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f], (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Sp R), Set.range x ⊆ {genericPoint X} → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  intro k _ _ Y _ s _ _ _ H
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hA : ∀ y : Y, ∃ A : Y.Opens, IsAffineOpen A ∧ y ∈ A := fun y ↦ by
    obtain ⟨A, h₁, h₂, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    exact ⟨A, h₁, h₂⟩
  choose A₀ hA₀ hyA using hA
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set Y))
    (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)
  let A : T → Y.Opens := fun i ↦ A₀ i
  have hcov : ∀ y : Y, ∃ i : T, y ∈ A i := fun y ↦ by
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h⟩
  have hP := fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i
    exists_isOpenImmersion_isProper ((A i).ι ≫ s))
  choose P t j ht hj hjt using hP
  let U : Y.Opens := Finset.univ.inf A
  have hUA : ∀ i, U ≤ A i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  have hU : genericPoint Y ∈ U := by
    have : ∀ i, genericPoint Y ∈ A i := fun i ↦
      ((genericPoint_spec Y).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩
    refine Finset.inf_induction (p := fun V : Y.Opens ↦ genericPoint Y ∈ V) trivial
      (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i
  have : Nonempty U.toScheme := ⟨⟨_, hU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨Q, q, ψ, _, hψ, hp⟩ := exists_isProper_factor P t ht (U.ι ≫ s)
    (fun i ↦ Y.homOfLE (hUA i) ≫ j i) (fun i ↦ by rw [Category.assoc, hjt, Y.homOfLE_ι_assoc])
    Finset.univ
  choose p hpt hψp using fun i ↦ hp i (Finset.mem_univ i)
  obtain ⟨i₀, -⟩ := hcov (genericPoint Y)
  have : IsImmersion (ψ ≫ p i₀) := by rw [hψp]; infer_instance
  have : IsImmersion ψ := IsImmersion.of_comp ψ (p i₀)
  have : QuasiCompact (ψ ≫ q) := by rw [hψ]; infer_instance
  have : QuasiCompact ψ := QuasiCompact.of_comp ψ q
  have : IsIntegral ψ.image := isIntegral_image ψ
  let z : ψ.image ⟶ Sp k := ψ.imageι ≫ q
  have hz : ψ.toImage ≫ z = U.ι ≫ s := by rw [ψ.toImage_imageι_assoc, hψ]
  have : IsLocallyNoetherian ψ.image := LocallyOfFiniteType.isLocallyNoetherian z
  let V : T → ψ.image.Opens := fun i ↦ (ψ.imageι ≫ p i) ⁻¹ᵁ (j i).opensRange
  let η : U.toScheme := ⟨_, hU⟩
  have hη : ∀ u : U.toScheme, η ⤳ u := fun u ↦
    (U.ι.isEmbedding.isInducing.specializes_iff).1 (genericPoint_specializes (U.ι u))
  have hs : ∀ x : ψ.image, ψ.toImage η ⤳ x := by
    intro x
    rw [specializes_iff_mem_closure]
    refine closure_minimal ?_ isClosed_closure (ψ.toImage.denseRange x)
    rintro _ ⟨u, rfl⟩
    exact specializes_iff_mem_closure.1 ((hη u).map ψ.toImage.continuous)
  have key : ∀ x : ψ.image, ∃ i, x ∈ V i := by
    intro x
    by_cases hne : ψ.toImage η = x
    · refine ⟨i₀, Y.homOfLE (hUA i₀) η, ?_⟩
      rw [← hne, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ψ.toImage_imageι_assoc, hψp]
    obtain ⟨O, _, _, _, c, hc₀, hcx⟩ :=
      exists_complete_discreteValuationRing_of_specializes (hs x) hne
    have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
    have : IsDominant (spMap (algebraMap O (FractionRing O))) := by
      refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
      exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
    have hpt' : (spMap (algebraMap O (FractionRing O)) ≫ c)
        (IsLocalRing.closedPoint (FractionRing O)) = ψ.toImage η := by
      refine Eq.trans (congrArg c (PrimeSpectrum.ext ?_)) hc₀
      change Ideal.comap (algebraMap O (FractionRing O)) (IsLocalRing.maximalIdeal _) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ hinj
    obtain ⟨l, hl, hlη⟩ := ValuativeGeneric.exists_lift_of_surjectiveOnStalks ψ.toImage
      (FractionRing O) _ η hpt'
    have hls : (l ≫ U.ι) ≫ s = spMap (algebraMap O (FractionRing O)) ≫ c ≫ z := by
      rw [Category.assoc, ← hz, reassoc_of% hl]
    obtain ⟨b, hb⟩ := H O (FractionRing O) (l ≫ U.ι) (c ≫ z) (by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Hom.comp_apply, hlη]
      rfl) hls
    have hbs : b ≫ s = c ≫ z := by
      refine ext_of_isDominant (spMap (algebraMap O (FractionRing O))) ?_
      rw [← Category.assoc, hb, hls]
    obtain ⟨i, hi⟩ := hcov (b (IsLocalRing.closedPoint O))
    have hr : Set.range b ⊆ Set.range (A i).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨v, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint v).map b.continuous).mem_open (A i).isOpen hi
    obtain ⟨b', hb'⟩ : ∃ b', b' ≫ (A i).ι = b := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
    have e : b' ≫ j i = c ≫ ψ.imageι ≫ p i := by
      refine ext_of_isDominant_of_isSeparated (t i) ?_
        (spMap (algebraMap O (FractionRing O))) ?_
      · rw [Category.assoc, hjt, reassoc_of% hb', hbs, Category.assoc, Category.assoc, hpt]
      · rw [← reassoc_of% hl, ψ.toImage_imageι_assoc, hψp, ← Category.assoc, ← Category.assoc]
        congr 1
        rw [← cancel_mono (A i).ι, Category.assoc, hb', hb, Category.assoc, Y.homOfLE_ι]
    refine ⟨i, b' (IsLocalRing.closedPoint O), ?_⟩
    have e' : (b' ≫ j i) (IsLocalRing.closedPoint O) =
        (c ≫ ψ.imageι ≫ p i) (IsLocalRing.closedPoint O) := by rw [e]
    exact e'.trans (congrArg (ψ.imageι ≫ p i) hcx)
  have hV : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 (key x)
  have hm : ∀ i, ∃ m : (V i).toScheme ⟶ A i, m ≫ j i = (V i).ι ≫ ψ.imageι ≫ p i := fun i ↦
    ⟨_, IsOpenImmersion.lift_fac (j i) _ (by rintro _ ⟨v, rfl⟩; exact v.2)⟩
  choose m hm using hm
  obtain ⟨g, hg, hgU⟩ := exists_extension_of_cover z s ψ.toImage U.ι V hV
    (fun i ↦ m i ≫ (A i).ι)
    (fun i ↦ by rw [Category.assoc, ← hjt, reassoc_of% hm, hpt])
    (fun i T a b e ↦ by
      rw [← Y.homOfLE_ι (hUA i), ← Category.assoc, ← Category.assoc]
      congr 1
      rw [← cancel_mono (j i), Category.assoc, hm, ← reassoc_of% e, ψ.toImage_imageι_assoc, hψp,
        Category.assoc])
  have : IsProper (g ≫ s) := by rw [hg]; infer_instance
  have : IsProper g := IsProper.of_comp g s
  have : IsDominant g := ⟨(U.isOpen.dense ⟨_, hU⟩).mono (by rwa [Scheme.Opens.range_ι] at hgU)⟩
  have : Surjective g := surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range
  have : UniversallyClosed s := .of_comp_surjective g s
  exact {}

end GlobalTheory.TraitProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc

namespace GlobalTheory.SiegLoc

def SiegData (g : ℕ) (φ : InvFun ℤ) (n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n))
    (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S)
    (d N : ℕ) : Prop :=
  IsProjOver s ∧ SmoothOfRelativeDimension (g * (g + 1) / 2) s ∧ j ≫ s = F.s ∧
    (∀ x : S, x ∈ closure (Set.range j ∩ s ⁻¹' {s x})) ∧
    IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j ∧
    1 ≤ d ∧ (∀ x : S, HasChart F s j e φ BD d x) ∧
    1 ≤ N ∧ IsGenerated (lbPow (hodge G g) N) ∧
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → IsAmpleLB (CechPic.tens (lbPow (hodge G g) (N * k)) (CechPic.dual BD.lb))

theorem siegAt_iff (g : ℕ) (φ : InvFun ℤ) (n : ℕ) :
    SiegAt g φ n ↔ ∃ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S)
      (_ : IsOpenImmersion j) (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left) (BD : EffCartierData S) (d N : ℕ),
      SiegData g φ n F S s j G e BD d N := Iff.rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def IsSiegPull {g n : ℕ} {F : SFam g n (zetaAway n)} {S : Scheme.{0}} (s : S ⟶ Sp (cycAway n)) (j : F.X ⟶ S)
    (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) {Xo : Moduli D l} {c : Coeff l} {R : Type} [CommRing R]
    {ω : R →+* c.F} (κ : cycAway n →+* R) (C : Model Xo c ω) (π : C.X ⟶ S) : Prop :=
  ∃ (μ : C.t.G.left ⟶ G.left) (y : Xo.XF c ⟶ F.X) (α : C.oF.t.G.left ⟶ F.univ.A.left)
    (α₂ : (G2 C.oF.t.G).left ⟶ (G2 F.univ.A).left),
    IsFinite π ∧ π ≫ s = C.s ≫ spMap κ ∧ IsGrpPullback C.t.G G π μ ∧
    y ≫ j = C.j ≫ π ∧ IsGrpPullback C.oF.t.G F.univ.A y α ∧ IsSquare α α₂ ∧
    LBIso (abelian₂ C.oF.t.G C.oF.t.PP.L) (F.univ.P.pull α₂) ∧ C.m.φ ≫ μ = α ≫ e

end GlobalTheory.SiegLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearOnIsFineOfLinearOnPolarisationBaseFunctionStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearOn_isFine_of_linearOn_polarisationBaseFunction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], 0 < D → IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), (∀ i, γ i ∈ balForms H.bar X) → (∀ i y, 0 ≤ γ i y y) → (baseFun (𝓞 E) D φs 𝓜).LinearOn γ → (restr (𝓞 E) φs).LinearOn γ ∧ ∀ M ∈ 𝓜, IsFine (M + 1) γ := by
  first | exact @GlobalTheory.PolFan.linearOn_and_isFine_of_linearOn_baseFun | exact GlobalTheory.PolFan.linearOn_and_isFine_of_linearOn_baseFun | (intros; apply GlobalTheory.PolFan.linearOn_and_isFine_of_linearOn_baseFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetryStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_conjugation_symmetry : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ σ' : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ) (p : Pts (Φ.C k).Y σ) (p' : Pts (Φ.C k).Y σ') (a : (Φ.C k).Y.Fnˣ), p'.1 = spMap (starRingEnd ℂ) ≫ p.1 → p ∈ Var.eqnSet σ (divOf (Φ.C k) n) a → (∀ R, Var.Met.h (metsOf x Φ k R σ' n) a p' = Var.Met.h (metsOf x Φ k R σ n) a p) ∧ Var.Met.h (refMet x Φ k σ' n) a p' = Var.Met.h (refMet x Φ k σ n) a p ∧ rFlag x Φ k σ' p' = rFlag x Φ k σ p := by
  first | exact @GlobalTheory.ShFam.mets_conj | exact GlobalTheory.ShFam.mets_conj | (intros; apply GlobalTheory.ShFam.mets_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisationBaseFunctionPropertiesStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationBaseFunction_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → (∀ B ∈ psdCone H.bar X, ∀ t : ℝ, 0 ≤ t → evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (t • B) = t * evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B) ∧ (∀ B ∈ psdCone H.bar X, ∀ B' ∈ psdCone H.bar X, evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B + evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) B' ≤ evalR (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) (B + B')) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β = n) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜).evalZ β) := by
  first | exact @GlobalTheory.PolFan.baseFun_props | exact GlobalTheory.PolFan.baseFun_props | (intros; apply GlobalTheory.PolFan.baseFun_props <;> assumption)
end

