import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsChartLoc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtensionComplexPointsEqCharacters
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

namespace GlobalTheory.ConstTan

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

@[simp] theorem fst_dualMapR (φ : R →+* R') (a : DualNumber R) : (dualMapR φ a).fst = φ a.fst := by
  simp [dualMapR]

@[simp] theorem snd_dualMapR (φ : R →+* R') (a : DualNumber R) : (dualMapR φ a).snd = φ a.snd := by
  simp [dualMapR]

theorem dualMapR_inl (φ : R →+* R') (a : R) : dualMapR φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a) := by
  ext <;> simp

theorem dualMapR_eps (φ : R →+* R') : dualMapR φ DualNumber.eps = DualNumber.eps := by
  ext <;> simp

theorem eq_dualMapR (φ : R →+* R') (ρ : DualNumber R →+* DualNumber R')
    (h : ∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (φ r)) (he : ρ DualNumber.eps = DualNumber.eps) :
    ρ = dualMapR φ := RingHom.ext fun a => by
  have e : a = TrivSqZeroExt.inl a.fst + TrivSqZeroExt.inl a.snd * DualNumber.eps := by ext <;> simp
  rw [e, map_add, map_add, map_mul, map_mul, h, h, he, dualMapR_inl, dualMapR_inl, dualMapR_eps]

theorem isLocalRing_dual (R : Type) [CommRing R] [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

end Dual

abbrev idealEps : Ideal (DualNumber ℂ⟦X⟧) :=
  (Ideal.span {(PowerSeries.X : ℂ⟦X⟧)}).map (algebraMap ℂ⟦X⟧ (DualNumber ℂ⟦X⟧))

theorem isAdicComplete_idealEps : IsAdicComplete idealEps (DualNumber ℂ⟦X⟧) :=
  have : Module.Finite ℂ⟦X⟧ (DualNumber ℂ⟦X⟧) := inferInstanceAs (Module.Finite ℂ⟦X⟧ (ℂ⟦X⟧ × ℂ⟦X⟧))
  isAdicComplete_map_of_finite _ (DualNumber ℂ⟦X⟧)

abbrev constEps : DualNumber ℂ →+* DualNumber ℂ⟦X⟧ := dualMapR (PowerSeries.C (R := ℂ))

section Jet

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def jet (F : V → ℂ) (z : V) : DualNumber ℂ := TrivSqZeroExt.inl (F 0) + TrivSqZeroExt.inr (fderiv ℂ F 0 z)

@[simp] theorem fst_jet (F : V → ℂ) (z : V) : (jet F z).fst = F 0 := by simp [jet]

@[simp] theorem snd_jet (F : V → ℂ) (z : V) : (jet F z).snd = fderiv ℂ F 0 z := by simp [jet]

theorem jet_mul {F G : V → ℂ} (hF : DifferentiableAt ℂ F 0) (hG : DifferentiableAt ℂ G 0) (z : V) :
    jet (fun v => F v * G v) z = jet F z * jet G z := by
  ext
  · simp
  · rw [snd_jet, fderiv_fun_mul hF hG]
    simp [TrivSqZeroExt.snd_mul, _root_.mul_comm]

theorem jet_pow {F : V → ℂ} (hF : DifferentiableAt ℂ F 0) (z : V) (n : ℕ) :
    jet (fun v => F v ^ n) z = jet F z ^ n := by
  induction n with
  | zero => ext <;> simp
  | succ n ih => rw [pow_succ, ← ih, ← jet_mul (hF.fun_pow n) hF]; simp only [pow_succ]

theorem jet_congr {F G : V → ℂ} (h : F =ᶠ[nhds 0] G) (z : V) : jet F z = jet G z := by
  rw [jet, jet, h.eq_of_nhds, h.fderiv_eq]

def IsJet (x : V → ℂ⟦X⟧) (z : V) (y : DualNumber ℂ⟦X⟧) : Prop :=
  (∀ n, DifferentiableAt ℂ (fun v => PowerSeries.coeff n (x v)) 0) ∧ y.fst = x 0 ∧
    ∀ n, PowerSeries.coeff n y.snd = fderiv ℂ (fun v => PowerSeries.coeff n (x v)) 0 z

variable {z : V}

theorem isJet_zero (z : V) : IsJet (fun _ => 0) z 0 := ⟨fun n => by simp, rfl, fun n => by simp⟩

theorem IsJet.add {x x' : V → ℂ⟦X⟧} {y y' : DualNumber ℂ⟦X⟧} (h : IsJet x z y) (h' : IsJet x' z y') :
    IsJet (fun v => x v + x' v) z (y + y') := by
  refine ⟨fun n => ?_, by simp [h.2.1, h'.2.1], fun n => ?_⟩
  · simp only [map_add]
    exact (h.1 n).fun_add (h'.1 n)
  · simp only [map_add, TrivSqZeroExt.snd_add]
    rw [fderiv_fun_add (h.1 n) (h'.1 n), h.2.2, h'.2.2, ContinuousLinearMap.add_apply]

theorem IsJet.sum {K : Type} (s : Finset K) {x : K → V → ℂ⟦X⟧} {y : K → DualNumber ℂ⟦X⟧}
    (h : ∀ i ∈ s, IsJet (x i) z (y i)) : IsJet (fun v => ∑ i ∈ s, x i v) z (∑ i ∈ s, y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isJet_zero z
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsJet.const_mul {x : V → ℂ⟦X⟧} {y : DualNumber ℂ⟦X⟧} (h : IsJet x z y) (r : ℂ⟦X⟧) :
    IsJet (fun v => r * x v) z (TrivSqZeroExt.inl r * y) := by
  refine ⟨fun n => ?_, by simp [h.2.1], fun n => ?_⟩
  · simp only [PowerSeries.coeff_mul]
    exact DifferentiableAt.fun_sum fun p _ => (h.1 _).const_mul _
  · have e : (TrivSqZeroExt.inl r * y : DualNumber ℂ⟦X⟧).snd = r * y.snd := by simp [TrivSqZeroExt.snd_mul]
    simp only [e, PowerSeries.coeff_mul]
    rw [fderiv_fun_sum fun p _ => (h.1 _).const_mul _, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [fderiv_const_mul (h.1 _), h.2.2]
    rfl

theorem isJet_C {F : V → ℂ} (hF : DifferentiableAt ℂ F 0) (z : V) :
    IsJet (fun v => PowerSeries.C (F v)) z (constEps (jet F z)) := by
  refine ⟨fun n => ?_, by simp, fun n => ?_⟩
  · by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn, hF]
  · by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

theorem mem_idealEps_pow {a : DualNumber ℂ⟦X⟧} {n : ℕ} (h : a ∈ idealEps ^ n) :
    PowerSeries.X ^ n ∣ a.fst ∧ PowerSeries.X ^ n ∣ a.snd := by
  rw [idealEps, ← Ideal.map_pow, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton] at h
  obtain ⟨c, rfl⟩ := h
  exact ⟨⟨c.fst, by simp [TrivSqZeroExt.algebraMap_eq_inl]⟩, ⟨c.snd, by
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_mul]; simp⟩⟩

theorem isJet_of_approx {x : V → ℂ⟦X⟧} {y : DualNumber ℂ⟦X⟧}
    (h : ∀ e : ℕ, ∃ x' y', IsJet x' z y' ∧ (∀ v, PowerSeries.X ^ (e + 1) ∣ x v - x' v) ∧ y - y' ∈ idealEps ^ (e + 1)) :
    IsJet x z y := by
  have key : ∀ (n : ℕ) (a b : ℂ⟦X⟧), PowerSeries.X ^ (n + 1) ∣ a - b →
      PowerSeries.coeff n a = PowerSeries.coeff n b := fun n a b hab => by
    have := PowerSeries.X_pow_dvd_iff.1 hab n (Nat.lt_succ_self n)
    rwa [map_sub, sub_eq_zero] at this
  refine ⟨fun n => ?_, PowerSeries.ext fun n => ?_, fun n => ?_⟩
  · obtain ⟨x', y', h₁, h₂, -⟩ := h n
    simp only [fun v => key n _ _ (h₂ v)]
    exact h₁.1 n
  · obtain ⟨x', y', h₁, h₂, h₃⟩ := h n
    rw [key n _ _ (h₂ 0), ← h₁.2.1]
    exact key n _ _ (by simpa using (mem_idealEps_pow h₃).1)
  · obtain ⟨x', y', h₁, h₂, h₃⟩ := h n
    simp only [fun v => key n _ _ (h₂ v)]
    rw [← h₁.2.2]
    exact key n _ _ (by simpa using (mem_idealEps_pow h₃).2)

theorem IsJet.dualMapR_eq {x : V → ℂ⟦X⟧} {y : DualNumber ℂ⟦X⟧} (h : IsJet x z y) (m : ℤ) (f : V → ℂ⸨X⸩)
    (hf : ∀ v, algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (x v) = HahnSeries.single m (1 : ℂ) * f v) (F : ℂ⸨X⸩)
    (hF : ∀ n, F.coeff n = fderiv ℂ (fun v => (f v).coeff n) 0 z) :
    dualMapR (algebraMap ℂ⟦X⟧ ℂ⸨X⸩) y = TrivSqZeroExt.inl (HahnSeries.single m (1 : ℂ)) *
      (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr F) := by
  have c : ∀ (g : ℂ⸨X⸩) (n : ℤ), (HahnSeries.single m (1 : ℂ) * g).coeff (n + m) = g.coeff n := fun g n => by
    rw [HahnSeries.coeff_single_mul_add, _root_.one_mul]
  refine TrivSqZeroExt.ext (by simp [h.2.1, hf]) ?_
  have e : (TrivSqZeroExt.inl (HahnSeries.single m (1 : ℂ)) *
      (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr F) : DualNumber ℂ⸨X⸩).snd = HahnSeries.single m (1 : ℂ) * F := by
    simp [TrivSqZeroExt.snd_mul]
  rw [e, snd_dualMapR]
  ext k
  obtain ⟨n, rfl⟩ : ∃ n, k = n + m := ⟨k - m, by ring⟩
  rw [c, hF]
  simp only [fun v => (c (f v) n).symm.trans (congrArg (fun q : ℂ⸨X⸩ => q.coeff (n + m)) (hf v).symm)]
  generalize n + m = k
  rw [LaurentSeries.coe_algebraMap]
  simp only [PowerSeries.coeff_coe]
  by_cases hk : k < 0
  · simp [hk]
  · simp only [if_neg hk]
    exact h.2.2 _

end Jet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
variable [Algebra (FractionRing ℂ) ℂ] {Y : Model Xo c β} {b : O →+* ℂ} {a : ArcIn D l β ℂ b} {χ : Sp ℂ⟦X⟧ ⟶ Y.X}

def TanRel (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ)
    (ν : Out.GtPt a.D₀ (epsR ℂ)) (g : Out.GtPt W.P.D.toPre (epsR ℂ⟦X⟧)) : Prop :=
  ∀ x, GenRelR (A := DualNumber ℂ⟦X⟧) W.w (g.s (W.e x)) (LB.pullGen _ _ _ (ν.s x) (spMap constEps))

def IsConstMul (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (j : ℕ)
    (x : a.D₀.X) (s₀ : a.D₀.SecB j x) (f : W.P.D.toPre.SecB j (W.e x)) (r : ℂ⟦X⟧) : Prop :=
  ∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (p : Sp Z ⟶ W.P.D.toPre.P.A.left) (κ : ℂ⟦X⟧ →+* Z)
    (jf : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : Fin 4 → a.D₀.P.L.ι), p ≫ W.P.D.toPre.P.A.hom = spMap κ →
    (∀ i, ⊤ ≤ (p ≫ W.P.D.toPre.famφB (W.e x) i) ⁻¹ᵁ
      (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
    ∃ u : Fin 4 → Zˣ, (∀ i, (u i : Z) =
        valR (p ≫ W.P.D.toPre.famφB (W.e x) i) _ (W.w.s (fun _ => j₀ i, jf i)).val) ∧
      (∏ i, u i ^ Out.DegPre.famε j i : Zˣ) *
          valR p (LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB (W.e x)) jf) (f.f jf) =
        κ r * valR (p ≫ W.φ) (LB.wchart a.D₀.P.L (a.D₀.famφB x) j₀) (s₀.f j₀)

def HasConstExp (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) {j : ℕ}
    (σ : Out.H0 W.P.U.LG.L j) : Prop :=
  ∃ f : ∀ y, W.P.D.toPre.SecB j y, (∀ e, W.P.U.toUnifPre.ExpandsAt e j σ f) ∧
    ∀ x : a.D₀.X, ∃ s₀ r, IsConstMul W j x s₀ (f (W.e x)) r

end GlobalTheory.ConstTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecValEqMulSvalSig
section
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace SecTransport

variable {X Z : Scheme.{0}}

abbrev valH {L : LB X} {m : ℕ} (σ : Out.H0 L m) {R : Type} [CommRing R] (x : Sp R ⟶ X) (i : L.ι) : R :=
  valR x (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i)) (σ.f (fun _ => i))

theorem exists_pull {L L' : LB X} (h : L = L') (hL : L'.IsLB) {m : ℕ} (σ : Out.H0 L m) (π : Z ⟶ X) :
    ∃ s : SecP L' π m,
      (∀ (R : Type) [CommRing R] (p : Sp R ⟶ Z) (x : Sp R ⟶ X) (i : L.ι) (i' : L'.ι), p ≫ π = x → HEq i i' →
        ⊤ ≤ x ⁻¹ᵁ L'.U i' → ArcPts.sval s p i' = valH σ x i) ∧
      ∀ (A K : Type) [CommRing A] [IsLocalRing A] [Field K] (ρ : A →+* K) (x : Sp A ⟶ X) (p : Sp K ⟶ Z)
        (τ : L.ι → A) (τ' : L'.ι → K) (f : K), p ≫ π = spMap ρ ≫ x → IsFrm L' (p ≫ π) τ' →
        (∀ i i', HEq i i' → ⊤ ≤ x ⁻¹ᵁ L.U i → τ' i' = ρ (τ i)) →
        (∀ i, ⊤ ≤ x ⁻¹ᵁ L.U i → ρ (valH σ x i) = f * ρ (τ i) ^ m) → HasVal s p τ' f := by
  subst h
  have ex : ∀ π' : Z ⟶ X, π' = π ≫ 𝟙 X → ∃ s : SecP L π' m, ∀ (R : Type) [CommRing R] (p : Sp R ⟶ Z) (x : Sp R ⟶ X)
      (i : L.ι), p ≫ π = x → ⊤ ≤ x ⁻¹ᵁ L.U i → ArcPts.sval s p i = valH σ x i := by
    rintro _ rfl
    refine ⟨DVR.pullSec L (fun _ : Fin 1 => 𝟙 X) (fun _ => (m : ℤ)) σ π, fun R _ p x i hx hi => ?_⟩
    subst hx
    exact (HolHom.valR_res p _ _ (GenericPoints.le_wchart hi)).trans (HolHom.valR_comp p π _ _).symm
  obtain ⟨s, hs⟩ := ex π (Category.comp_id _).symm
  refine ⟨s, fun R _ p x i i' hx hi hi' => ?_, fun A K _ _ _ ρ x p τ τ' f hp hτ h₁ h₂ => ?_⟩
  · obtain rfl := eq_of_heq hi
    exact hs R p x i hx hi'
  · obtain ⟨i, hi⟩ := GenericPoints.exists_chart_loc hL x
    have hi' := FormalValue.top_le_comp hi (spMap ρ)
    refine GenericPoints.hasVal_of_chart s p hτ (j := i) (hp ▸ hi') ?_
    rw [hs K p _ i hp hi', h₁ i i HEq.rfl hi, ← h₂ i hi]
    exact HolHom.valR_spMap ρ x (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i))
      (fun _ hz => Set.mem_iInter.2 fun _ => hi hz) _

end SecTransport

theorem secVal_eq_mul_sval_sig : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (Φ : GenPts Λ.A W.t gen) (j : ℕ) [NeZero j] (α : Λ.A.X) (th : (Fin Λ.A.gB → ℂ) → ℂ) (r : ℂ⸨X⸩) (σ : Out.H0 W.P.U.LG.L j), Ξ.IsGen Φ → th ∈ Λ.A.Theta j α → Ξ.Vals σ (fun v => r * Λ.A.FSum j α th v) → ∀ (q : Over.mk gen ⟶ W.t.G) (jL : W.P.U.LG.L.ι) (i : W.t.PP.L.ι), HEq jL i → ⊤ ≤ q.left ⁻¹ᵁ W.t.PP.L.U i → FormalValue.secVal (S := ℂ⸨X⸩) W.P.U.toUnifPre σ q.left jL = r * sval (Φ.sig j α th) (fib q) i := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ Φ j _ α th r σ hgen hth hval q jL i hi hq
  obtain ⟨s, hs₁, hs₂⟩ := SecTransport.exists_pull (congrArg RigLB.L W.P.bundle) W.t.PP.isLB σ
    (pullback.fst W.t.G.hom gen)
  have hfib : ∀ p : Over.mk gen ⟶ W.t.G, fib p ≫ pullback.fst W.t.G.hom gen = p.left := fun p =>
    pullback.lift_fst _ _ _
  have hv : ∀ v, HasVal s (fib (Φ.x v)) (Φ.τ v) (r * Λ.A.FSum j α th v) := fun v =>
    hs₂ ℂ⟦X⟧ ℂ⸨X⸩ (algebraMap _ _) (Ξ.x v).left (fib (Φ.x v)) (Ξ.τ v) (Φ.τ v) _ ((hfib _).trans (hgen v).1)
      (by rw [hfib]; exact Φ.frm v) (hgen v).2 (hval v)
  have hq₂ : fib q ≫ pullback.snd W.t.G.hom gen = spMap (RingHom.id _) := by
    rw [fib, pullback.lift_snd]
    exact (Spec.map_id _).symm
  have key := sval_eq_sum_of_hasVal E H _ Λ.A W.t gen Φ j s 1 (fun _ => r) (fun _ => α) (fun _ => th) (fun _ => hth)
    (fun v => by rw [Fin.sum_univ_one]; exact hv v) ℂ⸨X⸩ (RingHom.id _) (fib q) hq₂ i (by rw [hfib]; exact hq)
  rw [Fin.sum_univ_one] at key
  exact (hs₁ _ (fib q) q.left jL i (hfib q) hi hq).symm.trans key

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToUnitCompLeft
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstTerm

section Values

variable {A : Type} [CommRing A] {B B₀ : Scheme.{0}}

theorem valR_zpow (x : Sp A ⟶ B) (U : B.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (t : Γ(B, U)ˣ) (u : Aˣ)
    (hu : (u : A) = valR x U t.val) (n : ℤ) : valR x U (t ^ n).val = ((u ^ n : Aˣ) : A) := by
  have e : u = Units.map (HolHom.evalHom x U h).toMonoidHom t := Units.ext (hu.trans (HolHom.valR_eq x U h _))
  rw [e, ← map_zpow, HolHom.valR_eq x U h]
  rfl

theorem le_div {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} (x : Sp A ⟶ B) {k : M₀.ι} {m : M.ι}
    (h₀ : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ M₀.U k) (h : ⊤ ≤ x ⁻¹ᵁ M.U m) :
    ⊤ ≤ x ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => k, m) :=
  fun _ hz => ⟨Set.mem_iInter.2 fun _ => h₀ hz, h hz⟩

theorem valR_pullGen {A₀ : Type} [CommRing A₀] (ρ : A₀ →+* A) {M₀ : LB B₀} {K : Type} [Fintype K]
    {ψ : K → (Sp A₀ ⟶ B₀)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M₀ ψ ε)) (k : K → M₀.ι)
    (h : ⊤ ≤ (𝟙 (Sp A₀)) ⁻¹ᵁ LB.wchart M₀ ψ k) :
    valR (𝟙 (Sp A)) _ ((LB.pullGen M₀ ψ ε t (spMap ρ)).s k).val = ρ (valR (𝟙 (Sp A₀)) _ (t.s k).val) := by
  have h' : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ LB.wchart M₀ (fun i => spMap ρ ≫ ψ i) k :=
    fun z _ => Set.mem_iInter.2 fun i => Set.mem_iInter.1 (h (show spMap ρ z ∈ (⊤ : (Sp A₀).Opens) from trivial)) i
  refine (HolHom.valR_res (𝟙 (Sp A)) _ _ h').trans ((HolHom.valR_comp (𝟙 (Sp A)) (spMap ρ) _ _).symm.trans ?_)
  refine Eq.trans ?_ (HolHom.valR_spMap ρ (𝟙 (Sp A₀)) _ h _)
  rw [Category.id_comp, Category.comp_id]
  rfl

theorem prod_factors {G : Type} [CommGroup G] (u : Fin 4 → G) (j : ℕ) :
    (∏ i, u i ^ Out.DegPre.famε j i) * ∏ i, ![u 1, u 2, u 0, u 3] i ^ Out.DegPre.gtε i = u 0 ^ j := by
  simp only [Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub, zpow_neg, zpow_one,
    zpow_natCast]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

end Values

section Points

variable {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) {T : Over (Sp R)} (b : T ⟶ D.P.A) (α : D.X)

theorem comp_famφB (i : Fin 4) : b.left ≫ D.famφB α i = D.gtφT T b α (![2, 0, 1, 3] i) := by
  have h : ∀ p : 𝟙_ (Over (Sp R)) ⟶ D.P.A, b ≫ toUnit D.P.A ≫ p = toUnit T ≫ p := fun p => by
    rw [← Category.assoc, comp_toUnit]
  fin_cases i
  · exact Category.comp_id _
  · change (b ≫ (𝟙 D.P.A * toUnit _ ≫ D.c α)).left = ((toUnit _ ≫ D.c α) * b).left
    rw [MonObj.comp_mul, h, Category.comp_id, mul_comm]
  · exact congrArg (·.left) (h _)
  · exact congrArg (·.left) (h _)

end Points

section Core

open FrameValue

variable [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {D₀ : Out.DegPre ℂ} {n : ℕ}
  (u : HolUnif D₀.P.A D₀.P.L n) {α₀ : D₀.X} {c : Fin n → ℂ}

theorem toUnit_comp_left {B : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ B) :
    (show Sp ℂ ⟶ _ from (toUnit (Out.TF (R := ℂ) ℂ) ≫ p).left) = p.left := by
  have e : Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ = 𝟙 (Sp ℂ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    exact Spec.map_id _
  change (Out.jFK (R := ℂ) ℂ ≫ Out.jK ℂ) ≫ p.left = _
  rw [e]
  exact Category.id_comp _

theorem gtφ_eq (hc : u.ex c = D₀.c α₀) {b₀ : Out.TF (R := ℂ) ℂ ⟶ D₀.P.A} {z : Fin n → ℂ}
    (hb : (show Sp ℂ ⟶ _ from b₀.left) = (u.ex z).left) (k : Fin 4) :
    (show Sp ℂ ⟶ _ from Out.DegPre.gtφ D₀ ℂ b₀ α₀ k) = (u.ex (![c + z, c, z, 0] k)).left := by
  have hb' : b₀ = toUnit _ ≫ u.ex z := Over.OverMorphism.ext (hb.trans (toUnit_comp_left _).symm)
  have h0 : u.ex 0 = η[D₀.P.A] := by
    rw [(u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]
  fin_cases k
  · refine Eq.trans ?_ (toUnit_comp_left _)
    change (toUnit _ ≫ D₀.c α₀ * b₀).left = (toUnit _ ≫ u.ex (c + z)).left
    rw [hb', u.ex_add, MonObj.comp_mul, hc]
  · exact (toUnit_comp_left _).trans (congrArg (·.left) hc.symm)
  · exact hb
  · exact (toUnit_comp_left _).trans (congrArg (·.left) h0.symm)

omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in

theorem isLift_famφB (hc : u.ex c = D₀.c α₀) (z : Fin n → ℂ) :
    IsLift u (D₀.famφB α₀) (u.ex z).left ![z, z + c, c, 0] := fun k => by
  have h : ∀ p : 𝟙_ (Over (Sp ℂ)) ⟶ D₀.P.A, u.ex z ≫ toUnit D₀.P.A ≫ p = p := fun p => by
    rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  fin_cases k
  · exact Category.comp_id _
  · change (u.ex z ≫ (𝟙 D₀.P.A * toUnit _ ≫ D₀.c α₀)).left = (u.ex (z + c)).left
    rw [MonObj.comp_mul, h, Category.comp_id, u.ex_add, hc]
  · change (u.ex z ≫ toUnit _ ≫ D₀.c α₀).left = (u.ex c).left
    rw [h, hc]
  · change (u.ex z ≫ toUnit _ ≫ η[D₀.P.A]).left = (u.ex 0).left
    rw [h, (u.ker 0).2 (zero_mem _), Hom.one_def, toUnit_unit, Category.id_comp]

theorem core {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I} {S : Type} [CommRing S]
    [IsLocalRing S] (κ : R →+* S) (ρ : ℂ →+* S) {φ : D.toPre.P.A.left ⟶ D₀.P.A.left}
    (w : LB.Iso D.toPre.P.L (D₀.P.L.pull φ)) (g : Out.GtPt D.toPre (Over.mk (spMap κ))) (g₀ : Out.GtPtF D₀ ℂ)
    {α : D.toPre.X} {z : Fin n → ℂ} (hc : u.ex c = D₀.c α₀) (hb : (show Sp ℂ ⟶ _ from g₀.b.left) = (u.ex z).left)
    (hg : GenRelR (A := S) w (g.s α) (LB.pullGen _ _ _ (g₀.s α₀) (spMap ρ))) {j : ℕ} (s₀ : D₀.SecB j α₀)
    (f : D.toPre.SecB j α) (r : R)
    (hf : ∀ (p : Sp S ⟶ D.toPre.P.A.left) (jf : Fin 4 → D.toPre.P.L.ι) (j₀ : Fin 4 → D₀.P.L.ι),
      p ≫ D.toPre.P.A.hom = spMap κ →
      (∀ i, ⊤ ≤ (p ≫ D.toPre.famφB α i) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀ i, jf i)) →
      ∃ t : Fin 4 → Sˣ, (∀ i, (t i : S) = valR (p ≫ D.toPre.famφB α i) _ (w.s (fun _ => j₀ i, jf i)).val) ∧
        (∏ i, t i ^ Out.DegPre.famε j i : Sˣ) * valR p (LB.wchart D.toPre.P.L (D.toPre.famφB α) jf) (f.f jf) =
          κ r * valR (p ≫ φ) (LB.wchart D₀.P.L (D₀.famφB α₀) j₀) (s₀.f j₀))
    (jM : D.toPre.P.L.ι) (j₀ : D₀.P.L.ι) (jf jt : Fin 4 → D.toPre.P.L.ι) (hj : FormalValue.CohCharts g α jM jf jt)
    (hM : ⊤ ≤ (show Sp S ⟶ _ from g.b.left) ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => j₀, jM)) :
    valR (A := S) g.b.left _ (w.s (fun _ => j₀, jM)).val ^ j *
        (FormalValue.famVal g f jf * FormalValue.coordVal g α jt) =
      κ r * ρ (secVal u D₀.P.isLB s₀ (u.ex z).left ![z, z + c, c, 0] *
        genVal u D₀.P.isLB (g₀.s α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] * u.fr j₀ z ^ j) := by
  have hφ : ∀ k, FormalValue.coordφ g α k ≫ φ = spMap ρ ≫ (u.ex (![c + z, c, z, 0] k)).left := fun k =>
    (hg.1 k).trans (congrArg (spMap ρ ≫ ·) (gtφ_eq u hc hb k))
  have hq : ∀ i, FormalValue.basePt g ≫ D.toPre.famφB α i = FormalValue.coordφ g α (![2, 0, 1, 3] i) :=
    comp_famφB D.toPre g.b α
  have ejf : ∀ i, jf i = jt (![2, 0, 1, 3] i) := fun i => hj.2.2 (.inr (.inl i)) (.inr (.inr _)) (hq i)
  have ejM : jM = jt 2 := hj.2.2 (.inl PUnit.unit) (.inr (.inr 2)) rfl
  have h₀ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ D₀.P.L.U j₀ := by
    intro y _
    obtain rfl : y = spMap ρ (cpt S) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact (congrArg (fun q => q (cpt S) ∈ D₀.P.L.U j₀) (hφ 2)).mp (mem_pull.1 (hM trivial).1)
  obtain ⟨k, hk, ek⟩ : ∃ k : Fin 4 → D₀.P.L.ι,
      (∀ i, ⊤ ≤ (u.ex (![c + z, c, z, 0] i)).left ⁻¹ᵁ D₀.P.L.U (k i)) ∧ k 2 = j₀ := by
    refine ⟨![chartAt D₀.P.isLB (u.ex (c + z)).left, chartAt D₀.P.isLB (u.ex c).left, j₀,
      chartAt D₀.P.isLB (u.ex 0).left], fun i => ?_, rfl⟩
    fin_cases i
    exacts [le_chartAt D₀.P.isLB _, le_chartAt D₀.P.isLB _, h₀, le_chartAt D₀.P.isLB _]
  subst ek ejM
  obtain rfl : jf = fun i => jt (![2, 0, 1, 3] i) := funext ejf
  have hd : ∀ i, ⊤ ≤ FormalValue.coordφ g α i ⁻¹ᵁ (LB.div (D₀.P.L.pull φ) D.toPre.P.L).U (fun _ => k i, jt i) :=
    fun i => le_div _ (hφ i ▸ FormalValue.top_le_comp (hk i) _) (hj.2.1.trans (LB.wchart_le _ _ _ i))
  obtain ⟨t, ht, e₁⟩ := hf (FormalValue.basePt g) (fun i => jt (![2, 0, 1, 3] i)) (fun i => k (![2, 0, 1, 3] i))
    (Over.w g.b) (fun i => by rw [hq i]; exact hd _)
  simp only [hq] at ht
  have lf := isLift_famφB u hc z
  have lg : IsLift u (Out.DegPre.gtφ D₀ ℂ g₀.b α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0] :=
    fun i => (Category.id_comp _).trans (gtφ_eq u hc hb i)
  have cf : ⊤ ≤ (u.ex z).left ⁻¹ᵁ D₀.P.L.wchart (D₀.famφB α₀) (fun i => k (![2, 0, 1, 3] i)) := by
    refine (lf.le_iff _).2 fun i => ?_
    fin_cases i
    exacts [hk 2, add_comm c z ▸ hk 0, hk 1, hk 3]
  have cg := (lg.le_iff k).2 hk
  have e₂ : valR (FormalValue.basePt g ≫ φ) _ (s₀.f fun i => k (![2, 0, 1, 3] i)) = _ :=
    (congrArg (fun q => valR q _ (s₀.f fun i => k (![2, 0, 1, 3] i))) (hφ 2)).trans
      ((HolHom.valR_spMap ρ (u.ex z).left _ cf _).trans (congrArg ρ (valAt'_sec D₀.P.isLB s₀ lf cf)))
  have e₃ : FormalValue.coordVal g α jt = _ := (hg.2 jt k hd).trans (congrArg₂ (· * ·)
    (Finset.prod_congr rfl fun i _ => valR_zpow _ _ (hd i) _ (![t 1, t 2, t 0, t 3] i)
      (by fin_cases i; exacts [ht 1, ht 2, ht 0, ht 3]) _)
    ((valR_pullGen ρ (g₀.s α₀) k cg).trans (congrArg ρ (valAt'_gen D₀.P.isLB (g₀.isGen α₀) lg cg))))
  have e₄ : frameProd u (Out.DegPre.famε j) ![z, z + c, c, 0] (fun i => k (![2, 0, 1, 3] i)) *
      frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k = u.fr (k 2) z ^ j := by
    have n₀ : u.fr (k 0) (c + z) ≠ 0 := u.fr_ne _ _ (hk 0)
    have n₁ : u.fr (k 1) c ≠ 0 := u.fr_ne _ _ (hk 1)
    have n₂ : u.fr (k 2) z ≠ 0 := u.fr_ne _ _ (hk 2)
    have n₃ : u.fr (k 3) 0 ≠ 0 := u.fr_ne _ _ (hk 3)
    simp only [frameProd, Fin.prod_univ_four, Out.DegPre.famε, Out.DegPre.gtε, Matrix.cons_val, zpow_sub₀ n₂,
      zpow_neg, zpow_one, zpow_natCast, add_comm z c]
    field_simp
  have e₅ : (t 0 : S) ^ j * ∏ i, ((![t 1, t 2, t 0, t 3] i ^ (-Out.DegPre.gtε i) : Sˣ) : S) =
      ((∏ i, t i ^ Out.DegPre.famε j i : Sˣ) : S) := by
    rw [← Units.coe_prod, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← prod_factors t j]
    simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  replace e₁ := e₁.trans (congrArg (κ r * ·) e₂)
  refine (congrArg₂ (fun a b => a ^ j * (_ * b)) (ht 0).symm e₃).trans ?_
  rw [← e₄]
  simp only [map_mul] at e₁ ⊢
  rw [← e₅] at e₁
  unfold FormalValue.famVal
  linear_combination (ρ (genVal u D₀.P.isLB (g₀.s α₀) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![c + z, c, z, 0]) *
    ρ (frameProd u Out.DegPre.gtε ![c + z, c, z, 0] k)) * e₁

end Core

theorem main : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (j : ℕ) (α : Λ.A.X) (s₀ : a.D₀.SecB j (Λ.ε α)) (f : W.P.D.toPre.SecB j (W.e (Λ.ε α))) (r : ℂ⟦X⟧), (∀ (Z : Type) [CommRing Z] [IsLocalRing Z] (p : Sp Z ⟶ W.P.D.toPre.P.A.left) (κ : ℂ⟦X⟧ →+* Z) (jf : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : Fin 4 → a.D₀.P.L.ι), p ≫ W.P.D.toPre.P.A.hom = spMap κ → (∀ i, ⊤ ≤ (p ≫ W.P.D.toPre.famφB (W.e (Λ.ε α)) i) ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀ i, jf i)) → ∃ u : Fin 4 → Zˣ, (∀ i, (u i : Z) = valR (p ≫ W.P.D.toPre.famφB (W.e (Λ.ε α)) i) _ (W.w.s (fun _ => j₀ i, jf i)).val) ∧ (∏ i, u i ^ Out.DegPre.famε j i : Zˣ) * valR p (LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB (W.e (Λ.ε α))) jf) (f.f jf) = κ r * valR (p ≫ W.φ) (LB.wchart a.D₀.P.L (a.D₀.famφB (Λ.ε α)) j₀) (s₀.f j₀)) → ∀ v jM j₀ jf jt, FormalValue.CohCharts (Ξ.g v) (W.e (Λ.ε α)) jM jf jt → ⊤ ≤ (Ξ.g v).b.left ⁻¹ᵁ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, jM) → valR (A := ℂ⟦X⟧) (Ξ.g v).b.left _ (W.w.s (fun _ => j₀, jM)).val ^ j * (FormalValue.famVal (Ξ.g v) f jf * FormalValue.coordVal (Ξ.g v) (W.e (Λ.ε α)) jt) = r * PowerSeries.C (Λ.fn j α s₀ v.2 * eTwoPi (v.1 α) * Λ.u.fr j₀ v.2 ^ j) := by
  intro _ _ E _ _ _ H _ D l Xo c O _ β Y _ _ b a χ W Λ Ξ j α s₀ f r hf v jM j₀ jf jt hj hM
  have h := core Λ.u (algebraMap ℂ⟦X⟧ ℂ⟦X⟧) (PowerSeries.C (R := ℂ)) W.w (Ξ.g v) (Λ.ex0 v) (Λ.ct α) (Λ.ex0_b v)
    (Ξ.g_rel v (Λ.ε α)) s₀ f r (fun p => hf _ p _) jM j₀ jf jt hj hM
  rw [Λ.arcDict_expZero_section v α] at h
  exact h

end GlobalTheory.ConstTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusCoordinateRatioEqTorusCoordOverOriginStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCoordinateRatio_eq_torusCoord_over_origin : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g n : ℕ) (ex : (Fin g → ℂ) → Out.GtPtF D ℂ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ D.P.A) → Out.GtPt D Tt), (∀ Tt b, (sB Tt b).b = b ^ n) → (∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))) → (∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))) → (∀ z z', (ex z).IsAdd (ex z') (ex (z + z'))) → (∀ p : Out.GtPtF D ℂ, p.IsZero → IsTorusPt p (fun _ => 1)) ∧ ∀ u : D.X → (Fin g → ℂ) → ℂ, IsRatio ex n (sB D.P.A (𝟙 _)) u → ∀ (z : Fin g → ℂ) (xv : D.X → ℂ), (ex z).b = Out.DegPre.zeroF D ℂ → IsTorusPt (ex ((n : ℂ) • z)) xv → ∀ x, u x z = xv x := by
  first | exact @GlobalTheory.AbelianLetters.TorusRatio.ratio_eq_torus_coord | exact GlobalTheory.AbelianLetters.TorusRatio.ratio_eq_torus_coord | (intros; apply GlobalTheory.AbelianLetters.TorusRatio.ratio_eq_torus_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtensionComplexPointsEqCharactersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_complexPoints_eq_characters : ∀ [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (D : Out.DegPre ℂ) (g : ℕ) (u : HolUnif D.P.A D.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (ct : D.X →+ (Fin g → ℂ)), u.IsAH Hm χ → u.IsRig D.rig → (∀ x, u.ex (ct x) = D.c x) → ∀ z : Fin g → ℂ, (∀ lam : D.X →+ ℂ, ∃! p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left ∧ ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x)) ∧ ∀ p : Out.GtPtF D ℂ, (show Sp ℂ ⟶ _ from p.b.left) = (u.ex z).left → ∃ lam : D.X →+ ℂ, ∀ x, FrameValue.genVal u D.P.isLB (p.s x) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ)) ![ct x + z, ct x, z, 0] = eTwoPi (lam x) := by
  first | exact @GlobalTheory.TorusExtChar.points_eq_characters | exact GlobalTheory.TorusExtChar.points_eq_characters | (intros; apply GlobalTheory.TorusExtChar.points_eq_characters <;> assumption)
end

