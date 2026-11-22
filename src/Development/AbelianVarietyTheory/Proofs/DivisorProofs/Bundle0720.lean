import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0697
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0698
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOnTangentEqDerivativeBoundingFunction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.LieVal

open GlobalTheory.CatCoh

theorem main : ∀ {A : Over (Sp ℂ)} {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol F.V))) (k : K.K) (p : Tot I g), p ∈ K.W k → ∀ (w : Fin g → ℂ) (ρ : Hol (K.W k) →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p (0, w)) → ∀ (v : epsR ℂ ⟶ A), v.left = spMap ρ.toRingHom ≫ r.x k → ∀ (f : Form (A.hom ≫ 𝟙 _)) (per : Λ →+ Hol F.V) (q : GlobalTheory.CatCoh.C0 K.Oc), GlobalTheory.CatCoh.d0 K.Oc q = (r.coef.pullbackOneCocycle f.1).1 - (K.perZ per).1 → tanVal v f = fderiv ℂ (Hol.fn (W := K.W k) (q (K.triv k))) p (0, w) := by
  intro A I _ g Λ _ F K r k p hp w ρ hρ v hv f per q hq
  let e : Hol (K.W k) →+* DualNumber ℂ := (TrivSqZeroExt.inlHom ℂ ℂ).comp (Hol.ev p hp).toRingHom
  let T : K.Obj :=
    { k := k, C := DualNumber ℂ, alg := (e.comp (K.cst k)).toAlgebra
      J := RingHom.ker ((SqExt.dual ℂ).π : DualNumber ℂ →+* ℂ)
      nil := ⟨2, (SqExt.dual ℂ).sq⟩, ρ := e, ρ_cst := fun _ ↦ rfl }
  have hder : ∀ h : Hol (K.W k), fderiv ℂ h.fn p (0, w) = ∑ a, (dw a h).fn p * w a := fun h ↦ by
    have : ((0, w) : Tot I g) = ∑ a, w a • ((0, Pi.single a 1) : Tot I g) := by
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simp only [Prod.snd_sum, Prod.smul_snd]
        exact pi_eq_sum_univ' w
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    exact congrArg (· * w a) (Hol.fn_der _ h hp).symm
  have hexp : ∀ h : Hol (K.W k), ρ h = e h + ∑ a, e (dw a h) * TrivSqZeroExt.inr (w a) := fun h ↦ by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [(hρ h).1]
      simp [e, TrivSqZeroExt.fst_sum, Hol.ev_apply]
    · rw [(hρ h).2, hder]
      simp [e, TrivSqZeroExt.snd_sum, Hol.ev_apply, mul_comm]
  let a : K.triv k ⟶ T := Charts.ptHom T (K.le_refl k)
  let b : K.triv k ⟶ T := Charts.fromTriv T (K.le_refl k) ρ.toRingHom
    (fun c ↦ by
      change ρ (K.cst k c) = e (K.cst k c)
      rw [hexp]; simp [Charts.dw_cst])
    (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (w a), fun _ ↦ rfl,
      fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
        simp only [RingHom.comp_apply, Charts.sh_refl]
        exact hexp h⟩)
  have ea := congrFun (congrFun (congrFun hq _) _) a
  have eb := congrFun (congrFun (congrFun hq _) _) b
  change ((show DualNumber ℂ from q T) - e (Charts.sh (K.le_refl k) (q (K.triv k))) : DualNumber ℂ) =
    (show DualNumber ℂ from ev f.1 (r.functor.map a)) - e (K.cst k (per 0)) at ea
  change ((show DualNumber ℂ from q T) - ρ (q (K.triv k)) : DualNumber ℂ) =
    (show DualNumber ℂ from ev f.1 (r.functor.map b)) - e (K.cst k (per 0)) at eb
  rw [Charts.sh_refl] at ea
  let E := SqExt.dual ℂ
  have hfst : (E.π : E.C →+* E.B).comp ρ.toRingHom = (Hol.ev p hp).toRingHom :=
    RingHom.ext fun h ↦ (hρ h).1.trans (Hol.ev_apply p hp h).symm
  have halg : ∀ c : ℂ, e (K.cst k (algebraMap ℂ (Hol F.V) c)) = algebraMap ℂ (DualNumber ℂ) c := fun c ↦ by
    have : K.cst k (algebraMap ℂ (Hol F.V) c) = algebraMap ℂ (Hol (K.W k)) c := rfl
    rw [this]
    change TrivSqZeroExt.inl (Hol.ev p hp (algebraMap ℂ _ c)) = _
    rw [AlgHom.commutes]; rfl
  let Φ : E.thick _ (E.red_w (pt_w v)) ⟶ r.obj T :=
    { φ := { RingHom.id (DualNumber ℂ) with commutes' := fun c ↦ (halg c).symm }
      φ₀ := (Ideal.Quotient.mk T.J).comp (TrivSqZeroExt.inlHom ℂ ℂ)
      comm := fun c ↦ Ideal.Quotient.eq.2 (by
        change (TrivSqZeroExt.inl (TrivSqZeroExt.fst (R := ℂ) (M := ℂ) c) - (show TrivSqZeroExt ℂ ℂ from c)).fst = 0
        rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_inl, sub_self])
      dp := isDPMorphism_of_rat (C' := DualNumber ℂ) _ _ _ fun c hc ↦ hc
      pt := by
        have h0 : spMap ((Ideal.Quotient.mk T.J).comp (TrivSqZeroExt.inlHom ℂ ℂ)) ≫
            spMap (E.π : E.C →+* E.B) ≫ v.left = spMap ((Ideal.Quotient.mk T.J).comp e) ≫ r.x k := by
          rw [hv, ← Category.assoc (spMap (E.π : E.C →+* E.B)), ← Cris.spMap_comp, hfst, ← Category.assoc,
            ← Cris.spMap_comp]
        exact h0 }
  have mkHom : ∀ (C : Type) [CommRing C] [Algebra ℂ C] (ψ : Hol (K.W k) →ₐ[ℂ] C) (y : Sp C ⟶ A.left)
      (hy : y ≫ A.hom ≫ 𝟙 _ = spMap (algebraMap ℂ C)), y = spMap ψ.toRingHom ≫ r.x k →
      ∃ m : r.obj (K.triv k) ⟶ Thick.triv C y hy, ∀ c, m.φ c = ψ c := fun C _ _ ψ y hy e' ↦
    ⟨{ φ := { ψ.toRingHom with commutes' := fun c ↦ ψ.commutes c }
       φ₀ := Ideal.Quotient.lift ⊥ ψ.toRingHom fun c hc ↦ by rw [Ideal.mem_bot.1 hc, map_zero]
       comm := fun _ ↦ rfl
       dp := isDPMorphism_of_eq_bot _ rfl _ _
       pt := by
        refine Eq.trans ?_ e'.symm
        refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ r.x k) ?_)
        exact (Cris.spMap_comp _ _).symm }, fun _ ↦ rfl⟩
  obtain ⟨a', ha'⟩ := mkHom ℂ (Hol.ev p hp) _ (E.red_w (pt_w v)) (by
    rw [hv, ← Category.assoc, ← Cris.spMap_comp, hfst])
  obtain ⟨b', hb'⟩ := mkHom (DualNumber ℂ) ρ v.left (pt_w v) hv
  have e1 : r.functor.map a = a' ≫ E.secHom (E.red_w (pt_w v)) E.i E.π_i ≫ Φ := Thick.hom_ext fun c ↦ by
    change e (Charts.sh (K.le_refl k) c) = TrivSqZeroExt.inl (a'.φ c)
    exact (congrArg e (Charts.sh_refl _ c)).trans (congrArg TrivSqZeroExt.inl (ha' c).symm)
  have e2 : r.functor.map b = b' ≫ E.idHom (pt_w v) ≫ Φ := Thick.hom_ext fun c ↦ (hb' c).symm
  have z1 : ev f.1 a' = 0 := f.2 a' rfl rfl
  have z2 : ev f.1 b' = 0 := f.2 b' rfl rfl
  have g1 : ev f.1 (r.functor.map a) = Φ.φ (ev f.1 (E.secHom (E.red_w (pt_w v)) E.i E.π_i)) + ev f.1 Φ := by
    rw [e1]
    refine (ev_comp f.1 a' _).trans ?_
    rw [z1, map_zero, zero_add]
    exact ev_comp f.1 _ Φ
  have g2 : ev f.1 (r.functor.map b) = Φ.φ (ev f.1 (E.idHom (pt_w v))) + ev f.1 Φ := by
    rw [e2]
    refine (ev_comp f.1 b' _).trans ?_
    rw [z2, map_zero, zero_add]
    exact ev_comp f.1 _ Φ
  rw [g1] at ea
  rw [g2] at eb
  have key : (E.val v.left (pt_w v) f.1 : DualNumber ℂ) = ρ (q (K.triv k)) - e (q (K.triv k)) := by
    rw [SqExt.val_apply]
    have aux : ∀ x y z u s t c : DualNumber ℂ, x - y = s + u - c → x - z = t + u - c → s - t = z - y :=
      fun x y z u s t c h1 h2 ↦ by linear_combination h2 - h1
    exact aux _ _ _ _ _ _ _ ea eb
  rw [tanVal_apply, key, TrivSqZeroExt.snd_sub, (hρ _).2]
  exact sub_zero _

end GlobalTheory.AnPer.LieVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.Chart

theorem isEval_comp {p : ℕ} {O A A' : Type} {σ : Type} [CommRing O] [CommRing A] [CommRing A']
    [Algebra O A] [Algebra O A'] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (hE : IsEval p x E)
    (g : A →ₐ[O] A') : IsEval p (fun i => g (x i)) (g.comp E) := by
  refine ⟨fun i => by simp [hE.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := hE.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd g (hN f hf)
  rwa [map_pow, map_natCast] at this

theorem ev₂_eval : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n f,
    c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 ∧ c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f ∧
    c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) ∧
    c.ev₂ n (cob1 c.μ f) = cobOne O (G.A n) (c.ev n f) := by
  intro p O _ _ G d c n f
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    T.isAdicComplete_of_finite_projective_algebra p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  have h1 : c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 := by
    have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
        fun j => Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)
          (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inl j)
    have hE := isEval_comp (c.isEval n)
      (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f
  have h2 : c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f := by
    have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
        fun j => Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)
          (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inr j)
    have hE := isEval_comp (c.isEval n)
      (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f
  have h3 : c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) := by
    have hx : (fun j => c.ev₂ n (c.μ j)) =
        fun j => Bialgebra.comulAlgHom O (G.A n) (c.x n j) := funext fun j => c.comul n j
    have hE := isEval_comp (c.isEval n) (Bialgebra.comulAlgHom O (G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ c.isLaw.const hE f
  refine ⟨h1, h2, h3, ?_⟩
  rw [cob1, map_sub, map_sub, h1, h2, h3, cobOne_apply]

end GlobalTheory.QLog.Chart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartGroupLawEvalRightUnitStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_groupLaw_eval_right_unit : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A)}) A] {d : ℕ} (x : Fin d → A) (ev : MvPowerSeries (Fin d) O →ₐ[O] A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p x ev → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, ev (op μ (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0) i) = x i := by
  first | exact @GlobalTheory.chart_unit | exact GlobalTheory.chart_unit | (intros; apply GlobalTheory.chart_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartHasPeriodLinearIntegralStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_hasPeriod_linear_integral : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y y' b : F.B), c.HasPeriod F.θ t f y → c.HasPeriod F.θ t g y' → c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') ∧ (∀ s : MvPowerSeries (Fin d) F.B, constantCoeff s = 0 → c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0) := by
  first | exact @GlobalTheory.QLog.hasPeriod_linear | exact GlobalTheory.QLog.hasPeriod_linear | (intros; apply GlobalTheory.QLog.hasPeriod_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartNatMultipleEvalProperties
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.ChartMul

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ}

theorem isEval_algHom_comp {A A' σ : Type} [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A']
    {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (hE : IsEval p x E) (g : A →ₐ[O] A') :
    IsEval p (fun i => g (x i)) (g.comp E) := by
  refine ⟨fun i => by simp [hE.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := hE.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd g (hN f hf)
  rwa [map_pow, map_natCast] at this

theorem constantCoeff_nmul {R : Type} [CommRing R] {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) : constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    have e : nmul μ (k + 1) i = subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (μ i) := by
      simp only [nmul]
      rw [Function.iterate_succ_apply']
      rfl
    rw [e]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

variable [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem ev₂_inL (c : QLog.Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    T.isAdicComplete_of_finite_projective_algebra p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
      fun j => Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)
        (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inl j)
  have hE := isEval_algHom_comp (c.isEval n)
    (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n))
  rw [← hx] at hE
  exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f

theorem ev₂_inR (c : QLog.Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    T.isAdicComplete_of_finite_projective_algebra p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
      fun j => Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)
        (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inr j)
  have hE := isEval_algHom_comp (c.isEval n)
    (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n))
  rw [← hx] at hE
  exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f

theorem ev_nmul (c : QLog.Chart G d) (n k : ℕ) (i : Fin d) :
    c.ev n (nmul c.μ k i) = mulBy O (G.A n) k (c.x n i) := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := T.isAdicComplete_of_finite_projective_algebra p O (G.A n)
  have H := ((CEval.continuous_eval p O (G.A n) (Fin d) _ (c.nil n)).2 (c.ev n) (c.isEval n)).1
  induction k generalizing i with
  | zero =>
    have h0 : nmul c.μ 0 i = 0 := rfl
    rw [h0, map_zero]
    simp [mulBy, c.aug n i]
  | succ k ih =>
    let M : G.A n →ₐ[O] G.A n := (mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
    let L : G.A n ⊗[O] G.A n →ₐ[O] G.A n :=
      Algebra.TensorProduct.lift M (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _
    have hs : ∀ j, constantCoeff (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul c.isLaw.const k j
      · exact constantCoeff_X _
    have e : nmul c.μ (k + 1) i = subst (Sum.elim (nmul c.μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (c.μ i) := by
      simp only [nmul]
      rw [Function.iterate_succ_apply']
      rfl
    have hE := isEval_algHom_comp (c.isEval₂ n) L
    have hx : (fun j => L (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) j)) =
        fun j => c.ev n (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) := by
      funext j
      rcases j with j | j
      · simp [L, M, ih j]
      · simp [L, (c.isEval n).1 j]
    rw [hx] at hE
    rw [e, H _ _ _ hs hE, AlgHom.comp_apply, c.comul n i]
    have h1 : mulBy O (G.A n) (k + 1) (c.x n i) =
        (WithConv.toConv (AlgHom.id O (G.A n)) ^ (k + 1)).ofConv (c.x n i) :=
      DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id O (G.A n)) (k + 1)) (c.x n i)
    have h2 : (M : G.A n →ₐ[O] G.A n) = (WithConv.toConv (AlgHom.id O (G.A n)) ^ k).ofConv :=
      comp_mulBy_pts (AlgHom.id O (G.A n)) k
    rw [h1, pow_succ, AlgHom.convMul_apply]
    simp only [L, h2]

theorem ev_subst_nmul (c : QLog.Chart G d) (n k : ℕ) (f : MvPowerSeries (Fin d) O) :
    c.ev n (subst (nmul c.μ k) f) = mulBy O (G.A n) k (c.ev n f) := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := T.isAdicComplete_of_finite_projective_algebra p O (G.A n)
  have H := ((CEval.continuous_eval p O (G.A n) (Fin d) _ (c.nil n)).2 (c.ev n) (c.isEval n)).1
  let M : G.A n →ₐ[O] G.A n := (mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
  have hE := isEval_algHom_comp (c.isEval n) M
  have hx : (fun j => M (c.x n j)) = fun j => c.ev n (nmul c.μ k j) :=
    funext fun j => (ev_nmul c n k j).symm
  rw [hx] at hE
  exact H (Fin d) _ _ (constantCoeff_nmul c.isLaw.const k) hE f

theorem ev₂_pull2_nmul (c : QLog.Chart G d) (n k : ℕ) (s : MvPowerSeries (Fin d ⊕ Fin d) O) :
    c.ev₂ n (pull2 (nmul c.μ k) s) = pullbackTwo (mulBy O (G.A n) k) (c.ev₂ n s) := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    T.isAdicComplete_of_finite_projective_algebra p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  let M : G.A n →ₐ[O] G.A n := (mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
  let T : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] G.A n := Algebra.TensorProduct.map M M
  have hs : ∀ j, constantCoeff (Sum.elim (fun j => inL (nmul c.μ k j))
      (fun j => inR (nmul c.μ k j)) j) = 0 := by
    have hX : ∀ j : Fin d, constantCoeff (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
      fun _ => constantCoeff_X _
    have hY : ∀ j : Fin d, constantCoeff (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
      fun _ => constantCoeff_X _
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hX) hX
        (constantCoeff_nmul c.isLaw.const k j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hY) hY
        (constantCoeff_nmul c.isLaw.const k j)
  have hE := isEval_algHom_comp (c.isEval₂ n) T
  have hx : (fun j => T (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n))
      (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) j)) =
      fun j => c.ev₂ n (Sum.elim (fun j => inL (nmul c.μ k j)) (fun j => inR (nmul c.μ k j)) j) := by
    funext j
    rcases j with j | j
    · simp [T, M, ev₂_inL, ev_nmul]
    · simp [T, M, ev₂_inR, ev_nmul]
  rw [hx] at hE
  have e : pull2 (nmul c.μ k) s =
      subst (Sum.elim (fun j => inL (nmul c.μ k j)) (fun j => inR (nmul c.μ k j))) s := rfl
  rw [e, H _ _ _ hs hE, AlgHom.comp_apply]
  generalize c.ev₂ n s = t
  induction t with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a b => simp [T, M]

theorem nmul_ev : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n k,
    (∀ i, c.ev n (nmul c.μ k i) = mulBy O (G.A n) k (c.x n i)) ∧
    (∀ f, c.ev n (subst (nmul c.μ k) f) = mulBy O (G.A n) k (c.ev n f)) ∧
    ∀ s, c.ev₂ n (pull2 (nmul c.μ k) s) = pullbackTwo (mulBy O (G.A n) k) (c.ev₂ n s) :=
  fun _ _ _ _ _ _ c n k => ⟨ev_nmul c n k, ev_subst_nmul c n k, ev₂_pull2_nmul c n k⟩

end GlobalTheory.QLog.ChartMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawNatMultipleAddMulLaws
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NMul

variable {R : Type} [CommRing R] {d : ℕ}

theorem nmul_zero' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) :
    nmul μ 0 = fun _ => 0 := rfl

theorem nmul_succ' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) (fun i => X i) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem nmul_const (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul_zero']
  | succ n ih =>
    rw [nmul_succ']
    exact (GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ n) (fun i => X i) (fun _ => 0) ih
      (fun i => constantCoeff_X i) (fun _ => map_zero _)).1

theorem nmul_add (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (m n : ℕ) :
    nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) := by
  induction n with
  | zero =>
    rw [Nat.add_zero, nmul_zero']
    exact ((GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ m) (fun _ => 0) (fun _ => 0)
      (nmul_const μ hμ m) (fun _ => map_zero _) (fun _ => map_zero _)).2.2.2.1).symm
  | succ n ih =>
    rw [← Nat.add_assoc, nmul_succ', ih, nmul_succ']
    exact (GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ m) (nmul μ n) (fun i => X i)
      (nmul_const μ hμ m) (nmul_const μ hμ n) (fun i => constantCoeff_X i)).2.1

theorem nmul_one (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) :
    nmul μ 1 = fun i => X i := by
  rw [nmul_succ', nmul_zero']
  have h := GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (fun i => X i) (fun _ => 0) (fun _ => 0)
    (fun i => constantCoeff_X i) (fun _ => map_zero _) (fun _ => map_zero _)
  rw [← h.2.2.1, h.2.2.2.1]

theorem nmul_mul (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (m n : ℕ) :
    ∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i) := by
  have ha : HasSubst (nmul μ n) := hasSubst_of_constantCoeff_zero (nmul_const μ hμ n)
  induction m with
  | zero =>
    intro i
    rw [Nat.zero_mul, nmul_zero']
    exact (map_zero (substAlgHom (R := R) ha)).symm.trans (by rw [coe_substAlgHom])
  | succ m ih =>
    intro i
    rw [Nat.succ_mul, nmul_add μ hμ, nmul_succ']
    rw [(GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom R d μ hμ (Fin d) (nmul μ m) (fun i => X i) (fun _ => 0)
      (nmul_const μ hμ m) (fun i => constantCoeff_X i) (fun _ => map_zero _)).2.2.2.2
      (Fin d) (nmul μ n) (nmul_const μ hμ n) i]
    have e1 : (fun j => subst (nmul μ n) (nmul μ m j)) = nmul μ (m * n) := funext fun j => (ih j).symm
    have e2 : (fun j => subst (nmul μ n) ((X j : MvPowerSeries (Fin d) R))) = nmul μ n :=
      funext fun j => subst_X ha j
    rw [e1, e2]

theorem nmul_laws : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ m n : ℕ, (∀ i, constantCoeff (nmul μ n i) = 0) ∧
      nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) ∧
      (∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i)) ∧ nmul μ 1 = fun i => X i :=
  fun _ _ _ μ hμ m n => ⟨nmul_const μ hμ n, nmul_add μ hμ m n, nmul_mul μ hμ m n, nmul_one μ hμ⟩

end GlobalTheory.NMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalLogCoeffMemOfSubOneMemDpStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ : Type) (h : MvPowerSeries σ B), constantCoeff h = 1 → (∀ α, coeff α (h - 1) ∈ J) → In J (formalLog (map (algebraMap B Q) h)) := by
  first | exact @GlobalTheory.DPLog.formalLog_in_of_sub_one_mem | exact GlobalTheory.DPLog.formalLog_in_of_sub_one_mem | (intros; apply GlobalTheory.DPLog.formalLog_in_of_sub_one_mem <;> assumption)
end

