import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0006
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2224
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AutomorphicArithmetic.CMTraceForms.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleFinitePlacesUnramOrSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottomTriple_finitePlaces_unram_or_split : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.BotRam.bottom_ram | exact GlobalTheory.BotRam.bottom_ram | (intros; apply GlobalTheory.BotRam.bottom_ram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataValuesIsoTransportFormsLevelsFamStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationDataValuesIso_transport_formsLevelsFamilies : ∀ (F F' : Type) [Field F] [Field F'] (e : F ≃+* F') (N : NumD F) (N' : NumD F') (I : NumD.Hom (e : F →+* F') N N'), Function.Bijective I.φ → (∀ x, I.h x = 1) → I.lam = 1 → (∀ (k : ℕ) (β : N.Form k), ∃ β' : N'.Form k, ∀ a b, β'.be (I.e a) (I.e b) = β.be a b) ∧ ∀ (m g : ℕ), Odd m → ∀ (ζ : Fˣ) (q : (Fin (2 * g) → ZMod (m ^ 2)) → N.QT (m ^ 2)), QLevel N g (m ^ 2) ζ q → ∃ q' : (Fin (2 * g) → ZMod (m ^ 2)) → N'.QT (m ^ 2), QLevel N' g (m ^ 2) (Units.map (e : F →+* F').toMonoidHom ζ) q' ∧ ∀ a (f : N.X → N.A → F) (f' : N'.X → N'.A → F'), IsEvFam N m (q a) f → (∀ α x, f' (I.e α) (I.φ x) = e (f α x)) → IsEvFam N' m (q' a) f' := by
  first | exact @GlobalTheory.MBLow.TrNum.transport | exact GlobalTheory.MBLow.TrNum.transport | (intros; apply GlobalTheory.MBLow.TrNum.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationTorsionEqPeriodLatticeModLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl.Qk

section Per
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}

theorem cv_add (M Nn : Fin g → ℤ) : cv (M + Nn) = cv M + cv Nn := by funext i; simp [cv]
theorem cv_sub (M Nn : Fin g → ℤ) : cv (M - Nn) = cv M - cv Nn := by funext i; simp [cv]
theorem cv_nsmul (k : ℕ) (M : Fin g → ℤ) : cv ((k : ℤ) • M) = k • cv M := by funext i; simp [cv]

theorem perV_add (M Nn M' Nn' : Fin g → ℤ) : perV τ (M + M') (Nn + Nn') = perV τ M Nn + perV τ M' Nn' := by
  simp only [perV, cv_add, mulVec_add]; abel

theorem perV_sub (M Nn M' Nn' : Fin g → ℤ) : perV τ (M - M') (Nn - Nn') = perV τ M Nn - perV τ M' Nn' := by
  simp only [perV, cv_sub, mulVec_sub]; abel

theorem perV_nsmul (k : ℕ) (M Nn : Fin g → ℤ) : perV τ ((k : ℤ) • M) ((k : ℤ) • Nn) = k • perV τ M Nn := by
  simp only [perV, cv_nsmul, mulVec_smul, smul_add]

theorem perV_eq_zero (hp : (τ.map Complex.im).PosDef) {M Nn : Fin g → ℤ} (h : perV τ M Nn = 0) : M = 0 ∧ Nn = 0 := by
  have hN : Nn = 0 := by
    by_contra hne
    have hx : (fun i => (Nn i : ℝ)) ≠ 0 := fun e => hne (funext fun i => by simpa using congrFun e i)
    have h1 := hp.dotProduct_mulVec_pos hx
    have h2 : (τ.map Complex.im) *ᵥ (fun i => (Nn i : ℝ)) = 0 := by
      funext i
      have := congrArg Complex.im (congrFun h i)
      simpa [perV, cv, mulVec, dotProduct, Complex.im_sum] using this
    rw [h2] at h1
    simp at h1
  subst hN
  refine ⟨funext fun i => ?_, rfl⟩
  have := congrFun h i
  simpa [perV, cv, mulVec, dotProduct] using this

end Per

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}

theorem eq_zero_of_perV_full (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) {M Nn : Fin g → ℤ} (h0 : tP σ Nn = 0)
    (h : perV (d.full σ 0) M Nn = 0) : M = 0 ∧ Nn = 0 := by
  have h1 : perV d.τ (zP σ M) (zP σ Nn) = 0 := by
    have := congrArg (zP σ) h
    rw [Exp.leftComponent_periodVector, h0, Exp.cv_zero, mulVec_zero, add_zero] at this
    exact this
  obtain ⟨a, b⟩ := perV_eq_zero d.pos h1
  have h2 : tP σ M = 0 := by
    have := congrArg (tP σ) h
    rw [Exp.secondBlock_periodVector, h0, b, Exp.cv_zero, Exp.cv_zero, mulVec_zero, mulVec_zero, add_zero, add_zero] at this
    funext l
    have := congrFun this l
    simpa [cv, tP] using this
  exact ⟨Exp.ext_zP_tP σ a h2, Exp.ext_zP_tP σ b h0⟩

def yv (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin g' ⊕ Fin r) (Nn : Fin g → ℤ) : N.X := ∑ l, tP σ Nn l • bX l

theorem yv_add (σ : Fin g ≃ Fin g' ⊕ Fin r) (a b : Fin g → ℤ) : yv bX σ (a + b) = yv bX σ a + yv bX σ b := by
  simp [yv, tP, add_smul, Finset.sum_add_distrib]

theorem yv_sub (σ : Fin g ≃ Fin g' ⊕ Fin r) (a b : Fin g → ℤ) : yv bX σ (a - b) = yv bX σ a - yv bX σ b := by
  simp [yv, tP, sub_smul, Finset.sum_sub_distrib]

theorem yv_nsmul (σ : Fin g ≃ Fin g' ⊕ Fin r) (k : ℕ) (a : Fin g → ℤ) : yv bX σ ((k : ℤ) • a) = k • yv bX σ a := by
  simp [yv, tP, Finset.smul_sum, mul_smul]

theorem yv_of_tP (σ : Fin g ≃ Fin g' ⊕ Fin r) {a : Fin g → ℤ} (h : tP σ a = 0) : yv bX σ a = 0 := by
  simp [yv, h]

theorem tP_of_yv (σ : Fin g ≃ Fin g' ⊕ Fin r) {a : Fin g → ℤ} (h : yv bX σ a = 0) : tP σ a = 0 := by
  have := Exp.co_sum (bX := bX) (tP σ a)
  change co bX (yv bX σ a) = _ at this
  rw [h] at this
  funext l
  have := congrFun this l
  simpa [co, cv] using this.symm

theorem yv_surj (σ : Fin g ≃ Fin g' ⊕ Fin r) (z : N.X) : ∃ a, yv bX σ a = z :=
  ⟨Exp.asm σ 0 (bX.repr z), by rw [yv, Exp.secondBlock_assemble]; exact bX.sum_repr z⟩

end GlobalTheory.MBLow.Cl.Qk

namespace GlobalTheory.MBLow.Cl
open Qk

theorem torsion_eq_periods_mod : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ k : ℕ, 0 < k → (∀ p, ∃ M Nn, d.Rep σ k M Nn p) ∧ (∀ M Nn, ∃! p, d.Rep σ k M Nn p) ∧ (∀ M Nn M' Nn' p p', d.Rep σ k M Nn p → d.Rep σ k M' Nn' p' → d.Rep σ k (M + M') (Nn + Nn') (p * p')) ∧ ∀ M Nn M' Nn' p p', d.Rep σ k M Nn p → d.Rep σ k M' Nn' p' → (N.QEq p p' ↔ ∃ M₁ N₁, M' = M + (k : ℤ) • M₁ ∧ Nn' = Nn + (k : ℤ) • N₁) := by
  intro N g' r g bX d σ k hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := exp_onto_torusExt N g' r g bX d σ
  choose E hE hU using h1
  have hiff : ∀ v h, d.IsPt σ v h ↔ h = E v := fun v h => ⟨hU v h, fun e => e ▸ hE v⟩
  have hadd : ∀ v v', E (v + v') = E v * E v' := fun v v' => (hU _ _ (h3 _ _ _ _ (hE v) (hE v'))).symm
  have hzero : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hpow : ∀ (n : ℕ) v, E (n • v) = E v ^ n := fun n v => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hper : ∀ M Nn, E (perV (d.full σ 0) M Nn) = N.io (yv bX σ Nn) := fun M Nn => (hU _ _ (h5 M Nn)).symm
  have hker : ∀ v v', E v = E v' → ∃ M Nn, tP σ Nn = 0 ∧ v = v' + perV (d.full σ 0) M Nn := fun v v' h => by
    have e : E (v - v') * E v' = E v' := by rw [← hadd, sub_add_cancel, h]
    obtain ⟨M, Nn, hy, hl⟩ := (h4 (v - v')).1 ((hiff _ _).2 (mul_eq_right.1 e).symm)
    exact ⟨M, Nn, hy, by rw [← hl, add_sub_cancel]⟩
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hc1 : ∀ v : Fin g → ℂ, (k : ℂ)⁻¹ • (k • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hc2 : ∀ v : Fin g → ℂ, k • ((k : ℂ)⁻¹ • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  have hrep : ∀ M Nn (p : N.QT k), d.Rep σ k M Nn p ↔
      p.1.1.toAdd = yv bX σ Nn ∧ p.1.2 = E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn) :=
    fun M Nn p => and_congr Iff.rfl (hiff _ _)
  refine ⟨fun p => ?_, fun M Nn => ?_, fun M Nn M' Nn' p p' h h' => ?_, fun M Nn M' Nn' p p' h h' => ?_⟩
  · obtain ⟨v, hv⟩ := h2 p.1.2
    have hv' := (hiff _ _).1 hv
    obtain ⟨a, ha⟩ := yv_surj (bX := bX) σ p.1.1.toAdd
    have e : E (k • v) = E (perV (d.full σ 0) 0 a) := by
      rw [hpow, hper, ← hv', ha]
      exact N.mem_QT.1 p.2
    obtain ⟨M, Nn, hy, hl⟩ := hker _ _ e
    refine ⟨0 + M, a + Nn, (hrep _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [yv_add, yv_of_tP σ hy, add_zero, ha]
    · rw [perV_add, ← hl, hc1, hv']
  · refine ⟨⟨(Multiplicative.ofAdd (yv bX σ Nn), E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)), ?_⟩,
      (hrep _ _ _).2 ⟨rfl, rfl⟩, fun p hp => ?_⟩
    · rw [NumD.mem_QT, ← hpow, hc2, hper]
      rfl
    · obtain ⟨a, b⟩ := (hrep _ _ _).1 hp
      exact Subtype.ext (Prod.ext a b)
  · obtain ⟨a, b⟩ := (hrep _ _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _ _).1 h'
    refine (hrep _ _ _).2 ⟨?_, ?_⟩
    · rw [yv_add, ← a, ← a']
      rfl
    · rw [perV_add, smul_add, hadd, ← b, ← b']
      rfl
  · obtain ⟨a, b⟩ := (hrep _ _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _ _).1 h'
    constructor
    · rintro ⟨z, c, c'⟩
      obtain ⟨z₀, hz⟩ := yv_surj (bX := bX) σ z
      have e : E ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn') =
          E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn + perV (d.full σ 0) 0 z₀) := by
        rw [hadd, hper, hz, ← b, ← b', c']
      obtain ⟨M₀, N₀, hy, hl⟩ := hker _ _ e
      have key := eq_zero_of_perV_full d σ (M := M' - (M + (k : ℤ) • (0 + M₀)))
        (Nn := Nn' - (Nn + (k : ℤ) • (z₀ + N₀))) ?_ ?_
      · exact ⟨0 + M₀, z₀ + N₀, sub_eq_zero.1 key.1, sub_eq_zero.1 key.2⟩
      · apply tP_of_yv (bX := bX)
        rw [yv_sub, yv_add, yv_nsmul, yv_add, yv_of_tP σ hy, add_zero, hz, ← a, ← a', c, sub_self]
      · rw [perV_sub, perV_add, perV_nsmul, perV_add, ← hc2 (perV (d.full σ 0) M' Nn'), hl, add_assoc, smul_add, hc2,
          sub_self]
    · rintro ⟨M₁, N₁, rfl, rfl⟩
      refine ⟨yv bX σ N₁, ?_, ?_⟩
      · rw [a, a', yv_add, yv_nsmul]
      · rw [b, b', perV_add, perV_nsmul, smul_add, hc1, hadd, hper]

end GlobalTheory.MBLow.Cl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesNormsEqUniformizerZpowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationValues_norms_eq_uniformizer_zpow : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ‖ν.rg‖ = 1 ∧ ∀ χ, ∃ n : ℤ, ‖(N.ψ χ : C)‖ = ‖toF V C ϖ‖ ^ n := by
  first | exact @GlobalTheory.MBLow.DiscNorm.main | exact GlobalTheory.MBLow.DiscNorm.main | (intros; apply GlobalTheory.MBLow.DiscNorm.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationValuesTransportFieldIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationValues_transport_fieldIso : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (e : F ≃+* F'), (∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ (N : NumD F) (ν : NumOf D F N), ∃ (N' : NumD F') (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N'), Function.Bijective I.φ ∧ (∀ x, I.h x = 1) ∧ I.lam = 1 ∧ (∀ χ, ν'.eX (I.e χ) = ν.eX χ) ∧ ν'.th = ν.th ∧ ν'.rg = e ν.rg ∧ (∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J)) ∧ ∀ (k : ℕ) (s : Fam D F k), ∃ s' : Fam D F' k, (∀ f, ν.FamV s f → ∃ f', ν'.FamV s' f' ∧ ∀ α x, f' (I.e α) (I.φ x) = e (f α x)) ∧ ∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ α, jc ν' s' gm' (I.e α) = dualMap (e : F →+* F') (jc ν s gm α) := by
  first | exact @GlobalTheory.MBLow.FieldIso.transport_iso | exact GlobalTheory.MBLow.FieldIso.transport_iso | (intros; apply GlobalTheory.MBLow.FieldIso.transport_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseFlagBundlePreimageModuli
section
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem isOpenMap_scheme_comp {X₁ X₂ X₃ : Scheme.{0}} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} (hf : IsOpenMap f)
    (hg : IsOpenMap g) : IsOpenMap (f ≫ g) := hg.comp hf

theorem isOpenMap_cbase {X : Scheme.{0}} {T : Type} (m : T → ℕ) (U : X.affineOpens) : IsOpenMap (cbase m U) := by
  haveI : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact isOpenMap_scheme_comp (MvPolynomial.isOpenMap_comap_C) U.2.fromSpec.isOpenEmbedding.isOpenMap

theorem dense_genMap_preimage : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), Dense (genMap π ⁻¹' Set.range Y.jQ) := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ
  have hcell : ∀ b w, IsOpenMap (κ b w ≫ π) := fun b w => by
    rw [hZ.plk.base b w]; exact isOpenMap_cbase _ _
  have hπ : IsOpenMap π := by
    intro O hO
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨b, w, y, rfl⟩ := hZ.cover z
    refine ⟨(κ b w ≫ π) '' (κ b w ⁻¹' O), ?_, hcell b w _ (hO.preimage (κ b w).continuous), y, hz, rfl⟩
    rintro _ ⟨y', hy', rfl⟩
    exact ⟨κ b w y', hy', rfl⟩
  have hid : IsIso (spMap (RingHom.id c.F)) := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id]; infer_instance
  have he : genMap π = pullback.fst (π ≫ Y.s) (spMap (RingHom.id c.F)) ≫ π ≫
      inv (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    rw [← cancel_mono (pullback.fst Y.s (spMap (RingHom.id c.F)))]
    simp only [genMap, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hgen : IsOpenMap (genMap π) := by
    rw [he]
    exact isOpenMap_scheme_comp (pullback.fst (π ≫ Y.s) (spMap (RingHom.id c.F))).isOpenEmbedding.isOpenMap
      (isOpenMap_scheme_comp hπ (inv (pullback.fst Y.s (spMap (RingHom.id c.F)))).isOpenEmbedding.isOpenMap)
  exact Y.jQ_dense.preimage hgen

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityStatementHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

open IsLocalRing in

theorem eq_of_mem_maximalIdeal_of_padicComplexInt (T : CDVR) (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : (p : T.V) ∈ maximalIdeal T.V) (kO : T.V →+* 𝓞_ℂ_[q]) : p = q := by
  have hq : (q : T.V) ∈ maximalIdeal T.V := by
    by_contra h
    have hu : IsUnit (q : T.V) := by
      by_contra h'
      exact h ((mem_maximalIdeal _).2 h')
    have hu' : IsUnit (q : 𝓞_ℂ_[q]) := by simpa using hu.map kO
    have h1 := (PadicComplexInt.integers q).isUnit_iff_valuation_eq_one.1 hu'
    rw [map_natCast] at h1
    have h2 : ‖(q : ℂ_[q])‖ = 1 := by rw [← coe_valued, h1]; rfl
    have h3 : (q : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] (q : ℚ_[q]) := by simp
    rw [h3, norm_algebraMap', Padic.norm_p] at h2
    have : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
    exact absurd h2 (ne_of_lt (inv_lt_one_of_one_lt₀ this))
  by_contra hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes Fact.out Fact.out).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : ((a * p + b * q : ℤ) : T.V) ∈ maximalIdeal T.V := by
    push_cast
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hq)
  rw [hab, Int.cast_one] at h1
  exact (maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem exists_cdvr_point (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime]
    (hp : (p : F) ∈ V.nonunits) (R : Type) [CommRing R] [IsDomain R] [Algebra V R] [Algebra.FiniteType V R]
    (hinj : Function.Injective (algebraMap V R)) (M : Ideal R) (hM : M.IsMaximal) (hpM : (p : R) ∈ M) (e : R)
    (he : e ≠ 0) :
    ∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (φ : R →+* T.V), T.FinRes ∧ Function.Injective kO ∧ φ e ≠ 0 := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨hdvr, hfin⟩ := GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hp0 hp
  haveI := hdvr
  let O' := AdicCompletion (IsLocalRing.maximalIdeal V) V
  have hinj0 : Function.Injective (algebraMap V O') := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V
  haveI : CharZero V := inferInstance
  haveI : CharZero O' := charZero_of_injective_algebraMap hinj0
  haveI : IsLocalHom (algebraMap V O') := inferInstance
  have hsp : Ideal.map (algebraMap V R) (IsLocalRing.maximalIdeal V) ≤ M := by
    rw [Ideal.map_le_iff_le_comap]
    haveI : (Ideal.comap (algebraMap V R) M).IsPrime := Ideal.comap_isPrime _ _
    have hne : Ideal.comap (algebraMap V R) M ≠ ⊥ := by
      intro h
      have : ((p : V)) ∈ Ideal.comap (algebraMap V R) M := by
        rw [Ideal.mem_comap, map_natCast]; exact hpM
      rw [h, Ideal.mem_bot] at this
      exact hp0 (by exact_mod_cast this)
    have hmax := Ideal.IsPrime.isMaximal inferInstance hne
    rw [IsLocalRing.eq_maximalIdeal hmax]
  obtain ⟨V', i1, i2, i3, i4, i5, φ, -, hφe, hφM⟩ := GlobalTheory.exists_integral_point_of_complete_case
    (fun O B _ _ _ _ _ _ _ _ _ _ M hM hsp e he => GlobalTheory.exists_integral_point_through O B M hM hsp e he)
    V O' hinj0 R hinj M hM.ne_top hsp e he
  obtain ⟨-, -, hcpl, hch, hfin'⟩ := GlobalTheory.dvr_finite_over_complete_dvr O' V'
  let T : CDVR := { V := V' }
  have hT : T.FinRes := hfin' (Finite.of_surjective _ (AdicCompletion.residueField_map_bijective V).2)
  obtain ⟨q, hq, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hT
  have hpT : (p : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
    have := hφM _ hpM
    rwa [map_natCast] at this
  obtain rfl := eq_of_mem_maximalIdeal_of_padicComplexInt T p q hpT kO
  refine ⟨T, kO, φ, hT, fun a b hab => ?_, hφe⟩
  apply IsFractionRing.injective T.V T.Fr
  apply k.injective
  rw [← hk, ← hk, hab]

theorem densSt : DensSt := by
  intro F _ _ V p _ hp X s Xw hX hflat hlft hXw hne R _ ξ hξ hsp
  obtain ⟨x, ⟨y, rfl⟩, hx⟩ := hsp
  haveI : Nonempty (Sp R) := ⟨y⟩
  haveI : IsIntegral (Sp R) := isIntegral_of_isOpenImmersion ξ
  haveI : IsDomain R := (affine_isIntegral_iff (CommRingCat.of R)).1 inferInstance
  let f : V →+* R := (Spec.preimage (ξ ≫ s)).hom
  letI : Algebra V R := f.toAlgebra
  haveI : Algebra.FiniteType V R := by
    have h : LocallyOfFiniteType (ξ ≫ s) := inferInstance
    rw [← Spec.map_preimage (ξ ≫ s)] at h
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  have hinj : Function.Injective (algebraMap V R) := by
    have h : Flat (ξ ≫ s) := inferInstance
    rw [← Spec.map_preimage (ξ ≫ s)] at h
    haveI : Module.Flat V R := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) (mem_nonZeroDivisors_of_ne_zero h0)
    have h1 : a • (1 : R) = a • (0 : R) := by rw [Algebra.smul_def, _root_.mul_one, ha, smul_zero]
    exact one_ne_zero (hreg h1)
  have hopen : IsOpen (Set.range ξ) := ξ.isOpenEmbedding.isOpen_range
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := nonempty_preirreducible_inter hopen Xw.isOpen ⟨_, y, rfl⟩ hne
  have hzO : z ∈ ξ ⁻¹ᵁ Xw := hz
  obtain ⟨_, ⟨e, rfl⟩, hze, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hzO (ξ ⁻¹ᵁ Xw).isOpen
  have he : e ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hze (Ideal.zero_mem _)
  have hpy : (p : R) ∈ (y : PrimeSpectrum R).asIdeal := by
    have h1 : y ∉ ξ ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) := hx
    rw [Scheme.preimage_basicOpen_top, map_natCast] at h1
    have h2 : ((p : Γ(Sp R, ⊤))) = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (p : R) := (map_natCast _ _).symm
    rw [h2, basicOpen_eq_of_affine] at h1
    by_contra h3
    exact h1 ((PrimeSpectrum.mem_basicOpen _ _).2 h3)
  obtain ⟨M, hM, hyM⟩ := Ideal.exists_le_maximal _ (y : PrimeSpectrum R).isPrime.ne_top
  obtain ⟨T, kO, φ, hT, hkO, hφe⟩ := exists_cdvr_point F V p hp R hinj M hM (hyM hpy) e he
  refine ⟨kO.comp φ, ⟨T, kO, spMap φ ≫ ξ, hT, hkO, sp_sp _ _ _⟩, ?_⟩
  rintro _ ⟨w, rfl⟩
  have hw : w = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p]) := by
    apply PrimeSpectrum.ext
    haveI := (w : PrimeSpectrum ℂ_[p]).isPrime
    exact Ideal.eq_bot_of_prime _
  subst hw
  have hinj2 : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO) := Subtype.val_injective.comp hkO
  rw [← sp_sp φ kO ξ, sp_sp kO (algebraMap 𝓞_ℂ_[p] ℂ_[p]) (spMap φ ≫ ξ), bot_map hinj2 (spMap φ ≫ ξ)]
  have hq : (spMap φ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.V) ∈ PrimeSpectrum.basicOpen e := by
    show e ∉ Ideal.comap φ ⊥
    simpa using hφe
  exact hsub hq

end GlobalTheory.FlatModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtTwoCmFieldStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_oscillation_le_at_two_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime] (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H F vd → OscLe Xo c p cx (F * m * (1 + vd / 2) * Mb + Sm) := by
  first | exact @GlobalTheory.RefSum.oscLe_two | exact GlobalTheory.RefSum.oscLe_two | (intros; apply GlobalTheory.RefSum.oscLe_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeOddSplitUnramifiedPrimeStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_oscillation_le_odd_split_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → SplitInK H p → OscLe Xo c p cx ((F * m * Mb + Sm) / ((p : ℝ) - 1)) := by
  first | exact @GlobalTheory.OscSplit.oscLe_split | exact GlobalTheory.OscSplit.oscLe_split | (intros; apply GlobalTheory.OscSplit.oscLe_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSectionIntersectionNumberEqBase
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem interNumRed_section : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ (y : Fin Y.dim → CartierDiv W.Z) (e : Fin Y.dim → Y.Dv), (∀ i, IsPull W.p₁ (y i) (e i) ∨ IsPull W.p₂ (y i) (e i)) → letI := algebraΓOfHom (W.p₁ ≫ Y.str); interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) (fun i => toLB (y i)) = Y.inter e := by
  intro F _ Y W y e h
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hemb := W.δ.isClosedEmbedding
  have hcl : Set.range W.δ = closure {W.δ (genericPoint Y.X)} := by
    rw [← Set.image_singleton, hemb.closure_image_eq, genericPoint_spec Y.X, Set.image_univ]
  have hf : ∀ r : F, W.δ.appTop (algebraMap F Γ(W.Z, ⊤) r) = algebraMap F Γ(Y.X, ⊤) r := fun r => by
    show W.δ.appTop ((W.p₁ ≫ Y.str).appTop ((Scheme.ΓSpecIso (.of F)).inv r)) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Category.assoc, W.δ₁, Category.id_comp]
    rfl
  show interNumRed F _ _ = _
  rw [InterModel.interNumRed_eq_interNumOn F W.δ _ hcl, interNumOn_eq_interNum_pull hf fun i => isLB_toLB (y i)]
  refine (Var.inter_eq_of_toPic_eq (fun i => LB.isLB_pull (isLB_toLB (y i)) _) fun i => ?_).symm
  rw [cls_pull (isLB_toLB (y i)), toPic_apply]
  rcases h i with h | h
  · rw [← PullPres.pull_cls_toLB _ _ W.p₁ _ _ h, ← CechPic.pull_comp, W.δ₁, CechPic.pull_id]
  · rw [← PullPres.pull_cls_toLB _ _ W.p₂ _ _ h, ← CechPic.pull_comp, W.δ₂, CechPic.pull_id]

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberSectionValueLinearCombinationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumberSectionValue_linearCombination : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) (β : D.X) (s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))) (n : ℕ) (a : Fin n → F) (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F β) (DegPre.famε k))), (∀ j, s.f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) → ∀ (r : Sp (DualNumber F) ⟶ (DegPre.BF D F).left) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι), (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) → r ≫ (fst (TF (R := V) F) D.P.A).left = spMap (algebraMap F (DualNumber F)) → sE s r J = ∑ i, TrivSqZeroExt.inl (a i) * sE (σF i) r J := by
  first | exact @GlobalTheory.DualLin.sE_comb | exact GlobalTheory.DualLin.sE_comb | (intros; apply GlobalTheory.DualLin.sE_comb <;> assumption)
end

