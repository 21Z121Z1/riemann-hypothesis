import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import GroundTheory.AutomorphicForms.GeometricLemmaCells
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0327
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0348
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0358
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.EulerMove
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0018
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulLeSqAddSq
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LBoundProof

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem mul_le_sq_add_sq (p q : ℝ≥0∞) : p * q ≤ p ^ 2 + q ^ 2 := by
  rcases le_total p q with h | h
  · calc p * q ≤ q * q := by gcongr
      _ = q ^ 2 := (sq q).symm
      _ ≤ _ := le_add_self
  · calc p * q ≤ p * p := by gcongr
      _ = p ^ 2 := (sq p).symm
      _ ≤ _ := le_self_add

theorem lInt_eq {ι : Type} [Fintype ι] (D : Dom E a b) (k₁ k₂ : H E a b → ι → Hs (ι := ι) D) (τ : ℝ)
    (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) :
    lInt D k₁ k₂ τ U = (cutSet E a τ ×ˢ cutSet E b τ).indicator
      (fun x => ∑ i, inner ℂ (k₁ x i) (U (k₂ x i))) := by
  funext x
  by_cases h1 : x.1 ∈ cutSet E a τ <;> by_cases h2 : x.2 ∈ cutSet E b τ <;>
    simp [lInt, chiT, h1, h2, Set.indicator, Set.mem_prod]

theorem enorm_inner_le {ι : Type} (D : Dom E a b) (U : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) [Fintype ι]
    (u v : Hs (ι := ι) D) (C : ℝ≥0∞) (hu : ‖u‖ₑ ^ 2 ≤ C) (hv : ‖v‖ₑ ^ 2 ≤ C) :
    ‖inner ℂ u (U v)‖ₑ ≤ ‖U‖ₑ * (2 * C) := by
  have h1 : ‖inner ℂ u (U v)‖ₑ ≤ ‖u‖ₑ * ‖U v‖ₑ := by
    simp only [enorm_eq_nnnorm]
    exact_mod_cast nnnorm_inner_le_nnnorm (𝕜 := ℂ) u (U v)
  calc ‖inner ℂ u (U v)‖ₑ ≤ ‖u‖ₑ * ‖U v‖ₑ := h1
    _ ≤ ‖u‖ₑ * (‖U‖ₑ * ‖v‖ₑ) := by gcongr; exact U.le_opNorm_enorm v
    _ = ‖U‖ₑ * (‖u‖ₑ * ‖v‖ₑ) := by ring
    _ ≤ ‖U‖ₑ * (‖u‖ₑ ^ 2 + ‖v‖ₑ ^ 2) := by gcongr; exact mul_le_sq_add_sq _ _
    _ ≤ ‖U‖ₑ * (C + C) := by gcongr
    _ = ‖U‖ₑ * (2 * C) := by rw [two_mul]

theorem lBound_of : Mahler → CutCount → LBound := by
  intro hM hC E _ _ _ a b D ι _ k₁ k₂ C₀ Ω hcont hC₀ hΩ hnorm
  obtain ⟨C₁, N, hC₁, hcut⟩ := hC E a b D Ω hΩ
  refine ⟨2 * Fintype.card ι * C₀.toReal * C₁, N, fun τ hτ U => ?_⟩
  set S : Set (H E a b) := cutSet E a τ ×ˢ cutSet E b τ with hS
  haveI : BorelSpace (H E a b) := ⟨rfl⟩
  have hSm : MeasurableSet S := ((hM E a τ).1.prod (hM E b τ).1).measurableSet
  have hg : Continuous fun x => ∑ i, inner ℂ (k₁ x i) (U (k₂ x i)) :=
    continuous_finset_sum _ fun i _ => (hcont i).1.inner (U.continuous.comp (hcont i).2)
  have hmeas : AEStronglyMeasurable (lInt D k₁ k₂ τ U) D.ν := by
    rw [lInt_eq]
    exact hg.aestronglyMeasurable.indicator hSm
  set c : ℝ≥0∞ := Fintype.card ι * (‖U‖ₑ * (2 * C₀)) with hc
  have hcr : c = ENNReal.ofReal (Fintype.card ι * (‖U‖ * (2 * C₀.toReal))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_mul (norm_nonneg _),
      ofReal_norm, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hC₀, ENNReal.ofReal_ofNat]
  have hctop : c ≠ ⊤ := by rw [hcr]; exact ENNReal.ofReal_ne_top
  have hpt : ∀ x, ‖lInt D k₁ k₂ τ U x‖ₑ ≤ c * S.indicator (cnt (ratH E a b) Ω) x := by
    intro x
    rw [lInt_eq]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      calc ‖∑ i, inner ℂ (k₁ x i) (U (k₂ x i))‖ₑ ≤ ∑ i, ‖inner ℂ (k₁ x i) (U (k₂ x i))‖ₑ :=
            enorm_sum_le _ _
        _ ≤ ∑ _i : ι, ‖U‖ₑ * (2 * (C₀ * cnt (ratH E a b) Ω x)) :=
            Finset.sum_le_sum fun i _ => enorm_inner_le D U _ _ _ (hnorm x i).1 (hnorm x i).2
        _ = c * cnt (ratH E a b) Ω x := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
            ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  have hA : 0 ≤ 2 * Fintype.card ι * C₀.toReal * C₁ * (1 + τ) ^ N * ‖U‖ := by positivity
  have hle : ∫⁻ x, ‖lInt D k₁ k₂ τ U x‖ₑ ∂D.ν ≤
      ENNReal.ofReal (2 * Fintype.card ι * C₀.toReal * C₁ * (1 + τ) ^ N * ‖U‖) := by
    calc ∫⁻ x, ‖lInt D k₁ k₂ τ U x‖ₑ ∂D.ν ≤ ∫⁻ x, c * S.indicator (cnt (ratH E a b) Ω) x ∂D.ν :=
          lintegral_mono hpt
      _ = c * ∫⁻ x, S.indicator (cnt (ratH E a b) Ω) x ∂D.ν := lintegral_const_mul' _ _ hctop
      _ ≤ c * ENNReal.ofReal (C₁ * (1 + τ) ^ N) := by gcongr; exact hcut τ hτ
      _ = ENNReal.ofReal (2 * Fintype.card ι * C₀.toReal * C₁ * (1 + τ) ^ N * ‖U‖) := by
          rw [hcr, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  refine ⟨⟨hmeas, hle.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  rw [integral_norm_eq_lintegral_enorm hmeas]
  exact ENNReal.toReal_le_of_le_ofReal hA hle

end GlobalTheory.CompanionTheory.LBoundProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.Rodier

section Pi

variable {α : Type} [Fintype α] {Γ : α → Type} [∀ a, Group (Γ a)]

abbrev piSub (H : ∀ a, Subgroup (Γ a)) : Subgroup (∀ a, Γ a) := Subgroup.pi Set.univ H

def piChar {H : ∀ a, Subgroup (Γ a)} (χ : ∀ a, H a →* ℂˣ) : piSub H →* ℂˣ where
  toFun m := ∏ a, χ a ⟨m.1 a, m.2 a (Set.mem_univ a)⟩
  map_one' := Finset.prod_eq_one fun a _ => map_one (χ a)
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun a _ => map_mul (χ a) ⟨x.1 a, x.2 a (Set.mem_univ a)⟩ ⟨y.1 a, y.2 a (Set.mem_univ a)⟩

end Pi

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)

abbrev pm (w : Equiv.Perm (Fin N)) : GL (Fin N) k := GroundTheory.Automorphic.permGL k w

def cell (w : Equiv.Perm (Fin N)) : Set (GL (Fin N) k) :=
  {g | ∃ p ∈ parab k (stdBlocks d hd), ∃ n ∈ unipB k (Fin N), g = p * pm k w * n}

def wKey (i : Fin N) : (Fin h)ᵒᵈ ×ₗ Fin N := toLex (OrderDual.toDual (blk (stdBlocks d hd) i), i)

def wOpen : Equiv.Perm (Fin N) := Tuple.sort (wKey d hd)

variable {k}
variable {W : Type} [AddCommGroup W] [Module ℂ W]

def openFns (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) : Submodule ℂ (IndSp (stdBlocks d hd) ρ) where
  carrier := {f | ∀ g, f.1.1 g ≠ 0 → g ∈ cell k d hd (wOpen d hd)}
  add_mem' := by
    intro a b ha hb g hg
    by_cases h1 : a.1.1 g = 0
    · refine hb g fun h2 => hg ?_
      show a.1.1 g + b.1.1 g = 0
      rw [h1, h2, add_zero]
    · exact ha g h1
  zero_mem' := fun g hg => absurd rfl hg
  smul_mem' := by
    intro c a ha g hg
    refine ha g fun h1 => hg ?_
    show c • a.1.1 g = 0
    rw [h1, smul_zero]

variable (k)

abbrev unipM : Subgroup (Levi k fun a => Fin (d a)) := piSub fun a => unipB k (Fin (d a))

variable {k}

abbrev whitM (ψ : AddChar k Circle) : unipM k d →* ℂˣ := piChar fun a => whitChar ψ (d a)

variable (k)

def unipU : Subgroup (GL (Fin N) k) :=
  unipB k (Fin N) ⊓ (unipRadLower k (stdBlocks d hd)).comap (MulAut.conj (pm k (wOpen d hd))).toMonoidHom

def unipL : Subgroup (GL (Fin N) k) :=
  unipB k (Fin N) ⊓ (leviEmb k (stdBlocks d hd)).range.comap (MulAut.conj (pm k (wOpen d hd))).toMonoidHom

end GlobalTheory.CompanionTheory.Rodier

namespace GlobalTheory.CompanionTheory.Rodier

def smInt {X W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W] (μ : MeasureTheory.Measure X) (φ : X → W) : W :=
  ∑ᶠ v : W, (((μ (φ ⁻¹' {v})).toReal : ℝ) : ℂ) • v

end GlobalTheory.CompanionTheory.Rodier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelNullCast
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Onto

noncomputable section

namespace GlobalTheory.CompanionTheory.RelKill

theorem relNull_cast {K : Type} [CommRing K] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of K))
    {Q : ObjectProperty (Thick (smFun Y q))} {a n c c' N N' : ℕ} (hc : 1 + a = c) (hc' : 1 + a = c') (hN : 2 + n = N)
    (hN' : 2 + n = N') (r : CH.Cn (G q 1) 2) (z : CH.Cn (G q a) n)
    (h : RelNull (G q c) Q N (cupC q (a := 1) (a' := a) hc hN r z)) :
    RelNull (G q c') Q N' (cupC q (a := 1) (a' := a) hc' hN' r z) := by
  subst hc hc' hN hN'
  exact h

theorem relKillOf : TopRes → FormUniq → OmRes → RelKillOf := by
  intro hTop hFU hOR hSL hCD hZR hAO hON hAR hFL hDW hDL hFC hC1 hDC hCK K _ _ W Z Y q _ _ i π _ D d hd hB r hr hc1 a n z hz hzr
  obtain ⟨B⟩ := hB
  haveI := B.closed
  obtain ⟨m, U, σ, hσ, hU, haff, hcov⟩ := hDC K W Z Y q i π D d B
  obtain ⟨-, hQ, -⟩ := hSL K (pullback i π) Y Y (π ≫ q) (pullback.snd i π) (𝟙 Y)
  exact relNull_cast (π ≫ q) _ _ _ _ r z
    (kill_over hTop hFU hOR hSL hCD hZR hAO hAR hFL hDW hDL hFC hC1 hCK D hQ B.f B.f_nat B.f_u U σ hσ hU haff hcov
      r hr hc1 a n z hz hzr)

end GlobalTheory.CompanionTheory.RelKill
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalHHermScal
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def scalH (σ : E →ₐ[F] E) {n : ℕ} (l : R) (S : HermR R σ n) : HermR R σ n :=
  ⟨(algebraMap R (R ⊗[F] E) l) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h : sigR R σ (algebraMap R (R ⊗[F] E) l) = algebraMap R (R ⊗[F] E) l := by
      simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h, S.2 a b]⟩

theorem scalH_coe (σ : E →ₐ[F] E) {n : ℕ} (l : R) (S : HermR R σ n) :
    (scalH R σ l S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      (algebraMap R (R ⊗[F] E) l) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl

theorem scalH_hermScal (σ : E →ₐ[F] E) (l s : R) :
    scalH R σ l (hermScal R σ s) = hermScal R σ (l * s) := by
  apply Subtype.ext
  funext a b
  change (algebraMap R (R ⊗[F] E) l) * (s ⊗ₜ[F] (1 : E)) = (l * s) ⊗ₜ[F] (1 : E)
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

end Alg

theorem euler_move_c : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → ∀ κ : ℝ≥0, IsEulerProd b I κ minf m → IsEulerProd b (I.map e) κ minf' m' := by
  intro F E _ _ _ _ _ σ hcm d b n M I mi mi' m m' e ei ev me mei mev hpr hG ci c hc h1 h2 hf κ hE
  have tr : ∀ (J : Measure (Fin n → Fin M → AF F ⊗[F] E)) (a : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (w : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsEulerProd b J κ a w ↔ IsEulerProd b J 1 (κ • a) w := fun J a w => by
    have e1 : ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞, ∫⁻ X, φ X ∂(κ • a) = (κ : ℝ≥0∞) * ∫⁻ X, φ X ∂a := fun φ => by
      rw [ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul]
    simp only [IsEulerProd, e1, ENNReal.coe_one, one_mul, mul_assoc]
  rw [tr] at hE ⊢
  refine PositivityTheory.PlacePermOperatorBicommutantSpan.euler_move F E σ hcm d b n M I _ _ m m' e ei ev me mei mev hpr hG ci c hc ?_ h2 hf hE
  rw [Measure.map_smul, h1, smul_comm]

end GlobalTheory.CompanionTheory.SW.MassSimil

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparatelyFiniteDimFunctionsFinite
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin.ProdTrick

theorem exists_finset_separating {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V] :
    ∃ T : Finset X, ∀ v ∈ V, (∀ x ∈ T, v x = 0) → v = 0 :=
  _root_.UpperTheory.Reformulated.B.Qp2.exists_finset_separating V

theorem exists_finiteDimensional_of_slices :
    ∀ (X Y : Type) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)),
      FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ →
      ∃ 𝓥 : Submodule ℂ (X × Y → ℂ), FiniteDimensional ℂ 𝓥 ∧
        ∀ f : X × Y → ℂ, (∀ y, (fun x => f (x, y)) ∈ V₁) → (∀ x, (fun y => f (x, y)) ∈ V₂) →
          f ∈ 𝓥 := by
  intro X Y V₁ V₂ h₁ h₂
  obtain ⟨T, hT⟩ := exists_finset_separating V₁
  let S : Submodule ℂ (X × Y → ℂ) :=
    { carrier := {f | (∀ y, (fun x => f (x, y)) ∈ V₁) ∧ (∀ x, (fun y => f (x, y)) ∈ V₂)}
      add_mem' := fun {a b} ha hb =>
        ⟨fun y => V₁.add_mem (ha.1 y) (hb.1 y), fun x => V₂.add_mem (ha.2 x) (hb.2 x)⟩
      zero_mem' := ⟨fun _ => V₁.zero_mem, fun _ => V₂.zero_mem⟩
      smul_mem' := fun c a ha =>
        ⟨fun y => V₁.smul_mem c (ha.1 y), fun x => V₂.smul_mem c (ha.2 x)⟩ }
  let L : S →ₗ[ℂ] (T → V₂) :=
    { toFun := fun f t => ⟨fun y => (f : X × Y → ℂ) ((t : X), y), f.2.2 t⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply Subtype.ext
    funext ⟨x, y⟩
    have hy := hT _ (f.2.1 y) (fun t ht => by
      have := congrArg Subtype.val (congrFun hf ⟨t, ht⟩)
      exact congrFun this y)
    exact congrFun hy x
  have : FiniteDimensional ℂ S := FiniteDimensional.of_injective L hL
  exact ⟨S, this, fun f h1 h2 => ⟨h1, h2⟩⟩

end GlobalTheory.CompanionTheory.CTFin.ProdTrick
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeBetweenNonemptySpheres
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SimilExists

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def frame (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Fin 2 → E) : Matrix (Fin 2) (Fin 2) E :=
  !![x 0, -(σ (x 0) * J 0 1 + σ (x 1) * J 1 1); x 1, σ (x 0) * J 0 0 + σ (x 1) * J 1 0]

theorem frame_det (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Fin 2 → E) :
    (frame σ J x).det = hE σ J x x := by
  simp [frame, Matrix.det_fin_two, hE, hform, Fin.sum_univ_two]
  ring

theorem frame_gram {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {J : Matrix (Fin 2) (Fin 2) E}
    (hJ : IsHermND σ J) (x : Fin 2 → E) :
    cT (σ : E →+* E) (frame σ J x) * J * frame σ J x =
      hE σ J x x • Matrix.diagonal ![1, J.det] := by
  have h00 : σ (J 0 0) = J 0 0 := hJ.1 0 0
  have h11 : σ (J 1 1) = J 1 1 := hJ.1 1 1
  have h01 : σ (J 1 0) = J 0 1 := hJ.1 0 1
  have h10 : σ (J 0 1) = J 1 0 := hJ.1 1 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frame, cT, Matrix.mul_apply, Fin.sum_univ_two, hE, hform, Matrix.det_fin_two, hσ, h00, h11,
      h01, h10] <;> ring

theorem exists_similitude_of_vectors {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e)
    {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) {x x' : Fin 2 → E} {b b' : E}
    (hx : hE σ J x x = b) (hx' : hE σ J x' x' = b') (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J *
      (γ : Matrix (Fin 2) (Fin 2) E) = (b' / b) • J := by
  set P := frame σ J x with hP
  set P' := frame σ J x' with hP'
  have hdet : P.det = b := by rw [hP, frame_det, hx]
  have hdet' : P'.det = b' := by rw [hP', frame_det, hx']
  have hu : IsUnit P.det := by rw [hdet]; exact hb.isUnit
  have hinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hu
  have hc : cT (σ : E →+* E) P⁻¹ * cT (σ : E →+* E) P = 1 := by
    rw [← cT_mul, hinv, cT_one]
  have hg : cT (σ : E →+* E) P * J * P = b • Matrix.diagonal ![1, J.det] := by
    rw [hP, frame_gram hσ hJ, hx]
  have hg' : cT (σ : E →+* E) P' * J * P' = b' • Matrix.diagonal ![1, J.det] := by
    rw [hP', frame_gram hσ hJ, hx']
  have hJ' : J = b • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹) := by
    calc J = (cT (σ : E →+* E) P⁻¹ * cT (σ : E →+* E) P) * J * (P * P⁻¹) := by
          rw [hc, hinv, Matrix.one_mul, Matrix.mul_one]
      _ = cT (σ : E →+* E) P⁻¹ * (cT (σ : E →+* E) P * J * P) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hg, Matrix.mul_smul, Matrix.smul_mul]
  have hdetG : (P' * P⁻¹).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, hdet', hdet]
    simpa using ⟨hb', hb⟩
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (P' * P⁻¹) hdetG, ?_⟩
  change cT (σ : E →+* E) (P' * P⁻¹) * J * (P' * P⁻¹) = (b' / b) • J
  calc cT (σ : E →+* E) (P' * P⁻¹) * J * (P' * P⁻¹)
      = cT (σ : E →+* E) P⁻¹ * (cT (σ : E →+* E) P' * J * P') * P⁻¹ := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = b' • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹) := by
        rw [hg', Matrix.mul_smul, Matrix.smul_mul]
    _ = (b' / b) • (b • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹)) := by
        rw [smul_smul, div_mul_cancel₀ _ hb]
    _ = (b' / b) • J := by rw [← hJ']

theorem exists_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ J : Matrix (Fin 2) (Fin 2) E, IsHermND σ J → ∀ β β' : F, β ≠ 0 → β' ≠ 0 → (PositivityTheory.Rg.Mass.sph σ J β).Nonempty → (PositivityTheory.Rg.Mass.sph σ J β').Nonempty → ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J * (γ : Matrix (Fin 2) (Fin 2) E) = (algebraMap F E (β' / β)) • J := by
  intro F E _ _ _ _ _ σ hcm J hJ β β' hβ hβ' ⟨X, hX⟩ ⟨X', hX'⟩
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2]
    simp
  have hx : hE σ J (X 0) (X 0) = algebraMap F E β := congrFun (congrFun hX 0) 0
  have hx' : hE σ J (X' 0) (X' 0) = algebraMap F E β' := congrFun (congrFun hX' 0) 0
  have hb : algebraMap F E β ≠ 0 := by simpa using hβ
  have hb' : algebraMap F E β' ≠ 0 := by simpa using hβ'
  rw [map_div₀]
  exact exists_similitude_of_vectors hσ hJ hx hx' hb hb'

end GlobalTheory.CompanionTheory.SimilExists

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureIndependentChoices
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThetaIndep

theorem thetaMeas_gram_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ μ' : Measure (HA (AF F) σ J)) (𝓕 𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsHaarH F E σ M J μ' → IsFDH F E σ M J μ' 𝓕' → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} = thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T} := by
  intro F E _ _ _ _ _ σ hcm M J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕₂ n T
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact n
  have hrat := (GlobalTheory.T.gram_matrix_local_global F E σ hcm M J hJ n 0 T).2
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 n {X | gramE σ J X = T}
  have hl' := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ' 𝓕' hμ' h𝓕₂ n {X | gramE σ J X = T}
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  have hfin := ((GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ).2 μ hμ).2 𝓕 h𝓕
  have : μ.IsHaarMeasure := hμ
  have : μ'.IsHaarMeasure := hμ'
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm M J hJ).1
  have h𝓕₁ : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  have h0 := (GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕₁ hfin).1
  have hsm : μ' = Measure.haarScalarFactor μ' μ • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  have hc0 : Measure.haarScalarFactor μ' μ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ' μ).ne'
  set c : ℝ≥0 := Measure.haarScalarFactor μ' μ with hc
  have hac : μ ≪ μ' := by
    rw [hsm]
    exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc0)
  have h𝓕₃ : IsFundamentalDomain Γ 𝓕' μ' := h𝓕₂
  have h𝓕₄ : IsFundamentalDomain Γ 𝓕' μ := h𝓕₃.mono hac
  have hmass : μ 𝓕 = μ 𝓕' := h𝓕₁.measure_eq h𝓕₄
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [hl _ hΦ, hl' _ hΦ]
  set f : HA (AF F) σ J → ℝ≥0∞ := fun g => ∑' X : {X | gramE σ J X = T},
    Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) with hf
  have hle : ∀ (γ : Γ) g, f (γ • g) ≤ f g := fun γ g => by
    choose t ht using fun X : {X | gramE σ J X = T} => PositivityTheory.PlacePermOperatorBicommutantSpan.act_rat (n := n) γ⁻¹ X.1
    have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X) := ht
    have hT : ∀ X, gramE σ J (t X) = T := fun X =>
      Matrix.map_injective hinj (by simp only [← hrat, ← ht', ag]; rw [hrat, X.2])
    have hti : Function.Injective fun X => (⟨t X, hT X⟩ : {X | gramE σ J X = T}) := fun X Y e => by
      have h1 := congrArg (actW (AF F) σ J γ) ((ht' X).trans ((congrArg (fun Z => ratTup (AF F) Z.1) e).trans (ht' Y).symm))
      simp only [← a2, mul_inv_cancel, a1] at h1
      exact Subtype.ext (hri h1)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti _)
    rw [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, a2, ht']
  have hinv : ∀ (γ : Γ) g, f (γ • g) = f g := fun γ g =>
    (hle γ g).antisymm (by simpa using hle γ⁻¹ (γ • g))
  have hint : ∫⁻ g in 𝓕, f g ∂μ = ∫⁻ g in 𝓕', f g ∂μ := h𝓕₁.setLIntegral_eq h𝓕₄ f hinv
  have hcE0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0
  have hcT : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  rw [hint, hsm, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply, ← hmass]
  simp only [ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.mul_inv (Or.inl hcE0) (Or.inl hcT)]
  calc _ = ((c : ℝ≥0∞)⁻¹ * c) * ((μ 𝓕)⁻¹ * ∫⁻ g in 𝓕', f g ∂μ) := by rw [ENNReal.inv_mul_cancel hcE0 hcT, one_mul]
    _ = _ := by ring

end GlobalTheory.CompanionTheory.SW.ThetaIndep

end
end

