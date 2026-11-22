import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0333
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

section Dual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def DualCl (x y : IrrGL k) : Prop :=
  ∃ (n : ℕ) (π π' : IrrRep (GL (Fin n) k)), x = cls π ∧ y = cls π' ∧ Nonempty (π'.ρ.Equiv (contra π.ρ))

def SegDual (Δ Δ' : Segment k) : Prop :=
  Δ'.len = Δ.len ∧ DualCl (Δ.first.nu ((Δ.len : ℂ) - 1)) Δ'.first

end Dual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure CuspLaws (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (r : IrrGL (w.adicCompletion E) → WD h) : Prop where

  bij : Set.BijOn r {x | x.IsCusp} {y | IsIrrWD y}

  dim : ∀ x, x.IsCusp → (r x).lpDim = x.1

  twist : ∀ x, x.IsCusp → ∀ χ hχ, r (x.tw χ hχ) = (r x).lpTwist (χ.comp a) (ha.smooth hχ)

  central : ∀ x : IrrGL (w.adicCompletion E), x.IsCusp → ∀ ω, HasCentralChar x.rep ω →
    ∀ σ, ((r x).eig σ).prod = (ω (a σ) : ℂ)

  dual : ∀ x y, x.IsCusp → y.IsCusp → DualCl x y → r y = (r x).lpDual

  eps : ∀ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ → ψ ≠ 1 →
    ∀ x y : IrrGL (w.adicCompletion E), x.IsCusp → y.IsCusp → y.1 < x.1 →
      HasPairGamma ψ x.rep y.rep (e ψ ((r x).lpChar (r y)))

def IsLExt (r rc : IrrGL (w.adicCompletion E) → WD h) : Prop :=
  ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep → rc x = segSum r l

end GlobalTheory.LocLanglands

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsClassSystem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Links (PolF)
open Formalism.L2.NTheta (IsIdemAt)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ExportSeries

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

variable {D : D7} {S T : HSp D}

theorem Frame.Good.posDef {F : Frame S T} (h : F.Good) (τ : D.what₂.Tau) : (gramAt D S τ).PosDef := by
  have := (GlobalTheory.GalLift.Vec.isCartanInv_one (h.onbS τ)).2.2
  rwa [Matrix.mul_one] at this

theorem exists_isClassSystem (B : Base S T) (hF : B.F.Good) (ψ : Twist D Circle) :
    ∃ (m : ℕ) (h : Fin m → GA D S), IsClassSystem S (B.levJ ψ) h := by
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover S hF.posDef (B.levJ ψ)
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev S B.F.βS (B.levS ψ))
  have hl : ∀ x : Bridge.Gf S, ∃ k ∈ GfC S, finPt S k = x := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨k, hk, e⟩ := GlobalTheory.LevelOpen.exists_finPart D S g
    exact ⟨k, hk, Subtype.ext e⟩
  choose l hl1 hl2 using hl
  have hr : Equivalence fun g g' : Bridge.Gf S => ∃ (γ : GQ S) (k : B.levJ ψ), g = Bridge.ratF S γ * g' * k :=
    ⟨fun g => ⟨1, 1, by simp⟩, by
      rintro g g' ⟨γ, k, rfl⟩
      exact ⟨γ⁻¹, k⁻¹, by simp [mul_assoc]⟩, by
      rintro g g' g'' ⟨γ, k, rfl⟩ ⟨γ', k', rfl⟩
      exact ⟨γ * γ', k' * k, by simp [mul_assoc]⟩⟩
  obtain ⟨n, f, hf⟩ := GlobalTheory.UnRep.FullReps.exists_subfamily _ hr c
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.ParahoricCompact.exists_compact_entries B.F.βS
  refine ⟨n, fun a => l (c (f a)), fun a => hl1 _, fun g => ?_, fun a => ?_⟩
  · obtain ⟨a, ha⟩ := hc g
    simp only [hl2]
    exact hf g a ha
  · exact GlobalTheory.RepsObj.finite_stab S hF.posDef _ hC (fun k hk => hCe k.1 (Base.mem_St_of_mem_levJ hk)) _

end GlobalTheory.ExportSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HasGammaX
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RSGam

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n m : ℕ}

open Classical in

def zc {j : ℕ} (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (hn : m + (j + 1) = n) (π : Representation ℂ (GL (Fin n) k) V)
    (τ : Representation ℂ (GL (Fin m) k) V') (l : Module.Dual ℂ V) (l' : Module.Dual ℂ V') (v : V) (v' : V') (t : ℤ) : ℂ :=
  I (fun g => if ord k (GeneralLinearGroup.det g) = t then
    l (π (emb₂ k (stdSum hn) (g, 1)) v) * l' (τ g v') * (absPow k (-(j : ℂ) / 2) (GeneralLinearGroup.det g) : ℂ) else 0)

open Classical in

def zd [MeasurableSpace k] (μ : Measure k) {j : ℕ} (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (hn : m + (j + 1) = n)
    (π : Representation ℂ (GL (Fin n) k) V) (τ : Representation ℂ (GL (Fin m) k) V') (l : Module.Dual ℂ V)
    (l' : Module.Dual ℂ V') (v : V) (v' : V') (t : ℤ) : ℂ :=
  I (fun g => if ord k (GeneralLinearGroup.det g) = t then
    (∫ x : Fin j → Fin m → k, l (π (tilde (emb₂ k (stdSum hn) (g, 1) * lowUnip hn (padRow x) *
        emb₂ k (stdSum hn) (1, longElt (j + 1) k))) v) ∂(Measure.pi fun _ => Measure.pi fun _ => μ)) *
      l' (τ (tilde g) v') * (absPow k (-(j : ℂ) / 2) (GeneralLinearGroup.det g) : ℂ) else 0)

def HasGammaX (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin n) k) V) (τ : Representation ℂ (GL (Fin m) k) V')
    (γ : RatFunc ℂ) : Prop :=
  ∀ (j : ℕ) (hn : m + (j + 1) = n) [MeasurableSpace k] [BorelSpace k] (μ : Measure k), IsSelfDualFor ψ μ →
    ∀ ω : kˣ →* ℂˣ, HasCentralChar τ ω →
    ∀ (l : Module.Dual ℂ V) (l' : Module.Dual ℂ V'), IsFunctional ψ π l → IsFunctional ψ⁻¹ τ l' →
      ∀ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I → ∀ (v : V) (v' : V'),
        ∃ R R' : RatFunc ℂ, (∀ t, (R : LaurentSeries ℂ).coeff t = zc I hn π τ l l' v v' t) ∧
          (∀ t, (R' : LaurentSeries ℂ).coeff t = zd μ I hn π τ l l' v v' t) ∧
          ∀ᶠ x in Filter.cofinite, R'.eval (RingHom.id ℂ) x⁻¹ =
            (ω (-1) : ℂ) ^ (n - 1) * γ.eval (RingHom.id ℂ) x * R.eval (RingHom.id ℂ) x

def GamIs (ψ : AddChar k Circle) (x y : IrrGL k) (f : ℂ → ℂ) : Prop :=
  ∃ γ : RatFunc ℂ, HasGammaX ψ x.rep y.rep γ ∧ ∀ᶠ z in Filter.cofinite, γ.eval (RingHom.id ℂ) z = f z

end Local

section Galois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def NoInv (y : WD h) : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = y ∧
    ∀ v, (∀ σ : Ine (F := E) A, a.ρ (ineIncl h σ) v = v) → v = 0

open Classical in

def lroots (y : WD h) : Multiset ℂ :=
  if hy : ∃ (c : Multiset ℂ) (y' : WD h), (0 : ℂ) ∉ c ∧ y = (WD.lpUnr h c).lpSum y' ∧ NoInv y' then hy.choose else 0

def gamGal (e : WD h → ℂˣ) (y : WD h) (x : ℂ) : ℂ :=
  (e (y.lpTwist (unrChar h (WD.unitOf x)⁻¹) (isSmooth_unrChar h _)) : ℂ) *
    ((lroots y).map fun c => 1 - c⁻¹ * x * ((normV w : ℕ) : ℂ) ^ (-(1 / 2 : ℂ))).prod /
    ((lroots y).map fun c => 1 - c * x⁻¹ * ((normV w : ℕ) : ℂ) ^ (-(1 / 2 : ℂ))).prod

end Galois

end GlobalTheory.RSGam

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HasPairGammaZeroIff
section
noncomputable section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker

namespace GlobalTheory.LocLanglands.GammaModel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isSelfDualFor [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {c : kˣ}
    (hψ : HasConductor ψ c) : ∃ μ : Measure k, IsSelfDualFor ψ μ := by
  let ν : Measure k := Measure.addHaar
  have fin : ∀ d : kˣ, ν {x | valuation k x ≤ valuation k (d : k)} ≠ ⊤ := fun d =>
    (IsNonarchimedeanLocalField.isCompact_closedBall k _).measure_lt_top.ne
  have pos : ∀ d : kˣ, ν {x | valuation k x ≤ valuation k (d : k)} ≠ 0 := fun d => by
    have ho : IsOpen {x : k | valuation k x ≤ valuation k (d : k)} := by
      have h1 : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
      have h2 : {x : k | valuation k x ≤ valuation k (d : k)} = (fun x => ((d⁻¹ : kˣ) : k) * x) ⁻¹' (𝒪[k] : Set k) := by
        ext y
        show _ ↔ valuation k (((d⁻¹ : kˣ) : k) * y) ≤ 1
        have : 0 < valuation k (d : k) := by simp [zero_lt_iff]
        simp [inv_mul_le_iff₀ this]
      rw [h2]; exact h1.preimage (by fun_prop)
    exact (ho.measure_pos ν ⟨0, by simp⟩).ne'
  have f1 := fin 1
  have p1 := pos 1
  simp only [Units.val_one, map_one] at f1 p1
  set a := ν {x | valuation k x ≤ 1}
  set b := ν {x | valuation k x ≤ valuation k (c : k)}
  have hab0 : a * b ≠ 0 := mul_ne_zero p1 (pos c)
  have habt : a * b ≠ ⊤ := ENNReal.mul_ne_top f1 (fin c)
  let t : ENNReal := (a * b) ^ (-(1 / 2) : ℝ)
  have ht0 : t ≠ 0 := by simp [t, ENNReal.rpow_eq_zero_iff, habt, hab0]
  have htt : t ≠ ⊤ := by simp [t, ENNReal.rpow_eq_top_iff, habt, hab0]
  refine ⟨t • ν, Measure.IsAddHaarMeasure.smul ν ht0 htt, c, hψ, ?_⟩
  simp only [Measure.smul_apply, smul_eq_mul]
  change t * a * (t * b) = 1
  have : t * t = (a * b)⁻¹ := by
    simp only [t]
    rw [← ENNReal.rpow_add _ _ hab0 habt, ← ENNReal.rpow_neg_one]; norm_num
  rw [mul_mul_mul_comm, this, ENNReal.inv_mul_cancel hab0 habt]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem arg_three_one (g : GL (Fin 1) k) (x : Fin 1 → Fin 1 → k) :
    (emb₂ k (stdSum (rfl : 1 + (1 + 1) = 3)) (g, 1) * lowUnip rfl (padRow x) *
        emb₂ k (stdSum (rfl : 1 + (1 + 1) = 3)) (1, longElt (1 + 1) k)).val =
      !![g.val 0 0, 0, 0; x 0 0, 0, 1; 0, 1, 0] := by
  have e0 : (stdSum (rfl : 1 + (1 + 1) = 3)).symm 0 = Sum.inl 0 := by decide
  have e1 : (stdSum (rfl : 1 + (1 + 1) = 3)).symm 1 = Sum.inr 0 := by decide
  have e2 : (stdSum (rfl : 1 + (1 + 1) = 3)).symm 2 = Sum.inr 1 := by decide
  have p0 : padRow x 0 0 = x 0 0 := rfl
  have p1 : padRow x 1 0 = 0 := rfl
  rw [Units.val_mul, Units.val_mul, val_emb₂, val_emb₂]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, lowUnip, longElt, e0, e1, e2, p0, p1, Fin.ext_iff]

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem lowUnip_zero {m r n : ℕ} (hn : m + r = n) : lowUnip hn (0 : Matrix (Fin r) (Fin m) k) = 1 := by
  ext1
  simp [lowUnip]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem longElt_one : longElt (0 + 1) k = 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [longElt]

theorem hasPairGamma_succ_iff {m : ℕ} {ψ : AddChar k Circle} {c : kˣ} (hψ : HasConductor ψ c)
    (π : Representation ℂ (GL (Fin (m + 1)) k) V) (τ : Representation ℂ (GL (Fin m) k) V') (e : ℂ) :
    HasPairGamma ψ π τ e ↔ HasPairEps ψ π τ e := by
  have key : ∀ [MeasurableSpace k] (μ : Measure k) (l : Module.Dual ℂ V) (v : V) (g : GL (Fin m) k),
      (∫ x : Fin 0 → Fin m → k, l (π (tilde (emb₂ k (stdSum (rfl : m + (0 + 1) = m + 1)) (g, 1) *
        lowUnip rfl (padRow x) * emb₂ k (stdSum (rfl : m + (0 + 1) = m + 1)) (1, longElt (0 + 1) k))) v)
          ∂(Measure.pi fun _ => Measure.pi fun _ => μ)) = l (π (tilde (corner g)) v) := by
    intro _ μ l v g
    have h0 : ∀ x : Fin 0 → Fin m → k, padRow x = 0 := fun x => by
      ext i j; fin_cases i; simp [padRow, Fin.snoc]
    simp only [h0, lowUnip_zero, longElt_one, mul_one]
    rw [show ((1, 1) : GL (Fin m) k × GL (Fin (0 + 1)) k) = 1 from rfl, map_one, mul_one, Measure.pi_of_empty]
    simp [corner]
  constructor
  · intro H ω hω l l' hl hl' I hI v v'
    borelize k
    obtain ⟨μ, hμ⟩ := exists_isSelfDualFor hψ
    have := H 0 rfl μ hμ ω hω l l' hl hl' I hI v v'
    simp only [key] at this
    simpa [corner] using this
  · intro H j hn _ _ μ hμ ω hω l l' hl hl' I hI v v'
    obtain rfl : j = 0 := by omega
    have := H ω hω l l' hl hl' I hI v v'
    simp only [key]
    simpa [corner] using this

theorem hasPairGamma_zero_iff {j : ℕ} {ψ : AddChar k Circle} {c : kˣ} (hψ : HasConductor ψ c)
    (π : Representation ℂ (GL (Fin (0 + (j + 1))) k) V) (hπ : IsGeneric ψ π) (e : ℂ) :
    HasPairGamma ψ π (detRep (Fin 0) 1) e ↔ e = 1 := by
  have h0 : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  have key : ∀ [MeasurableSpace k] (μ : Measure k) (l : Module.Dual ℂ V) (v : V) (g : GL (Fin 0) k),
      (∫ x : Fin j → Fin 0 → k, l (π (tilde (emb₂ k (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))) (g, 1) *
        lowUnip rfl (padRow x) * emb₂ k (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))) (1, longElt (j + 1) k))) v)
          ∂(Measure.pi fun _ => Measure.pi fun _ => μ)) = l v := by
    intro _ μ l v g
    have h1 : ∀ x : Fin j → Fin 0 → k, padRow x = 0 := fun x => Subsingleton.elim _ _
    have h2 : emb₂ k (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))) (1, longElt (j + 1) k) = longElt (0 + (j + 1)) k := by
      ext a b
      obtain ⟨a, rfl⟩ := (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))).surjective a
      obtain ⟨b, rfl⟩ := (stdSum (rfl : 0 + (j + 1) = 0 + (j + 1))).surjective b
      rw [val_emb₂]
      rcases a with a | a
      · exact a.elim0
      rcases b with b | b
      · exact b.elim0
      simp [longElt, Fin.ext_iff]
    have h3 : tilde (longElt (0 + (j + 1)) k) = 1 := by
      ext1
      have : (longElt (0 + (j + 1)) k).val.transpose = (longElt (0 + (j + 1)) k).val := by
        ext a b
        simp only [longElt, transpose_apply, of_apply]
        congr 1
        exact propext ⟨fun h => by simp [h], fun h => by simp [h]⟩
      change (longElt (0 + (j + 1)) k).val * (longElt (0 + (j + 1)) k).val.transpose = 1
      rw [this]; exact antidiag_mul_self _ _
    simp only [h1, lowUnip_zero, mul_one, h0 g, h2]
    rw [show ((1, 1) : GL (Fin 0) k × GL (Fin (j + 1)) k) = 1 from rfl, map_one, one_mul, h3]
    have hd : (Measure.pi fun _ : Fin 0 => μ) = Measure.dirac fun a => isEmptyElim a := Measure.pi_of_empty _ _
    rw [hd]
    simp
  constructor
  · intro H
    borelize k
    obtain ⟨μ, hμ⟩ := exists_isSelfDualFor hψ
    obtain ⟨l, hl0, hl⟩ := hπ
    obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
      by_contra h; push Not at h; exact hl0 (LinearMap.ext h)
    have := H j rfl μ hμ 1 (fun z v => by simp [detRep]) l LinearMap.id hl
      (fun u hu v => by simp [detRep, superDiag]) _ isInvIntegral_zero v 1
    simp only [key] at this
    rw [LinearMap.proj_apply, LinearMap.proj_apply,
      show ((1, 1) : GL (Fin 0) k × GL (Fin (j + 1)) k) = 1 from rfl, map_one (emb₂ k _)] at this
    simp [detRep] at this
    exact (mul_eq_right₀ hv).1 this.symm
  · rintro rfl j' hn _ _ μ hμ ω hω l l' hl hl' I hI v v'
    obtain rfl : j = j' := by omega
    have hω1 : ω (-1) = 1 := by
      have := hω (-1) 1
      simp [detRep] at this
      exact Units.ext (by simpa using this.symm)
    simp only [key, hω1]
    simp only [Units.val_one, one_pow, one_mul]
    congr 1
    funext g
    rw [h0 (tilde g), h0 g, show ((1, 1) : GL (Fin 0) k × GL (Fin (j + 1)) k) = 1 from rfl, map_one]
    simp

end GlobalTheory.LocLanglands.GammaModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableOfCharOne
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N t : ℕ}

namespace IrrGL

def IsEssSqInt (x : IrrGL k) : Prop :=
  ∃ (δ : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), UnitaryDual.IsSquareIntegrable δ ∧ x = δ.tw χ hχ

theorem IsEssSqInt.tw {x : IrrGL k} (h : x.IsEssSqInt) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : (x.tw χ hχ).IsEssSqInt := by
  obtain ⟨δ, ψ, hψ, hδ, rfl⟩ := h
  exact ⟨δ, ψ * χ, hψ.mul hχ, hδ, tw_tw _ _ _ _ _⟩

theorem IsEssSqInt.nu {x : IrrGL k} (h : x.IsEssSqInt) (s : ℂ) : (x.nu s).IsEssSqInt := h.tw _ _

end IrrGL

def IsBoxSum (x : Fin t → IrrGL k) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ (Δ : Fin t → Segment k) (σ : Equiv.Perm (Fin t)) (hd : ∑ a, (x (σ a)).1 = N),
    (∀ i, IsLSeg (Δ i) (x i).rep) ∧ (∀ i j, i < j → ¬ (Δ (σ i)).Precedes (Δ (σ j))) ∧
      IsCosocle π (prodIrr (fun a => x (σ a)) hd)

def IsGenSpeh (π₀ : IrrGL k) (t : ℕ) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  π₀.IsCusp ∧ IsUnitarisable π₀.rep ∧ 0 < t ∧ IsBoxSum (spehFactor π₀ t) π

section BoxSum

variable {x : Fin t → IrrGL k} {π : Representation ℂ (GL (Fin N) k) V}

theorem IsBoxSum.of_equiv (h : IsBoxSum x π) {σ' : Representation ℂ (GL (Fin N) k) W} (φ : π.Equiv σ') :
    IsBoxSum x σ' := by
  obtain ⟨Δ, σ, hd, hL, hP, hc⟩ := h
  exact ⟨Δ, σ, hd, hL, hP, hc.of_equiv φ (.refl _)⟩

theorem IsBoxSum.sum_fst (h : IsBoxSum x π) : ∑ a, (x a).1 = N := by
  obtain ⟨-, σ, hd, -⟩ := h
  rw [← hd]
  exact (Equiv.sum_comp σ (fun a => (x a).1)).symm

theorem isBoxSum_single {y : IrrGL k} {Δ : Segment k} (hΔ : IsLSeg Δ y.rep) :
    IsBoxSum (fun _ : Fin 1 => y) y.rep := by
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_one y (by simp)
  exact ⟨fun _ => Δ, Equiv.refl _, by simp, fun _ => hΔ, fun i j hij => absurd (Subsingleton.elim i j) hij.ne,
    (isCosocle_self y.2.rep.irr).of_equiv (.refl _) φ⟩

end BoxSum

section GenSpeh

theorem IsGenSpeh.of_equiv {π₀ : IrrGL k} {π : Representation ℂ (GL (Fin N) k) V} (h : IsGenSpeh π₀ t π)
    {σ : Representation ℂ (GL (Fin N) k) W} (φ : π.Equiv σ) : IsGenSpeh π₀ t σ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.of_equiv φ⟩

theorem IsGenSpeh.mul_eq {π₀ : IrrGL k} {π : Representation ℂ (GL (Fin N) k) V} (h : IsGenSpeh π₀ t π) :
    t * π₀.1 = N := by
  rw [← h.2.2.2.sum_fst]
  simp [spehFactor]

example : ¬ IsGenSpeh (IrrGL.ofChar (1 : kˣ →* ℂˣ) isSmoothChar_one) 1 (detRep (Fin 2) (1 : kˣ →* ℂˣ)) := fun h => by
  have := h.mul_eq
  simp [IrrGL.ofChar] at this

example (π₀ : IrrGL k) (π : Representation ℂ (GL (Fin 0) k) V) : ¬ IsGenSpeh π₀ 0 π := fun h => h.2.2.1.false

example : IsBoxSum (fun _ : Fin 1 => IrrGL.ofChar (1 : kˣ →* ℂˣ) isSmoothChar_one)
    (IrrGL.ofChar (1 : kˣ →* ℂˣ) isSmoothChar_one).rep :=
  isBoxSum_single (single_spec (IrrGL.isCusp_ofChar _ _)).2.1

end GenSpeh

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.DefiniteBC

namespace GlobalTheory.FormDict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def recT {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (T : GlobalTheory.RowTie.WDTie N A)
    (hL : GlobalTheory.Published.LocalLanglandsGL) : RecMap A :=
  fun w _ σ => (T.e w).symm (ParLaws.locRec hL (N.plOm.2 w) (GlobalTheory.LocLanglands.cls (ParLaws.toRep σ)))

end GlobalTheory.FormDict

end
end

