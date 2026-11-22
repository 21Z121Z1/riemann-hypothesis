import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0049
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemStabGLAdeleIff
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0454
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0455
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0453
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMoves
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.LevMove

section General

open Formalism.MainNotions.StandardLattice (latHat intAf)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in

theorem int_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) {f : FiniteAdeleRing (𝓞 F) F} (hf : f ∈ intAf F)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ latHat F E (L : Set (Fin n → E))) :
    (f ⊗ₜ[F] (1 : E)) • z ∈ latHat F E (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨f * a, fun v => ?_, x, hx, ?_⟩
    · rw [map_mul]; exact mul_mem (hf v) (ha v)
    · funext i
      change (f ⊗ₜ[F] (1 : E)) * a ⊗ₜ x i = (f * a) ⊗ₜ x i
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

omit [NumberField E] in

theorem ideal_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) {c : 𝓞 E} (hc : c ∈ 𝔪)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ latHat F E (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E)) • z ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, c • x, Submodule.smul_mem_smul hc hx, ?_⟩
    funext i
    change ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c : E)) * a ⊗ₜ x i = a ⊗ₜ ((c : E) * x i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem inv_int_at {c : 𝓞 F} (v : HeightOneSpectrum (𝓞 F)) (hv : c ∉ v.asIdeal) :
    evalV F v (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((c : F)⁻¹)) ∈ v.adicCompletionIntegers F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F c) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 hv
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = v.valuation F (c : F) :=
    v.valuedAdicCompletion_eq_valuation' (K := F) (c : F)
  have h3 : algebraMap F (Fv F v) ((c : F)⁻¹) = (algebraMap F (v.adicCompletion F) (c : F))⁻¹ := map_inv₀ _ _
  rw [h3, map_inv₀, h2]
  change (v.valuation F (algebraMap (𝓞 F) F c))⁻¹ ≤ 1
  rw [h1, inv_one]

theorem vanish_smul_mem (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) {c : 𝓞 F} (hc0 : c ≠ 0)
    (hc : algebraMap (𝓞 F) (𝓞 E) c ∈ 𝔪) {f : FiniteAdeleRing (𝓞 F) F} (hf : f ∈ intAf F)
    (hfc : ∀ v : HeightOneSpectrum (𝓞 F), c ∈ v.asIdeal → evalV F v f = 0)
    {z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hz : z ∈ latHat F E (L : Set (Fin n → E))) :
    (f ⊗ₜ[F] (1 : E)) • z ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  set b : FiniteAdeleRing (𝓞 F) F := algebraMap F (FiniteAdeleRing (𝓞 F) F) ((c : F)⁻¹) * f with hbdef
  have hb : b ∈ intAf F := fun v => by
    by_cases hv : c ∈ v.asIdeal
    · rw [hbdef, map_mul, hfc v hv, mul_zero]; exact zero_mem _
    · rw [hbdef, map_mul]; exact mul_mem (inv_int_at v hv) (hf v)
  have hcF : (c : F) ≠ 0 := fun h => hc0 (RingOfIntegers.coe_injective (by simpa using h))
  have hfb : (f ⊗ₜ[F] (1 : E) : FiniteAdeleRing (𝓞 F) F ⊗[F] E) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((algebraMap (𝓞 F) (𝓞 E) c : 𝓞 E) : E)) * (b ⊗ₜ[F] (1 : E)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    change f ⊗ₜ[F] (1 : E) = b ⊗ₜ[F] (algebraMap F E (c : F))
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', hbdef,
      Algebra.smul_def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hcF, map_one, one_mul]
  rw [hfb, mul_smul]
  exact ideal_smul_mem L 𝔪 hc (int_smul_mem L hb hz)

end General

end GlobalTheory.Ker.LevMove

namespace GlobalTheory.Ker.LevMove

section Core

open Formalism.MainNotions.StandardLattice (latHat intAf)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem exists_ind (v : HeightOneSpectrum (𝓞 F)) : ∃ α : FiniteAdeleRing (𝓞 F) F,
    evalV F v α = 1 ∧ ∀ w, w ≠ v → evalV F w α = 0 := by
  obtain ⟨e, h1, h0⟩ := GlobalTheory.UnRep.SmallMat.exists_indicator ({v} : Finset (HeightOneSpectrum (𝓞 F)))
  exact ⟨e, h1 v (Finset.mem_singleton_self v), fun w hw => h0 w (by simpa using hw)⟩

theorem ind_int {v : HeightOneSpectrum (𝓞 F)} {α : FiniteAdeleRing (𝓞 F) F} (h1 : evalV F v α = 1)
    (h0 : ∀ w, w ≠ v → evalV F w α = 0) : α ∈ intAf F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [h1]; exact one_mem _
  · rw [h0 w hw]; exact zero_mem _

theorem mem_of_vanish (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (h𝔪 : 𝔪 ≠ ⊥)
    {x : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hx : x ∈ latHat F E (L : Set (Fin n → E)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal →
      ∀ α : FiniteAdeleRing (𝓞 F) F, evalV F v α = 1 → (∀ w, w ≠ v → evalV F w α = 0) →
        (α ⊗ₜ[F] (1 : E)) • x = 0) :
    x ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  set N := Ideal.absNorm 𝔪 with hNdef
  have hN0 : N ≠ 0 := fun h => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h)
  have hNE : ((N : 𝓞 E)) ∈ 𝔪 := Ideal.absNorm_mem 𝔪
  set c₁ : 𝓞 F := (N : 𝓞 F) with hc₁
  have hc₁0 : c₁ ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hc₁m : algebraMap (𝓞 F) (𝓞 E) c₁ ∈ 𝔪 := by rw [hc₁, map_natCast]; exact hNE
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {c₁}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  set P := hfin.toFinset with hP
  have hmemP : ∀ v, v ∈ P ↔ c₁ ∈ v.asIdeal := fun v => by
    rw [hP, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  choose ind hind1 hind0 using (exists_ind (F := F))
  set e₁ : FiniteAdeleRing (𝓞 F) F := ∑ v ∈ P, ind v with he₁
  have hev : ∀ w, evalV F w e₁ = if w ∈ P then 1 else 0 := fun w => by
    rw [he₁, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single w (fun b _ hb => hind0 b w (Ne.symm hb)) (fun h => absurd hw h), hind1]
    · exact Finset.sum_eq_zero fun b hb => hind0 b w (fun h => hw (h ▸ hb))
  have hsplit : x = ((1 - e₁) ⊗ₜ[F] (1 : E)) • x + ∑ v ∈ P, (ind v ⊗ₜ[F] (1 : E)) • x := by
    rw [← Finset.sum_smul, ← TensorProduct.sum_tmul, ← he₁, ← add_smul, ← TensorProduct.add_tmul, sub_add_cancel,
      Algebra.TensorProduct.one_def.symm, one_smul]
  rw [hsplit]
  refine add_mem ?_ (sum_mem fun v hv => ?_)
  · refine vanish_smul_mem L 𝔪 hc₁0 hc₁m (fun w => ?_) (fun w hw => ?_) hx
    · rw [map_sub, map_one, hev]; split_ifs
      · rw [sub_self]; exact zero_mem _
      · rw [sub_zero]; exact one_mem _
    · rw [map_sub, map_one, hev, if_pos ((hmemP w).2 hw), sub_self]
  · by_cases hI : 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal
    · rw [hloc v hI (ind v) (hind1 v) (hind0 v)]; exact zero_mem _
    · obtain ⟨c, hc, hcv⟩ := SetLike.not_le_iff_exists.1 hI
      have hc0 : c ≠ 0 := fun h => hcv (h ▸ zero_mem _)
      refine vanish_smul_mem L 𝔪 hc0 hc (ind_int (hind1 v) (hind0 v)) (fun w hw => hind0 v w ?_) hx
      rintro rfl; exact hcv hw

end Core

end GlobalTheory.Ker.LevMove

namespace GlobalTheory.Ker.LevMove

variable {D : D7}

theorem fmt_mul' (V : HSp D) (g g' : GA D V) : fmt V (g * g') = fmt V g * fmt V g' := by
  simp only [fmt, Formalism.L2.Theta.mt, map_mul, Units.val_mul, Matrix.map_mul]

theorem fmt_one' (V : HSp D) : fmt V 1 = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem smul_fmt_sub_one {T : HSp D} {I : Ideal (𝓞 D.host.F)} {g : GA D T} (h : TrivAt T I g)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : I ≤ v.asIdeal) {α : Af D.host.F} (h1 : evalV D.host.F v α = 1)
    (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    ((α ⊗ₜ[D.host.F] (1 : D.host.E) : AfE D)) • (fmt T g - 1) = 0 := by
  ext i j
  have := congrArg (finPart D) (h v hv (pairA D.host.F 0 α) ⟨α, rfl, h1, h0⟩ i j)
  rw [map_mul, map_zero] at this
  have e1 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) =
    α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  have e2 : finPart D ((mt T g - 1) i j) = (fmt T g - 1) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
    congr 1
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [e1, e2] at this
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  exact this

theorem smul_algebra {R : Type} [CommRing R] {k : ℕ} (P : R) (A A' B : Matrix (Fin k) (Fin k) R)
    (hA : P • A = P • 1) (hB : P • B = P • 1) (e : A * A' = 1) : P • (A' * B - 1) = 0 := by
  have h' : P • A' = P • 1 := by
    calc P • A' = (P • 1) * A' := by rw [Matrix.smul_mul, one_mul]
      _ = (P • A) * A' := by rw [hA]
      _ = P • 1 := by rw [Matrix.smul_mul, e]
  rw [smul_sub, ← Matrix.smul_mul, h', Matrix.smul_mul, one_mul, hB, sub_self]

theorem smul_vec {R : Type} [CommRing R] {k : ℕ} (P : R) (M : Matrix (Fin k) (Fin k) R) (u : Fin k → R)
    (h : P • (M - 1) = 0) : P • (M *ᵥ u - u) = 0 := by
  have : M *ᵥ u - u = (M - 1) *ᵥ u := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [this, ← Matrix.smul_mulVec, h, Matrix.zero_mulVec]

end GlobalTheory.Ker.LevMove

theorem GlobalTheory.Ker.LevMove.levK_of_two_moves : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ L → C.LevK Lv (g₁⁻¹ * g₂) 1 := by
  intro D S T C Lv g₁ g₂ L h1 h2 t1 t2 hL m1 m2
  have hfull : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have e1 : fmt T g₁ * fmt T g₁⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  have e2 : fmt T g₂ * fmt T g₂⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  obtain ⟨-, -, -, laws⟩ := GlobalTheory.Ker.isMov_laws D T.rank C.X.Λ hfull
  obtain ⟨-, hb1, -, -, -⟩ := (laws _ _ e1).2 L hL m1
  obtain ⟨-, -, -, hcomp, -⟩ := (laws _ _ e2).2 L hL m2
  have hk : IsMov (fmt T (g₁⁻¹ * g₂)) C.X.Λ C.X.Λ := by
    rw [GlobalTheory.Ker.LevMove.fmt_mul']; exact hcomp _ _ hb1
  refine ⟨mul_mem (inv_mem h1) h2, hk, 1, ?_, fun i => ?_⟩
  · rw [OneMemClass.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · have hs : ∑ j, (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) j i • Lv.β j = Lv.β i := by
      simp [Matrix.one_apply]
    rw [hs]
    have hb : toAf (Lv.β i) ∈ hatV C.X.Λ :=
      AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, Lv.β i, Lv.β_mem i, rfl⟩
    refine GlobalTheory.Ker.LevMove.mem_of_vanish (F := D.host.F) C.X.Λ Lv.𝔪 Lv.ne_bot
      (sub_mem ((hk _).2 ⟨_, hb, rfl⟩) hb) ?_
    intro v hv α a1 a0
    have P1 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t1 hv a1 a0
    have P2 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t2 hv a1 a0
    set P : AfE D := α ⊗ₜ[D.host.F] (1 : D.host.E) with hPdef
    have q1 : P • fmt T g₁ = P • 1 := by rw [smul_sub] at P1; exact sub_eq_zero.1 P1
    have q2 : P • fmt T g₂ = P • 1 := by rw [smul_sub] at P2; exact sub_eq_zero.1 P2
    have q : P • (fmt T (g₁⁻¹ * g₂) - 1) = 0 := by
      rw [GlobalTheory.Ker.LevMove.fmt_mul']
      exact GlobalTheory.Ker.LevMove.smul_algebra P _ _ _ q1 q2 e1
    exact GlobalTheory.Ker.LevMove.smul_vec P _ _ q
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalLatticeEqIffIdempotentComponentsOver
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocHat

open GlobalTheory.StdFrames (cpt cpt_ext toAd_spec)

variable {D : D7} {n : ℕ}

theorem mem_hat_iff_locL {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG) (y : Fin n → EAf D) :
    y ∈ hat Λ ↔ ∀ v : HeightOneSpectrum (𝓞 D.host.F),
      (fun i => Formalism.UG.prV (E := D.host.E) v (y i)) ∈ Formalism.L2.Herm.locL v Λ := by
  haveI : Module.Finite (𝓞 D.host.E) Λ := Module.Finite.iff_fg.mpr h
  rw [mem_hat]
  exact GlobalTheory.LatticeStabLocal.mem_latS_adele_iff Λ y

theorem prV_eq_zero_iff_cpt (v : HeightOneSpectrum (𝓞 D.host.F)) (z : EAf D) :
    Formalism.UG.prV (E := D.host.E) v z = 0 ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → cpt Q z = 0 := by
  refine (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (toAd_spec D) v z).trans ?_
  exact Iff.rfl

theorem mem_hat_iff_of_supp {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG)
    (v : HeightOneSpectrum (𝓞 D.host.F)) {y : Fin n → EAf D}
    (hy : ∀ w, w ≠ v → ∀ i, Formalism.UG.prV (E := D.host.E) w (y i) = 0) :
    y ∈ hat Λ ↔ (fun i => Formalism.UG.prV (E := D.host.E) v (y i)) ∈ Formalism.L2.Herm.locL v Λ := by
  rw [mem_hat_iff_locL h]
  refine ⟨fun H => H v, fun H w => ?_⟩
  by_cases hwv : w = v
  · subst hwv
    exact H
  · have hz : (fun i => Formalism.UG.prV (E := D.host.E) w (y i)) = 0 := by
      ext i
      exact hy w hwv i
    rw [hz]
    exact Submodule.zero_mem _
set_option maxHeartbeats 800000 in

theorem locL_le {Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG) (h' : Λ'.FG)
    (v : HeightOneSpectrum (𝓞 D.host.F))
    (H : ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ → idem Q • y ∈ hat Λ') :
    Formalism.L2.Herm.locL v Λ ≤ Formalism.L2.Herm.locL v Λ' := by
  obtain ⟨e, -, -, he1, he0⟩ :=
    GlobalTheory.StdFrames.exists_idem (D := D) {Q : Pl D.host.E | Q.under (𝓞 D.host.F) = v}

  have hpe : Formalism.UG.prV (E := D.host.E) v e = 1 := by
    have h0 : Formalism.UG.prV (E := D.host.E) v (e - 1) = 0 := by
      rw [prV_eq_zero_iff_cpt]
      intro Q hQ
      rw [map_sub, map_one, he1 Q hQ, sub_self]
    rwa [map_sub, map_one, sub_eq_zero] at h0

  have key : ∀ x ∈ Λ, (e • fun i => inc D (x i)) ∈ hat Λ' := by
    intro x hx
    refine mem_hat_of_idem h' fun w => ?_
    rw [smul_smul]
    by_cases hw : w.under (𝓞 D.host.F) = v
    · have hwe : idem w * e = idem w := by
        refine cpt_ext fun Q => ?_
        rw [map_mul]
        by_cases hQ : Q = w
        · subst hQ
          rw [cpt_idem_self, he1 Q hw, one_mul]
        · rw [cpt_idem_ne hQ, zero_mul]
      rw [hwe]
      exact H w hw _ (smul_mem_hat (idem_mem w) (inc_mem_hat hx))
    · have hwe : idem w * e = 0 := by
        refine cpt_ext fun Q => ?_
        rw [map_mul, map_zero]
        by_cases hQ : Q = w
        · subst hQ
          rw [he0 Q hw, mul_zero]
        · rw [cpt_idem_ne hQ, zero_mul]
      rw [hwe, zero_smul]
      exact zero_mem_hat

  unfold Formalism.L2.Herm.locL Formalism.UG.latS
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  have hm := (mem_hat_iff_locL h' _).mp (key x hx) v
  have hxe : (fun i => Formalism.UG.prV (E := D.host.E) v ((e • fun i => inc D (x i)) i)) =
      fun i => Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) (x i) := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hpe, one_mul]
    rw [Formalism.UG.P.afsplit_prV_inclE]
  rw [hxe] at hm
  exact hm

theorem prV_idem_smul {v : HeightOneSpectrum (𝓞 D.host.F)} {Q : Pl D.host.E} (hQ : Q.under (𝓞 D.host.F) = v)
    (y : Fin n → EAf D) : ∀ w, w ≠ v → ∀ i, Formalism.UG.prV (E := D.host.E) w ((idem Q • y) i) = 0 := by
  intro w hw i
  have hQw : Formalism.UG.prV (E := D.host.E) w (idem Q) = 0 := by
    rw [prV_eq_zero_iff_cpt]
    intro Q' hQ'
    apply cpt_idem_ne
    intro hEq
    subst hEq
    exact hw (hQ'.symm.trans hQ)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, hQw, zero_mul]

theorem locL_eq_iff_idem : ∀ (D : D7) (n : ℕ) (Λ Λ' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Λ.FG → Λ'.FG → ∀ v : HeightOneSpectrum (𝓞 D.host.F), Formalism.L2.Herm.locL v Λ = Formalism.L2.Herm.locL v Λ' ↔ ∀ Q : Pl D.host.E, Q.under (𝓞 D.host.F) = v → ∀ y : Fin n → EAf D, idem Q • y ∈ hat Λ ↔ idem Q • y ∈ hat Λ' := by
  intro D n Λ Λ' h h' v
  constructor
  · intro heq Q hQ y
    rw [mem_hat_iff_of_supp h v (prV_idem_smul hQ y), mem_hat_iff_of_supp h' v (prV_idem_smul hQ y), heq]
  · intro H
    exact le_antisymm (locL_le h h' v fun Q hQ y => (H Q hQ y).mp)
      (locL_le h' h v fun Q hQ y => (H Q hQ y).mpr)

end GlobalTheory.LocHat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeConjRead

open Classical

variable {D : D7}

def colMat {n : ℕ} (w : Fin n → Fin n → EAf D) : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => w j i

def pairAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) :
    Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D :=
  if GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 then
    flagV D.R.rS D.R.k (Yc D 0).rank (f0T X h) (e0T X h) (bwdT X h) (z0T X h)
  else flagV D.R.rS D.R.k (Yc D 0).rank (f0T X h) (e0T X h) (fun i => bwT X h (Fin.rev i)) (z0T X h)

def hY (D : D7) (x y : Fin (Yc D 0).rank → EAf D) : EAf D :=
  Formalism.UG.hform (GlobalTheory.StdFrames.sg D) (GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram) x y

def SmallAt (PP : Pl D.host.E) (x : EAf D) : Prop := Valued.v (GlobalTheory.StdFrames.cpt PP x) < 1

def PairTable {M A : Type} [Ring A] (p : M → M → A) (sm : A → Prop) {ρ k : ℕ} (e f : Fin ρ → M) (b b' : Fin k → M)
    (z : M) : Prop :=
  (∀ a c, sm (p (f a) (e c) - if a = c then 1 else 0)) ∧ (∀ a j, sm (p (f a) (b j))) ∧ (∀ a, sm (p (f a) z)) ∧
  (∀ a c, sm (p (f a) (f c))) ∧
  (∀ i a, sm (p (b' i) (e a))) ∧ (∀ i j, sm (p (b' i) (b j) - if i = j then 1 else 0)) ∧ (∀ i, sm (p (b' i) z)) ∧
  (∀ i a, sm (p (b' i) (f a))) ∧
  (∀ a, sm (p z (e a))) ∧ (∀ j, sm (p z (b j))) ∧ sm (p z z + 1) ∧ (∀ a, sm (p z (f a))) ∧
  (∀ a c, sm (p (e a) (e c))) ∧ (∀ a j, sm (p (e a) (b j))) ∧ (∀ a, sm (p (e a) z)) ∧
  (∀ a c, sm (p (e a) (f c) - if a = c then 1 else 0))

def sgnD {A : Type} [Ring A] (ρ k : ℕ) {n : ℕ} (a : Fin n) : A := if a.1 = ρ + k then -1 else 1

end GlobalTheory.SeeConjRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerModelSymplecticEqOrientedPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerModel_symplectic_eq_orientedPair : ∀ (D : D7) (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d),
    Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram → Ws.J = D.host.xi0 • reindex e e X.gramᵀ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ u v, GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J) u v = symplO (sgn ε S) X (cS u) (cS v) := by
  first | exact @GlobalTheory.SquareAgree.SympForm.symp_model_eq_symplO | exact GlobalTheory.SquareAgree.SympForm.symp_model_eq_symplO | (intros; apply GlobalTheory.SquareAgree.SympForm.symp_model_eq_symplO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChainStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepVector_lift_pair_flagLevel_realized_chain : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.chain_ωY → R.chain_vY → ∀ t k, k + 1 < D.R.m → ∀ (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) g0 κ → IsLevelLift (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) g0 κ' → (levChi _ (R.βY k) (flagL (R.datYt t k R.triv)) κ)⁻¹ • R.ωY t k (κ, κ') (R.vY t k) = (levChi _ (R.βY (k + 1)) (flagL (R.datYt t (k + 1) R.triv)) κ')⁻¹ • R.vY t k := by
  first | exact @GlobalTheory.StepVecLaw.stepVec_lifts | exact GlobalTheory.StepVecLaw.stepVec_lifts | (intros; apply GlobalTheory.StepVecLaw.stepVec_lifts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralConvergentDefiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_convergent_definite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), GlobalTheory.FunPr.Hypotheses₂ → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ i, Xs i ∈ lieAt T (τs i)) → ∀ h : GA D T, ContDiff ℝ ∞ fun t : Fin k → ℝ => (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) (h * (List.ofFn fun i => oneP θ T (τs i) (Xs i) (t i)).prod) := by
  first | exact @GlobalTheory.DefLiftSmooth.lift_smooth | exact GlobalTheory.DefLiftSmooth.lift_smooth | (intros; apply GlobalTheory.DefLiftSmooth.lift_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralMeasurableDefiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_measurable_definite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), GlobalTheory.FunPr.Hypotheses₂ → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ W : Submodule ℂ (GA D T → ℂ), FiniteDimensional ℂ W ∧ (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ T τ k f ∈ W := by
  first | exact @GlobalTheory.DefiniteLiftZfin.lift_zfin | exact GlobalTheory.DefiniteLiftZfin.lift_zfin | (intros; apply GlobalTheory.DefiniteLiftZfin.lift_zfin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralUnfoldingDefiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_unfolding_definite : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), GlobalTheory.FunPr.Hypotheses₂ → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC T, ‖(l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν)) (x * g)‖ ≤ C * normInf θ T g ^ N := by
  first | exact @GlobalTheory.LiftGrowthDef.lift_growth | exact GlobalTheory.LiftGrowthDef.lift_growth | (intros; apply GlobalTheory.LiftGrowthDef.lift_growth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftCuspFormAutomorphicSmoothModerateGrowthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_cuspForm_automorphic_smooth_moderateGrowth : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D := by
  first | exact @GlobalTheory.Chain.LiftReg.liftProps_obj | exact GlobalTheory.Chain.LiftReg.liftProps_obj | (intros; apply GlobalTheory.Chain.LiftReg.liftProps_obj <;> assumption)
end

