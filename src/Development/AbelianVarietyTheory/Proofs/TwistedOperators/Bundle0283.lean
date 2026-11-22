import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevContinuousModelRepOfSobolevBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SobFrame

section Conj

variable {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ}

theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dRep (fun g => σ (P * g * P⁻¹)) (P⁻¹ * X * P) w = dRep σ X w := by
  unfold dRep
  simp only [exp_smul_conj_inv hP, conj_cancel hP]

theorem foldr_dRep_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) (w : H) :
    (l.map fun X => P⁻¹ * X * P).foldr (dRep fun g => σ (P * g * P⁻¹)) w = l.foldr (dRep σ) w := by
  induction l with
  | nil => rfl
  | cons X l ih => simp only [List.map_cons, List.foldr_cons, ih, dRep_conj_inv hP]

theorem smoothVec_conj_inv (hP : IsUnit P) {A B : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hAB : ∀ X ∈ A, P⁻¹ * X * P ∈ B) {w : H} (hw : SmoothVec B (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec A σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => hAB _ (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

end Conj

theorem conj_mem_lieAt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) :
    (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
  have hX' : Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X = 0 := hX
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
  rw [← M.fr_gram τ]
  have e : ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) +
      (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * X * M.fr τ) =
      (M.fr τ)ᴴ * ((Xᴴ * Formalism.REAL.Jm (M.ε τ) + Formalism.REAL.Jm (M.ε τ) * X) * M.fr τ) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hc, Matrix.mul_nonsing_inv_cancel_left _ _ hd,
      Matrix.add_mul, Matrix.mul_add]
  rw [e, hX', Matrix.zero_mul, Matrix.mul_zero]

theorem sobCont_rep_of_bound : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ)
    (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ X ∈ l, X ∈ GlobalTheory.SmoothGlob.lieSet (M.ε τ)) →
    (∀ w, SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w → ‖ℓ w‖ ≤ C * GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w) →
    Sobolev₂ (lieAt V τ) (M.rep τ) ℓ := by
  intro D V S M τ ℓ L C hL hC
  have hP := M.fr_unit τ
  refine ⟨L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ), C, ?_, fun w hw => ?_⟩
  · intro l hl X hX
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
    obtain ⟨X₀, hX₀, rfl⟩ := List.mem_map.1 hX
    exact conj_mem_lieAt M τ (hL l₀ hl₀ X₀ hX₀)
  · have hw' : SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w :=
      smoothVec_conj_inv (σ := M.σ τ) hP (fun _ hX => conj_mem_lieAt M τ hX) hw
    have hs : ((L.map (List.map fun X => (M.fr τ)⁻¹ * X * M.fr τ)).map
        fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum = GlobalTheory.SmoothGlob.sobNorm (M.σ τ) L w := by
      unfold GlobalTheory.SmoothGlob.sobNorm
      rw [List.map_map]
      congr 1
      refine List.map_congr_left fun l _ => ?_
      exact congrArg norm (foldr_dRep_conj_inv (σ := M.σ τ) hP l w)
    rw [hs]
    exact hC w hw'

end GlobalTheory.SobFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitInclMemExtSubIff
section
noncomputable section

namespace GlobalTheory.SplitFlag

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions GlobalTheory.AdelicU GlobalTheory.Cusp
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)}

def wPart (τ : E →ₐ[F] Fv F v) (W : Submodule E V.V) : Submodule (Fv F v) (Fin V.rank → Fv F v) where
  carrier := splitVec τ '' (extSub (F := F) V (Fv F v) W : Set (Fin V.rank → Fv F v ⊗[F] E))
  zero_mem' := ⟨0, zero_mem _, funext fun _ => map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    exact ⟨y + z, add_mem hy hz, splitVec_add τ y z⟩
  smul_mem' := by
    rintro c _ ⟨y, hy, rfl⟩
    refine ⟨algebraMap (Fv F v) (Fv F v ⊗[F] E) c • y, Submodule.smul_mem _ _ hy, ?_⟩
    rw [splitVec_smul, AlgHom.commutes]
    rfl

theorem splitVec_mem_wPart (τ : E →ₐ[F] Fv F v) {W : Submodule E V.V} {y : Fin V.rank → Fv F v ⊗[F] E}
    (hy : y ∈ extSub (F := F) V (Fv F v) W) : splitVec τ y ∈ wPart τ W := ⟨y, hy, rfl⟩

theorem wPart_mono (τ : E →ₐ[F] Fv F v) {A B : Submodule E V.V} (h : A ≤ B) : wPart τ A ≤ wPart τ B := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, GlobalTheory.Cusp.extSub_mono V _ h hy, rfl⟩

section Perp

theorem le_perp_perp (W : Submodule E V.V) : W ≤ perp V (perp V W) := fun y hy =>
  GlobalTheory.Cusp.mem_perp.2 fun x hx => by
    have := GlobalTheory.Cusp.mem_perp.1 hx y hy
    simp only [HSpace.hD] at this ⊢
    rw [← V.herm.eq, this, map_zero]

theorem perp_perp (W : Submodule E V.V) : perp V (perp V W) = W := by
  refine (Submodule.eq_of_le_of_finrank_eq (le_perp_perp W) ?_).symm
  have h1 := GlobalTheory.IsoDim.finrank_perp_add V W
  have h2 := GlobalTheory.IsoDim.finrank_perp_add V (perp V W)
  omega

end Perp

section Split

variable (hc : CMData F E) (h : IsCMExt F E hc.sig) (τ : E →ₐ[F] Fv F v)

include h in

theorem mem_extSub_iff_split {W : Submodule E V.V} {y : Fin V.rank → Fv F v ⊗[F] E} :
    y ∈ extSub (F := F) V (Fv F v) W ↔
      splitVec τ y ∈ wPart τ W ∧ splitVec (τ.comp hc.sig) y ∈ wPart (τ.comp hc.sig) W := by
  refine ⟨fun hy => ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩, fun ⟨⟨y₁, h₁, e₁⟩, ⟨y₂, h₂, e₂⟩⟩ => ?_⟩
  rw [← (splitVecEquiv h τ).symm_apply_apply y]
  change splitIncl h τ (splitVec τ y) + splitIncl h (τ.comp hc.sig) (splitVec (τ.comp hc.sig) y) ∈ _
  rw [← e₁, ← e₂, splitIncl_splitVec, splitIncl_splitVec]
  exact add_mem (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)

include h in
theorem splitIncl_mem_extSub_iff {W : Submodule E V.V} {u : Fin V.rank → Fv F v} :
    splitIncl h τ u ∈ extSub (F := F) V (Fv F v) W ↔ u ∈ wPart τ W := by
  rw [mem_extSub_iff_split hc h τ, splitVec_splitIncl, splitVec_comp_splitIncl]
  exact and_iff_left (zero_mem _)

end Split

section Dual

variable (hc : CMData F E) (h : IsCMExt F E hc.sig) (hJ : IsHermND hc.sig V.gram) (τ : E →ₐ[F] Fv F v)

include h hJ in

theorem mem_wPart_comp_iff {W : Submodule E V.V} {u' : Fin V.rank → Fv F v} :
    u' ∈ wPart (τ.comp hc.sig) W ↔ ∀ u ∈ wPart τ (perp V W), u' ⬝ᵥ V.gram.map τ *ᵥ u = 0 := by
  rw [← splitIncl_mem_extSub_iff hc h (τ.comp hc.sig)]
  conv_lhs => rw [← perp_perp W]
  rw [GlobalTheory.Cusp.mem_extSub_perp hc V]
  constructor
  · rintro H _ ⟨x, hx, rfl⟩
    have := congrArg (splitProj (τ.comp hc.sig)) (H x hx)
    change splitProj (τ.comp hc.sig) (hLin hc.sig V.gram (Fv F v) (splitIncl h (τ.comp hc.sig) u') x) = _ at this
    rwa [splitProj_comp_hLin h hJ, splitVec_splitIncl, map_zero] at this
  · intro H x hx
    change hLin hc.sig V.gram (Fv F v) (splitIncl h (τ.comp hc.sig) u') x = 0
    refine split_ext h τ ?_ ?_
    · rw [splitProj_hLin, splitVec_splitIncl_comp, map_zero, Matrix.mulVec_zero, dotProduct_zero]
    · rw [splitProj_comp_hLin h hJ, splitVec_splitIncl, map_zero]
      exact H _ ⟨x, hx, rfl⟩

end Dual

section Chain

def flagChain (𝔉 : IsoFlag V) (τ : E →ₐ[F] Fv F v) (j : Fin (2 * 𝔉.k + 2)) :
    Submodule (Fv F v) (Fin V.rank → Fv F v) :=
  if hj : (j : ℕ) ≤ 𝔉.k then wPart τ (𝔉.X ⟨j, by omega⟩)
  else wPart τ (perp V (𝔉.X ⟨2 * 𝔉.k + 1 - j, by omega⟩))

variable (𝔉 : IsoFlag V) (τ : E →ₐ[F] Fv F v)

theorem flagChain_of_le {j : Fin (2 * 𝔉.k + 2)} (hj : (j : ℕ) ≤ 𝔉.k) :
    flagChain 𝔉 τ j = wPart τ (𝔉.X ⟨j, by omega⟩) := dif_pos hj

theorem flagChain_of_lt {j : Fin (2 * 𝔉.k + 2)} (hj : 𝔉.k < (j : ℕ)) :
    flagChain 𝔉 τ j = wPart τ (perp V (𝔉.X ⟨2 * 𝔉.k + 1 - j, by omega⟩)) := dif_neg (not_le.2 hj)

theorem flagChain_mono : Monotone (flagChain 𝔉 τ) := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  rcases le_or_gt (i : ℕ) 𝔉.k with hi | hi <;> rcases le_or_gt (j : ℕ) 𝔉.k with hj | hj
  · rw [flagChain_of_le 𝔉 τ hi, flagChain_of_le 𝔉 τ hj]
    exact wPart_mono τ (𝔉.strictMono.monotone (Fin.mk_le_mk.2 hij'))
  · rw [flagChain_of_le 𝔉 τ hi, flagChain_of_lt 𝔉 τ hj]
    exact wPart_mono τ (𝔉.le_perp _ _)
  · omega
  · rw [flagChain_of_lt 𝔉 τ hi, flagChain_of_lt 𝔉 τ hj]
    exact wPart_mono τ (GlobalTheory.Cusp.perp_anti (𝔉.strictMono.monotone (Fin.mk_le_mk.2 (by omega))))

theorem wPart_bot : wPart τ (⊥ : Submodule E V.V) = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, GlobalTheory.Cusp.extSub_bot, Submodule.mem_bot] at hy
  rw [hy, Submodule.mem_bot]
  exact funext fun _ => map_zero _

theorem wPart_top {hc : CMData F E} (h : IsCMExt F E hc.sig) : wPart τ (⊤ : Submodule E V.V) = ⊤ :=
  eq_top_iff.2 fun u _ => ⟨splitIncl h τ u, by rw [GlobalTheory.Cusp.extSub_top]; trivial, splitVec_splitIncl h τ u⟩

theorem flagChain_zero : flagChain 𝔉 τ 0 = ⊥ := by
  rw [flagChain_of_le 𝔉 τ (Nat.zero_le _)]
  convert wPart_bot τ
  exact 𝔉.zero

theorem flagChain_last {hc : CMData F E} (h : IsCMExt F E hc.sig) : flagChain 𝔉 τ (Fin.last _) = ⊤ := by
  rw [flagChain_of_lt 𝔉 τ (by simp; omega)]
  convert wPart_top τ h
  have : (⟨2 * 𝔉.k + 1 - (Fin.last (2 * 𝔉.k + 1) : ℕ), by simp⟩ : Fin (𝔉.k + 1)) = 0 := Fin.ext (by simp)
  rw [this, 𝔉.zero, GlobalTheory.Cusp.perp_bot]

end Chain

end GlobalTheory.SplitFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFrameLinkMapInvertsHermitianSkewAdjoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.KapAdjLine

theorem kap_starAdj : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (x : WO (negSp F.Lz) (G.V (.core (2 * ρ + 1)))), (F.lnk ρ).κ _ (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ x) = x := by
  unfold OnStd
  intro D _ _ _ _ _ _ G _ _ _ F hF ρ x
  have hτ : (F.lnk ρ).τ = D.host.xi0 • (1 : Matrix (Fin (negSp F.Lz).rank) (Fin (negSp F.Lz).rank) D.host.E) := by
    have hl := F.line ρ
    have hu : Unique (Fin (negSp F.Lz).rank) := by rw [hl.1]; infer_instance
    have hz : F.ζ (ρ + 1) = (-D.host.xi0) • F.ζ ρ := by rw [hF.ζ, hF.ζ (ρ), pow_succ', mul_smul]
    have e : (F.lnk ρ).τ *ᵥ F.ζ ρ = -((-D.host.xi0) • F.ζ ρ) := by rw [← hz]; exact (F.lnk ρ).map
    have h2 := hl.2
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_unique] at h2
    have b : F.ζ ρ default ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h2)
    have e1 := congrFun e default
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_unique, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_mul, neg_neg] at e1
    funext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact mul_right_cancel₀ b e1
  rw [Lnk.κ, hτ, rat_smul, rat_one, Matrix.smul_mul, Matrix.one_mul, smul_smul, ← map_mul,
    mul_inv_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_one, one_smul, GlobalTheory.Unf.LinkGram.ofAdj_starAdj]

end GlobalTheory.KapAdjLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_reduction_onto_finiteLevelGroup : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ γ : G0g D.nd, ∃ k ∈ X.B.I.Kset, cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = γ := by
  first | exact @GlobalTheory.SeeMatchOnto.onto | exact GlobalTheory.SeeMatchOnto.onto | (intros; apply GlobalTheory.SeeMatchOnto.onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOZeroRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.AnnPieces

variable {D : D7}

theorem hO_add_right (S T : HSp D) (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem hO_zero_right (S T : HSp D) (x : WO S T) : hO S T x 0 = 0 := by
  unfold hO
  simp

theorem hO_zero_left (S T : HSp D) (y : WO S T) : hO S T 0 y = 0 := by
  unfold hO
  simp

theorem symplO_add_right (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO
  rw [hO_add_right, mul_add, map_add]

theorem symplO_zero_right (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  unfold symplO
  rw [hO_zero_right, mul_zero, map_zero]

theorem symplO_neg_right (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem mxAt_mul {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {a : Mx D m n} (ha : MxAt P a) (M : Mx D n k) : MxAt P (a ⬝ M) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem mxAt_zero {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} : MxAt P (0 : Mx D m n) := fun _ _ => zero_mem _

theorem mxAt_add {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {a b : Mx D m n} (ha : MxAt P a) (hb : MxAt P b) : MxAt P (a + b) :=
  fun i j => add_mem (ha i j) (hb i j)

theorem mxAt_neg {P : GlobalTheory.FinPl.Pl D → Prop} {m n : ℕ} {a : Mx D m n} (ha : MxAt P a) : MxAt P (-a) :=
  fun i j => neg_mem (ha i j)

variable {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem hO_extY_right (u : WO V W) (a' : Mx D W.rank ρ) : hO V W u (d.extY W a') = hO V W (d.extX W (u ⬝ d.jX)) (d.extY W a') := by
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY,
    HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY, Matrix.mul_zero, Matrix.mul_one, hO_zero_right, pairS, adj_zero,
    Matrix.zero_mul, Matrix.trace_zero, add_zero]

theorem hO_extX_left (a : Mx D W.rank ρ) (u' : WO V W) : hO V W (d.extX W a) u' = hO V W (d.extX W a) (d.extY W (u' ⬝ d.jY)) := by
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extY_apply, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY,
    HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY, Matrix.mul_zero, Matrix.mul_one, pairS, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.trace_zero, add_zero, zero_add, hO_zero_left, hO_zero_right]

end GlobalTheory.AscFin.AnnPieces

namespace GlobalTheory.AscFin.AnnPieces

variable {D : D7} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (d : HypDec V V₀ ρ) (ψ : AddChar (AF D.host.F) ℂ) (Γ : AddSubgroup (WO V W))

theorem symplO_extY_right (u : WO V W) (a' : Mx D W.rank ρ) :
    symplO V W u (d.extY W a') = symplO V W (d.extX W (u ⬝ d.jX)) (d.extY W a') := by
  unfold symplO
  rw [hO_extY_right]

theorem symplO_extX_left (a : Mx D W.rank ρ) (u' : WO V W) :
    symplO V W (d.extX W a) u' = symplO V W (d.extX W a) (d.extY W (u' ⬝ d.jY)) := by
  unfold symplO
  rw [← hO_extX_left]

theorem extY_mul_jY (a' : Mx D W.rank ρ) : d.extY W a' ⬝ d.jY = a' := by
  rw [HypDec.extY_apply, Matrix.mul_assoc, HypDec.pY_jY, Matrix.mul_one]

theorem extX_mul_jX (a : Mx D W.rank ρ) : d.extX W a ⬝ d.jX = a := by
  rw [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]

def annY : AddSubgroup (Mx D W.rank ρ) where
  carrier := {a' | MxAt (fun _ => True) a' ∧ ∀ a, d.extX W a ∈ Γ → ψ (symplO V W (d.extX W a) (d.extY W a')) = 1}
  zero_mem' := ⟨mxAt_zero, fun a _ => by rw [map_zero, symplO_zero_right, AddChar.map_zero_eq_one]⟩
  add_mem' := fun {x y} hx hy => ⟨mxAt_add hx.1 hy.1, fun a ha => by
    rw [map_add, symplO_add_right, AddChar.map_add_eq_mul, hx.2 a ha, hy.2 a ha, one_mul]⟩
  neg_mem' := fun {x} hx => ⟨mxAt_neg hx.1, fun a ha => by
    rw [map_neg, symplO_neg_right, AddChar.map_neg_eq_inv, hx.2 a ha, inv_one]⟩

def annSet : Set (WO V W) := {u' | MxAt (fun _ => True) u' ∧ ∀ u ∈ Γ, ψ (symplO V W u u') = 1}

variable {d ψ Γ}

theorem extY_mem_annSet (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ) {a' : Mx D W.rank ρ} (ha' : a' ∈ annY d ψ Γ) :
    d.extY W a' ∈ annSet ψ Γ :=
  ⟨mxAt_mul ha'.1 _, fun u hu => by rw [symplO_extY_right]; exact ha'.2 _ (hX u hu)⟩

theorem mul_jY_mem_annY {u' : WO V W} (hu' : u' ∈ annSet ψ Γ) : u' ⬝ d.jY ∈ annY d ψ Γ :=
  ⟨mxAt_mul hu'.1 _, fun a ha => by rw [← symplO_extX_left]; exact hu'.2 _ ha⟩

theorem annY_eq_image (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ) :
    (annY d ψ Γ : Set (Mx D W.rank ρ)) = (fun u : WO V W => u ⬝ d.jY) '' annSet ψ Γ :=
  Set.ext fun a' => ⟨fun h => ⟨_, extY_mem_annSet hX h, extY_mul_jY d a'⟩, by
    rintro ⟨u, hu, rfl⟩
    exact mul_jY_mem_annY hu⟩

theorem A₂_eq (dW : HypDec W W₀ σ) (Γ₂ : AddSubgroup (WO V W)) :
    (piecesOf d dW ψ Γ Γ₂).A₂ = annY d ψ Γ := by
  show AddSubgroup.closure (annY d ψ Γ : Set (Mx D W.rank ρ)) = _
  exact AddSubgroup.closure_eq _

theorem pieces_dualA (dW : HypDec W W₀ σ) (Γ₂ : AddSubgroup (WO V W))
    (hX : ∀ u ∈ Γ, d.extX W (u ⬝ d.jX) ∈ Γ)
    (hc : IsCompact (annSet ψ Γ))
    (ho : ∃ U : Set (WO V W), IsOpen U ∧ (0 : WO V W) ∈ U ∧
      ∀ u' ∈ U, MxAt (fun _ => True) u' → ∀ u ∈ Γ, ψ (symplO V W u u') = 1)
    (hb : ∀ u, MxAt (fun _ => True) u → (∀ u' ∈ annSet ψ Γ, ψ (symplO V W u u') = 1) → u ∈ Γ) :
    FinLat (piecesOf d dW ψ Γ Γ₂).A₂ ∧
      (∀ a, MxAt (fun _ => True) a → (a ∈ (piecesOf d dW ψ Γ Γ₂).A₁ ↔
        ∀ a' ∈ (piecesOf d dW ψ Γ Γ₂).A₂, ψ (symplO V W (d.extX W a) (d.extY W a')) = 1)) ∧
      (∀ a', MxAt (fun _ => True) a' → (a' ∈ (piecesOf d dW ψ Γ Γ₂).A₂ ↔
        ∀ a ∈ (piecesOf d dW ψ Γ Γ₂).A₁, ψ (symplO V W (d.extX W a) (d.extY W a')) = 1)) := by
  rw [A₂_eq]
  refine ⟨⟨fun a' ha' => ha'.1, ?_, ?_⟩, fun a ha => ⟨fun h a' ha' => ha'.2 a h, fun h => ?_⟩,
    fun a' ha' => ⟨fun h a ha => h.2 a ha, fun h => ⟨ha', h⟩⟩⟩
  · rw [annY_eq_image hX]
    exact hc.image (continuous_id.matrix_mul continuous_const)
  · obtain ⟨U, hU, h0, hUm⟩ := ho
    refine ⟨(fun a' => d.extY W a') ⁻¹' U, hU.preimage (continuous_id.matrix_mul continuous_const), ?_, ?_⟩
    · show d.extY W 0 ∈ U
      rw [map_zero]
      exact h0
    · intro a' ha' hfin
      refine ⟨hfin, fun b hb' => ?_⟩
      have := hUm _ ha' (mxAt_mul hfin _) _ hb'
      rwa [symplO_extY_right, extX_mul_jX] at this
  · show d.extX W a ∈ Γ
    refine hb _ (mxAt_mul ha _) fun u' hu' => ?_
    rw [symplO_extX_left]
    exact h _ (mul_jY_mem_annY hu')

end GlobalTheory.AscFin.AnnPieces

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoModerateGrowthSizeDifferenceQuotientStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_moderateGrowthSize_differenceQuotient : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (N : ℕ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V 2 N φ ≠ ⊤ → Filter.Tendsto (fun t : ℝ => GlobalTheory.Size.growthSize V N (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  first | exact @GlobalTheory.Size.DiffQuot.tendsto_growthSize_diffQuot | exact GlobalTheory.Size.DiffQuot.tendsto_growthSize_diffQuot | (intros; apply GlobalTheory.Size.DiffQuot.tendsto_growthSize_diffQuot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoModerateGrowthSizeTranslateNearOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_moderateGrowthSize_translate_near_one : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (N : ℕ), ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V 1 N φ ≠ ⊤ → Filter.Tendsto (fun u : Matrix (Fin V.rank) (Fin V.rank) ℂ => GlobalTheory.Size.growthSize V N (rTr V (atTau θ V τ u) φ - φ)) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (nhds 0) := by
  first | exact @GlobalTheory.Size.NearOne.tendsto_growthSize_translate | exact GlobalTheory.Size.NearOne.tendsto_growthSize_translate | (intros; apply GlobalTheory.Size.NearOne.tendsto_growthSize_translate <;> assumption)
end

