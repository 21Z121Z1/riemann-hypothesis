import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0452
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0034
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0438
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MonoAtOfJacFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MonoAtOfSplitW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0445
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0442
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0453
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMultipleMemSplitCoreLatticeCompletionIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LineIdeal

theorem e_half : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : Submodule 𝒪[k] (n → k)), IsSumFrame o ζ α α₀ → α₀.IsLat M (lastKer Λ) → ∀ c : AE D, ((fun r => p.e * (c * incA D (vecB o ζ r))) ∈ latV S₀ M (· = p.v) ↔ p.pr c ∈ 𝒪[k]) := by

  intro D k _ _ _ _ p n _ _ S₀ A L o ζ α α₀ M Λ hsum hlat c
  have key : (fun r => p.e * (c * incA D (vecB o ζ r))) =
      fun r => p.sec ((α₀.b *ᵥ Pi.single (Sum.inr 0) (p.pr c)) r) := by
    funext r
    have hb : α₀.b r (Sum.inr 0) = p.pr (incA D (vecB o ζ r)) := by
      rw [hsum]; rfl
    have hv : (α₀.b *ᵥ Pi.single (Sum.inr 0) (p.pr c)) r = α₀.b r (Sum.inr 0) * p.pr c := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, hb, ← map_mul, p.sec_pr, mul_comm (incA D _) c]
  rw [key, ← hlat, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
  have h1 : (Pi.single (Sum.inr 0) (p.pr c) : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
    funext j; simp
  simp [h1]

theorem mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ c : AE D, c ∈ idAt D P → ((fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M P ↔ (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k])) := by

  intro D k _ _ _ _ ι p I P hP n _ _ S₀ A L o ζ hζ α α₀ M Λ hM hfr c hc
  have hyid : ∀ r, (fun r => c * incA D (vecB o ζ r)) r ∈ idAt D P := fun r => Ideal.mul_mem_right _ _ hc
  have hloc : (fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M P ↔ ∀ i,
      GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M (· = (p i).v) := by
    constructor
    · intro h i
      exact GlobalTheory.FinPlLoc.smul_latV _ (GlobalTheory.FinPlLoc.idem_mem_intAt _) h
    · intro h
      refine (GlobalTheory.FinPlLoc.part_lat P S₀ M _ hM.1).2 ⟨hyid, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (hP.mem v).1 hv
      have h1 : e • (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) =
          e • (fun r => c * incA D (vecB o ζ r)) := by
        rw [smul_smul, mul_comm, (GlobalTheory.FinPlLoc.mem_idAt_iff _ e).1 he.1]
      rw [← h1]
      exact GlobalTheory.FinPlLoc.smul_latV _ he (h i)
  rw [hloc]
  refine forall_congr' fun i => ?_
  have hεid : ∀ r, (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r ∈ idAt D (· = (p i).v) :=
    fun r => Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_intAt _).1
  rw [GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts D k (p i) S₀ M _ hεid]
  have he : GlobalTheory.FinPlLoc.idem D (· = (p i).v) * (p i).e = (p i).e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (FrameLat.e_mem_idAt (p i))
  have hce_id : cA D (p i).e ∈ idAt D (· = (p i).v) := by
    have := Ideal.sub_mem _ (FrameLat.sum_mem_idAt (p i)) (FrameLat.e_mem_idAt (p i))
    rwa [add_sub_cancel_left] at this
  have hce : GlobalTheory.FinPlLoc.idem D (· = (p i).v) * cA D (p i).e = cA D (p i).e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hce_id
  have e1 : (fun r => (p i).e * (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r) =
      fun r => (p i).e * (c * incA D (vecB o ζ r)) := by
    funext r
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (p i).e, he]
  have e2 : (fun r => cA D (p i).e * (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r) =
      fun r => cA D (p i).e * (c * incA D (vecB o ζ r)) := by
    funext r
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (cA D (p i).e), hce]
  rw [e1, e2, e_half D k (p i) n S₀ A L o ζ (α i) (α₀ i) M (Λ i) (hfr i).1 (hfr i).2 c,
    GlobalTheory.T.conjugateHalf_lineMultiple_mem_iff_integral D k (p i) n S₀ A L o ζ (α i) (α₀ i) M (Λ i) hM (hfr i).1 (hfr i).2 c]

end GlobalTheory.LineIdeal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorBesselExistence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.Fam.RatDec

variable {D : D7}

theorem quad_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (G : Matrix (Fin m) (Fin m) D.host.E)
    (v : Fin n → D.host.E) : star (A *ᵥ v) ⬝ᵥ G *ᵥ (A *ᵥ v) = star v ⬝ᵥ (Aᴴ * G * A) *ᵥ v := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem conj_mul_mul {S S' : HSp D} {a b : ℕ} (P : Matrix (Fin S'.rank) (Fin S.rank) D.host.E)
    (A : Matrix (Fin S.rank) (Fin a) D.host.E) (B : Matrix (Fin S.rank) (Fin b) D.host.E) :
    (P * A)ᴴ * S'.gram * (P * B) = Aᴴ * (Pᴴ * S'.gram * P) * B := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

def pullDec {S S' S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (P : Matrix (Fin S'.rank) (Fin S.rank) D.host.E)
    (hP : Pᴴ * S'.gram * P = S.gram) (hr : S.rank = S'.rank) : HypDec S' S₀ ρ where
  e := P * d.e
  e' := P * d.e'
  i₀ := P * d.i₀
  ee := by rw [conj_mul_mul, hP, d.ee]
  e'e' := by rw [conj_mul_mul, hP, d.e'e']
  e'e := by rw [conj_mul_mul, hP, d.e'e]
  iso := by rw [conj_mul_mul, hP, d.iso]
  i₀e := by rw [conj_mul_mul, hP, d.i₀e]
  i₀e' := by rw [conj_mul_mul, hP, d.i₀e']
  rank_add := d.rank_add.trans hr

theorem mat_of_isom (W₁ W₂ : HSp D) (φ : W₁.V ≃ₗ[D.host.E] W₂.V) (hφ : ∀ x y, W₂.hT (φ x) (φ y) = W₁.hT x y) :
    ∃ P : Matrix (Fin W₂.rank) (Fin W₁.rank) D.host.E, Pᴴ * W₂.gram * P = W₁.gram := by
  refine ⟨Matrix.of fun k j => W₂.frame.equivFun (φ (W₁.frame j)) k, ?_⟩
  ext i j
  have h := GlobalTheory.LandherrSignature.form_eq W₂.hT W₂.frame (W₂.frame.equivFun (φ (W₁.frame i)))
    (W₂.frame.equivFun (φ (W₁.frame j)))
  simp only [LinearEquiv.symm_apply_apply] at h
  rw [hφ] at h
  have hG : (Matrix.of fun a b => W₂.hT (W₂.frame a) (W₂.frame b)) = W₂.gram := rfl
  rw [hG] at h
  rw [show W₁.gram i j = W₁.hT (W₁.frame i) (W₁.frame j) from rfl, h]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, mulVec, Matrix.of_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  simp_rw [mul_assoc]
  first | exact Finset.sum_comm | (congr 1; exact Finset.sum_comm)

theorem yc_facts (j : ℕ) (hj : j ≤ D.R.m) :
    (Yc D j).SigOK ∧ (Yc D j).rank = D.R.rankY j ∧ ∀ τ, (Yc D j).sig τ = sigYD D.R j := by
  have hmin : min j D.R.m = j := min_eq_left hj
  refine ⟨D.sp.Y_sig _, ?_, fun τ => ?_⟩
  · show (D.sp.Y (min j D.R.m)).rank = _
    rw [hmin]; exact D.sp.Y_rank j hj
  · show (D.sp.Y (min j D.R.m)).sig τ = _
    rw [hmin]; exact D.Y_sigval j hj τ

theorem bes_to_Yc (j ρ : ℕ) (hj : j ≤ D.R.m) {V : HSp D} (b : BesAt V (D.sp.X j) ρ) (hr : V.rank = D.R.rankY j)
    (hs : V.SigOK) (hsig : ∀ τ, V.sig τ = sigYD D.R j) :
    ∃ b' : BesAt (Yc D j) (D.sp.X j) ρ, star b'.ζ ⬝ᵥ b'.L.gram *ᵥ b'.ζ = star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ := by
  obtain ⟨hYs, hYr, hYsig⟩ := yc_facts (D := D) j hj
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D V (Yc D j) hs hYs (hr.trans hYr.symm)
    (fun τ => (hsig τ).trans (hYsig τ).symm)
  obtain ⟨P, hP⟩ := mat_of_isom V (Yc D j) φ hφ
  exact ⟨⟨b.V₀, b.L, pullDec b.d P hP (hr.trans hYr.symm), b.o, b.ζ, b.line, b.cpt,
    ((GlobalTheory.Unf.VolExist.measures_exist D).2.1 _ _ _ _).some⟩, rfl⟩

theorem jac_to_Yc (j ρ : ℕ) (hj : j ≤ D.R.m) {V : HSp D} (b : JacAt V (D.sp.X j) ρ) (hr : V.rank = D.R.rankY j)
    (hs : V.SigOK) (hsig : ∀ τ, V.sig τ = sigYD D.R j) : Nonempty (JacAt (Yc D j) (D.sp.X j) ρ) := by
  obtain ⟨hYs, hYr, hYsig⟩ := yc_facts (D := D) j hj
  obtain ⟨φ, hφ⟩ := GlobalTheory.LandherrSignature.exists_isometry_host D V (Yc D j) hs hYs (hr.trans hYr.symm)
    (fun τ => (hsig τ).trans (hYsig τ).symm)
  obtain ⟨P, hP⟩ := mat_of_isom V (Yc D j) φ hφ
  exact ⟨⟨pullDec b.d P hP (hr.trans hYr.symm), b.cpt, ((GlobalTheory.Unf.VolExist.measures_exist D).2.1 _ _ _ _).some⟩⟩

def besOf {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : GlobalTheory.Core.Mi.SBes X h u ψ (D.sp.X 0)) : BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS :=
  ⟨B.V₀, B.L, B.d, B.o, B.ζ, B.line, B.cpt, B.vN⟩

def besF (b0 : BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS)
    (b' : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ) :
    ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ
  | 0, ρ, h => cast (congrArg (BesAt (Yc D 0) (D.sp.X 0)) (show D.R.m / 2 - 1 = ρ by omega)) b0
  | j + 1, ρ, h => b' (j + 1) ρ h

theorem besF_zero (b0 : BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS)
    (b' : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m) :
    besF b0 b' 0 D.R.rS h0 = b0 := rfl

theorem besF_norm (b0 : BesAt (D.sp.Y 0) (D.sp.X 0) D.R.rS)
    (b' : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ) (c N : D.host.E)
    (h0 : star b0.ζ ⬝ᵥ b0.L.gram *ᵥ b0.ζ = c)
    (h' : ∀ j ρ h, star (b' j ρ h).ζ ⬝ᵥ (b' j ρ h).L.gram *ᵥ (b' j ρ h).ζ * N ^ (j / 2) = c) :
    ∀ j ρ h, star (besF b0 b' j ρ h).ζ ⬝ᵥ (besF b0 b' j ρ h).L.gram *ᵥ (besF b0 b' j ρ h).ζ * N ^ (j / 2) = c
  | 0, ρ, h => by
    obtain rfl : D.R.rS = ρ := by show D.R.m / 2 - 1 = ρ; omega
    rw [besF_zero b0 b' h, Nat.zero_div, pow_zero, mul_one]
    exact h0
  | j + 1, ρ, h => h' (j + 1) ρ h

theorem sbes_norm {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : GlobalTheory.Core.Mi.SBes X h u ψ (D.sp.X 0)) (hE : GlobalTheory.Core.Mi.IdE X)
    (hz : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = X.ιE (X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq X h) k))) :
    star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(((D.mem u).A.T : ℕ) : D.host.E) := by
  have hw : B.d.i₀ *ᵥ (B.o.iB *ᵥ B.ζ) = GlobalTheory.Core.SBesEx.cY X h (X.zu u) := funext hz
  rw [← B.o.isoB, ← quad_mulVec, ← B.d.iso, ← quad_mulVec, hw, GlobalTheory.Core.SBesEx.cY_isom D X h hE, X.zu_norm]

theorem tau_line {n p : ℕ} (hn : n = 1) (hp : p = 1) (G : Matrix (Fin n) (Fin n) D.host.E)
    (G₀ : Matrix (Fin p) (Fin p) D.host.E) (ζ : Fin n → D.host.E) (ζ₀ : Fin p → D.host.E) (lam c : D.host.E)
    (h₀ : star ζ₀ ⬝ᵥ G₀ *ᵥ ζ₀ ≠ 0)
    (hrel : star lam * lam * (star ζ ⬝ᵥ G *ᵥ ζ) = c * (star ζ₀ ⬝ᵥ G₀ *ᵥ ζ₀)) :
    (Matrix.of fun i k => lam * ζ i / ζ₀ k)ᴴ * (G * Matrix.of fun i k => lam * ζ i / ζ₀ k) = c • G₀ ∧
      (Matrix.of fun i k => lam * ζ i / ζ₀ k) *ᵥ ζ₀ = lam • ζ := by
  subst hn; subst hp
  simp only [dotProduct, mulVec, Fin.sum_univ_one, Pi.star_apply] at h₀ hrel
  have hz : ζ₀ 0 ≠ 0 := fun h => h₀ (by rw [h]; simp)
  have hz' : star (ζ₀ 0) ≠ 0 := star_ne_zero.2 hz
  constructor
  · refine Matrix.ext fun i k => ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fin.sum_univ_one, Matrix.smul_apply,
      smul_eq_mul, star_div₀, star_mul', star_inv₀]
    field_simp
    first | linear_combination hrel | (rw [div_eq_iff (mul_ne_zero hz' hz)]; linear_combination hrel)
  · funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [mulVec, dotProduct, Matrix.of_apply, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
    field_simp

set_option maxHeartbeats 1000000 in

theorem exists_yRat : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ a : XGeo D, IsLineVec a.Lz a.ζ₀ → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → ∃ (y : YRat a) (B : GlobalTheory.Core.Mi.SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), y.Tau (-D.host.xi0 ^ (D.R.m / 2)) ∧ B.lev = (y.bes 0 D.R.rS h0).lev (a.x 0).vol ∧ B.Adapted (W.S.tr u).wt ∧ GlobalTheory.MiTop.Framed B ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(((D.mem u).A.T : ℕ) : D.host.E) ∧ ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) k)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP a hLz hT0
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hN : D.host.xi0 * star D.host.xi0 ≠ 0 := mul_ne_zero hxi (star_ne_zero.2 hxi)

  obtain ⟨lam0, hlam0, hB⟩ := GlobalTheory.Core.Mi.exists_sBes_scaled_dual D W.S.X W.Q.instEq u W.Q.Rl.ψ _ (W.S.tr u)
    hP.bot.idE W.Q.stdChar
  obtain ⟨B, hA, hvA, hz, he, he'⟩ := hB 1 (a.x 0).vol one_ne_zero
  have hz1 : ∀ k, (B.d.i₀ *ᵥ vecB B.o B.ζ) k = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) k)) :=
    fun k => by rw [hz k, one_mul]
  have hB0 := sbes_norm B hP.bot.idE hz1

  have hI := GlobalTheory.T.exists_thetaLiftSpaces_positiveIndex_with_lineNorms D u (fun j hj => D.X_posDef j hj)
  have hbes : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), ∃ b : BesAt (Yc D j) (D.sp.X j) ρ,
      star b.ζ ⬝ᵥ b.L.gram *ᵥ b.ζ * (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E) := by
    intro j ρ h
    obtain ⟨V, b, hr, hs, hsig, hn⟩ := hI.1 j ρ h
    obtain ⟨b2, hb2⟩ := bes_to_Yc j ρ (by omega) b hr hs hsig
    exact ⟨b2, by rw [hb2]; exact hn⟩
  choose b' hb' using hbes
  have hjac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → Nonempty (JacAt (Yc D (j + 1)) (D.sp.X (j + 1)) ρ) := by
    intro j ρ h
    obtain ⟨V, b, hr, hs, hsig⟩ := hI.2 j ρ h
    exact jac_to_Yc (j + 1) ρ (by omega) b hr hs hsig
  obtain ⟨bes, hbes_def⟩ : ∃ f, f = besF (besOf B) b' := ⟨_, rfl⟩
  have h0 : 0 + 2 * D.R.rS + 2 = D.R.m := by
    show 0 + 2 * (D.R.m / 2 - 1) + 2 = D.R.m
    obtain ⟨k, hk⟩ := D.R.m_even
    have := D.R.two_le_m
    omega
  have hbes0 : bes 0 D.R.rS h0 = besOf B := by rw [hbes_def]; rfl
  have hnorm : ∀ j ρ h, star (bes j ρ h).ζ ⬝ᵥ (bes j ρ h).L.gram *ᵥ (bes j ρ h).ζ *
      (D.host.xi0 * star D.host.xi0) ^ (j / 2) = -(((D.mem u).A.T : ℕ) : D.host.E) := by
    rw [hbes_def]; exact besF_norm (besOf B) b' _ _ hB0 hb'

  have hlnk : ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), Nonempty (Link ((bes j (σ + 1) h).lev (a.x j).vol)
      (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ) := by
    intro j σ h
    have hn1 := hnorm j (σ + 1) h
    have hn2 := hnorm (j + 1 + 1) σ (idx_step h)
    have e : (j + 1 + 1) / 2 = j / 2 + 1 := by omega
    rw [e, pow_succ] at hn2
    have hrel : star (bes j (σ + 1) h).ζ ⬝ᵥ (bes j (σ + 1) h).L.gram *ᵥ (bes j (σ + 1) h).ζ =
        D.host.xi0 * star D.host.xi0 * (star (bes (j + 1 + 1) σ (idx_step h)).ζ ⬝ᵥ
          (bes (j + 1 + 1) σ (idx_step h)).L.gram *ᵥ (bes (j + 1 + 1) σ (idx_step h)).ζ) := by
      apply mul_right_cancel₀ (pow_ne_zero (j / 2) hN)
      rw [hn1]
      linear_combination -hn2
    have hl := (GlobalTheory.Unf.LinkExist.link_of_norm D (σ + 1) ((bes j (σ + 1) h).lev (a.x j).vol)
      (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ D.host.xi0
      (bes (j + 1 + 1) σ (idx_step h)).line hrel).2
    rwa [div_self hxi, one_smul] at hl
  have hvol := GlobalTheory.Unf.VolExist.measures_exist D

  have hrelT : ∀ j (h : j + 2 * 0 + 2 = D.R.m), star (-D.host.xi0 ^ (D.R.m / 2)) * (-D.host.xi0 ^ (D.R.m / 2)) *
      (star (bes j 0 h).ζ ⬝ᵥ (bes j 0 h).L.gram *ᵥ (bes j 0 h).ζ) =
        -(D.host.xi0 * star D.host.xi0) * (star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀) := by
    intro j h
    have hn := hnorm j 0 h
    have e : D.R.m / 2 = j / 2 + 1 := by omega
    have hl : star (-D.host.xi0 ^ (D.R.m / 2)) * (-D.host.xi0 ^ (D.R.m / 2)) =
        (D.host.xi0 * star D.host.xi0) ^ (D.R.m / 2) := by
      rw [star_neg, star_pow, neg_mul_neg, mul_pow]; ring
    rw [hl, e, pow_succ, hT0]
    linear_combination (D.host.xi0 * star D.host.xi0) * hn
  refine ⟨⟨bes, fun j ρ h => (hjac j ρ h).some, fun j σ h => (hlnk j σ h).some, fun j σ h => (hvol.2.2.1 _ _).some,
    fun j h => Matrix.of fun i k => -D.host.xi0 ^ (D.R.m / 2) * (bes j 0 h).ζ i / a.ζ₀ k⟩, B, h0, ?_, ?_, hA,
    ⟨1, lam0, one_ne_zero, hlam0, hz, he, he'⟩, hB0, hz1⟩
  · intro j h
    exact tau_line (bes j 0 h).line.1 hLz.1 _ _ _ _ _ _ hLz.2 (hrelT j h)
  · show B.lev = (bes 0 D.R.rS h0).lev (a.x 0).vol
    rw [hbes0, ← hvA]
    rfl

end GlobalTheory.Fam.RatDec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureIdentityAltBis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_identity_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N j)) → ∃ b : ∀ j, GA D (Yc D j), (∀ j, b j ∈ GfC (Yc D j)) ∧ (∀ j, j < D.R.m → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (N j) P) ∧ ∀ PP h j c (hc : j + c = (l PP h).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (l PP h).q) (Yc D j) (b j) ((pk W).βY j) (((FY PP h j c hc).β * (bas PP h j c hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
  first | exact @GlobalTheory.RLatMove.move_main | exact GlobalTheory.RLatMove.move_main | (intros; apply GlobalTheory.RLatMove.move_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.AdaptSplit

open GlobalTheory.FinPl (latV MonoAt PrimAt ColsAt idAt intAt colMul Lat SplitPt)
open GlobalTheory.FinPl.FrameLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem monoAt_of_besFrame (hU : q.UnitAA) {σ : ℕ} (B : BesLev D σ) {n : Type} [Fintype n] [DecidableEq n] {s : k}
    (hs : valuation k s = 1) (hz : valuation k ((ofSplit q).hz B) = 1) {FA : Frame k B.A.rank n}
    {F : Frame k B.V.rank (n ⊕ Fin (2 * σ + 1))} {F₀ : Frame k B.V₀.rank (n ⊕ Unit)} (hF : (ofSplit q).IsBesFrame B s FA F)
    (hcore : (ofSplit q).IsCoreFrame B s FA F₀) {L : Lat B.V} {L₀ : Lat B.V₀} (hL : IsSelfDualC B.V L)
    (hL₀ : IsSelfDualC B.V₀ L₀) (h : IntIn q B.V F L) (h₀ : IntIn q B.V₀ F₀ L₀) : MonoAt B.d L L₀ q.v := by
  obtain ⟨-, b1, b2, b3, b4⟩ := hF
  have hxi : valuation k (ofSplit q).xi = 1 := GlobalTheory.MonoSplit.xi_unit q hU
  refine GlobalTheory.MonoSplit.monoAt_of_splitW q B.d hL hL₀
    (GlobalTheory.MonoSplit.splitW_of_frame q B.d F F₀ _ _ (fun i => ?_) (fun i => ?_)
      (fun r a => ?_) (fun l hl r => ?_) b2 b4 h h₀)
  · rw [map_mul, map_pow, hs, hxi, one_pow, mul_one]
  · rw [map_mul, map_mul, map_pow, map_div₀, map_div₀, Valuation.map_neg, Valuation.map_neg, hs, hz, hxi, map_one]
    simp
  · refine (b1 r a).trans ?_
    change ((_ * _ : Matrix _ _ _).map (GlobalTheory.MonoSplit.prE q) * _ : Matrix _ _ _) r a = _
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun t _ => congrArg _ (hcore.1 t a).symm
  · refine (b3 l hl r).trans ?_
    change _ * GlobalTheory.MonoSplit.prE q _ = _
    rw [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, mul_left_comm]
    exact congrArg _ (hcore.2 t).symm

theorem line_jac (hU : q.UnitAA) {ρ : ℕ} (J : JacLev D ρ) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {s hh : k}
    (hs : valuation k s = 1) (hz : valuation k hh = 1) {F₀ : Frame k J.W₀.rank n} {F : Frame k J.W.rank (n ⊕ Fin c)}
    (hF : (ofSplit q).IsJacFrame J s hh F₀ F) {L : Lat J.W} (hL : IsSelfDualC J.W L) (h : IntIn q J.W F L) (i : Fin ρ)
    (a : AE D) (ha : a ∈ idAt D (· = q.v)) : colMul J.d.jX i a ∈ latV J.W L (· = q.v) ↔ a ∈ intAt D (· = q.v) := by
  obtain ⟨b, m, hb, hA, hB, hC⟩ := GlobalTheory.JacFramePair.isJacFrame_pairing D k (ofSplit q) ρ J s hh n c F₀ F hF hs hz
    (GlobalTheory.MonoSplit.xi_unit q hU) i
  exact GlobalTheory.SplitLine.line_mem_latV_iff D k q J.W L _ F _ b m hL h hb hA hB hC a ha

theorem line_bes (hU : q.UnitAA) {σ : ℕ} (B : BesLev D σ) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {s : k}
    (hs : valuation k s = 1) (hz : valuation k ((ofSplit q).hz B) = 1) {FA : Frame k B.A.rank n}
    {F : Frame k B.V.rank (n ⊕ Fin c)} (hF : (ofSplit q).IsBesFrame B s FA F) {L : Lat B.V} (hL : IsSelfDualC B.V L)
    (h : IntIn q B.V F L) (i : Fin (σ + 1)) (a : AE D) (ha : a ∈ idAt D (· = q.v)) :
    colMul (xLast B.d (vecB B.o B.ζ)) i a ∈ latV B.V L (· = q.v) ↔ a ∈ intAt D (· = q.v) := by
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · obtain ⟨m, hA, hB, hC⟩ := GlobalTheory.BesPair.besz_pairings D k (ofSplit q) σ B s n c FA F hF hs hz
    have e := GlobalTheory.SplitLine.line_mem_latV_iff D k q B.V L _ F _ s m hL h hs hA hB hC a ha
    convert e using 2
    funext r
    simp [GlobalTheory.FinPl.colMul, xLast, HypDec.j0, rat, ratV, Matrix.mulVec, dotProduct, map_sum]
  · obtain ⟨b, m, hb, hA, hB, hC⟩ := GlobalTheory.BesPair.bes_cols D k (ofSplit q) σ B s n c FA F hF hs hz
      (GlobalTheory.MonoSplit.xi_unit q hU) i'
    have e := GlobalTheory.SplitLine.line_mem_latV_iff D k q B.V L _ F _ b m hL h hb hA hB hC a ha
    convert e using 2
    funext r
    simp [GlobalTheory.FinPl.colMul, xLast, HypDec.jX, rat]

theorem psiE_triv_iff (hU : q.UnitAA) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {s : AE D}
    (hs : s ∈ idAt D (· = q.v)) : (∀ o ∈ intAt D (· = q.v), psiE ψ (s * o) = 1) ↔ s ∈ intAt D (· = q.v) := by
  obtain ⟨ψk, hk, hc⟩ := GlobalTheory.SplitWeilChar.weil_char_conductor_one D k q ψ hψ hU
  have hxi : valuation k (ofSplit q).xi = 1 := GlobalTheory.MonoSplit.xi_unit q hU
  have hc' : ∀ x : k, (∀ y : k, valuation k y ≤ valuation k x → ψk y = 1) ↔ x ∈ 𝒪[k] := fun x => by
    rw [hc x, Units.val_one, map_one, Valuation.mem_integer_iff]
  have half : ∀ t : AE D, (∀ o ∈ intAt D (· = q.v), psiE ψ (t * o) = 1) → q.pr t ∈ 𝒪[k] := by
    intro t ht
    by_cases h0 : q.pr t = 0
    · rw [h0]; exact zero_mem _
    refine (hc' _).1 fun y hy => ?_
    have hr : y / q.pr t ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ hy zero_le'
    have h1 := ht _ (hU.1 _ (sec_mem_intAt q _ hr)).1
    rw [mul_left_comm, mul_comm t, sec_mul_right, div_mul_cancel₀ _ h0] at h1
    exact Circle.ext ((hk y).trans h1)
  constructor
  · intro h
    refine (GlobalTheory.SplitLine.mem_intAt_iff_pr q hs).2 ⟨half s h, half _ fun o ho => ?_⟩
    rw [← GlobalTheory.LocBesChar.psiE_cA, RingHom.map_mul, Formalism.L2.Theta.cA_cA]
    exact h _ (GlobalTheory.JacMono.conj_intAt q ho)
  · intro h o ho
    have hb := GlobalTheory.IwaDecomp.intAt_mul' h ho
    obtain ⟨h1, h2⟩ := (GlobalTheory.SplitLine.mem_intAt_iff_pr q hb.1).1 hb
    rw [GlobalTheory.LocBesChar.psiE_supp (ofSplit q) hk ((idem_iff q _).1 hb.1), (hc' 1).2 (one_mem _) _ ?_]
    · rfl
    · rw [map_div₀, hxi, div_one, map_one]
      exact (Valuation.mem_integer_iff _ _).1 (add_mem h1 h2)

theorem primAt_of_lines (hU : q.UnitAA) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (L : Lat S)
    (h : ∀ (i : Fin ρ), ∀ a ∈ idAt D (· = q.v), colMul d.jX i a ∈ latV S L (· = q.v) ↔ a ∈ intAt D (· = q.v)) :
    PrimAt ψ d L q.v := by
  intro i j _ s hs
  rw [psiE_triv_iff q hU hψ hs]
  constructor
  · intro H
    have hε : q.e + cA D q.e ∈ intAt D (· = q.v) :=
      ⟨sum_mem_idAt q, by
        rw [RingHom.map_add]
        exact add_mem (e_mem_intAt q).2 (GlobalTheory.JacMono.conj_intAt q (e_mem_intAt q)).2⟩
    have h1 := (h i _ (Ideal.mul_mem_right _ _ hs)).1 (H _ ((h j _ hε.1).2 hε))
    rwa [mul_comm, (idem_iff q s).1 hs] at h1
  · intro H a ha
    have h1 : a ∈ idAt D (· = q.v) := by
      have h2 := GlobalTheory.IwaPlace.mulVec_mem_idAt d.pX (latV_supp ha) j
      rwa [GlobalTheory.JacMono.mulVec_colMul, d.pX_jX, GlobalTheory.FinPl.colMul, Matrix.one_apply_eq, mul_one] at h2
    exact (h i _ (Ideal.mul_mem_right _ _ hs)).2 (GlobalTheory.IwaDecomp.intAt_mul' H ((h j a h1).1 ha))

end GlobalTheory.Fam.AdaptSplit

open GlobalTheory.Fam.AdaptSplit in

theorem GlobalTheory.Fam.adaptFB_of_normalFrames : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), GlobalTheory.FinPl.AdaptFB (commOf (pk W) u (mkGeo m b₀)).ψ ((commOf (pk W) u (mkGeo m b₀)).J j (σ + 1) h) ((commOf (pk W) u (mkGeo m b₀)).B (j + 1 + 1) σ (idx_step h)) (N₁ (j + 1)) ((commOf (pk W) u (mkGeo m b₀)).x (j + 1)).L (N₁ (j + 1 + 1)) (M₁ (j + 1 + 1) σ (idx_step h)) (PP.under (𝓞 D.host.F)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hT0 hτ hNT hζ hsd hgP htP hdis hPre hOrth hbas FY sc hFr N₁ M₁ hsdN hIntN hsdM hIntM PP hP j σ h
  obtain ⟨hsc, -, hhz, hbes, hjac, -⟩ := hFr PP hP
  have hs := (l PP hP).hs
  have hU := (l PP hP).unit
  rw [← (l PP hP).under]
  have hj1 : j + 1 + (2 * (σ + 1)) = (l PP hP).s + 1 := by omega
  have hj2 : j + 1 + 1 + (2 * σ + 1) = (l PP hP).s + 1 := by omega
  have hJ := hjac j (σ + 1) h (2 * (σ + 1)) hj1
  have hB := hbes (j + 1 + 1) σ (idx_step h) (2 * σ + 1) hj2
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.LocMod.GValProof.core_of_bes _ _ _ _ _ hB
  have hM := hIntM PP hP (j + 1 + 1) σ (idx_step h) (by omega) F₀ hF₀
  have hV := hsdN (j + 1) (by omega)
  have hV₀ := (hIs.x (j + 1) (by omega)).sd
  have hW' := hsdN (j + 1 + 1) (by omega)
  have hLJ := line_jac (l PP hP).q hU _ (hsc _) (hhz _ _ _) hJ hV (hIntN PP hP (j + 1) _ hj1)
  have hLB := line_bes (l PP hP).q hU _ (hsc _) (hhz _ _ _) hB hW' (hIntN PP hP (j + 1 + 1) _ hj2)
  refine ⟨GlobalTheory.FinPl.TamePlaces.tame D _, hV, hV₀, hW', hsdM _ _ _, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.JacMono.monoAt_of_jacFrame (l PP hP).q hU _ hV hV₀ (hsc _) (hhz _ _ _) hJ (hIntN PP hP (j + 1) _ hj1)
      ((l PP hP).latX (j + 1) (by omega))
  · exact monoAt_of_besFrame (l PP hP).q hU _ (hsc _) (hhz _ _ _) hB hF₀ hW' (hsdM _ _ _) (hIntN PP hP (j + 1 + 1) _ hj2) hM
  · exact primAt_of_lines (l PP hP).q hU hIs.std _ _ hLJ
  · intro i b hb
    rw [hU.2, hLJ i b hb]
    exact (hLB i b hb).symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattices_single_orbit_tamePlace : ∀ (D : D7) (S₀ : HSp D) (v : Pl D) (Λ Λ' : AddSubgroup (Fin S₀.rank → AE D)), Tame D v → IsSDAt S₀ v Λ → IsSDAt S₀ v Λ' → ∃ γ ∈ grpAt S₀ (· = v), ∀ y : Fin S₀.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ mt S₀ γ *ᵥ y ∈ Λ') := by
  first | exact @GlobalTheory.IwaOrbit.selfDual_orbit | exact GlobalTheory.IwaOrbit.selfDual_orbit | (intros; apply GlobalTheory.IwaOrbit.selfDual_orbit <;> assumption)
end

