import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0602
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0634
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0635
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0631
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberMaximalCompactPreservesPolynomialFock
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.FockCompactX

open GlobalTheory.RealLift GlobalTheory.FockCompactW

section Der

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem at_mul_left {m p q : Type} [Fintype p] {z : Matrix p q (AE F E)} (hz : At (evI F) z)
    (A : Matrix m p (AE F E)) : At (evI F) (A * z) := by
  intro u hu; rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]

theorem sd_intertwine_left {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {χ₁ χ₂ : Chr F E} {om : Rep σ Y W}
    (hw : M.IsWeil ψ χ₁ χ₂ om) (h : UA σ Y.J) {f f₁ g g₁ : SInf F (Fin n × Fin d)}
    (hf : Acts (evI F) (om (h, 1)) f g) (hf₁ : Acts (evI F) (om (h, 1)) f₁ g₁) {u : Matrix (Fin n) (Fin d) (AE F E)}
    (hD : SD (M.heisLine ψ u) f f₁) : SD (M.heisLine ψ (mat h * u)) g g₁ := by
  have hS := IsUWeilPair.isUSplitting hw
  intro r hr l hl
  have h1 := hD r hr _ (hS.adm (h, 1) l hl)
  simp only [LinearMap.comp_apply] at h1
  rw [sa_of_acts hf₁ r hr] at h1
  refine h1.congr_of_eventuallyEq (.of_forall fun t => ?_)
  have h2 := hS.impl (h, 1) (realAd F t • u) (pureA F f r) (Submodule.subset_span ⟨f, r, hr, rfl⟩)
  have h3 : actAB (cA σ) ((h, 1) : UA σ Y.J × UA σ W.J) (realAd F t • u) = realAd F t • (mat h * u) := by
    change mat h * (realAd F t • u) * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ = _
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
  rw [h3, sa_of_acts hf r hr] at h2
  exact congrArg l h2.symm

end Der

theorem pol_stable_compact_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ k ∈ KInf σ X τ, ∀ f ∈ M.Pol ψ τ,
          ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ _ n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hw τ _ _ k hk f hf f₁ hf₁
  have h1 : (1 : UA σ W.J) ∈ UAt σ W (evI F) := by
    intro u _
    simp [mat]
  obtain ⟨A, hA⟩ := exists_op_of_UAt hψ hw (k, 1) hk.1 h1
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ
  have hL := actsLaws F (Fin n × Fin d)
  have hSD : ∀ u, At (evI F) u → ∀ φ, SD (M.heisLine ψ u) φ (D u φ) := fun u hu φ => (hD u hu φ).1
  have hAD : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) φ (D u φ) :=
    fun u hu φ => (hL φ _ φ).1 _ (FockCompactW.heisLine_zero M ψ u) (hSD u hu φ)
  have hint : ∀ u, At (evI F) u → ∀ φ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ (mat k * u)) (A φ) (A (D u φ)) :=
    fun u hu φ => (hL _ _ φ).1 _ (FockCompactW.heisLine_zero M ψ _)
      (sd_intertwine_left hw k (hA φ) (hA _) (hSD u hu φ))
  have hkk : mat k * mat k⁻¹ = 1 := by
    change mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  have hcan : ∀ u : Matrix (Fin n) (Fin d) (AE F E), mat k * (mat k⁻¹ * u) = u := fun u => by
    rw [← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hle : M.Pol ψ τ ≤ (M.Pol ψ τ).comap A := by
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu φ hφ φ₁ hφ₁ => ?_⟩
    · refine Submodule.mem_sInf.2 fun N hN => hN.1 _ ?_
      obtain ⟨ε, hε⟩ := hf₀
      refine ⟨ε, fun u u' hu hu' huu g g' hg hg' => ?_⟩
      have hv := at_mul_left hu (mat k⁻¹)
      have hv' := at_mul_left hu' (mat k⁻¹)
      have h1 := hint _ hv f₀
      have h2 := hint _ hv' f₀
      rw [hcan] at h1 h2
      have e1 := (hL _ _ _).2.2.1 _ hg h1
      have e2 := (hL _ _ _).2.2.1 _ hg' h2
      have key := hε _ _ hv hv' (fun w => ?_) _ _ (hAD _ hv f₀) (hAD _ hv' f₀)
      · rw [e1, e2, key, map_smul]
      · have hm : (mat k⁻¹).map (piInf (τ w)) * (mat k).map (piInf (τ w)) = 1 := by
          rw [← Matrix.map_mul]
          change (mat (k⁻¹ * k)).map _ = 1
          rw [inv_mul_cancel]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        have hm' : (mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w)) = 1 := mul_eq_one_comm.1 hm
        have hc : (mat k⁻¹).map (piInf (τ w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (τ w)) := by
          calc _ = (mat k⁻¹).map (piInf (τ w)) * X.θ w *
                ((mat k).map (piInf (τ w)) * (mat k⁻¹).map (piInf (τ w))) := by rw [hm', Matrix.mul_one]
            _ = (mat k⁻¹).map (piInf (τ w)) * (X.θ w * (mat k).map (piInf (τ w))) *
                (mat k⁻¹).map (piInf (τ w)) := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [← (hk.2 w).eq, ← Matrix.mul_assoc, hm, Matrix.one_mul]
        rw [Matrix.map_mul, Matrix.map_mul, huu w, Matrix.mul_smul]
        congr 1
        simp only [← Matrix.mul_assoc]
        rw [hc]
    · have e : φ₁ = D u φ := (hL _ _ _).2.2.1 _ hφ₁ (hAD u hu φ)
      rw [e]
      exact Submodule.mem_sInf.2 fun N hN =>
        hN.2 _ (at_mul_left hu _) _ (Submodule.mem_sInf.1 hφ N hN) _ (hint u hu φ)
  rw [(hL f f₁ (A f)).2.2.2.1 _ hf₁ (hA f)]
  exact hle hf

end GlobalTheory.FockCompactX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagGenDiag
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

variable {D : D7}

section Rescale

variable {S S₀ : HSp D} {ρ : ℕ}

theorem sandwich {m n : ℕ} (A : Matrix (Fin S.rank) (Fin m) D.host.E) (B : Matrix (Fin S.rank) (Fin n) D.host.E)
    (P : Matrix (Fin m) (Fin m) D.host.E) (Q : Matrix (Fin n) (Fin n) D.host.E) :
    (A * P)ᴴ * S.gram * (B * Q) = Pᴴ * (Aᴴ * S.gram * B) * Q := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

def diagDec (d : HypDec S S₀ ρ) (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) : HypDec S S₀ ρ where
  e := d.e * diagonal l
  e' := d.e' * diagonal fun a => (star (l a))⁻¹
  i₀ := d.i₀
  ee := by rw [sandwich, d.ee, Matrix.mul_zero, Matrix.zero_mul]
  e'e' := by rw [sandwich, d.e'e', Matrix.mul_zero, Matrix.zero_mul]
  e'e := by
    rw [sandwich, d.e'e, Matrix.mul_one, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply, star_inv₀, star_star]
    exact inv_mul_cancel₀ (hl a)
  iso := d.iso
  i₀e := by rw [← Matrix.mul_assoc, d.i₀e, Matrix.zero_mul]
  i₀e' := by rw [← Matrix.mul_assoc, d.i₀e', Matrix.zero_mul]
  rank_add := d.rank_add

theorem perp_diag {e : Matrix (Fin S.rank) (Fin ρ) D.host.E} (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0)
    (x : Fin S.rank → D.host.E) (hx : ((e * diagonal l)ᴴ * S.gram).mulVec x = 0) : (eᴴ * S.gram).mulVec x = 0 := by
  rw [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, ← mulVec_mulVec] at hx
  funext j
  have := congrFun hx j
  rw [mulVec_diagonal] at this
  simp only [Pi.zero_apply, Pi.star_apply, mul_eq_zero, star_eq_zero] at this
  rcases this with h | h
  · exact absurd h (hl j)
  · exact h

theorem flagGen_diag {e : Matrix (Fin S.rank) (Fin ρ) D.host.E} (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) (g : GA D S)
    (hg : (∀ i : Fin ρ, ∃ a : Fin ρ → AE D, (∀ j, i ≤ j → a j = 0) ∧
      (subOne S g).mulVec (ratV fun k => e k i) = (e.map (incA D)).mulVec a) ∧
      ∀ x : Fin S.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * S.gram).mulVec x = 0 →
        ∃ a : Fin ρ → AE D, (subOne S g).mulVec (ratV x) = (e.map (incA D)).mulVec a) :
    (∀ i : Fin ρ, ∃ a : Fin ρ → AE D, (∀ j, i ≤ j → a j = 0) ∧
      (subOne S g).mulVec (ratV fun k => (e * diagonal l) k i) = ((e * diagonal l).map (incA D)).mulVec a) ∧
      ∀ x : Fin S.rank → D.host.E,
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (e * diagonal l) * S.gram).mulVec x = 0 →
        ∃ a : Fin ρ → AE D, (subOne S g).mulVec (ratV x) = ((e * diagonal l).map (incA D)).mulVec a := by
  have hmv : ∀ a : Fin ρ → AE D, ((e * diagonal l).map (incA D)).mulVec (fun j => incA D (l j)⁻¹ * a j) =
      (e.map (incA D)).mulVec a := fun a => by
    funext k
    simp only [mulVec, dotProduct, Matrix.map_apply, mul_diagonal]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_assoc, ← mul_assoc (incA D (l j)), ← map_mul, mul_inv_cancel₀ (hl j), map_one, one_mul]
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha0, ha⟩ := hg.1 i
    refine ⟨fun j => incA D (l j)⁻¹ * (incA D (l i) * a j), fun j hj => ?_, ?_⟩
    · show incA D (l j)⁻¹ * (incA D (l i) * a j) = 0
      rw [ha0 j hj, mul_zero, mul_zero]
    have hcol : (ratV fun k => (e * diagonal l) k i) = incA D (l i) • ratV fun k => e k i := by
      funext k
      show incA D ((e * diagonal l) k i) = incA D (l i) * incA D (e k i)
      rw [mul_diagonal, map_mul, mul_comm]
    rw [hcol, mulVec_smul, ha, ← mulVec_smul, ← hmv]
    rfl
  · have h1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (e * diagonal l) = (e * diagonal l)ᴴ := rfl
    have h2 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e = eᴴ := rfl
    rw [h1] at hx
    obtain ⟨a, ha⟩ := hg.2 x (by rw [h2]; exact perp_diag l hl x hx)
    exact ⟨_, ha.trans (hmv a).symm⟩

theorem nFlag_diag (e : Matrix (Fin S.rank) (Fin ρ) D.host.E) (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) :
    NFlag S (e * diagonal l) = NFlag S e := by
  have hl' : ∀ a, (l a)⁻¹ ≠ 0 := fun a => inv_ne_zero (hl a)
  have e0 : diagonal l * diagonal (fun a => (l a)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact mul_inv_cancel₀ (hl a)
  have e1 : e * diagonal l * diagonal (fun a => (l a)⁻¹) = e := by
    rw [Matrix.mul_assoc, e0, Matrix.mul_one]
  unfold NFlag
  congr 1
  ext g
  refine ⟨fun h => ?_, fun h => flagGen_diag l hl g h⟩
  have := flagGen_diag (e := e * diagonal l) (fun a => (l a)⁻¹) hl' g h
  rwa [e1] at this

def trMeas {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (ν : Measure N) : Measure N' := h ▸ ν

def trSet {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (𝓝 : Set N) : Set N' := h ▸ 𝓝

theorem isUnit_trans {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (ν : Measure N) (𝓝 : Set N)
    (hu : ν.IsHaarMeasure ∧ IsFundamentalDomain ((GQ S).subgroupOf N) 𝓝 ν ∧ ν 𝓝 = 1) :
    (trMeas h ν).IsHaarMeasure ∧ IsFundamentalDomain ((GQ S).subgroupOf N') (trSet h 𝓝) (trMeas h ν) ∧
      trMeas h ν (trSet h 𝓝) = 1 := by
  subst h
  exact hu

def volNOf {S₀' : HSp D} {ρ' : ℕ} {d : HypDec S S₀ ρ} {d' : HypDec S S₀' ρ'} (h : NFlag S d.e = NFlag S d'.e)
    (v : VolN d) : VolN d' :=
  ⟨trMeas h v.ν, trSet h v.𝓝, isUnit_trans h v.ν v.𝓝 v.unit⟩

end Rescale

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj

variable {T : Type}

noncomputable def splitFam {S : Arrow T → Type} {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z), (p.comp q).Fam S → p.Fam S × q.Fam S
  | _, .nil, d => (d, ())
  | _, .snoc _ q, d => ((splitFam q d.1).1, ((splitFam q d.1).2, d.2))

theorem all_splitFam {S : Arrow T → Type} (P : ∀ a, S a → Prop) {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : (p.comp q).Fam S), Path.Fam.All P d →
      Path.Fam.All P (splitFam q d).1 ∧ Path.Fam.All P (splitFam q d).2
  | _, .nil, _, h => ⟨h, trivial⟩
  | _, .snoc _ q, d, h => ⟨(all_splitFam P q d.1 h.1).1, (all_splitFam P q d.1 h.1).2, h.2⟩

noncomputable def getD {S : Arrow T → Type} (t : T) (i : ℕ) : ∀ (n : ℕ), (downPath t i n).Fam S → ∀ j, j < n → S (.down t i j)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, j, h =>
    if hj : j < n then getD t i n (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).2 j hj
    else (show n = j by omega) ▸ (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).1.2

theorem getD_all {S : Arrow T → Type} (P : ∀ a, S a → Prop) (t : T) (i : ℕ) :
    ∀ (n : ℕ) (d : (downPath t i n).Fam S), Path.Fam.All P d → ∀ j (h : j < n), P (.down t i j) (getD t i n d j h)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, hd, j, h => by
    have hs := all_splitFam P (p := Path.one (.down t i n)) (downPath t i n) d hd
    unfold getD
    split_ifs with hj
    · exact getD_all P t i n _ hs.2 j hj
    · obtain rfl : n = j := by omega
      exact hs.1.2

end GlobalTheory.RowChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepLeftChangeMeasurePreserving
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.StepLeft
open Classical

theorem affine {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k) :
    (fun a : StepVar n c n' => (g * stepPt x₀ e) a.1.1 a.1.2) =
      (stepLin n' g).mulVec e + fun a => (g * stepPt x₀ (0 : StepVar n c n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2 := by
  funext a
  obtain ⟨⟨r, s⟩, ha⟩ := a
  have h1 : (stepLin n' g).mulVec e ⟨(r, s), ha⟩ =
      ∑ t, g r t * (if h : (Free (c / 2 + 1) (t, s) ∨ Kept (t, s)) then e ⟨(t, s), h⟩ else 0) := by
    have h2 : (stepLin n' g).mulVec e ⟨(r, s), ha⟩ = ∑ b : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)),
        (if s = b.2 then g r b.1 else 0) * (if h : (Free (c / 2 + 1) b ∨ Kept b) then e ⟨b, h⟩ else 0) := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun b => Free (c / 2 + 1) b ∨ Kept b)]
      rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun b : {b // ¬ (Free (c / 2 + 1) b ∨ Kept b)} => _)
        (fun b _ => by rw [dif_neg b.2, mul_zero]), add_zero]
      simp only [Matrix.mulVec, dotProduct, stepLin, of_apply]
      refine Finset.sum_congr rfl fun b _ => by rw [dif_pos b.2]
    rw [h2, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_eq_single s]
    · simp
    · intro s' _ hs
      simp [Ne.symm hs]
    · simp
  simp only [Pi.add_apply]
  rw [h1]
  simp only [stepPt, Matrix.mul_apply, Matrix.add_apply, of_apply, mul_add, Finset.sum_add_distrib, Pi.zero_apply,
    dite_eq_ite, ite_self, mul_zero, Finset.sum_const_zero, add_zero]
  ring

theorem det_unip {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (u : GL (n ⊕ Fin c) k) (hu : u ∈ symN k n c) : (stepLin n' u.val).det = 1 := by
  apply GlobalTheory.RootExSource.det_eq_one_of_unip (fun a : StepVar n c n' => GlobalTheory.DiagVol.ordL c a.1.1)
  intro a b hab
  have hu' : u.val a.1.1 b.1.1 = (1 : Matrix _ _ k) a.1.1 b.1.1 := GlobalTheory.DiagVol.symN_le_unipSub hu a.1.1 b.1.1 hab
  simp only [stepLin, of_apply]
  by_cases hab' : a = b
  · subst hab'; simp [hu']
  · rw [Matrix.one_apply_ne hab']
    split_ifs with h
    · rw [hu', Matrix.one_apply_ne]
      intro hr
      exact hab' (Subtype.ext (Prod.ext hr h))
    · rfl

theorem var_inl_iff {n n' : Type} {c : ℕ} (r t : n) (s : n' ⊕ Fin (c + 1)) :
    (Free (c / 2 + 1) ((Sum.inl r : n ⊕ Fin c), s) ∨ Kept ((Sum.inl r : n ⊕ Fin c), s)) ↔
      (Free (c / 2 + 1) ((Sum.inl t : n ⊕ Fin c), s) ∨ Kept ((Sum.inl t : n ⊕ Fin c), s)) := by
  rcases s with s | s <;> simp [Free, Kept]

theorem embX_apply_eq_zero {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] {c : ℕ} (κ : GL n k)
    (r t : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) (hr : Free (c / 2 + 1) (r, s) ∨ Kept (r, s))
    (ht : ¬ (Free (c / 2 + 1) (t, s) ∨ Kept (t, s))) : (embX c κ).val r t = 0 := by
  change (fromBlocks κ.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r t = 0
  rcases r with r | r <;> rcases t with t | t
  · exact absurd ((var_inl_iff r t s).1 hr) ht
  · rfl
  · rfl
  · simp only [fromBlocks_apply₂₂]
    rw [Matrix.one_apply_ne]
    rintro rfl
    exact ht hr

theorem mul_embX {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (κ : GL n k) (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) :
    stepLin n' ((embX c κ).val * g) = stepLin n' (embX c κ).val * stepLin n' g := by
  ext a b
  obtain ⟨⟨r, s⟩, ha⟩ := a
  obtain ⟨⟨r', s'⟩, hb⟩ := b
  set E := (embX c κ).val
  set F : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k := fun d =>
    (if s = d.2 then E r d.1 else 0) * (if d.2 = s' then g d.1 r' else 0) with hF
  have hF0 : ∀ d : {d : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // ¬ (Free (c / 2 + 1) d ∨ Kept d)}, F d.1 = 0 := by
    rintro ⟨⟨t, s''⟩, hd⟩
    by_cases h1 : s = s''
    · subst h1
      have hz : E r t = 0 := embX_apply_eq_zero κ r t s ha hd
      simp [hF, hz]
    · simp [hF, h1]
  have hR : (stepLin n' E * stepLin n' g) ⟨(r, s), ha⟩ ⟨(r', s'), hb⟩ = ∑ d, F d := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun d => Free (c / 2 + 1) d ∨ Kept d),
      Finset.sum_eq_zero (s := Finset.univ) (fun d _ => hF0 d), add_zero]
    simp only [Matrix.mul_apply, stepLin, of_apply, hF]
  rw [hR, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single s]
  · simp only [stepLin, of_apply, hF, Matrix.mul_apply]
    split_ifs with h
    · simp
    · simp [h]
  · intro s'' _ hs
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [hF, Ne.symm hs]
  · simp

theorem mp_affine {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) (hM : valuation k M.det = 1) (b : ι → k) :
    MeasurePreserving (fun e => M.mulVec e + b) (Measure.pi fun _ : ι => ν) (Measure.pi fun _ : ι => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  have hU : IsUnit M.det := isUnit_iff_ne_zero.2 fun h => by rw [h, map_zero] at hM; exact zero_ne_one hM
  have h1 := GlobalTheory.WeilM.smul_map_mulVec_pi ν M hU.unit hU.unit_spec
  have h2 : distribHaarChar k hU.unit = 1 := by
    have := nabs_of_valuation_eq_one (k := k) (x := hU.unit) (by rw [hU.unit_spec]; exact hM)
    exact NNReal.coe_eq_one.1 this
  rw [h2, ENNReal.coe_one, one_smul] at h1
  have hm : Measurable M.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  exact (measurePreserving_add_right (Measure.pi fun _ : ι => ν) b).comp ⟨hm, h1⟩

end GlobalTheory.StepLeft

namespace GlobalTheory.StepLeft
open Classical

theorem left_change : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure],
    ∀ v ∈ symN k n c, ∀ κ : GL n k, valuation k (gdet κ : k) = 1 → ∀ x₀ : Matrix n n' k,
      ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k), MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧
        ∀ e, ((v * embX c κ)⁻¹).val * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (φ e) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ν _ v hv κ hκ x₀
  haveI := GlobalTheory.SplitWeil.secondCountable k
  set g := ((v * embX c κ)⁻¹).val with hgdef
  set M := stepLin n' g with hMdef
  set b : StepVar n c n' → k := fun a =>
    (g * stepPt x₀ (0 : StepVar n c n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2 with hb
  have hg : g = (embX c κ⁻¹).val * (v⁻¹).val := by
    rw [hgdef, _root_.mul_inv_rev, map_inv, Units.val_mul]
  have hκ' : valuation k (gdet κ⁻¹ : k) = 1 := by
    rw [gdet, map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    exact (congrArg (·⁻¹) hκ).trans inv_one
  have hdet : valuation k M.det = 1 := by
    rw [hMdef, hg, mul_embX, det_mul, map_mul, det_unip _ (inv_mem hv), map_one, mul_one]
    exact GlobalTheory.T.valuation_det_stageVariables_embedGL_eq_one (n' := n') (c := c) κ⁻¹ hκ'
  have hM0 : IsUnit M.det := isUnit_iff_ne_zero.2 fun h => by rw [h, map_zero] at hdet; exact zero_ne_one hdet
  have hcont : ∀ (A : Matrix (StepVar n c n') (StepVar n c n') k) (w : StepVar n c n' → k),
      Continuous fun e : StepVar n c n' → k => A.mulVec e + w := fun A w =>
    (continuous_const.matrix_mulVec continuous_id).add continuous_const
  let φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k) :=
    { toFun := fun e => M.mulVec e + b
      invFun := fun e => M⁻¹.mulVec e + M⁻¹.mulVec (-b)
      left_inv := fun e => by
        simp only [mulVec_add, mulVec_mulVec, nonsing_inv_mul _ hM0, one_mulVec, mulVec_neg, add_neg_cancel_right]
      right_inv := fun e => by
        simp only [mulVec_add, mulVec_mulVec, mul_nonsing_inv _ hM0, one_mulVec, mulVec_neg, neg_add_cancel_right]
      measurable_toFun := (hcont M b).measurable
      measurable_invFun := (hcont M⁻¹ _).measurable }
  refine ⟨φ, mp_affine ν M hdet b, fun e => ?_⟩
  change g * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (M.mulVec e + b)
  rw [hMdef, hb, ← affine]
  exact GlobalTheory.T.periodStep_inv_mul_point_shape v hv κ x₀ e

end GlobalTheory.StepLeft

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeRealPlacePureDatumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDerivative_realPlace_pureDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        ∀ f : WO S X → ℂ, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f →
        ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) (g₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (M.heisLine Bs.ψ (cS.symm (lineAt θ τ z 1))) g g₁ →
          IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ) (dRho (heisO ψ (sgn ε S) X) θ τ z f) := by
  first | exact @GlobalTheory.HeisLineTransfer.isDatum_dRho_heisO | exact GlobalTheory.HeisLineTransfer.isDatum_dRho_heisO | (intros; apply GlobalTheory.HeisLineTransfer.isDatum_dRho_heisO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeFiniteSpanStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergLine_derivative_finite_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ (m : ℕ) (L : Fin m → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)),
      ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D f) ∧
        ∀ f, D f ∈ Submodule.span ℂ (Set.range fun i => L i f) := by
  first | exact @GlobalTheory.HeisDerivSpan.heisLine_deriv_finite_span | exact GlobalTheory.HeisDerivSpan.heisLine_deriv_finite_span | (intros; apply GlobalTheory.HeisDerivSpan.heisLine_deriv_finite_span <;> assumption)
end

