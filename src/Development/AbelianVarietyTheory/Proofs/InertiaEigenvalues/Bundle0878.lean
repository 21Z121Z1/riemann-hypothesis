import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.IntegralSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0330
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0814
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0816
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0811
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0865
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0871
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0873
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesRay
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cmp.SeriesRay

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke

variable {D : D7}

section Forms

variable {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)

theorem sum_mem_intForms (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))) {m : ℕ} (x : Fin m → C.d.c₂.F)
    (hx : ∀ k, ∀ la ∈ S, la.valuation C.d.c₂.F (x k) ≤ 1) (φ : Fin m → GA D (T.V j σ) → ℂ) (hφ : ∀ k, φ k ∈ C.intForms a n S) :
    (∑ k, C.σ₂ (x k) • φ k) ∈ C.intForms a n S := by
  choose f hf e using hφ
  refine ⟨∑ k, x k • f k, ⟨⟨sum_mem fun k _ => Submodule.smul_mem _ _ (hf k).1.1, ?_⟩, fun la hla v hv => ?_⟩, ?_⟩
  · rw [map_sum]
    exact sum_mem fun k _ => by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (hf k).1.2
  · have hV := isVal_valSet la v hv
    exact GlobalTheory.IdemInt.nonneg_sum hV _ _ fun k _ => GlobalTheory.IdemInt.nonneg_smul hV (hx k la hla) ((hf k).2 la hla v hv)
  · simp only [← e, Cover.rd, map_sum, map_smulₛₗ, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _

end Forms

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

variable {T i} in

def FieldRay (Lat : Submodule ℤ (VsV D i ℂ)) (C : Cover T ((i : ℕ) + 1) T.σ₀) : Prop :=
  (R.C.mu0 i * R.C.eta⁻¹).ValuesIn (-1 / 2) C.σ₂ ∧
    (∀ v ∈ Lat, ∀ m, ∃ a, C.σ₂ a = MvPolynomial.coeff m (v : Pol ℂ D.what₂.Tau (Vc D i).rank)) ∧ IntegralSeries.HasRay C

def SerIntRay (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i) (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ)
    (c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) : Prop :=
  ∃ ph : ℂ, ‖ph‖ = 1 ∧ ∀ l : ℕ, l.Prime → ∀ s ∈ GfC (Vc D i), ∀ Lat : Submodule ℤ (VsV D i ℂ), Lat.FG →
    ∃ c : ℕ, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, TwistSeries.IsTowerCover T i l C → (∀ a, Dom a κ.n → C.IsPinned a κ.n) →
      FieldRay R Lat C → ∀ S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F)), TwistSeries.OverPrime l S →
        ∀ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, TwistSeries.IsTwist C.σ₂ C.d.pd xi →
          ∀ Φ f : WO (Vc D i) (Wc D i) → ℂ, TwistSeries.IsLevelVec R i C.d.l₂.M Φ f → (∀ t, TwistSeries.IntVal C.σ₂ S (Φ t)) →
            ∀ v ∈ Lat, ∃ φ ∈ C.intForms (wtA κ) κ.n S, ∀ g : GA D (Wc D i),
              castDict hV φ g = (l : ℂ) ^ c *
                (ph * (((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) *
                  TwistSeries.series R i u s f (c0 v) g))

omit [Algebra T.Q.c.F D.what₂.LL] in

def DescIntAll : Prop :=
  ∀ l : ℕ, l.Prime → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, TwistSeries.IsTowerCover T i l C → (∀ a, Dom a κ.n → C.IsPinned a κ.n) →
    TwistSeries.UnramAt C.inc (IntegralSeries.placesOver C.d.c₂.F l) →
      ∀ φ ∈ C.intForms (wtA κ) κ.n (IntegralSeries.placesOver C.d.c₂.F l),
        (∀ k ∈ T.Kf ((i : ℕ) + 1) T.σ₀, ∀ h, φ (h * k) = φ h) →
        ∃ (m : ℕ) (x : Fin m → ℂ) (ψ : Fin m → (GA D (T.V ((i : ℕ) + 1) T.σ₀) → ℂ)),
          (∀ a, TwistSeries.IntVal C.σ₂ (IntegralSeries.placesOver C.d.c₂.F l) (x a)) ∧
            (∀ a, ψ a ∈ baseInt T ((i : ℕ) + 1) T.σ₀ (wtA κ) κ.n (TwistSeries.below C.inc (IntegralSeries.placesOver C.d.c₂.F l))) ∧
            φ = ∑ a, x a • ψ a

section Data

variable {T}

variable {R i}

abbrev sb (U : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) :=
  GlobalTheory.AdTh.PhaseMap.sub (m := (Wc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1) U

end Data

section First

variable {T R i κ}

def ker1 (s : GA D (Vc D i)) (g : GA D (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) : PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] ℂ :=
  LinearMap.proj 0 ∘ₗ R.ωP i A.μ0 (s, g) ∘ₗ
    pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) f

variable {hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i} {v₀ : (R.MW i (sg0 D A)).Vec} {u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ}
  {c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W} {ka : ℂ} {J : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank}

variable (u c0 ka J) in

structure Dict : Prop where
  norm : ‖ka‖ = 1
  rat : ∀ k : Subfield ℂ, (inC T.Q.c).fieldRange ≤ k → ∀ v : VsV D i ℂ,
    (∀ m, MvPolynomial.coeff m (v : Pol ℂ D.what₂.Tau (Vc D i).rank) ∈ k) ↔ ∀ d, MvPolynomial.coeff d (J v) ∈ k
  eq : ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v,
    IntegralSeries.fock R i (R.BV i) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 v)) = ka • IntegralSeries.fock R i (fun _ => 1) f (J v)

theorem Dict.series (h : Dict u c0 ka J) {f} (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) (s v g) :
    TwistSeries.series R i u s f (c0 v) g = ka * ker1 (R := R) s g f (J v) := by
  have e := congrArg (fun x => R.ωP i A.μ0 (s, g) x 0) (h.eq f hf v)
  simp only [map_smul] at e
  exact e

end First

def SerIntStd : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
      IntegralSeries.SerIntAt T R i T.σ₀ hV (κ i) (v₀ i (sg0 D A)) ∧ IntegralSeries.DescIntAt T T.σ₀ ((i : ℕ) + 1) (wtA (κ i)) (κ i).n

def SerIntCommon : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
      (∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
        ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, TwistSeries.IsCoefMap R i c0 → SerIntRay T R i (κ i) hV u c0) ∧
      DescIntAll T i (κ i)

end GlobalTheory.Cmp.SeriesRay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalKernelNormSqMulLatticeIndexEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.LocKerMod

theorem idxAt_frame : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.LFun.IsFrameAt w (frameLat T) a → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, ∀ g : GlobalTheory.FinZeta.Gv T v, GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g = a * (k₁ * t * k₂) * a⁻¹ → idxAt T w h g = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := GlobalTheory.T.localLatticeIndex_cartanDecomposition_eq_normPow

theorem latIndex_inert : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = idxAt T w h g := GlobalTheory.T.selfDualLatticeIndex_inertPlace_eq_localIndex

theorem latIndex_split : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (h' : w'.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → w ≠ w' → ∀ g : GlobalTheory.FinZeta.Gv T v, latIndex T (GlobalTheory.FinZeta.embV T v g) = idxAt T w h g * idxAt T w' h' g := GlobalTheory.T.selfDualLatticeIndex_splitPlace_eq_mul
end GlobalTheory.LocKerMod

namespace GlobalTheory.LocKerMod
open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.LFun.SplitTie

theorem idx_inert : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c e → ∀ (d : Fin T.rank → ℤ) (t : GU c T.rank), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU c T.rank, ∀ k₂ ∈ KU c T.rank, latIndex T (GlobalTheory.FinZeta.embV T v (e.symm (k₁ * t * k₂))) = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := by
  intro D T v w h hw c ϖ e hU he d t ht k₁ hk₁ k₂ hk₂
  obtain ⟨-, ⟨a, ha, -, hea⟩, -⟩ := he
  have hϖ : IsUnifV D.host.E w ϖ := hU.2.2.2.1
  have hK : ∀ k ∈ KU c T.rank, (k : GL (Fin T.rank) (w.adicCompletion D.host.E)) ∈ KGL w T.rank :=
    fun k hk => (Subgroup.mem_subgroupOf.1 hk).2
  rw [latIndex_inert D T v w h hw]
  refine idxAt_frame D T v w h a ha ϖ hϖ d (t : GL (Fin T.rank) (w.adicCompletion D.host.E)) ht _ (hK k₁ hk₁) _
    (hK k₂ hk₂) _ ?_
  have h1 := hea (e.symm (k₁ * t * k₂))
  rw [MulEquiv.apply_symm_apply] at h1
  rw [show ((k₁ : GL (Fin T.rank) (w.adicCompletion D.host.E)) * t * k₂) = ((k₁ * t * k₂ : GU c T.rank) : GL (Fin T.rank) (w.adicCompletion D.host.E)) by simp, h1]
  group

theorem idx_split : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, latIndex T (GlobalTheory.FinZeta.embV T v (e.symm (k₁ * t * k₂))) = qV D.host.E w ^ (∑ i, |d i|).toNat := by
  intro D T v w h hv e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  have hE := isCMExt_host D
  have hJ := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 T
  have hL := SelfDual.isSelfDualAt_frameLat D T v
  obtain ⟨-, w', hne, hu, -, -, -⟩ := GlobalTheory.LFun.SplitChart.split_chart_and_places hE hJ (frameLat_fg T)
    (SelfDual.isLattice_frameLat T).span_eq_top h hv hL
  have h' : w'.under (𝓞 D.host.F) = v := (hu w').2 (Or.inr rfl)
  obtain ⟨c, hc, hqc, -, he'⟩ := exists_conj_chart hE hJ hL hne h h' he
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    unfold IsUnifV at hϖ
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hO : ∀ a, c a ∈ Formalism.UG.Ov D.host.E w' ↔ a ∈ Formalism.UG.Ov D.host.E w := fun a => map_mem_Ov_iff c hc a
  have htinv : ((t⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)) : Matrix _ _ _) = Matrix.diagonal (fun i => ϖ ^ (-d i)) := by
    have h1 : (t : Matrix _ _ _) * Matrix.diagonal (fun i => ϖ ^ (-d i)) = 1 := by
      rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
    rw [Matrix.coe_units_inv, Matrix.inv_eq_right_inv h1]
  have hdiag : (invT c T.rank t).1 = Matrix.diagonal (fun i => c ϖ ^ (-d i)) := by
    ext i j
    rw [invT_val, htinv, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp [map_zpow₀]
    · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]
  have hunif : IsUnifV D.host.E w' (c ϖ) := by
    unfold IsUnifV at hϖ ⊢
    rw [hc, hϖ]
  have hK : ∀ k ∈ KGL w T.rank, invT c T.rank k ∈ KGL w' T.rank := fun k hk => (mem_iff_invT c hO k).1 hk
  obtain ⟨⟨a, ha, hea⟩, -⟩ := he
  obtain ⟨⟨a', ha', hea'⟩, -⟩ := he'
  rw [latIndex_split D T v w w' h h' hv hne]
  have e1 : GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)) = a * (k₁ * t * k₂) * a⁻¹ := by
    have := hea (e.symm (k₁ * t * k₂))
    rw [MulEquiv.apply_symm_apply] at this
    calc _ = a * (a⁻¹ * GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h (e.symm (k₁ * t * k₂)) * a) * a⁻¹ := by group
      _ = _ := by rw [← this]
  have e2 : GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' (e.symm (k₁ * t * k₂)) =
      a' * (invT c T.rank k₁ * invT c T.rank t * invT c T.rank k₂) * a'⁻¹ := by
    have := hea' (e.symm (k₁ * t * k₂))
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, map_mul, map_mul] at this
    calc _ = a' * (a'⁻¹ * GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h' (e.symm (k₁ * t * k₂)) * a') * a'⁻¹ := by group
      _ = _ := by rw [← this]
  have hs : ∑ i, |d i| = (∑ i, max (d i) 0) + ∑ i, max (-d i) 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total 0 (d i) with hd | hd
    · rw [abs_of_nonneg hd, max_eq_left hd, max_eq_right (by omega), add_zero]
    · rw [abs_of_nonpos hd, max_eq_right hd, max_eq_left (by omega), zero_add]
  rw [idxAt_frame D T v w h a ha ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ _ e1,
    idxAt_frame D T v w' h' a' ha' (c ϖ) hunif (fun i => -d i) _ hdiag _ (hK k₁ hk₁) _ (hK k₂ hk₂) _ e2, hqc,
    ← pow_add, hs, Int.toNat_add (Finset.sum_nonneg fun i _ => le_max_right _ _) (Finset.sum_nonneg fun i _ => le_max_right _ _)]
end GlobalTheory.LocKerMod

namespace GlobalTheory.LocKerMod

theorem exists_over {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
  have := v.isMaximal
  obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1
      (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
  exact ⟨⟨Q, hQ.isPrime, fun h0 => v.ne_bot (by
    rw [← e, h0, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)])⟩,
    HeightOneSpectrum.ext e⟩

theorem norm_split (q : ℕ) (hq : 0 < q) (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) (m s : ℤ) (hs : 0 ≤ s) :
    ‖z ^ m * (q : ℂ) ^ (-((N : ℂ) / 2) * (s : ℂ))‖ ^ 2 * ((q ^ s.toNat : ℕ) : ℝ) ^ N = 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [norm_mul, norm_zpow, hz, _root_.one_zpow, one_mul, show (q : ℂ) = ((q : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hq']
  have hre : (-((N : ℂ) / 2) * (s : ℂ)).re = -((N : ℝ) / 2) * s := by
    simp [Complex.mul_re]
  rw [hre, ← Real.rpow_natCast, ← Real.rpow_mul hq'.le, Nat.cast_pow, ← Real.rpow_natCast (q : ℝ) s.toNat,
    ← Real.rpow_natCast, ← Real.rpow_mul hq'.le, ← Real.rpow_add hq']
  have : (s.toNat : ℝ) = s := by exact_mod_cast Int.toNat_of_nonneg hs
  rw [this]
  have : -((N : ℝ) / 2) * s * ((2 : ℕ) : ℝ) + s * N = 0 := by push_cast; ring
  rw [this, Real.rpow_zero]

theorem norm_inert (q : ℕ) (hq : 0 < q) (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) (m : ℤ) (hm : 0 ≤ m) :
    ‖(z * ((q : ℂ) ^ N)⁻¹) ^ m‖ ^ 2 * (((q ^ 2) ^ m.toNat : ℕ) : ℝ) ^ N = 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  simp only [Int.toNat_natCast, zpow_natCast, norm_pow, norm_mul, norm_inv, hz, one_mul, Complex.norm_natCast]
  push_cast
  rw [← pow_mul, ← pow_mul, ← pow_mul, inv_pow, ← pow_mul]
  rw [show N * (k * 2) = 2 * (k * N) by ring]
  exact inv_mul_cancel₀ (pow_ne_zero _ hq'.ne')

theorem sq_norm_mul_latIndex : ∀ (D : D7) (T : HSp D) (N : ℕ) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : GlobalTheory.FinZeta.Gv T v → ℂ), GlobalTheory.FinZeta.IsLocKer T N (GlobalTheory.LFun.val χ) v φ → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w) → ∀ a : GlobalTheory.FinZeta.Gv T v, ‖φ a‖ ^ 2 * (latIndex T (GlobalTheory.FinZeta.embV T v a) : ℝ) ^ N = 1 := by
  intro D T N χ v φ hφ _ a
  obtain ⟨w, h⟩ := exists_over (D := D) v
  by_cases hs : IsSplit (E := D.host.E) v
  · obtain ⟨e, he⟩ := (GlobalTheory.ChartsAll.exists_charts D T v w h).1 hs
    have hk := (hφ w h).1 hs e he
    obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV (E := D.host.E) w
    obtain ⟨d, -, k₁, hk₁, k₂, hk₂, ec⟩ :=
      Formalism.UG.Final.CartanDecomp D.host.E w T.rank ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ (e a)
    have htd : (k₁⁻¹ * e a * k₂⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 =
        Matrix.diagonal (fun i => ϖ ^ d i) := by
      rw [Units.val_mul, Units.val_mul, ec]
      simp [Matrix.mul_assoc]
      rfl
    have ha : a = e.symm (k₁ * (k₁⁻¹ * e a * k₂⁻¹) * k₂) := by
      rw [show k₁ * (k₁⁻¹ * e a * k₂⁻¹) * k₂ = e a by group, MulEquiv.symm_apply_apply]
    have hv := hk ϖ hϖ d _ htd k₁ hk₁ k₂ hk₂
    rw [Function.comp_apply, ← ha] at hv
    rw [hv]
    conv_lhs => rw [ha]
    rw [idx_split D T v w h hs e he ϖ hϖ d _ htd k₁ hk₁ k₂ hk₂]
    exact norm_split _ (Nat.pos_of_ne_zero fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0))
      _ (GlobalTheory.LFun.norm_val χ w) N _ _ (Finset.sum_nonneg fun i _ => abs_nonneg (d i))
  · have hI := GlobalTheory.LFun.exists_isInertChart D.sp.cm.sig (isCMExt_host D) v
    obtain ⟨hw, -, hch⟩ := (GlobalTheory.ChartsAll.exists_charts D T v w h).2 hs
    obtain ⟨-, ⟨c, hc, -⟩, -, hN, H⟩ := hI.2 w h hw
    obtain ⟨ϖ, hU⟩ := (H c hc).1
    obtain ⟨e, he⟩ := hch c hc
    have hk := (hφ w h).2 hw c ϖ e hU he
    obtain ⟨d, t, -, ht, k₁, hk₁, k₂, hk₂, ea⟩ := GlobalTheory.LFun.cartanU hU (e a)
    have ha : a = e.symm (k₁ * t * k₂) := by rw [← ea, MulEquiv.symm_apply_apply]
    have hv := hk d t ht k₁ hk₁ k₂ hk₂
    rw [Function.comp_apply, ← ha] at hv
    rw [hv]
    conv_lhs => rw [ha]
    rw [idx_inert D T v w h hw c ϖ e hU he d t ht k₁ hk₁ k₂ hk₂]
    have hq : qV D.host.E w = qV D.host.F v ^ 2 := hN
    rw [hq]
    exact norm_inert _ (Nat.pos_of_ne_zero fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0))
      _ (GlobalTheory.LFun.norm_val χ w) N _ (Finset.sum_nonneg fun i _ => le_max_right _ _)

end GlobalTheory.LocKerMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNonzeroRationalVectorLeShortestVector
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global
  GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

namespace GlobalTheory.RSTheta

theorem summable_tsum_norm_le_of_le_shortest (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (N : ℕ) (hN : Module.finrank ℝ (Fin a → Cinf E) ≤ N) :
    ∃ (M : ℕ) (C : ℝ), ∀ (h : GA E a) (A : ℝ) (c : (Fin a → E) → ℂ), 0 ≤ A →
      (∀ ξ : Fin a → E, (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)) ∉ latt a J →
        c ξ = 0) →
      (∀ ξ ξ' : Fin a → E, ξ' ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)) ∈ latt a J →
        ‖c ξ‖ * (1 + ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)‖) ^ M ≤
          A * ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)‖ ^ N) →
      Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∧
        ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ ≤ C * A := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · haveI : IsEmpty {ξ : Fin 0 → E // ξ ≠ 0} := ⟨fun ξ => ξ.2 (Subsingleton.elim _ _)⟩
    exact ⟨0, 0, fun _ _ _ _ _ _ => ⟨summable_empty, by simp⟩⟩
  set D := Module.finrank ℝ (Fin a → Cinf E) with hD
  have hD1 : 1 ≤ D := by rw [hD, finrank_pi_Cinf]; exact Nat.mul_pos ha Module.finrank_pos
  have hND : (D : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨K, hK, hlat⟩ := GlobalTheory.LatticeCount.tsum_one_add_norm_rpow_neg_le_regimes (V := Fin a → Cinf E)
    hD1 (M := ((N + D + 1 : ℕ) : ℝ)) (by push_cast; linarith)
  rw [← hD] at hlat
  refine ⟨N + D + 1, 2 ^ N * K, fun g A c hA hsupp hdec => ?_⟩
  let T : (Fin a → E) →+ (Fin a → Ad E) :=
    { toFun := fun ξ => (fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val
      map_zero' := by simp only [Pi.zero_apply, map_zero]; exact zero_vecMul _
      map_add' := fun x y => by simp only [Pi.add_apply, map_add]; exact add_vecMul _ _ _ }
  let TI : (Fin a → E) →+ (Fin a → Cinf E) := ((pInf E).toAddMonoidHom.compLeft (Fin a)).comp T
  let TF : (Fin a → E) →+ (Fin a → Af E) := ((pFin E).toAddMonoidHom.compLeft (Fin a)).comp T
  let P : AddSubgroup (Fin a → E) := (AddSubgroup.pi Set.univ fun _ => idealFiniteAdeles J).comap TF
  have hP : ∀ ξ, ξ ∈ P ↔ TF ξ ∈ latt a J := fun ξ => ⟨fun h i => h i trivial, fun h i _ => h i⟩
  obtain ⟨δ, hδ, hδle⟩ := exists_le_norm g (isCompact_latt J)
  replace hδle : ∀ ξ ∈ P, ξ ≠ 0 → δ ≤ ‖TI ξ‖ := fun ξ h h0 => hδle ξ h0 ((hP ξ).1 h)
  have hsP : ∀ ξ, c ξ ≠ 0 → ξ ∈ P := fun ξ h => (hP ξ).2 (by_contra fun h' => h (hsupp ξ h'))
  set S : Set ℝ := (fun ξ => ‖TI ξ‖) '' {ξ | ξ ∈ P ∧ ξ ≠ 0} with hS
  rcases S.eq_empty_or_nonempty with hS0 | hS0
  · have : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ = 0 := fun ξ => by
      by_contra h
      exact Set.eq_empty_iff_forall_notMem.1 hS0 _ ⟨ξ.1, ⟨hsP _ (norm_ne_zero_iff.1 h), ξ.2⟩, rfl⟩
    simp only [this, tsum_zero]
    exact ⟨summable_zero, by positivity⟩
  have hr : 0 < sInf S := hδ.trans_le (le_csInf hS0 (by rintro _ ⟨ξ, hξ, rfl⟩; exact hδle ξ hξ.1 hξ.2))
  have hrle : ∀ ξ ∈ P, ξ ≠ 0 → sInf S ≤ ‖TI ξ‖ := fun ξ h h0 =>
    csInf_le ⟨0, by rintro _ ⟨ξ, -, rfl⟩; exact norm_nonneg _⟩ ⟨ξ, ⟨h, h0⟩, rfl⟩
  obtain ⟨_, ⟨ξ₀, hξ₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hS0 (show sInf S < 2 * sInf S by linarith)
  generalize sInf S = r at hr hrle hlt
  obtain ⟨hsum, hlo, hhi⟩ := hlat (P.map TI) r hr (by
    rintro _ ⟨ξ, hξ, rfl⟩ h0
    exact hrle ξ hξ fun e => h0 (by rw [e, map_zero]))
  set B : ℝ := A * (2 * r) ^ N with hB
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ ξ, ‖c ξ‖ ≤ B * (1 + ‖TI ξ‖) ^ (-(((N + D + 1 : ℕ)) : ℝ)) := fun ξ => by
    have h1 := hdec ξ ξ₀ hξ₀.2 ((hP _).1 hξ₀.1)
    have hpos : 0 < (1 + ‖TI ξ‖) ^ (N + D + 1) := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hA)
    exact pow_le_pow_left₀ (norm_nonneg _) hlt.le _
  let j : {ξ // ξ ∈ P ∧ ξ ≠ 0} → {ξ : Fin a → E // ξ ≠ 0} := fun ξ => ⟨ξ.1, ξ.2.2⟩
  have hj : Function.Injective j := fun x y h => Subtype.ext (congrArg (fun z : {ξ : Fin a → E // ξ ≠ 0} => z.1) h)
  have hjs : ∀ ξ ∉ Set.range j, ‖c ξ‖ = 0 := fun ξ h => by
    by_contra h'
    exact h ⟨⟨ξ.1, hsP _ (norm_ne_zero_iff.1 h'), ξ.2⟩, rfl⟩
  let ι : {ξ // ξ ∈ P ∧ ξ ≠ 0} → ((P.map TI : Set (Fin a → Cinf E)) \ {0} : Set (Fin a → Cinf E)) := fun ξ =>
    ⟨TI ξ.1, ⟨ξ.1, ξ.2.1, rfl⟩, norm_pos_iff.1 (hr.trans_le (hrle _ ξ.2.1 ξ.2.2))⟩
  have hι : Function.Injective ι := fun x y h => Subtype.ext (by
    by_contra hne
    have h1 := hrle _ (P.sub_mem x.2.1 y.2.1) (sub_ne_zero.2 hne)
    rw [map_sub, show TI x.1 = TI y.1 from congrArg Subtype.val h, sub_self, norm_zero] at h1
    exact h1.not_gt hr)
  have hs1 := (hsum.mul_left B).comp_injective hι
  have hs2 : Summable ((fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∘ j) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hterm ξ.1) hs1
  refine ⟨(hj.summable_iff hjs).1 hs2, ?_⟩
  rw [← hj.tsum_eq (f := fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) fun ξ h => by_contra fun h' => h (hjs ξ h')]
  refine (Summable.tsum_le_tsum_of_inj ι hι (fun _ _ => by positivity) (fun ξ => hterm ξ.1) hs2
    (hsum.mul_left B)).trans ?_
  rw [tsum_mul_left]
  have key : ∀ e : ℝ, r ^ ((N : ℝ) + e) ≤ 1 → B * (K * r ^ e) ≤ 2 ^ N * K * A := by
    intro e he
    calc B * (K * r ^ e) = 2 ^ N * K * A * r ^ ((N : ℝ) + e) := by
          rw [hB, Real.rpow_add hr, Real.rpow_natCast, mul_pow]; ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) he
  rcases le_total r 1 with h1 | h1
  · exact (mul_le_mul_of_nonneg_left (hlo h1) hB0).trans (key _ (Real.rpow_le_one hr.le h1 (by linarith)))
  · exact (mul_le_mul_of_nonneg_left (hhi h1) hB0).trans
      (key _ (Real.rpow_le_one_of_one_le_of_nonpos h1 (by push_cast; linarith)))

end GlobalTheory.RSTheta
end
end

