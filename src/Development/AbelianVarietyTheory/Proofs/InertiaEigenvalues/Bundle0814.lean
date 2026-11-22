import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteDimensionalSpan
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.IntegralSeries
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0167
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0807
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0805
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTieWithSeries
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesInstall

variable {D : D7} {ρ : Setup D.ntw}

abbrev RdV (D : D7) (ρ : Setup D.ntw) : Type :=
  ∀ i (j : Fin D.R.m) b k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k]
    (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)

def rdVLin (rdV : RdV D ρ) (i) (j : Fin D.R.m) (b k Q ψ) :
    D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₗ[D.ntw.Ok i k]
      Via (D.ntw.Ok i k) (ρ.ek i b k) (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank) where
  toFun f := rdV i j b k Q ψ f
  map_add' f g := map_add _ f g
  map_smul' c f := by
    rw [← algebraMap_smul (FractionRing (D.ntw.Ok i k)) c f, map_smulₛₗ]
    rfl

open Classical in

def latI (rdV : RdV D ρ) (i) : ∀ n b k Q ψ, Submodule (D.ntw.Ok i k) (D.nexp.MtV i n b k Q ψ)
  | 0, b, k, Q, ψ => D.nexp.MtLat i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => if h : n < D.R.m ∧ TwOK i k Q ψ then
      (Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ)).comap (rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) else D.nexp.MtLat i (n + 1) b k Q ψ

def Onto (ρ : Setup D.ntw) (rdV : RdV D ρ) : Prop :=
  ∀ i j b k Q ψ, TwOK i k Q ψ → Function.Injective (rdV i j b k Q ψ) ∧ (∀ F ∈ ρ.mt i j b k Q ψ, F ∈ Set.range (rdV i j b k Q ψ)) ∧
    Submodule.span (FractionRing (D.ntw.Ok i k)) {f | rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ} = ⊤

theorem latI_eq (rdV : RdV D ρ) {i} (j : Fin D.R.m) {b k Q ψ} (h : TwOK i k Q ψ) :
    latI rdV i ((j : ℕ) + 1) b k Q ψ = (Via.lat (ρ.mt i j b k Q ψ)).comap (rdVLin rdV i j b k Q ψ) :=
  dif_pos ⟨j.2, h⟩

theorem mem_latI (rdV : RdV D ρ) {i} (j : Fin D.R.m) {b k Q ψ} (h : TwOK i k Q ψ) (f) :
    f ∈ latI rdV i ((j : ℕ) + 1) b k Q ψ ↔ rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ := by
  rw [latI_eq rdV j h]; exact Iff.rfl

theorem latI_fg (rdV : RdV D ρ) (hV : Onto ρ rdV) (hL : ρ.LatFG) (i) :
    ∀ n b k Q ψ, (latI rdV i n b k Q ψ).FG
  | 0, b, k, Q, ψ => D.nexp.MtLat_fg i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => by
    rw [latI]
    split_ifs with h
    · obtain ⟨hinj, hon, -⟩ := hV i ⟨n, h.1⟩ b k Q ψ h.2
      refine Submodule.fg_of_fg_map_injective (rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) hinj ?_
      rw [Submodule.map_comap_eq_self (f := rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) (q := Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ))
        fun x (hx : x ∈ Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ)) => by obtain ⟨y, hy⟩ := hon (Via.out _ _ x) hx; exact ⟨y, hy⟩]
      exact Via.lat_fg (hL i ⟨n, h.1⟩ b k Q ψ h.2)
    · exact D.nexp.MtLat_fg i (n + 1) b k Q ψ

theorem latI_span (rdV : RdV D ρ) (hV : Onto ρ rdV) (i) :
    ∀ n b k Q ψ, Submodule.span (FractionRing (D.ntw.Ok i k)) (latI rdV i n b k Q ψ : Set (D.nexp.MtV i n b k Q ψ)) = ⊤
  | 0, b, k, Q, ψ => D.nexp.MtLat_span i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => by
    rw [latI]
    split_ifs with h
    · exact (hV i ⟨n, h.1⟩ b k Q ψ h.2).2.2
    · exact D.nexp.MtLat_span i (n + 1) b k Q ψ

variable (hρ : ρ.Good) (rd : Rds D.nexp ρ) (hF : ∀ i j b, Faithful (rd i j b))

include hF in
theorem exists_thPI (rdV : RdV D ρ) (i) (j : Fin D.R.m) (b k Q ψ) :
    ∃ φ : D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₗ[D.ntw.Ok i k] D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b,
      ∀ f, ρ.sum i j b k Q ψ (rdV i j b k Q ψ f) ∈ Set.range (rdK (rd i j b) hρ k) →
        rdK (rd i j b) hρ k (φ f) = ρ.sum i j b k Q ψ (rdV i j b k Q ψ f) :=
  exists_lift ((ρ.sum i j b k Q ψ).comp (rdV i j b k Q ψ)) (rdK (rd i j b) hρ k) ((hF i j b).injective_rdK hρ k)
    (divisible_baseChange D.nexp i _ b k)

def thPI (rdV : RdV D ρ) (i) : ∀ n b k Q ψ,
    D.nexp.MtV i n b k Q ψ →ₗ[D.ntw.Ok i k] D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i n b
  | 0, _, _, _, _ => 0
  | n + 1, b, k, Q, ψ => if h : n < D.R.m then (exists_thPI hρ rd hF rdV i ⟨n, h⟩ b k Q ψ).choose else 0

theorem exists_tie_withSeries : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), (∀ i j b, Faithful (rd i j b)) → ρ.LevelOf D.nexp → ρ.LatFG → ∀ rdV : ∀ i (j : Fin D.R.m) b k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank), (∀ i j b k Q ψ, TwOK i k Q ψ → Function.Injective (rdV i j b k Q ψ) ∧ (∀ F ∈ ρ.mt i j b k Q ψ, F ∈ Set.range (rdV i j b k Q ψ)) ∧ Submodule.span (FractionRing (D.ntw.Ok i k)) {f | rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ} = ⊤) → ∃ Dat th lev thPsi h1 thU thP MtLat h2 h3, (∀ i j, j ∉ Finset.Icc 1 D.R.m → ∀ b, IsEmpty (Dat i j b)) ∧ ∃ t : Comparison₂ hρ (Y := { D.nexp with Dat := Dat, th := th, lev := lev, thPsi := thPsi, thPsi_one := h1, thU := thU, thP := thP, MtLat := MtLat, MtLat_fg := h2, MtLat_span := h3 }) rd, ∀ i j b, (t i j b).rdV = rdV i j b := by
  intro D ρ hρ rd hF hU hL rdV hV
  refine ⟨Model.Dat rd, Model.th rd, Model.lev rd, Model.thPsi hρ rd, Model.thPsi_one hρ rd hF, Model.thU rd,
    thPI hρ rd hF rdV, latI rdV, latI_fg rdV hV hL, latI_span rdV hV, ?_, ?_⟩
  · intro i n hn b
    cases n with
    | zero => exact ⟨fun d => d.elim⟩
    | succ n =>
      refine ⟨fun d => hn (Finset.mem_Icc.2 ⟨Nat.succ_pos n, d.1⟩)⟩
  · refine ⟨fun i j b =>
      { supp := fun d => d.2.s
        cls := fun d => d.2.h
        coef := fun d => d.2.P
        rdV := rdV i j b
        U_eq := hU.U_eq i j b
        psiU_eq := hU.psiU_eq i j b
        dat := fun d => d.2.isDatum
        dat_onto := fun s h P h1 h2 => ⟨⟨j.2, s, h, P, h1, h2⟩, rfl, rfl, rfl⟩
        lev_iff := fun _ _ => Set.Finite.mem_toFinset _
        th_eq := fun d => d.2.rat.choose_spec
        thPsi_iff := fun _ _ _ _ _ _ => Iff.rfl
        thU_eq := fun Q M d hQ x hx => by
          have h : InRange D.ntw i Q ∧ ∀ a, ρ.xi i j b D.nexp Q M d.2.h d.2.P a ∈ Set.range (rd i j b) :=
            ⟨hQ, fun a => ⟨x a, hx a⟩⟩
          refine (dif_pos h).trans (congrArg (grpSum D.nexp (ρ.ch i) Q M) (funext fun a => (hF i j b).injective ?_))
          exact (h.2 a).choose_spec.trans (hx a).symm
        thU_off := fun _ _ _ h => dif_neg h
        rdV_inj := fun k Q ψ h => (hV i j b k Q ψ h).1
        mtLat_iff := fun k Q ψ h F => by
          refine ⟨fun hF' => ?_, fun ⟨f, hf, e'⟩ => ?_⟩
          · obtain ⟨f, rfl⟩ := (hV i j b k Q ψ h).2.1 F hF'
            exact ⟨f, (mem_latI rdV j h f).2 hF', rfl⟩
          · exact e' ▸ (mem_latI rdV j h f).1 hf
        thP_eq := fun k Q ψ _ f hf => by
          have e : thPI hρ rd hF rdV i ((j : ℕ) + 1) b k Q ψ = (exists_thPI hρ rd hF rdV i j b k Q ψ).choose := dif_pos j.2
          exact (congrArg (fun φ => rdK (rd i j b) hρ k (φ f)) e).trans
            ((exists_thPI hρ rd hF rdV i j b k Q ψ).choose_spec f hf) }, fun _ _ _ => rfl⟩

end GlobalTheory.SeriesInstall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistHeckeCharacter
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AntiCycRead

variable (D : D7)

def quo : (AE D)ˣ →* (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
  MonoidHom.mk' (fun x => Units.map (finPart D).toMonoidHom x *
      (Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x)⁻¹)
    (fun x y => by simp only [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _)

theorem quo_mul (x : (AE D)ˣ) :
    ((quo D x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) *
        sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) = finPart D (x : AE D) := by
  have hsv : ((Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := GlobalTheory.DetRootChar.finPart_sigR D x
  rw [← hsv]
  show ((Units.map (finPart D).toMonoidHom x * (Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x)⁻¹ :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) * _ = _
  rw [← Units.val_mul, inv_mul_cancel_right]
  rfl

theorem quo_eq_of (x : (AE D)ˣ) (u : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ)
    (hu : (u : Af D.host.F ⊗[D.host.F] D.host.E) * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) =
      finPart D (x : AE D)) : quo D x = u := by
  set s : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ :=
    Units.map ((finPart D).comp (sigR (AF D.host.F) D.sp.cm.sig)).toMonoidHom x with hs
  have hsv : (s : Af D.host.F ⊗[D.host.F] D.host.E) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hs]; exact GlobalTheory.DetRootChar.finPart_sigR D x
  have h1 := quo_mul D x
  rw [← hsv] at h1 hu
  have : ((quo D x * s : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ)) = u * s := Units.ext (by simp [h1, hu])
  exact mul_right_cancel this

theorem ker_trivial (δ : (AE D)ˣ →* Circle) (hF : ∀ a, δ (idF D a) = 1) (hfin : ∃ m : ℕ, 0 < m ∧ ∀ x, δ x ^ m = 1)
    (x : (AE D)ˣ) (hx : quo D x = 1) : δ x = 1 := by
  have h1 := quo_mul D x
  rw [hx, Units.val_one, one_mul] at h1
  obtain ⟨a, y, hy, hxy⟩ := GlobalTheory.DetRootChar.exists_idF_mul D x h1
  obtain ⟨m, hm, hδ⟩ := hfin
  obtain ⟨z, hz⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D m hm y hy
  rw [hxy, map_mul, hF, mul_one, ← hz, map_pow, hδ]

theorem quo_of_isDetRoot (W : HSp D) (g : GA D W) (x : (AE D)ˣ) (hx : IsDetRoot W g x) :
    quo D x = Matrix.GeneralLinearGroup.det (finHom W g) := by
  apply quo_eq_of
  have hdet : ((Matrix.GeneralLinearGroup.det (finHom W g) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
      Af D.host.F ⊗[D.host.F] D.host.E) = finPart D (matHom W g).1.det :=
    (GlobalTheory.DetRootChar.finPart_det D W g).symm
  rw [hdet, ← GlobalTheory.DetRootChar.finPart_sigR, ← RingHom.map_mul]
  exact (congrArg _ hx).symm

end GlobalTheory.AntiCycRead

end

noncomputable section

namespace GlobalTheory.AntiCycRead

variable (D : D7)

theorem val_of_quo (χ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* Circle) (Y : (AE D)ˣ) :
    (((Circle.toUnits.comp χ) (quo D Y) : ℂˣ) : ℂ) = ((χ (quo D Y) : Circle) : ℂ) := by
  simp

theorem exists_rat (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (a : D.host.E)
    (hxa : (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 ⊗ₜ a) (hx : GlobalTheory.FinalJoin.NormOne x)
    [Nontrivial (Af D.host.F)] : ∃ w : D.host.Eˣ, quo D (Units.map (incA D).toMonoidHom w) = x := by
  have hN : (x : Af D.host.F ⊗[D.host.F] D.host.E) *
      sigR (Af D.host.F) D.sp.cm.sig (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 := hx
  rw [hxa] at hN
  have ha : a * D.sp.cm.sig a = 1 := by
    apply Algebra.TensorProduct.includeRight_injective (A := Af D.host.F) (R := D.host.F)
      (algebraMap D.host.F (Af D.host.F)).injective
    show (1 : Af D.host.F) ⊗ₜ[D.host.F] (a * D.sp.cm.sig a) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)
    rw [← Algebra.TensorProduct.one_def]
    simpa [sigR] using hN
  have hu : a ∈ unitary D.host.E := ⟨by rw [mul_comm]; exact ha, ha⟩
  obtain ⟨w, hw0, hw⟩ := GlobalTheory.NormOneHilbert90Units.exists_ne_zero_mul_conj_eq_of_unitary D ⟨a, hu⟩
  refine ⟨Units.mk0 w hw0, ?_⟩
  apply quo_eq_of
  have hfY : finPart D ((Units.map (incA D).toMonoidHom (Units.mk0 w hw0) : (AE D)ˣ) : AE D) =
      (1 : Af D.host.F) ⊗ₜ[D.host.F] w := rfl
  rw [hfY, hxa]
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← Formalism.BasicNotions.Examples₂.star_eq_conj] at hw
  exact congrArg _ hw

theorem exists_cong (N : ℕ) (hN : Odd N) (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (hx : GlobalTheory.FinalJoin.NormOne x)
    (w : Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ intAE D)
    (hwe : (x : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = N • w) :
    ∃ Y : (AE D)ˣ, FinUnit Y ∧ (∃ y ∈ intAE D, finPart D (Y : AE D) - 1 = N • y) ∧ quo D Y = x := by
  have hn : (x : Af D.host.F ⊗[D.host.F] D.host.E) *
      sigR (Af D.host.F) D.sp.cm.sig (x : Af D.host.F ⊗[D.host.F] D.host.E) = 1 := hx
  obtain ⟨y, y', hy, hy', hyy, hroot, q, hq, hqe⟩ :=
    GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN (x : Af D.host.F ⊗[D.host.F] D.host.E) w hw hwe hn
  obtain ⟨Y, h1, h2, h3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨h1, h2 ▸ hy, h3 ▸ hy'⟩, ⟨q, hq, h2 ▸ hqe⟩, ?_⟩
  apply quo_eq_of
  rw [h2]
  exact hroot.symm

theorem exists_normOne (x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) (hx : GlobalTheory.FinalJoin.NormOne x) :
    ∃ Y : (AE D)ˣ, quo D Y = x := by
  obtain ⟨y, hy⟩ := (GlobalTheory.IdeleNinety.finiteIdeles_normOne_eq_div_conj_with_congruence D).1 x hx
  obtain ⟨Y, -, h1, -⟩ := GlobalTheory.DetRootCong.exists_idele D (y : Af D.host.F ⊗[D.host.F] D.host.E)
    ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) y.mul_inv
  have hc : ((Formalism.L2.Pj.cjFin D y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.IdeleNinety.coe_cjFin D y
  refine ⟨Y, ?_⟩
  apply quo_eq_of
  rw [h1, ← hc, hy, ← Units.val_mul, div_mul_cancel]

end GlobalTheory.AntiCycRead

end

noncomputable section

namespace GlobalTheory.AntiCycRead

theorem read_anticyc : ∀ (D : D7) (W : HSp D) (L : Type) [Field L] (σ : L →+* ℂ) (p : ℕ), Odd p → ∀ δ : (AE D)ˣ →* Circle, IsHeckeChar D δ → (∀ a, δ (Formalism.L2.Theta.idF D a) = 1) → (∃ m : ℕ, 0 < m ∧ ∀ x, δ x ^ m = 1) → (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = p • y) → δ x = 1) → (∀ x, ∃ y : L, σ y = ((δ x : Circle) : ℂ)) → ∃ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist σ p xi ∧ ∀ (g : GA D W) (x : (AE D)ˣ), IsDetRoot W g x → ((xi (Matrix.GeneralLinearGroup.det (finHom W g)) : ℂˣ) : ℂ) = ((δ x : Circle) : ℂ) := by
  intro D W L _ σ p hp δ hH hF hfin hcong hval
  obtain ⟨χ, hχ⟩ := GlobalTheory.DetRootChar.circle_hom_factor (quo D) δ (ker_trivial D δ hF hfin)
  have hxi : ∀ Y : (AE D)ˣ, (((Circle.toUnits.comp χ) (quo D Y) : ℂˣ) : ℂ) = ((δ Y : Circle) : ℂ) := by
    intro Y
    rw [val_of_quo, hχ]
  refine ⟨Circle.toUnits.comp χ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x a hxa hx
    rcases subsingleton_or_nontrivial (Af D.host.F) with hs | hs
    · have h0 : ∀ z : Af D.host.F ⊗[D.host.F] D.host.E, z = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul b e => rw [Subsingleton.elim b 0, TensorProduct.zero_tmul]
        | add u v hu hv => rw [hu, hv, add_zero]
      have hx1 : x = 1 := Units.ext ((h0 _).trans (h0 _).symm)
      rw [hx1, map_one]
    obtain ⟨w, hw⟩ := exists_rat D x a hxa hx
    apply Units.ext
    rw [← hw, hxi, hH.2 w]
    rfl
  · rintro x hx ⟨w, hw, hwe⟩
    obtain ⟨Y, hY, hYc, hQ⟩ := exists_cong D p hp x hx w hw hwe
    apply Units.ext
    rw [← hQ, hxi, hcong Y hY hYc]
    rfl
  · intro x hx
    obtain ⟨Y, hQ⟩ := exists_normOne D x hx
    obtain ⟨a, ha⟩ := hval Y
    refine ⟨a, ?_⟩
    rw [← hQ, hxi]
    exact ha
  · intro g x hx
    rw [← quo_of_isDetRoot D W g x hx, hxi]

end GlobalTheory.AntiCycRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserNormGapPadicEmbedding
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifGap

open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p])

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem norm_lt_one_of_valuation_lt_one {x : F} (hx : (placeAt φ).valuation F x < 1) : ‖φ x‖ < 1 := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (placeAt φ) x hx.le
  have hd : ‖φ ((d : 𝓞 F) : F)‖ = 1 := le_antisymm (norm_int_le_one φ _) (not_lt.1 d.2)
  have hdv : (placeAt φ).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F)) ≤ 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one _ _
  have hn : (placeAt φ).intValuation n < 1 := by
    have h0 : (placeAt φ).valuation F (algebraMap (𝓞 F) F n) < 1 := by
      rw [← hnd, map_mul]
      exact (mul_le_of_le_one_right' hdv).trans_lt hx
    rwa [HeightOneSpectrum.valuation_of_algebraMap] at h0
  have hnm : ‖φ (n : F)‖ < 1 := (mem_placeAt φ n).1 ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ n).1 hn)
  have h2 := congrArg (fun t => ‖φ t‖) hnd
  simp only [map_mul, norm_mul] at h2
  have h3 : ‖φ x‖ * ‖φ ((d : 𝓞 F) : F)‖ = ‖φ (n : F)‖ := h2
  rw [hd, mul_one] at h3
  rw [h3]; exact hnm

theorem exists_unif_norm_gap : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]),
    ∃ ϖ : F, 0 < ‖φ ϖ‖ ∧ ‖φ ϖ‖ < 1 ∧ ∀ c : F, ‖φ c‖ < 1 → ‖φ c‖ ≤ ‖φ ϖ‖ := by
  intro p _ F _ _ φ
  set v := (placeAt φ).valuation F with hv
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F (placeAt φ)
  have hϖ1 : v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  refine ⟨ϖ, norm_pos_iff.2 ((map_ne_zero φ).2 hϖ0), norm_lt_one_of_valuation_lt_one φ hϖ1, fun c hc => ?_⟩
  by_cases hc0 : c = 0
  · rw [hc0, map_zero, norm_zero]; exact norm_nonneg _
  have hvc : v c < 1 := by
    by_contra hge
    rw [not_lt] at hge
    have hinv : v c⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ hge
    have h1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ hinv
    rw [map_inv₀, norm_inv] at h1
    have hpos : 0 < ‖φ c‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hc0)
    have := (inv_le_one₀ hpos).1 h1
    exact absurd hc (not_lt.2 this)
  have hq : v (c / ϖ) ≤ 1 := by
    rw [map_div₀, hϖ]
    exact div_le_one_of_le₀ (le_exp_neg_one_of_lt_one hvc) zero_le'
  have h1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ hq
  rw [map_div₀, norm_div] at h1
  have hpos : 0 < ‖φ ϖ‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hϖ0)
  exact (div_le_one hpos).1 h1

end GlobalTheory.UnifGap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharacterEqLadicHeckeCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwChiGal

open GlobalTheory.GalChar (IsGal toQ inQ block)

theorem firstTwistCharacter_eq_ladic_heckeCharacter : ∀ (D : D7) (cf : CharFrame D) (chiD : Formalism.L2.NC.NChiData D), Formalism.L2.NC.NormalizedCharacterCompatibility D chiD → (∀ x, chiD.etaT.χ x = cf.eta.1 x) → (∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x) → (∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x) → ValLL0 D cf → ∀ (art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om), GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ (i : D.ntw.Tw) (b : Bool) (ρ : GlobalTheory.Triple.Reading D.ntw i b) (j : Fin D.R.m), ∃ n, GlobalTheory.GalChar.IsGal art ρ.κ ρ.ι (GlobalTheory.Triple.blockChar cf (D.ntw.l i) j) n (D.ntw.chi1 i (j.1 + 1) b) := by
  intro D cf chiD T hEta hMu hDel hC art ha i b ρ j
  obtain ⟨χ', n, h'⟩ := GlobalTheory.Triple.exists_blockChar ha hC ρ j
  have hj1 : 1 ≤ j.1 + 1 := Nat.le_add_left 1 j.1
  have hj2 : j.1 + 1 ≤ D.R.m := j.2
  obtain ⟨B1, hB1⟩ := T.chi1 i (j.1 + 1) b hj1 hj2
  have hχ : ∀ x, (chiD.firstHeckeCharacter i (j.1 + 1)).χ x = (cf.mu0 j * cf.delAt (D.ntw.l i) * cf.eta⁻¹).1 x := by
    intro x
    simp only [Formalism.L2.NC.NChiData.firstHeckeCharacter, Formalism.L2.NC.HC.mul_χ, Formalism.L2.NC.HC.inv_χ, MonoidHom.mul_apply,
      MonoidHom.inv_apply, hMu j x, hDel i x, hEta x]
    rfl
  set χb := GlobalTheory.Triple.blockChar cf (D.ntw.l i) j with hχb
  have hev : ∀ᶠ P in Filter.cofinite, P ∉ B1 := Filter.eventually_cofinite.2 (by simpa using B1.finite_toSet)
  have hc1 : Continuous (inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b)) :=
    GlobalTheory.GalChar.continuous_units _ ((GlobalTheory.GalChar.isEmbedding_toQ (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg).continuous.comp
      (D.ntw.twistCharacterFamily_continuous i (j.1 + 1) b))
  have e : inQ ρ.κ χ' = inQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b) := by
    refine GlobalTheory.GalChar.eq_of_frob ha (h'.cont (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg) hc1 ?_
    filter_upwards [hev, GlobalTheory.GalChar.unr_ae χb,
      GlobalTheory.GalChar.away_ae (E := D.host.E) (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero] with v hv hu hl A hA σ hσ
    refine GlobalTheory.ChiLocGal.frob_any (D.nd.plOm.2 v) hA (fun σ' hσ' => ?_) hσ
    obtain ⟨α, hα, x, hx, hσx⟩ := hB1 v hv
    have hval : ((χb.val v : ℂˣ) : ℂ) = (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x)⁻¹ :=
      GlobalTheory.ChiLocGal.val_block (GlobalTheory.ChiLocGal.val_of_at hχ hα) hx
    have e1 := h'.frob ha (Or.inl hl) hu (D.nd.plOm.2 v) hσ'
    rw [hval, inv_inv] at e1
    apply Units.ext
    apply ρ.ι.injective
    show ρ.ι (toQ ρ.κ (χ' σ' : (D.ntw.O0 i)ˣ)) = ρ.ι (toQ ρ.κ (D.ntw.chi1 i (j.1 + 1) b σ' : (D.ntw.O0 i)ˣ))
    rw [e1]
    show Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x = ρ.ι (ρ.κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
      (D.ntw.chi1 i (j.1 + 1) b σ' : (D.ntw.O0 i)ˣ)))
    rw [hσx σ' hσ']
    exact (ρ.read x).symm
  have : χ' = D.ntw.chi1 i (j.1 + 1) b := MonoidHom.ext fun g => GlobalTheory.GalChar.inQ_inj ρ.κ (DFunLike.congr_fun e g)
  exact ⟨n, this ▸ h'⟩

end GlobalTheory.TwChiGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartProjectorSpectralAtEveryLocalisation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.EtaJoin.SpecAll

theorem specPr_all : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M →
    ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → (∀ i : D.nd.Loc, ClassSum (M.loc i)) →
    (∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i)) → D.nd.EigSpan → Rows.IsotInternal D.what₂ →
    SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ i, SpecPr D i := by
  intro D M HT HR AV Tn HS CS TC HE II UnitaryCharacterOfReals PZ GF i
  have SU : SplitUnif D := GlobalTheory.SplitConjPlace.splitEx_all D
  have hZ : ZSpec D i :=
    GlobalTheory.EtaJoin.TypeSum.main D M i HT AV SU (GlobalTheory.T.gramClass_vacuumCombination_orbitSum_mod_lower D M AV i (CS i)) (TC i) II PZ
      (GlobalTheory.T.every_heckeRow_good_at_goodPointLocalisation D M HT AV Tn HS UnitaryCharacterOfReals GF i)
  have hT : TypeTie D i := GlobalTheory.T.typeSpace_projection_to_pointEigenspaces D M i HT HR AV SU (GlobalTheory.T.sphericalHeckeScalarOnTypeSpaces_all_places D M HT AV i) HE
  exact GlobalTheory.EtaJoin.SpecProj.specPr_of_zSpec_typeTie D i hZ hT

end GlobalTheory.EtaJoin.SpecAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkSSOfSides
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwHkSS

theorem hkSS_of_sides : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), CommG D → HkComm D → SupFull D → HkSS D := by
  intro D X E Y hG hC hSF
  have hX : Formalism.IndefR.NX.NExpHeckeRowX X.R X.cG Y.S Y.YS Y.H (fun j => Formalism.IndefR.NX.goodProjW Y.S j D.nexp.eLL0) :=
    ⟨fun i k P hs ho _ _ hk α R hα hR x _ => Y.reads i k P hs ho hk α R hα hR x⟩
  exact GlobalTheory.GoodSpan.hkSS_of_rows_guarded X.R X.F X.cG Y.S Y.YS Y.H hG hC hSF hX X.char X.unif X.integral
    (fun i P P' hP hc => Y.Z.good.goodSetup_badPlaces_conj i P hP P' hc) (fun i => Y.Z.good.goodSetup_placesOverTwo_subset i) Y.Sb
    (fun i _ j hj b k P hk x => Y.hk_emb i j b k P x (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2 hk)
    Y.B_range Y.hk_split

end GlobalTheory.TwHkSS
end
end

