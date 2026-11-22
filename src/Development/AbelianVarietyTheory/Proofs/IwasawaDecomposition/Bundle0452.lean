import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Mathlib
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0159
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteNotIsUnitOneAddSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0082
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Formalism.LocalToGlobal.Columns.RecLevelLoc

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtTwTieStd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem mtTwTie_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → t.MtTwTie := by
  intro B X I hok l Z L hT Gi Gl K Y cX ex t hS
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  cases t
  dsimp only at *
  subst hX
  cases hseam
  subst hSS
  cases htup
  refine ⟨(QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E)), ⟨fun y => ?_, fun k z hz => ?_⟩,
    fun μ _ _ => ⟨tildeQ B.host I.SQ (I.xi μ), fun x => ?_, fun u => ?_⟩⟩
  · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (show DtQ B.host I.SQ from y)
    refine ⟨finAf B.host.F B.host.E a, ?_⟩
    exact mk_eq_of_snd_eq B.host I.SQ (afIso_finAf B.host.F B.host.E a)
  · have hz' : (show B.host.E from z.1) * B.host.conj (k : B.host.E) = k := hz
    show (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) (ratId B.host.F B.host.E k)) : DtQ B.host I.SQ) = e1Q B.host I.SQ z
    rw [← isUnitaryPointsMap_unitaryRationalPointsFiner B.host I.SQ k z hz']
    refine mk_eq_of_snd_eq B.host I.SQ ?_
    show afIso B.host.F B.host.E ((k : B.host.E) ⊗ₜ[B.host.F] 1) = _
    rw [afIso_tmul_one]
    rfl
  · have hk : KDq B.host I.SQ ≤ ((I.xi μ).1.comp (finPartI B.host.E)).ker :=
      (KDq_anti B.host (I.Q_subset_SQ μ)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).2.2 μ).1
    show tildeQ B.host I.SQ (I.xi μ) (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x)) = _
    rw [tildeQ_mk B.host I.SQ hk, finPartI_eq_self fun _ => rfl]
    exact Units.ext ((hok.xi_reads μ).apply _ x rfl)
  · rw [hO.mt u μ]
    rfl

end GlobalTheory.Mem.Col2.TC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormNatCastEqOne
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

namespace GlobalTheory.Mem.Col2.TC.AdaptedBases

variable {D : D7}

theorem conj_eq_complexConj (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm

theorem norm_natCast_eq_one {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : ¬ p ∣ k) : ‖(k : ℂ_[p])‖ = 1 := by
  rw [GlobalTheory.EigenGenerator.norm_natCast_eq]
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hk)

theorem exists_unitary_at (p : ℕ) (hp : p.Prime) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) :
    ∃ G : Matrix (Fin N) (Fin N) D.host.E, (G.map D.host.conj).transpose * G = 1 ∧
      (∀ x ∈ L, ∃ k : ℕ, ¬ p ∣ k ∧ ∃ c : Fin N → 𝓞 D.host.E, (k : D.host.E) • x = G.mulVec (fun a => (c a : D.host.E))) ∧
      (∀ a, ∃ k : ℕ, ¬ p ∣ k ∧ (k : D.host.E) • (fun i => G i a) ∈ L) := by
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram D.sp.cm.cmUnram
  have hsd : (⟨L, hL.1, hL.2.1⟩ : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat D.host.E N).SelfDual := by
    intro x
    have h3 := hL.2.2 x
    refine h3.trans (forall₂_congr fun y _ => ?_)
    have e : stdH D.host.E N y x = GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm x y := by
      unfold stdH GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
      rfl
    rw [e]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
  obtain ⟨γ, hγ, h1, h2⟩ := GlobalTheory.GenusSelfDual.inGenus_of_selfDual hsd p hp
  refine ⟨LinearMap.toMatrix' γ.toLinearMap, ?_, fun x hx => ?_, fun a => ?_⟩
  · ext a b
    have h := hγ (Pi.single b 1) (Pi.single a 1)
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm (Pi.single b (1 : D.host.E)) (Pi.single a 1) = if a = b then 1 else 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
      rw [Finset.sum_eq_single b]
      · by_cases hab : a = b
        · subst hab; simp
        · simp [Pi.single_apply, Ne.symm hab, hab]
      · intro j _ hj
        simp [Pi.single_apply, hj]
      · simp
    rw [hr] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply, LinearMap.toMatrix'_apply,
      LinearEquiv.coe_coe, conj_eq_complexConj]
    rw [← h]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · obtain ⟨k, hk, hkx⟩ := h1 x hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hkx
    choose c hc using GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.mem_stdMod.1 hy
    refine ⟨k, hk, c, ?_⟩
    rw [LinearMap.toMatrix'_mulVec, Nat.cast_smul_eq_nsmul]
    rw [← hyx]
    have : (fun a => (c a : D.host.E)) = y := funext hc
    rw [this]
    rfl
  · have hm : (fun i => LinearMap.toMatrix' γ.toLinearMap i a) ∈ ((GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.Lat.std D.host.E N).map γ).L := by
      refine Submodule.mem_map.2 ⟨Pi.single a 1, GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.single_mem_stdMod a, ?_⟩
      funext i
      simp [LinearMap.toMatrix'_apply]
    obtain ⟨k, hk, hkx⟩ := h2 _ hm
    exact ⟨k, hk, by rwa [Nat.cast_smul_eq_nsmul]⟩

end GlobalTheory.Mem.Col2.TC.AdaptedBases

namespace GlobalTheory.Mem.Col2.TC.AdaptedBases

variable {D : D7}

theorem basR_of {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (G : Matrix (Fin N) (Fin N) D.host.E) (hdet : G.det ≠ 0)
    (h1 : ∀ x ∈ L, ∃ k : ℕ, ¬ p ∣ k ∧ ∃ c : Fin N → 𝓞 D.host.E, (k : D.host.E) • x = G.mulVec (fun a => (c a : D.host.E)))
    (h2 : ∀ a, ∃ k : ℕ, ¬ p ∣ k ∧ (k : D.host.E) • (fun i => G i a) ∈ L) :
    GL3Columns.BasR D lam τ L (G.map (tauEmb D lam τ)) := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.JetTieCompare.exists_tauHom D lam τ
  unfold GL3Columns.BasR
  rw [hρ]
  have hdet' : (G.map ρ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero ρ).2 hdet
  refine ⟨hdet', fun x hx a => ?_, fun a => ?_⟩
  · obtain ⟨k, hk, c, hc⟩ := h1 x hx
    have hk1 := norm_natCast_eq_one (p := p) hk
    have hk0 : (k : ℂ_[p]) ≠ 0 := fun h => by rw [h, norm_zero] at hk1; exact zero_ne_one hk1
    have hv : (fun i => ρ (x i)) = (G.map ρ).mulVec ((k : ℂ_[p])⁻¹ • fun a => ρ (c a : D.host.E)) := by
      funext i
      have e := congrArg (fun v => ρ (v i)) hc
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast] at e
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hk0, e, RingHom.map_mulVec]
      rfl
    rw [hv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet'), Matrix.one_mulVec, Pi.smul_apply,
      smul_eq_mul, norm_mul, norm_inv, hk1, inv_one, one_mul]
    exact GlobalTheory.JetTieCompare.norm_int_le ρ (c a)
  · obtain ⟨k, hk, hkL⟩ := h2 a
    have hk1 := norm_natCast_eq_one (p := p) hk
    have hk0 : (k : ℂ_[p]) ≠ 0 := fun h => by rw [h, norm_zero] at hk1; exact zero_ne_one hk1
    refine ⟨1, fun _ => (k : ℂ_[p])⁻¹, fun _ => (k : D.host.E) • fun i => G i a, fun _ => by rw [norm_inv, hk1, inv_one],
      fun _ => hkL, fun i => ?_⟩
    simp only [Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Matrix.map_apply]
    rw [inv_mul_cancel_left₀ hk0]

theorem dualM_eq_self {N : ℕ} {G : Matrix (Fin N) (Fin N) D.host.E} (h : (G.map D.host.conj).transpose * G = 1) : dualM G = G :=
  Matrix.inv_eq_right_inv h

theorem basR_smul {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {τ : D.what₂.Tau} {N : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {M : Matrix (Fin N) (Fin N) ℂ_[p]} (hM : GL3Columns.BasR D lam τ L M)
    {s : ℂ_[p]} (hs : ‖s‖ = 1) : GL3Columns.BasR D lam τ L (s • M) := by
  have hs0 : s ≠ 0 := fun h => by rw [h, norm_zero] at hs; exact zero_ne_one hs
  obtain ⟨h0, h1, h2⟩ := hM
  refine ⟨?_, fun x hx a => ?_, fun a => ?_⟩
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs0) h0
  · have e : (s • M)⁻¹ = s⁻¹ • M⁻¹ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hs0, one_smul,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h0)]
    rw [e, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, hs, inv_one, one_mul]
    exact h1 x hx a
  · obtain ⟨n, r, x, hr, hx, he⟩ := h2 a
    refine ⟨n, fun k => s * r k, x, fun k => by rw [norm_mul, hs, one_mul]; exact hr k, hx, fun i => ?_⟩
    rw [Matrix.smul_apply, he i, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem ne_two_ne_q_of_adPl {w : D.what₂.places.Pl} (hw : AdPl D w) :
    D.what₂.places.resChar w ∉ D.host.small ∧ D.what₂.places.resChar w ≠ D.host.q := by
  unfold AdPl Formalism.BasicNotions.Host.cls at hw
  constructor
  · intro h
    simp [Formalism.BasicNotions.primeClass, h] at hw
  · intro h
    rw [h, Formalism.BasicNotions.primeClass_q] at hw
    simp at hw

theorem dgenUnitAd (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : DgenUnitAd P O := by
  intro w hw u μ τ
  obtain ⟨h2, hq⟩ := ne_two_ne_q_of_adPl hw
  obtain ⟨M, hM, hemb, hs⟩ := (O u μ).dgen_gen
  obtain ⟨s, hs1, hs2⟩ := hs τ
  rw [← hs1]
  exact GlobalTheory.EigenGenerator.norm_generator_eq_one D _ (P.lam w) h2 hq M hemb τ s hs2

theorem exists_sys (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (u : D.what₂.Word)
    (μ : D.what₂.Tup) : ∃ Pm : SysFam D u μ,
      (∀ i, i ≤ D.R.m → ∀ c τ, GL3Columns.BasR D (P.lam w) τ ((O u μ).lat i c).1 ((Pm i c τ).map (tauEmb D (P.lam w) τ))) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', SamePr (P.lam w) τ τ' → Pm i c τ' = Pm i c τ) ∧
      (∀ i, i ≤ D.R.m → ∀ c τ τ', ConjPr (P.lam w) τ τ' → Pm i c τ' = dualM (Pm i c τ)) := by
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  choose G hG h1 h2 using fun i (c : (D.chTw u μ).cls i) =>
    exists_unitary_at (D := D) (D.what₂.places.resChar w) hp ((O u μ).lat i c).1 ((O u μ).lat i c).2
  refine ⟨fun i c _ => G i c, fun i _ c τ => ?_, fun _ _ _ _ _ _ => rfl, fun i _ c _ _ _ => (dualM_eq_self (hG i c)).symm⟩
  exact basR_of (P.lam w) τ _ (G i c) (Matrix.det_ne_zero_of_left_inverse (hG i c)) (h1 i c) (h2 i c)

end GlobalTheory.Mem.Col2.TC.AdaptedBases

open IsDedekindDomain Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

variable {D : D7}

def wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :=
  Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
    {c | ∃ a : 𝓞 X.B.I.E, (∃ b ∈ w.asIdeal, X.ιE (a : X.B.I.E) = (b : D.host.E)) ∧
      c = Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E)}

def ModW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ}
    (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (t : ZMod g) : Prop :=
  c - ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w

def argS (X : HidaSetting D) (x : X.B.I.Gf) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F :=
  (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat x *ᵥ nxt X.e0 X.z0 a)) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0

theorem otherInstanceCharacter_eq_psi_symmetricArgument (X : HidaSetting D) (x : X.B.I.Gf) :
    X.chi2 x = X.psiEf (divN X.B.I X.B.g (argS X x)) := rfl

open Classical in

def side (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Bool := decide (GlobalTheory.Mem.SymFrame.EwAt X w)

def wtA (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 1 else if i.1 + 1 < ρ + k then (if s then 1 else 0) else 0

def wtB (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 0 else if i.1 + 1 < ρ + k then (if s then 0 else -1) else if i.1 = ρ + k then 1 else -1

theorem wt_add (ρ k : ℕ) (s : Bool) {r : ℕ} (i j : Fin r) :
    wtA ρ k s i j + wtB ρ k s i j = 1 ∨ wtA ρ k s i j + wtB ρ k s i j = -1 := by
  unfold wtA wtB
  split_ifs <;> simp

theorem hA_smul_right' (X : HidaSetting D) (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (x y : VA X.B.I) :
    hA X.B.I x (c • y) = c * hA X.B.I x y := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hA_add_right' (X : HidaSetting D) (x y z : VA X.B.I) :
    hA X.B.I x (y + z) = hA X.B.I x y + hA X.B.I x z := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_zero_right' (X : HidaSetting D) (x : VA X.B.I) : hA X.B.I x 0 = 0 := by
  simp [hA, Formalism.UG.hform]

theorem hA_mem_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {x v : VA X.B.I} (hx : x ∈ X.B.I.Lf)
    (hv : v ∈ wLf X w) : hA X.B.I x v ∈ wInt X w := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨y, hy⟩, rfl⟩ := hv
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, y', hy', rfl⟩ := hy
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • y') i)) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) •
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (y' i)) := by
        funext i; simp [map_mul]
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • y') i)) ∈ wInt X w
      rw [e, hA_smul_right']
      have hint : hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (y' i)) ∈
          Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
        GlobalTheory.St.G.FrameClose.hA_int hx (Submodule.subset_span ⟨⟨y', hy'⟩, rfl⟩)
      rw [mul_comm]
      exact (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
        (Submodule.subset_span ⟨a, ha, rfl⟩)
    | zero =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((0 : Fin X.B.I.n → X.B.I.E) i)) = 0 := by
        funext i; simp
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((0 : Fin X.B.I.n → X.B.I.E) i)) ∈ wInt X w
      rw [e, hA_zero_right']; exact zero_mem _
    | add a b _ _ ha hb =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((a + b) i)) =
          (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a i)) +
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (b i)) := by
        funext i; simp
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((a + b) i)) ∈ wInt X w
      rw [e, hA_add_right']; exact add_mem ha hb
    | smul c a _ ha =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((c • a) i)) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (c : X.B.I.E) •
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a i)) := by
        funext i; simp [Algebra.smul_def, map_mul]
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((c • a) i)) ∈ wInt X w
      rw [e, hA_smul_right']
      have hc : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (c : X.B.I.E) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
        Formalism.UG.P.easyc_inclE_mem _ _ _ (by first | exact ⟨c, rfl⟩ | exact c.2 | simp [Formalism.UG.intOE])
      exact (wInt X w).smul_mem (⟨_, hc⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) ha
  | zero => rw [hA_zero_right']; exact zero_mem _
  | add a b _ _ ha hb => rw [hA_add_right']; exact add_mem ha hb
  | smul c a _ ha =>
    show hA X.B.I x ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • a) ∈ wInt X w
    rw [hA_smul_right']
    exact (wInt X w).smul_mem c ha

theorem hA_sub_right' (X : HidaSetting D) (x y z : VA X.B.I) :
    hA X.B.I x (y - z) = hA X.B.I x y - hA X.B.I x z := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hA_sum_right' (X : HidaSetting D) {ι : Type} (s : Finset ι) (x : VA X.B.I) (y : ι → VA X.B.I) :
    hA X.B.I x (∑ j ∈ s, y j) = ∑ j ∈ s, hA X.B.I x (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hA_zero_right' X x
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hA_add_right', ih]

theorem hA_isMatIn (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hN : GlobalTheory.Mem.SymFrame.IsMatIn X w u x N)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (i : Fin D.R.r) :
    hA X.B.I y (X.B.I.fmat x *ᵥ u i) -
      ∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I y (u j) ∈ wInt X w := by
  have h := hA_mem_wInt X w hy (hN i)
  rw [hA_sub_right', hA_sum_right'] at h
  simpa only [hA_smul_right'] using h

theorem wInt_of_zmod (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (hc : ZMod' X.B.I X.B.g c) : c ∈ wInt X w := by
  obtain ⟨t, ht, rfl⟩ := hc
  obtain ⟨m, hm⟩ : D.host.g k ∣ X.B.g := by
    rw [X.g_eq]; fin_cases k
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have hgen : ((D.host.g k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
    refine Submodule.subset_span ⟨(D.host.g k : 𝓞 X.B.I.E), ⟨_, hg, ?_⟩, ?_⟩
    · simp
    · simp
  have e : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t =
      ((m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t) * (D.host.g k : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    rw [hm, Nat.cast_mul]; ring
  rw [e]
  exact (wInt X w).smul_mem (⟨_, mul_mem (natCast_mem _ m) ht⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hgen

end GlobalTheory.Mem.SymChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevel
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

theorem adAt_eq_one_of_prV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) {z : AfE F E}
    (hz : Formalism.UG.prV (E := E) (P.under (𝓞 F)) z = 1) : adAt F P z = 1 := by
  set v := P.under (𝓞 F)
  have h1 : Formalism.UG.P.afsplitEps E v * z = Formalism.UG.P.afsplitEps E v := by
    rw [← Formalism.UG.P.afsplit_decomp, hz]
    rfl
  have h2 : Formalism.UG.P.afsplitEps E v = (1 : E) ⊗ₜ[F] Formalism.UG.P.afsplitI v (1 : v.adicCompletion F) := by
    rw [Formalism.UG.P.afsplitEps, Algebra.TensorProduct.one_def, Formalism.UG.P.afsplitIE_tmul]
  have h3 : adAt F P (Formalism.UG.P.afsplitEps E v) = 1 := by
    rw [h2, adAt_apply, GlobalTheory.Mem.ReadTwist.afIso_one_tmul (k := 1)]
    · simp
    · rw [Formalism.UG.P.afsplitI_self]; simp
  have h4 := congrArg (adAt F P) h1
  rwa [map_mul, h3, one_mul] at h4

theorem detPt_eq_u1Dt_of_level : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q) (y k : GL (Fin n) (AfE H.F H.E)) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), LevOk H SG SQ → IsPtOf (host_cmData R H) (y * k) (extTo SQ p) → k ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → Formalism.L2.Herm.Carries k (stdLat H.E n) (stdLat H.E n) → (∀ P ∈ uSG SG SQ, Formalism.UG.bc (Formalism.UG.prV (E := H.E) (P.under (𝓞 H.F))) k = 1) → Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det y → detPt H SQ p = u1Dt H SQ x := by
  intro R H n ST SG Q SQ p y k x hl hp hk hc hbc hx
  obtain ⟨a, ha⟩ := exists_lift H x
  obtain ⟨b, hb⟩ := DetLift.exists_isDetLift R H n k hk
  have hab : IsDetLift (host_cmData R H) (y * k) (a * b) := by
    unfold IsDetLift at ha hb ⊢
    rw [map_mul, map_mul, ha, hb, hx, map_mul]
  have hK : b ∈ KDq H SQ := by
    refine mem_KDq_of_conj hl b (fun w => ?_) fun P hP => ?_
    · rw [DetSpec.val_compAt_eq hb ⟨stdLat_lattice, stdLat_unimodular⟩ hc (fr := fun _ => LinearEquiv.refl _ _)
        (fun _ _ => Iff.rfl) w]
      simp
    · have hdet : adAt H.F P (k : Matrix (Fin n) (Fin n) (AfE H.F H.E)).det = 1 := by
        refine adAt_eq_one_of_prV P ?_
        have h := congrArg (fun g => Matrix.det (Units.val g)) (hbc P hP)
        simp only [Formalism.UG.bc, Units.coe_map, Units.val_one, Matrix.det_one] at h
        rw [RingHom.map_det]
        exact h
      have hs0 : adAt H.F P (Formalism.UG.sigR (host_cmData R H).sig _ (finAf H.F H.E b : AfE H.F H.E)) ≠ 0 :=
        (((Units.isUnit (finAf H.F H.E b)).map (Formalism.UG.sigR (host_cmData R H).sig _)).map (adAt H.F P)).ne_zero
      rw [DetSpec.compAt_eq hb P, hdet, one_mul, div_self hs0, sub_self, map_zero]
      exact zero_lt_one
  rw [normOneFiniteAdeleDetClass_of_isDetLift H SQ x a ha, ← DetSpec.mk_eq_detPt R H n ST SG Q SQ p (y * k) (a * b) hl hp hab,
    QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff b).2 hK, mul_one]

end GlobalTheory.Mem.Col2.FullDt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointLatticeIffBaseLatticeDecorated
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PtLat

theorem latS_deco_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (S : Submodule (𝓞 E) (Fin n → E)) (k t y : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q), t ∈ K1 hc n ST SG → (∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) → IsPtOf hc (y * (k * t)) p → ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) p.deco.1.L ↔ (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q S k t y p ht hS hp x
  have hp0 : IsPtOf hc (y * (k * t)) (extTo ∅ p) :=
    hp.extTo (Finset.empty_subset _) (Finset.disjoint_empty_right _)
  obtain ⟨hg, hd⟩ := (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ _ _ rfl).1 hp0
  have hd' : p.deco.1 = decoRaw ST SG (y * (k * t)) := hd
  have hcar := decoRaw_carries hc n ST SG hg x
  rw [hd']
  refine hcar.trans ?_
  have hst := mirabolicLevel_le_stabilizer_base hc n ST (principal_le_congruence_subgroup hc n ST SG (Subgroup.inv_mem _ ht))
  have e : (((y * (k * t))⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x =
      ((t⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        (((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (((y⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x)) := by
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  exact ((hst _).symm).trans (hS _).symm

end GlobalTheory.Mem.Col2.PtLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalNormOneClassEqFiniteAdelicDetClass
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.FullDt

theorem e1Q_eq_u1Dt_of_det_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (z : unitary H.E) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), Matrix.GeneralLinearGroup.det x.1 = Formalism.L2.Herm.unitaryOneRationalAdele H.F z → e1Q H SQ z = u1Dt H SQ x := by
  intro R H SQ z x hx
  obtain ⟨k, hk⟩ := exists_eq_div_conj H z
  rw [← isUnitaryPointsMap_unitaryRationalPointsFiner H SQ k z hk]
  symm
  apply normOneFiniteAdeleDetClass_of_isDetLift
  unfold IsDetLift
  rw [hx]
  have hf : finAf H.F H.E (Neutral.B1.diagUnits H.E k) = Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k := by
    apply Units.ext
    apply (afIso H.F H.E).injective
    rw [afIso_finAf]
    show _ = afIso H.F H.E ((k : H.E) ⊗ₜ[H.F] 1)
    rw [afIso_tmul_one]
    rfl
  rw [hf]
  have key : Formalism.L2.Herm.unitaryOneRationalAdele H.F z * conjId (host_cmData R H).sig
      (Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k) =
      Units.map (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F)).toMonoidHom k := by
    apply Units.ext
    show Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (z : H.E) *
      Formalism.UG.sigR (host_cmData R H).sig _ (Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (k : H.E)) =
      Formalism.UG.inclE (F := H.F) (FiniteAdeleRing (𝓞 H.F) H.F) (k : H.E)
    rw [sigR_inclE, ← map_mul, bridge_star_holds R H, hk]
  rw [h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul]
  exact key.symm

end GlobalTheory.Mem.Col2.FullDt
end

