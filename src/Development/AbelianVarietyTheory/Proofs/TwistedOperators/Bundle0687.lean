import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0676
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0252
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0649
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0668
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0647

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLineMapKeepsLatticesLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.LastLineLat

variable {D : D7}

theorem of_tmul_eq (p : AF D.host.F) {m n : ℕ} (y : Fin m → Fin n → D.host.E) :
    (Matrix.of fun i j => p ⊗ₜ[D.host.F] y i j : Mx D m n) = (p ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • rat (Matrix.of y) := by
  ext i j
  simp only [rat, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  change _ = _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem cA_tmul_one (p : AF D.host.F) : cA D (p ⊗ₜ[D.host.F] (1 : D.host.E)) = p ⊗ₜ[D.host.F] (1 : D.host.E) := by
  simp [cA, sigR]

theorem adj_rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : adj (rat M : Mx D m n) = rat Mᴴ := by
  ext i j
  simp [adj, rat, Matrix.conjTranspose_apply, GlobalTheory.DualPairCheck.cA_incA]

theorem rat_smul' {m n : ℕ} (c : D.host.E) (M : Matrix (Fin m) (Fin n) D.host.E) :
    (rat (c • M) : Mx D m n) = incA D c • rat M := by
  ext i j
  simp [rat]

theorem kap_gen {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {c0 : D.host.E} (hτ : ∀ i k, τ i k = c0)
    (V : HSp D) (p : AF D.host.F) (a : D.host.E) (s : Fin V.rank → D.host.E)
    (t : Fin L''.rank → D.host.E) :
    kap τ V (Matrix.of fun i j => p ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * V.gram k j)) =
      Matrix.of fun i j => p ⊗ₜ[D.host.F] (s i * star (D.host.xi0⁻¹ * c0 * ∑ l, a * t l) * ∑ k, L.gram k j) := by
  have hy : (Matrix.of fun i j => a * t i * ∑ k, star (s k) * V.gram k j) =
      Matrix.vecMulVec (fun i => a * t i) (star s) * V.gram := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Finset.mul_sum, mul_assoc]
  have h1 := of_tmul_eq (D := D) p (fun i j => a * t i * ∑ k, star (s k) * V.gram k j)
  rw [hy] at h1
  have h2 := of_tmul_eq (D := D) p (fun i j => s i * star (D.host.xi0⁻¹ * c0 * ∑ l, a * t l) * ∑ k, L.gram k j)
  beta_reduce at h1 h2
  rw [h1, h2]
  unfold GlobalTheory.FinPl.kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have he := cA_tmul_one (D := D) p
  generalize (p ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) = e at he ⊢
  rw [Matrix.mul_smul, adj_smul, he]
  rw [rat_mul (Matrix.vecMulVec (fun i => a * t i) (star s)) V.gram, ← Matrix.mul_assoc (rat τ), ← rat_mul τ,
    show (rat V.gram : Mx D V.rank V.rank) = gA V from rfl, adj_mul, adj_gA, adj_rat, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, giA_gA_cancel, show gA L = (rat L.gram : Mx D L.rank L.rank) from rfl, ← rat_mul, smul_comm,
    ← rat_smul']
  congr 2
  ext i j
  congr 1
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, hτ,
    Pi.star_apply, Matrix.of_apply, smul_eq_mul, star_sum, star_mul', star_star, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg,
    Finset.mul_sum, Finset.sum_mul, inv_neg]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.LastLineLat

namespace GlobalTheory.LastLineLat

variable {D : D7}

theorem kap_add' {L L'' : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (S : HSp D) (w w' : WO S L'') :
    kap τ S (w + w') = kap τ S w + kap τ S w' := by
  have hadj : ∀ x y : Mx D L.rank S.rank, adj (x + y) = adj x + adj y := fun x y => by
    ext i j
    simp [adj]
  unfold GlobalTheory.FinPl.kap GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  rw [Matrix.mul_add (rat τ) w w', hadj, Matrix.add_mul, Matrix.mul_add, smul_add]

theorem line_mem {L V : HSp D} (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (hJ : D.host.AA ≤ D.host.AAbar * J)
    (Λ : Set (Fin V.rank → D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (α : Af D.host.F)
    (hα : α ∈ intAf D.host.F) (hP : ∀ v, ¬ P v → evalV D.host.F v α = 0) (s : Fin V.rank → D.host.E) (hs : s ∈ Λ)
    (c : D.host.E) (hc : c ∈ D.host.AA) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star c * ∑ k, L.gram k j) : Mx D V.rank L.rank) ∈
      latO L V (GlobalTheory.RowShape.latPi L J : Set _) Λ P := by
  have hc' : c ∈ D.host.AAbar * J := hJ hc
  refine FractionalIdeal.mul_induction_on (C := fun c => (Matrix.of fun i j =>
      pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star c * ∑ k, L.gram k j) : Mx D V.rank L.rank) ∈
      latO L V (GlobalTheory.RowShape.latPi L J : Set _) Λ P) hc' ?_ ?_
  · intro b hb e he
    refine AddSubgroup.subset_closure ⟨α, hα, hP, star b, ?_, fun _ => e, ?_, s, hs, ?_⟩
    · rw [bridge_star_holds D.R D.host b]; exact Formalism.L2.Pj.conj_mem_AA D hb
    · exact Submodule.mem_pi.2 fun _ _ => he
    · ext i j
      simp only [Matrix.of_apply, star_mul', Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun _ _ => by ring
  · intro x y hx hy
    have : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star (x + y) * ∑ k, L.gram k j) :
        Mx D V.rank L.rank) = (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star x * ∑ k, L.gram k j)) +
        (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (s i * star y * ∑ k, L.gram k j)) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.add_apply, star_add, mul_add, add_mul, TensorProduct.tmul_add]
    rw [this]
    exact add_mem hx hy

theorem AA_le_lineId (D : D7) (j : ℕ) (hj : j + 2 = D.R.m) :
    D.host.AA ≤ D.host.AAbar * GlobalTheory.RowShape.lineId D j := by
  have hb : D.host.AAbar ≠ 0 := by
    intro h
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h] at h1
    simp at h1
  unfold GlobalTheory.RowShape.lineId
  rw [show (D.R.m - 2 - j) / 2 + 1 = 1 by omega, pow_one, pow_one, mul_comm D.host.AA, ← mul_assoc,
    mul_inv_cancel₀ hb, one_mul]

theorem mul_mem_AA {a : D.host.E} (ha : a ∈ D.host.AA) {t : D.host.E}
    (ht : t ∈ ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) : a * t ∈ D.host.AA := by
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff] at ht
  obtain ⟨y, rfl⟩ := ht
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ y ha

end GlobalTheory.LastLineLat

namespace GlobalTheory.LastLineLat

theorem kap_latO (D : D7) (V : HSp D) (Λ : Set (Fin V.rank → D.host.E)) (j : ℕ) (hj : j + 2 = D.R.m)
    (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∀ w ∈ latO V (pLine D) Λ (GlobalTheory.RowShape.topL D : Set _) (· = v),
      kap lastTau V w ∈ latO (Model.nLine D) V (GlobalTheory.RowShape.lineL D j : Set _) Λ (· = v) := by
  have hle : latO V (pLine D) Λ (GlobalTheory.RowShape.topL D : Set _) (· = v) ≤
      (latO (Model.nLine D) V (GlobalTheory.RowShape.lineL D j : Set _) Λ (· = v)).comap (AddMonoidHom.mk' (kap lastTau V) (kap_add' lastTau V)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.mk'_apply]
    rw [kap_gen lastTau (c0 := -D.host.xi0) (fun _ _ => rfl)]
    refine line_mem _ (AA_le_lineId D j hj) Λ _ α hα hP s hs _ ?_
    have hx := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
    rw [show D.host.xi0⁻¹ * -D.host.xi0 = -1 by rw [mul_neg, inv_mul_cancel₀ hx], neg_one_mul]
    have ht' : t ∈ GlobalTheory.RowShape.latPi (pLine D) 1 := ht
    exact Submodule.neg_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) (Submodule.sum_mem _ fun l _ => mul_mem_AA ha (Submodule.mem_pi.1 ht' l (Set.mem_univ _)))
  exact fun w hw => hle hw

end GlobalTheory.LastLineLat

theorem GlobalTheory.LastLineLat.kap_lastTau_latO : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j + 2 = D.R.m → ∀ v, ∀ w ∈ latO (ch.G.V (.top (j + 1))) (pLine D) (ch.G.Λ (.top (j + 1)) : Set _) (GlobalTheory.RowShape.topL D : Set _) (· = v),
    GlobalTheory.FinPl.kap lastTau _ w ∈ latO (GlobalTheory.SeeSaw.Model.nLine D) (ch.G.V (.top (j + 1))) (GlobalTheory.RowShape.lineL D j : Set _) (ch.G.Λ (.top (j + 1)) : Set _) (· = v) := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ j hj v
  exact GlobalTheory.LastLineLat.kap_latO D _ _ j hj v
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLinearLeftLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LastPositionLin
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {M : Vol G} {t : T}

theorem lastDat_lin (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj))
    (g : GA D (G.V (.grid D.R.m j)))
    (Φ Φ' : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ) (c : ℂ)
    (hΦ : IsThetaFunO W.ψ _ _ Φ) (hΦ' : IsThetaFunO W.ψ _ _ Φ')
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (u v) :
    lastDat W hM j hj vN g (c • Φ + Φ') Φ₂ u v =
      c * lastDat W hM j hj vN g Φ Φ₂ u v + lastDat W hM j hj vN g Φ' Φ₂ u v := by
  set s := (lastAt G W t hM j hj vN).s with hs
  have hw := s.weil
  have h1 := hw.om_pres (g, 1) Φ hΦ
  have h2 := hw.om_pres (g, 1) Φ' hΦ'
  have h3 : IsThetaFunO W.ψ _ _ (c • s.om (g, 1) Φ) := GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c h1
  have e1 : (s.om (g, 1)) (c • Φ + Φ') = c • (s.om (g, 1)) Φ + (s.om (g, 1)) Φ' := by
    have := (s.om (g, 1)).map_add (c • Φ) Φ'
    have h' := (s.om (g, 1)).map_smul c Φ
    exact this.trans (congrArg (· + (s.om (g, 1)) Φ') h')
  have key : GlobalTheory.Unf.flatBF s (s.om (g, 1) (c • Φ + Φ')) =
      c • GlobalTheory.Unf.flatBF s (s.om (g, 1) Φ) + GlobalTheory.Unf.flatBF s (s.om (g, 1) Φ') := by
    rw [e1, (GlobalTheory.FlatLin.flatBF_linear D (GlobalTheory.Unf.Flat.flatLaw D) _ _ _ _ s _ _ c h3 h2).1,
      (GlobalTheory.FlatLin.flatBF_linear D (GlobalTheory.Unf.Flat.flatLaw D) _ _ _ _ s _ _ c h1 h1).2]
  have keyx : ∀ x, GlobalTheory.Unf.flatBF s (s.om (g, 1) (c • Φ + Φ')) x =
      c * GlobalTheory.Unf.flatBF s (s.om (g, 1) Φ) x + GlobalTheory.Unf.flatBF s (s.om (g, 1) Φ') x := fun x => by
    rw [key]; rfl
  unfold lastDat GlobalTheory.FinPl.lastBi GlobalTheory.MixModel.OrthDec.boxT
  rw [← hs]
  beta_reduce
  erw [keyx]
  ring

theorem conAt_last_lin (hM : M.Is t) (P : PolDown G) (h : Pts G) (Φ : SchDown G t) (j : ℕ) (hj : j + 2 = D.R.m)
    (a : Fin D.R.m) (ha : (a : ℕ) = j + 0) (φ φ' : Sch G (.down t D.R.m a)) (c : ℂ)
    (hφ : IsThetaFunO W.ψ _ _ φ) (hφ' : IsThetaFunO W.ψ _ _ φ') (u v) :
    conAt W hM (fockD W t (Function.update Φ a (c • φ + φ')) P) h j u v =
      c * conAt W hM (fockD W t (Function.update Φ a φ) P) h j u v +
        conAt W hM (fockD W t (Function.update Φ a φ') P) h j u v := by
  obtain ⟨k, hk⟩ := a
  simp only [add_zero] at ha
  subst ha
  have h0 : k + 2 * 0 + 2 = D.R.m := by omega
  unfold conAt
  rw [dif_pos h0, dif_pos h0, dif_pos h0]
  have hne : (⟨k + 1, by omega⟩ : Fin D.R.m) ≠ ⟨k, hk⟩ := fun e => by simp at e
  simp only [fockD, Function.update_self, Function.update_of_ne hne]
  have hf : W.fock (.mu t D.R.m k) (c • φ + φ') (P ⟨k, hk⟩) =
      c • W.fock (.mu t D.R.m k) φ (P ⟨k, hk⟩) + W.fock (.mu t D.R.m k) φ' (P ⟨k, hk⟩) :=
    GlobalTheory.FockFiniteHeis.pureTensorO_lin W.ψ W.θ _ _ W.ψ_std W.θ_is _ _ _ _ c hφ hφ' _
  have th : ∀ f : Sch G (.down t D.R.m (⟨k, hk⟩ : Fin D.R.m)), IsThetaFunO W.ψ _ _ f →
      IsThetaFunO W.ψ (G.V (.grid D.R.m k)) (G.V (.grid D.R.m (k + 1))) (W.fock (.mu t D.R.m k) f (P ⟨k, hk⟩)) :=
    fun f hf => Formalism.IndefR.Fin.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ f _ hf
  erw [hf]
  exact lastDat_lin W hM k h0 _ _ _ _ c (th φ hφ) (th φ' hφ') _ u v

end GlobalTheory.LastPositionLin

open GlobalTheory.RowClaim GlobalTheory.ConnectionLinear in

theorem GlobalTheory.LastPositionLin.lastLin_zero : Big fun ch => GlobalTheory.ConnectionLinear.LastLin ch 0 := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intros D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _
  intro j _ hj t M hM P h Φ a ha φ φ' c _ hφ hφ' u v
  exact GlobalTheory.LastPositionLin.conAt_last_lin ch.W hM P h Φ j hj a ha φ φ' c hφ hφ' u v
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastSeesawLinearRightLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.ConnectionLinear
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastLinR

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem castSch_lin {V : HSp D} {n n' : ℕ} (e : n = n') (c : ℂ) (f g : WO V (G.V (.grid D.R.m n)) → ℂ) :
    castSch G e (c • f + g) = c • castSch G e f + castSch G e g := by
  subst e; rfl

theorem lastDat_lin (Wl : G.Weil) {t : T} {M : Vol G} (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m)
    (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj)) (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (c : ℂ) (Φ₂ Φ₂' : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (u v) :
    lastDat Wl hM j hj vN g Φ₁ (c • Φ₂ + Φ₂') u v = c * lastDat Wl hM j hj vN g Φ₁ Φ₂ u v + lastDat Wl hM j hj vN g Φ₁ Φ₂' u v := by
  simp only [lastDat, GlobalTheory.FinPl.lastBi, OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.LastLinR

namespace GlobalTheory.ConnectionLinear

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem lastLin_one (ch : Choice R) : LastLin ch 1 := by
  intro j hj hjm t M hM P h Φ a ha φ φ' c hΦ hφ hφ' u v
  have h0 : j + 2 * 0 + 2 = D.R.m := by omega
  have hlt : j + 1 < D.R.m := by omega
  obtain rfl : a = ⟨j + 1, hlt⟩ := Fin.ext ha
  have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hlt⟩ := fun e => by simp [Fin.ext_iff] at e
  unfold conAt
  rw [dif_pos h0, dif_pos h0, dif_pos h0]
  simp only [fockD, Function.update_of_ne hne, Function.update_self]
  have hlin : ch.W.fock (.mu t D.R.m (j + 1)) (c • φ + φ') (P ⟨j + 1, hlt⟩) =
      c • ch.W.fock (.mu t D.R.m (j + 1)) φ (P ⟨j + 1, hlt⟩) + ch.W.fock (.mu t D.R.m (j + 1)) φ' (P ⟨j + 1, hlt⟩) := by
    simp only [GridData.Weil.fock]
    exact GlobalTheory.FockFiniteHeis.pureTensorO_lin _ _ _ _ ch.W.ψ_std ch.W.θ_is _ _ _ _ c hφ hφ' _
  rw [hlin, GlobalTheory.LastLinR.castSch_lin, GlobalTheory.LastLinR.lastDat_lin]

end

theorem big_lastLin_one : Big fun ch => LastLin ch 1 :=
  by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _
  exact lastLin_one ch

end GlobalTheory.ConnectionLinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastTwoStepsLocalModelExtendByZeroTopStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.LastStepExt0

theorem model_last : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (hChr : ChrP ch) (hArr : ArrP ch) (hJac : JacP ch)
    (t : T) (w : Pl D.host.E) (hw : w ∈ locPl ch.G t) (p : Place D (Kw w)) (hp : IsPlc w p)
    (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w))
    (M : Vol ch.G) (hM : M.Is t) (φ : EdgeDat ch t w) (v f : SchDown ch.G t)
    (hvf : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j))
    (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m)
    (h₃ : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, D.R.m))
    (h₄ : (locGrid ch.G t w).rank (D.R.m, j + 1) = topRank (locGrid ch.G t w) (j + 1)),
    ∃ T₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) →ₗ[ℂ]
        (WO (ch.G.V (.top (j + 1))) (ch.G.V (.grid D.R.m D.R.m)) → ℂ),
      p.IsModel ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w D.R.m le_rfl) T₂ ∧
      (∀ O, IsOne O → T₂ O = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (v ⟨j + 1, by omega⟩)
        ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)) ∧
      ∃ Φ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, D.R.m))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)),
        (∀ z, Φ.1 z = phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
          (.theta D.R.m (j + 1)) (z.submatrix (Fin.cast h₃) (Fin.cast h₄))ᵀ) ∧
        T₂ Φ = fun x => castSch ch.G (show j + 1 + 1 = D.R.m by omega) (f ⟨j + 1, by omega⟩)
          ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hChr hArr hJac t w hw p hp β M hM φ v f hvf j hj h₃ h₄
  suffices key : ∀ (n : ℕ) (hn : j + 1 + 1 = n) (hnm : n ≤ D.R.m)
      (h₃' : (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, n)),
      ∃ T₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, n))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) →ₗ[ℂ]
        (WO (ch.G.V (.top (j + 1))) (ch.G.V (.grid D.R.m n)) → ℂ),
      p.IsModel ch.W.ψ (frTop ch.S.toGridChoice t w (j + 1) (by omega)) (frRow ch.S.B t w n hnm) T₂ ∧
      (∀ O, IsOne O → T₂ O = fun x => castSch ch.G hn (v ⟨j + 1, by omega⟩)
        ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)) ∧
      ∃ Φ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, n))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)),
        (∀ z, Φ.1 z = phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
          (.theta D.R.m (j + 1)) (z.submatrix (Fin.cast h₃') (Fin.cast h₄))ᵀ) ∧
        T₂ Φ = fun x => castSch ch.G hn (f ⟨j + 1, by omega⟩)
          ((rowJac ch.G (j + 1) (by omega) 0 (by omega)).ext0 _ x)
  · exact key D.R.m (by omega) le_rfl h₃
  intro n hn hnm h₃'
  subst hn
  have hj1 : j + 1 < D.R.m := by omega
  have hc : topRank (locGrid ch.G t w) (j + 1) + 0 = (locGrid ch.G t w).rank (D.R.m, j + 1) := by omega
  have hloc : ∀ i (hi : i ≤ D.R.m), D.R.m ≤ i + 1 →
      p.IsLoc (frRow ch.S.B t w i hi) 1 ((epsV ch.G t w * (repsAt ch.G t w).elt β) (D.R.m, i)) := by
    intro i hi hmi
    rw [Pi.mul_apply, epsV_eq_one t w hmi, elt_eq_one t w β hmi, mul_one]
    refine ⟨fun a b => by simp [Formalism.L2.Theta.mt], ?_⟩
    have : Formalism.L2.Theta.mt (ch.G.V (.grid D.R.m i)) 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
    simp [(frRow ch.S.B t w i hi).βγ]
  obtain ⟨Tm, hTm, hOne, Φ, hΦ, hTΦ⟩ := hArr t w hw p hp φ (j + 1) hj1 (v ⟨j + 1, hj1⟩) (f ⟨j + 1, hj1⟩) (hvf ⟨j + 1, hj1⟩)
    (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem t w X) 1 1 1 1 (hloc (j + 1) hj1.le (by omega))
    (hloc (j + 1 + 1) hj1 (by omega)) (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0)
    (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1))) (frame hc) (Equiv.refl _)
  have hJ := hJac t w hw p hp M hM j 0 hj (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt ch.G j 0 hj)).some 1 (Or.inl ⟨rfl, rfl⟩) 0 hc
  have hFT : (mvFr p (1 : GA D (ch.G.V (.grid D.R.m (j + 1 + 1)))) (frRow ch.S.B t w (j + 1 + 1) hj1)
      (epsV ch.G t w (D.R.m, j + 1 + 1)) (Equiv.refl _)).β = (frRow ch.S.B t w (j + 1 + 1) hj1).β := by
    simp only [mvFr]
    rw [epsV_eq_one t w (by omega)]
    have : Formalism.L2.Theta.mt (ch.G.V (.grid D.R.m (j + 1 + 1))) 1 = 1 := by simp [Formalism.L2.Theta.mt]
    rw [this, Matrix.map_one p.π (map_zero _) (map_one _)]
    simp
  obtain ⟨Tm', hTm', hTT⟩ := Place.exists_isModel_chg D (Kw w) p _ _ _ _
    (mvFr p 1 (frRow ch.S.B t w (j + 1) hj1.le) (epsV ch.G t w (D.R.m, j + 1)) (frame hc))
    (mvFr p 1 (frRow ch.S.B t w (j + 1 + 1) hj1) (epsV ch.G t w (D.R.m, j + 1 + 1)) (Equiv.refl _)) _ _
    (mvFr p 1 (frRow ch.S.B t w (j + 1) hj1.le) (epsV ch.G t w (D.R.m, j + 1)) (frame hc))
    (frRow ch.S.B t w (j + 1 + 1) hj1) ch.W.ψ Tm hTm
  have hTT' : ∀ Ψ, Tm' Ψ = Tm Ψ := fun Ψ => hTT Ψ Ψ fun x => by
    rw [hFT, Frame.γβ, Frame.γβ, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨T₂, hT₂, hval⟩ := RankZeroSrc.localModel_rankZeroWitt_source_isModel D (Kw w) p ch.W.ψ ch.W.ψ_std (jacAt ch.G hM (j + 1) 0 (by omega)) _ _ _ _
    (frTop ch.S.toGridChoice t w (j + 1) (by omega)) _ hJ _ (frRow ch.S.B t w (j + 1 + 1) hj1) Tm' hTm'
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Kw w) (n := Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
    (n' := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0)
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := Kw w) (n := Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
    (n' := Fin (topRank (locGrid ch.G t w) (j + 1)))
  have hc1 : Continuous fun x : Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Kw w) => x.toCols₁ :=
    continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply i)
  have hc2 : Continuous fun x : Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w) =>
        (fromCols x 0 : Matrix _ (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Kw w)) :=
    continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · exact (continuous_apply j).comp (continuous_apply i)
      · exact j.elim0
  refine ⟨T₂, hT₂, fun O hO => ?_, ?_⟩
  · let O' : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1)))
        (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin 0) (Kw w)) :=
      ⟨fun x => O.1 x.toCols₁, GlobalTheory.FinPl.Comm.comp_mem_SB O.2 hc1 hc2 RankZeroSrc.fromCols_toCols₁⟩
    have hO' : IsOne O' := by
      funext x
      show O.1 x.toCols₁ = _
      rw [hO]
      by_cases h2 : ∀ r q, x r q ∈ 𝒪[Kw w]
      · rw [Set.indicator_of_mem (s := {x : Matrix _ _ (Kw w) | ∀ r q, x r q ∈ 𝒪[Kw w]}) (a := x.toCols₁) (fun r q => h2 r (Sum.inl q)),
          Set.indicator_of_mem (s := {x : Matrix _ _ (Kw w) | ∀ r q, x r q ∈ 𝒪[Kw w]}) h2]
      · rw [Set.indicator_of_notMem (s := {x : Matrix _ _ (Kw w) | ∀ r q, x r q ∈ 𝒪[Kw w]}) h2, Set.indicator_of_notMem (a := x.toCols₁)]
        intro h1
        apply h2
        intro r q
        rcases q with q | q
        exacts [h1 r q, q.elim0]
    funext x
    refine (hval O O' (fun y => by simp [O', Matrix.toCols₁_fromCols]) x).trans ?_
    refine (congrFun (hTT' O') _).trans ?_
    refine (congrFun (hOne O' hO') _).trans ?_
    simp only [show ((1 : GA D (ch.G.V (.grid D.R.m (j + 1)))), (1 : GA D (ch.G.V (.grid D.R.m (j + 1 + 1))))) = 1 from rfl,
      map_one, Module.End.one_apply]
    rfl
  · let Φ₂ : SB (Matrix (Fin ((locGrid ch.G t w).rank (D.R.m, j + 1 + 1))) (Fin (topRank (locGrid ch.G t w) (j + 1))) (Kw w)) :=
      ⟨fun x => Φ.1 (fromCols x 0), GlobalTheory.FinPl.Comm.comp_mem_SB Φ.2 hc2 hc1 fun x => Matrix.toCols₁_fromCols x 0⟩
    have hs : ∀ b, (frame hc).symm b = Sum.inl (Fin.cast h₄ b) := fun b => by
      rw [Equiv.symm_apply_eq]
      ext
      rfl
    refine ⟨Φ₂, fun z => ?_, ?_⟩
    · show Φ.1 (fromCols z 0) = _
      rw [hΦ]
      congr 2
      ext a b
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply, hs, Matrix.fromCols_apply_inl]
      rfl
    · funext x
      refine (hval Φ₂ Φ (fun _ => rfl) x).trans ?_
      refine (congrFun (hTT' Φ) _).trans ?_
      refine (congrFun hTΦ _).trans ?_
      simp only [mul_one, show ((1 : GA D (ch.G.V (.grid D.R.m (j + 1)))), (1 : GA D (ch.G.V (.grid D.R.m (j + 1 + 1))))) = 1 from rfl,
        map_one, Module.End.one_apply]
      rfl

end GlobalTheory.LastStepExt0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedIntegralFiniteSupport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.StripPlaces

theorem exists_comb_trivial_off : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁ (z : GA D (G.V (.grid i j)) →₀ ℂ),
  ∃ (z' : GA D (G.V (.grid i j)) →₀ ℂ) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    translates z' (kerSmall W Θ' g g₁) = translates z (kerSmall W Θ' g g₁) ∧ zdeg z' = zdeg z ∧
    ∀ b ∈ z'.support, ∀ v ∉ P, GlobalTheory.AdelicU.proj D.sp.cm.sig (G.V (.grid i j)).gram v b = 1 := by
  intro _ _ _ _ _
  classical
  obtain ⟨CF0, hA⟩ := GlobalTheory.T.exists_lattice_for_matched_frames ‹_› ‹_› ‹_› ‹_› ‹_›
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hA⟩ := hA ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩
  intro G W hW B ρ hρ t i j Θ Θ' hM g g₁ z
  obtain ⟨L, S, hLfg, hLsp, hinv⟩ := hA D large₂ hε hx Γ Pl0 T A Ks R F hS G W hW B ρ hρ t i j Θ Θ' hM g g₁
  choose b' P hP hK using fun b => GlobalTheory.T.exists_finiteSupport_mul_latticeStabilizer (G.V (.grid i j)) L hLfg hLsp S b
  set f := kerSmall W Θ' g g₁ with hf
  have key : ∀ b u, f (u * b' b) = f (u * b) := fun b u => by
    have := hinv _ (hK b) (u * b' b)
    rw [← this, mul_assoc, mul_inv_cancel_left]
  refine ⟨z.mapDomain b', z.support.biUnion P, ?_, ?_, ?_⟩
  · funext u
    simp only [translates]
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    exact Finsupp.sum_congr fun b _ => by rw [key]
  · simp only [zdeg]
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  · intro c hc v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hc)
    exact hP b v fun h => hv (Finset.mem_biUnion.2 ⟨b, hb, h⟩)

end GlobalTheory.StripPlaces
end

