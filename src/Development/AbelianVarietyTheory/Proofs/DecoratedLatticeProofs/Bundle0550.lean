import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0420
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0541
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0544
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0467
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0545
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0547
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0489
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairIdentity
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.MiTop

theorem lattice_ratio_vector_of_scalar_factorisation {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (e c θ θ' : R)
    (X X' Sm Sm' Kk Z : GL n R) (hZ : Z.val = c • (1 : Matrix n n R))
    (hT : X⁻¹ * Sm = Z * (X'⁻¹ * Sm') * Kk) (zY zY' Γ : n → R)
    (hm : e • Matrix.mulVec (Sm⁻¹).val zY = e • (θ • Γ)) (hm' : e • Matrix.mulVec (Sm'⁻¹).val zY' = e • (θ' • Γ)) :
    e • ((θ * c) • Matrix.mulVec ((X'⁻¹ * Sm') * Kk * (X'⁻¹ * Sm')⁻¹).val (Matrix.mulVec (X'⁻¹).val zY')) =
      e • (θ' • Matrix.mulVec (X⁻¹).val zY) := by
  set M := (X'⁻¹ * Sm') * Kk * (X'⁻¹ * Sm')⁻¹ with hM
  have hg : Z * M * X'⁻¹ = (X⁻¹ * Sm) * Sm'⁻¹ := by
    rw [hM, hT]; group
  have h2 : c • Matrix.mulVec M.val (Matrix.mulVec (X'⁻¹).val zY') = Matrix.mulVec (Z * M * X'⁻¹).val zY' := by
    have : (Z * M * X'⁻¹).val = c • (M.val * (X'⁻¹).val) := by
      rw [Units.val_mul, Units.val_mul, hZ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [this, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have h3 : e • (θ • Matrix.mulVec (Sm'⁻¹).val zY') = e • (θ' • Matrix.mulVec (Sm⁻¹).val zY) := by
    rw [smul_comm e θ (Matrix.mulVec (Sm'⁻¹).val zY'), hm', smul_comm e θ' (Matrix.mulVec (Sm⁻¹).val zY), hm,
      smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [mul_smul, h2, hg, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, h3,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul]
  congr 3
  group

theorem redFn_scalar_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Formalism.L2.DIV.Pl E)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (c : E ⊗[F] Formalism.L2.Herm.Af F) (hx : x ∈ Formalism.L2.DIV.St β)
    (hc : x.val = c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (i₀ : Fin n) :
    ∃ hci : c ∈ Formalism.L2.Herm.intAf F E,
      (Formalism.L2.DIV.resS F PP ⟨c, hci⟩ = 1 → Formalism.L2.DIV.redFn β PP x = 1) := by
  obtain ⟨y, rfl⟩ := hx
  have hy : (Formalism.L2.DIV.intGL F E n y).val = c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have e1 : Formalism.L2.DIV.intGL F E n y = β⁻¹ * Formalism.L2.DIV.frGL β y * β := by
      simp only [Formalism.L2.DIV.frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e1, Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hent : ∀ i j, ((y.val i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
      (c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) i j := fun i j => by
    rw [← hy]; rfl
  have hci : c ∈ Formalism.L2.Herm.intAf F E := by
    have h := hent i₀ i₀
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    rw [← h]; exact (y.val i₀ i₀).2
  refine ⟨hci, fun h1 => ?_⟩
  rw [Formalism.L2.DIV.redFn_frGL]
  apply Units.ext
  ext i j
  have hyij : y.val i j = if i = j then ⟨c, hci⟩ else 0 := by
    apply Subtype.ext
    rw [hent i j, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  show Formalism.L2.DIV.resS F PP (y.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j
  rw [hyij, Matrix.one_apply]
  split_ifs <;> simp [h1]

set_option maxHeartbeats 2000000 in

theorem centralRatio_red_eq_one : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ rJ W, tOf f B a₀ a = z * tOf f' B' a₀' a' * k → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, Formalism.L2.DIV.redFn (W.Q.Rl.βY 0) PP (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z)) = 1 := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr u u' f f' B B' hPl hPl' a₀ a a₀' a' hA hA' z hzf hzc k hk heq PP hPP
  classical
  by_cases hS : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z) ∈ Formalism.L2.DIV.St (W.Q.Rl.βY 0)
  swap
  · unfold Formalism.L2.DIV.redFn Formalism.L2.DIV.ext1
    rw [dif_neg hS]
  rcases Nat.eq_zero_or_pos (Yc D 0).rank with h0 | hpos
  · apply Units.ext; ext i; exact absurd i.2 (by omega)
  obtain ⟨c, hc⟩ := GlobalTheory.T.center_adelicUnitaryGroup_finitePart_scalar (Yc D 0) (show GA D (Yc D 0) from z) hzc hzf
  obtain ⟨hci, hfin⟩ := redFn_scalar_eq_one (W.Q.Rl.βY 0) PP _ c hS hc ⟨0, hpos⟩
  apply hfin
  obtain ⟨-, hconj⟩ := hA'.2.2.2
  have hκ : tOf f' B' a₀' a' * k * (tOf f' B' a₀' a')⁻¹ ∈ rowJ W.S.X W.Q.instEq := by
    have := ((hconj k).1).1 hk
    simpa using this
  obtain ⟨Γ, hΓ⟩ := GlobalTheory.T.base_moves_vector_z_alt W hP hr PP hPP
  obtain ⟨θ, hθ, hθ1, hm⟩ := hΓ u f B (by first | exact hPl | exact PlacedP.placed f B hPl) a₀ a hA
  obtain ⟨θ', hθ', hθ1', hm'⟩ := hΓ u' f' B' (by first | exact hPl' | exact PlacedP.placed f' B' hPl') a₀' a' hA'
  have hmul : ∀ x y : GA D (D.sp.Y 0), Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (x * y : GA D (D.sp.Y 0))) =
      Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from x) * Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y) :=
    fun x y => map_mul (Formalism.IndefR.Lev.finE (Yc D 0)) x y
  have hinv : ∀ x : GA D (D.sp.Y 0), Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (x⁻¹ : GA D (D.sp.Y 0))) =
      (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from x))⁻¹ :=
    fun x => map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) x
  have ht : ∀ (u : D.what₂.Word) (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) a₀ a,
      Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from tOf f B a₀ a) =
        (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u)))⁻¹ *
          Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0)) := by
    intro u f B a₀ a
    unfold tOf
    rw [mul_assoc, hmul, hinv]
  have hT := congrArg (fun g : GA D (D.sp.Y 0) => Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from g)) heq
  simp only [hmul, ht] at hT
  have hcong := GlobalTheory.T.row_level_integral_twist W hP hr u u' _ hκ (θ * c) θ' (Subring.mul_mem _ hθ hci) hθ' PP hPP (fun ei hei => by
    have key := lattice_ratio_vector_of_scalar_factorisation (toEAf D ei) c θ θ' _ _ _ _ _ _ hc hT _ _ Γ (hm ei hei) (hm' ei hei)
    have hκE : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (tOf f' B' a₀' a' * k * (tOf f' B' a₀' a')⁻¹ : GA D (D.sp.Y 0))) =
        Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from tOf f' B' a₀' a') * Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from k) *
          (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from tOf f' B' a₀' a'))⁻¹ :=
      ((map_mul (Formalism.IndefR.Lev.finE (Yc D 0)) _ _).trans (congrArg₂ (· * ·) (map_mul (Formalism.IndefR.Lev.finE (Yc D 0)) _ _)
        (map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) _)))
    rw [ht u' f' B' a₀' a'] at hκE
    rw [← hκE] at key
    exact key)
  have e1 : (⟨θ * c, Subring.mul_mem _ hθ hci⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨θ, hθ⟩ * ⟨c, hci⟩ := rfl
  rw [e1, map_mul, hθ1, hθ1', one_mul] at hcong
  exact hcong

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairTranslate
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.CentralUnitGen

theorem scalar_keeps {R : Type} [CommRing R] {S : Subring R} {n : ℕ} (Λ : Submodule S (Fin n → R)) (w : Fin n → R)
    (Mt Mt' Mk Mki : Matrix (Fin n) (Fin n) R) (c c' : R)
    (h1 : Mt = (c • (1 : Matrix (Fin n) (Fin n) R)) * Mt' * Mk) (h2 : (c' * c) • (1 : Matrix (Fin n) (Fin n) R) = 1)
    (hkk : Mk * Mki = 1)
    (hk : ∀ y, y ∈ Λ ↔ Matrix.mulVec Mk y ∈ Λ) (hki : ∀ y, y ∈ Λ ↔ Matrix.mulVec Mki y ∈ Λ)
    (hw : ∀ c0 : R, ((∃ x ∈ Λ, Matrix.mulVec Mt x = c0 • w) ↔ c0 ∈ S) ∧ ((∃ x ∈ Λ, Matrix.mulVec Mt' x = c0 • w) ↔ c0 ∈ S)) :
    ∀ y, y ∈ Λ ↔ Matrix.mulVec (c • (1 : Matrix (Fin n) (Fin n) R)) y ∈ Λ := by
  have e2 : Mt' * Mk = (c' • (1 : Matrix (Fin n) (Fin n) R)) * Mt := by
    rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul, smul_smul, h2, Matrix.one_mul]
  have hcI : c ∈ S := by
    obtain ⟨x', hx', ex'⟩ := ((hw 1).2).2 (one_mem _)
    refine ((hw c).1).1 ⟨Matrix.mulVec Mki x', (hki x').1 hx', ?_⟩
    rw [Matrix.mulVec_mulVec, h1, Matrix.mul_assoc, Matrix.mul_assoc, hkk, Matrix.mul_one, ← Matrix.mulVec_mulVec, ex', one_smul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc'I : c' ∈ S := by
    obtain ⟨x, hx, ex⟩ := ((hw 1).1).2 (one_mem _)
    refine ((hw c').2).1 ⟨Matrix.mulVec Mk x, (hk x).1 hx, ?_⟩
    rw [Matrix.mulVec_mulVec, e2, ← Matrix.mulVec_mulVec, ex, one_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
  intro y
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · intro hy
    exact Λ.smul_mem ⟨c, hcI⟩ hy
  · intro hy
    have h3 := Λ.smul_mem ⟨c', hc'I⟩ hy
    have e3 : (c' * c) • y = y := by
      have := congrArg (fun A => Matrix.mulVec A y) h2
      simpa only [Matrix.smul_mulVec, Matrix.one_mulVec] using this
    rw [← e3, mul_smul]
    exact h3

end GlobalTheory.CentralUnitGen

namespace GlobalTheory.CentralUnitGen

theorem proj_mem_center {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {g : GlobalTheory.AdelicU.GAd σ J}
    (hg : g ∈ Subgroup.center (GlobalTheory.AdelicU.GAd σ J)) : GlobalTheory.AdelicU.proj σ J v g ∈ Subgroup.center (GlobalTheory.AdelicU.GLoc σ J v) := by
  refine Subgroup.mem_center_iff.2 fun x => ?_
  have e := congrArg (GlobalTheory.AdelicU.proj σ J v) (Subgroup.mem_center_iff.1 hg (GlobalTheory.AdelicU.emb σ J v x))
  rwa [map_mul, map_mul, GlobalTheory.AdelicU.proj_emb_self] at e

end GlobalTheory.CentralUnitGen

namespace GlobalTheory.MiTop

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem centralRatio_unit_gen : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ rJ W, tOf f B a₀ a = z * tOf f' B' a₀' a' * k → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ v) → (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → (((D.mem u').A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v z ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig (D.sp.Y 0).gram ((pk W).ΛY 0) v := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr u u' f f' B B' hPl hPl' a₀ a a₀' a' hA hA' z hzf hzc k hk he v hv hTu hTu'
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hfr := (GlobalTheory.Fam.sdY_frames W hP 0 hm).2
  have hkS : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.St ((pk W).βY 0) :=
    Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2)
  have hkv := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D (Yc D 0) _ ((pk W).ΛY 0) hfr k).1 hkS v
  have hkv' := Subgroup.inv_mem _ hkv
  obtain ⟨c, hc⟩ := GlobalTheory.T.center_localUnitaryGroup_finitePlace_scalar D (D.sp.Y 0) v _ (GlobalTheory.CentralUnitGen.proj_mem_center _ _ v hzc)
  obtain ⟨c', hc'⟩ := GlobalTheory.T.center_localUnitaryGroup_finitePlace_scalar D (D.sp.Y 0) v _ (GlobalTheory.CentralUnitGen.proj_mem_center _ _ v (Subgroup.inv_mem _ hzc))
  obtain ⟨w, hw⟩ := GlobalTheory.T.placed_bessel_pair_lattice W hP hr u u' f f' B B' hPl hPl' a₀ a a₀' a' hA hA' v hv hTu hTu'
  have h2 : (c' * c) • (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) = 1 := by
    have h := congrArg (fun g => (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v g)).1) (inv_mul_cancel z)
    simp only [map_mul, map_one, Units.val_mul, Units.val_one] at h
    rw [hc, hc', Matrix.smul_mul, Matrix.one_mul, smul_smul] at h
    exact h
  have h1 := congrArg (fun g => (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v g)).1) he
  simp only [map_mul, Units.val_mul] at h1
  rw [hc] at h1
  have hkk : (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k)).1 *
      (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram
      (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v k)⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  refine GlobalTheory.AdelicU.mem_stabLoc.2 ?_
  rw [hc]
  exact GlobalTheory.CentralUnitGen.scalar_keeps _ w _ _ _ _ c c' h1 h2 hkk (GlobalTheory.AdelicU.mem_stabLoc.1 hkv)
    (GlobalTheory.AdelicU.mem_stabLoc.1 hkv') hw

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSiegelEisensteinModerateGrowthConvergen
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.SphGrowth

theorem spherical_eisenstein_modGrowth : ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ σ : ℝ, (V.rank : ℝ) / 2 < σ → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (σ : ℂ))) :=
  fun D V _ a ha hI σ hσ => GlobalTheory.T.siegelEisensteinSum_moderateGrowth_convergent D V a ha hI 1 σ _ (GlobalTheory.Eis.sph_mem hI (σ : ℂ)) (by simpa using hσ)

end GlobalTheory.Core.Rk.SphGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairStabiliserMemChartLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.StabLev

theorem stab_mem_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ b, ∀ i (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k), g • Q j i = Q j i → (β j i).gl g ∈ A.U j b := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hStd j hj b i g hg
  rw [hA.U j hj b]
  refine ⟨GlobalTheory.T.splitPlaceFrameGL_mem_compactRealTrivial _ _ _ _ _ _ _, ?_⟩
  obtain ⟨x, hx⟩ := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl ((β j i).gl g)
  have hmem : x.1 ∈ (A.K j hj b).lev.U := by
    rw [(A.K j hj b).lev.U_eq]
    refine ⟨x.2, fun v => ?_⟩
    by_cases hv : v = (p i).v
    · subst hv
      have hT := GlobalTheory.T.standardDatum_splitPlaces_over_levelPrime I hOk hPins l Z u k ι p β Q L hStd i
      exact GlobalTheory.T.splitPlace_component_keeps_level_functional I hOk hPins l Z u a Ch A hA k ι p β Q L hStd j hj b i g hg x hx hT
        (GlobalTheory.T.splitPlace_component_mem_baseLattice_level_of_fixes_pair I hOk hPins l Z u a Ch A hA k ι p β Q L hStd j hj b i g hg x hx)
    · rw [GlobalTheory.T.splitFrameGL_finiteMatrix_offPlace_eq_one _ _ _ _ _ _ g _ (rankN (I.rec7 l Z) j hj) x.1 hx v hv]
      exact Subgroup.one_mem _
  exact ⟨⟨x.1, hmem⟩, hx⟩

end GlobalTheory.AdForm.StabLev

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensColPhiOneCharIndSmul
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

section Translate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_phiOne_charInd_smul (χ : AddChar 𝓀[k] ℂ) (P₁ : Pair k n') (Q : Pair k n) (g : GL n k)
    (x : Matrix n (n' ⊕ Fin 1) k) :
    tensCol (phiOne P₁ Q) (charInd χ Q) ((g⁻¹ : GL n k).val * x) =
      tensCol (phiOne P₁ (g • Q)) (charInd χ (g • Q)) x := by
  have hcol : (fun i => ((g⁻¹ : GL n k).val * x) i (Sum.inr 0)) = (g⁻¹ : GL n k) • (fun i => x i (Sum.inr 0)) := rfl
  have hsub : ((g⁻¹ : GL n k).val * x).submatrix id Sum.inl = (g⁻¹ : GL n k).val * x.submatrix id Sum.inl := rfl
  have hphi : ∀ z : Matrix n n' k, phiOne P₁ (g • Q) z = phiOne P₁ Q ((g⁻¹ : GL n k).val * z) := by
    intro z
    have h := phiOne_smul (P := P₁) (Q := Q) (x := z) (1 : GL n' k) g
    rw [one_smul] at h
    rw [h, Units.val_one, Matrix.mul_one]
  have hchi : ∀ y : n → k, charInd χ (g • Q) y = charInd χ Q ((g⁻¹ : GL n k) • y) := by
    intro y
    unfold charInd vecInd
    rw [Pair.smul_lat, mem_smul_iff]
    split_ifs with hy
    · have hv := Pair.hasVal_ev (P := g • Q) (x := y) (by rw [Pair.smul_lat, mem_smul_iff]; exact hy)
      rw [Pair.smul_hasVal] at hv
      rw [hv.ev_eq]
    · simp
  unfold tensCol
  rw [hsub, hcol, hphi, hchi]

end Translate

end GlobalTheory.FinPl

namespace GlobalTheory.FinPl

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMeanEqOrbitSumMeanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_mean_eq_orbit_sum_mean : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (Th : GA D V → ℂ), IsBase W x₀ → IsTh ψ d W x₀ Th → ∀ Ψ : WO V W → ℂ, IsThetaFunO ψ V W Ψ → ∫ n in vN.𝓝, Th n.1 * om (n.1, 1) Ψ 0 ∂vN.ν = ∫ n in vN.𝓝, ∑' x : Orb W x₀, Th n.1 * term ψ d W vS (om (n.1, 1) Ψ) x.1 ∂vN.ν := by
  first | exact @GlobalTheory.Unf.mean_theta_orbit | exact GlobalTheory.Unf.mean_theta_orbit | (intros; apply GlobalTheory.Unf.mean_theta_orbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelSplitPlacesEqJetClassicalTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

namespace GlobalTheory.KJInf.CoreG

theorem om_inv_om {D : D7} (S T : HSp D) (om : Om S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    om (g⁻¹, h⁻¹) (om (g, h) f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, ← Prod.one_eq_mk, map_one]
  rfl

theorem selfDual_latFr {D : D7} (V : HSp D) (hV : V.gram = 1) {n : ℕ} (hn : V.rank = n) (g : GA D V)
    (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hN : Moves V hn g N) :
    ∃ Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E), IsSelfDualC V Λ ∧
      (Λ : Set (Fin V.rank → D.host.E)) = latFr V hn N := by
  subst hn
  exact ⟨N, GlobalTheory.SplitMove.selfDual_move V hV g N hN, rfl⟩

theorem thC_const_mul (D : D7) {a b : ℕ} (δ : ℂ) (sc : ℝ) (SS : Finset (Formalism.L2.DIV.Pl D.host.E))
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ)
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (κ : ℂ) (E : VCx D.what₂.Tau a b → ℂ) :
    thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (fun z => κ * E z) =
      fun z => κ * thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E z := by
  funext z
  simp only [thC, xiV, xiL, xiS, Formalism.L2.Th1.H.sumU, Formalism.L2.Th1.H.opU, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end GlobalTheory.KJInf.CoreG

namespace GlobalTheory.KJInf.CoreG

theorem thetaKernel_eq_jet_thC : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ s : ℂ, (∀ f, IsHol θ S T ψ f → ∀ P, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP S T hS hT s (xiN θ S T hS hT δ sc f) P) → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ c : ℕ, 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ, (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Φ (actO S T g⁻¹ h⁻¹ (γ.map fun r => e * incA D r)) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → ∀ (κ : ℂ) (E : VCx D.what₂.Tau a b → ℂ), (xiN θ S T hS hT δ sc (om (g, h) vac) = fun z => κ * E z) → ∀ P, thetaKO om g h (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) w P) = κ * jetP S T hS hT s (thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E) P := by
  intro D ψ θ S T a b hS hT δ sc hP s hs μ om hW e SS hE vac Φ w hV hSB hTh g hg h hh N N' hN hN' c hc hcP h2 hLa Ξ hΦ hΞ1 hΞ2 κ E hκ P
  obtain ⟨hSBm, hThm⟩ := GlobalTheory.SplitMove.isThetaAt_move D ψ θ S T a b hS hT δ sc hP μ om hW e SS hE vac Φ w hV.2.theta hV.2.lat
    hSB hTh g hg h hh N N' hN hN'
  obtain ⟨hVm, -, -⟩ := GlobalTheory.MovedVac.vac_moved D ψ θ S T a b hS hT δ sc hP μ om hW vac hV g hg h hh N N' hN hN'
  have hD : IsHol θ S T ψ (om (g, h) w) ∧ xiN θ S T hS hT δ sc (om (g, h) w) =
      thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (xiN θ S T hS hT δ sc (om (g, h) vac)) := by
    exact GlobalTheory.T.datumReading_splitPlaces_eq_classicalTheta D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa (selfDual_latFr S hP.gS hS g N hN)
        (selfDual_latFr T hP.gT hT h N' hN') _ _ _ Ξ hVm hSBm hThm hΦ hΞ1 hΞ2
  obtain ⟨hHolm, hxi⟩ := hD
  have hHolw : IsHol θ S T ψ w := by
    have := (GlobalTheory.AdForm.FinComm.finite_comm_creation D ψ θ S T a b hS hT δ sc hP μ om hW g⁻¹ (inv_mem hg) h⁻¹ (inv_mem hh)
      _ hHolm).1
    rwa [om_inv_om] at this
  have hcomm := ((GlobalTheory.AdForm.FinComm.finite_comm_creation D ψ θ S T a b hS hT δ sc hP μ om hW g hg h hh w hHolw).2 P).2
  have hdiff : Differentiable ℂ fun z =>
      κ * thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E z := by
    rw [← thC_const_mul, ← hκ, ← hxi]
    exact (GlobalTheory.AdForm.VacRead.xiN_entire_and_injective D ψ θ S T a b hS hT δ sc hP).1 _ hHolm
  unfold thetaKO
  rw [hcomm, hs _ hHolm P, hxi, hκ, thC_const_mul]
  unfold jetP
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [GlobalTheory.ColNorms.jetC_const_mul _ _ _ hdiff]
  ring

end GlobalTheory.KJInf.CoreG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_commutation_value : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (commOf (pk W) u a.g).Is → ∀ t, ∃ J : QJ a t, J.ReadsLow := by
  first | exact @GlobalTheory.LowJoin.exists_readsLow | exact GlobalTheory.LowJoin.exists_readsLow | (intros; apply GlobalTheory.LowJoin.exists_readsLow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowStepRelationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_row_step_relation : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ t' (J' : QJ a t'), J'.Reads → ∀ (α' : J'.Ch j) (P : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p ∈ P, GlobalTheory.PenBridge.plF J p ∧ ¬ GlobalTheory.PenBridge.plF J' p) → ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ P), (∀ i, (J.G i).q.v ∈ P → GlobalTheory.PenBridge.rd J j hj x i ∈ KO (J.G i).k _) → x ∈ J'.A.U j (J'.ι j α') := by
  first | exact @GlobalTheory.PenBridge.supp_mem_level | exact GlobalTheory.PenBridge.supp_mem_level | (intros; apply GlobalTheory.PenBridge.supp_mem_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlacesGroupEqProductLocalGroupsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaces_group_eq_product_local_groups : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ P : (∀ i, GL ((F.Q i).X (j + 1) ⊕ Fin (2 * σ + 2)) (F.Q i).k) →* GA D (c.V (j + 1)), (∀ (H : Subgroup (GA D (c.V (j + 1)))) y, (∀ i, (F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i) ∈ H) → P y ∈ H) ∧ (∀ y, P y ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q)) ∧ ∀ x ∈ GlobalTheory.FinPl.grpAt _ (· ∈ w.Q), ∃ y, x = P y ∧ ∀ i, x * ((F.Q i).gl (j + 1) (2 * σ + 2) (by have := (F.Q i).hs; omega) (y i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V (j + 1)) (· = (F.Q i).q.v) := by
  first | exact @GlobalTheory.QProd.prod_local | exact GlobalTheory.QProd.prod_local | (intros; apply GlobalTheory.QProd.prod_local <;> assumption)
end

