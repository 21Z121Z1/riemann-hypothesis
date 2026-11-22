import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0353
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Formalism.LocalRingCardinality.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0461
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJacFramePairing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.JacFramePair

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pair_col (p : Place D k) {N ρ : ℕ} {κ : Type} [Fintype κ] (G : Matrix (Fin N) (Fin N) D.host.E)
    (X : Matrix (Fin N) κ D.host.E) (e : Matrix (Fin N) (Fin ρ) D.host.E) (j : κ) (i : Fin ρ) :
    ∑ r, p.pr (X r j) * p.pr (star ((G *ᵥ fun r => e r i) r)) = p.pr (star ((Xᴴ * G * e) j i)) := by
  have h : star ((Xᴴ * G * e) j i) = ∑ r, X r j * star ((G *ᵥ fun r => e r i) r) := by
    rw [Matrix.mul_assoc, Matrix.mul_apply, star_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hv : (G * e) r i = (G *ᵥ fun r => e r i) r := by simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [star_mul', Matrix.conjTranspose_apply, star_star, hv, mul_comm]
  rw [h]
  change _ = Witness.prH p _
  rw [map_sum]
  exact Finset.sum_congr rfl fun r _ => (map_mul (Witness.prH p) _ _).symm

theorem pair_scaled (p : Place D k) {N ρ : ℕ} {κ Z : Type} [Fintype κ] (G : Matrix (Fin N) (Fin N) D.host.E)
    (X : Matrix (Fin N) κ D.host.E) (e : Matrix (Fin N) (Fin ρ) D.host.E) (β : Matrix (Fin N) Z k) (m : Z) (j : κ)
    (t : k) (h : ∀ r, β r m = t * p.pr (X r j)) (i : Fin ρ) :
    ∑ r, β r m * p.pr (star ((G *ᵥ fun r => e r i) r)) = t * p.pr (star ((Xᴴ * G * e) j i)) := by
  simp_rw [h, mul_assoc, ← Finset.mul_sum, pair_col]

theorem pr_zero (p : Place D k) : p.pr 0 = 0 := map_zero (Witness.prH p)

theorem pr_one (p : Place D k) : p.pr 1 = 1 := map_one (Witness.prH p)

theorem pr_star_one (p : Place D k) {ρ : ℕ} (i' i : Fin ρ) :
    p.pr (star ((1 : Matrix (Fin ρ) (Fin ρ) D.host.E) i' i)) = if i' = i then 1 else 0 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp [pr_zero, pr_one]

theorem isJacFrame_pairing : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (ρ : ℕ) (J : JacLev D ρ) (s hh : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)),
    p.IsJacFrame J s hh F₀ F → valuation k s = 1 → valuation k hh = 1 → valuation k p.xi = 1 → ∀ i : Fin ρ,
    ∃ (b : k) (m₀ : n ⊕ Fin c), valuation k b = 1 ∧ (∀ r, b * p.pr (J.d.e r i) = F.β r m₀) ∧
      (∀ m, ∑ r, F.β r m * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) ∈ 𝒪[k]) ∧
      ∃ m, valuation k (∑ r, F.β r m * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r))) = 1 := by
  intro D k _ _ _ _ p ρ J s hh n _ _ c F₀ F hJ hs hhh hx i
  obtain ⟨hc, h1, h2, h3⟩ := hJ
  subst hc
  have vt : ∀ l : ℕ, valuation k (s * (hh / p.xi) * (-1 / p.xi) ^ l) = 1 := fun l => by
    simp [map_mul, map_div₀, map_pow, Valuation.map_neg, hs, hhh, hx]
  have inrLo : ∀ (j : Fin (2 * ρ)) (hj : j.val < ρ),
      ∑ r, F.β r (Sum.inr j) * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) = 0 := fun j hj => by
    rw [pair_scaled p J.W.gram J.d.e J.d.e F.β (Sum.inr j) (⟨j.val, hj⟩ : Fin ρ) _ (h2 ⟨j.val, hj⟩ j rfl), J.d.ee]
    simp [pr_zero]
  have inrHi : ∀ (j : Fin (2 * ρ)) (hj : ρ ≤ j.val),
      ∑ r, F.β r (Sum.inr j) * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) =
        s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - 1 - j.val)) *
          (if (⟨2 * ρ - 1 - j.val, by omega⟩ : Fin ρ) = i then 1 else 0) := fun j hj => by
    rw [pair_scaled p J.W.gram J.d.e' J.d.e F.β (Sum.inr j) (⟨2 * ρ - 1 - j.val, by omega⟩ : Fin ρ) _
      (h3 ⟨2 * ρ - 1 - j.val, by omega⟩ j (by simp only; omega)), J.d.e'e, pr_star_one]
  refine ⟨s * p.xi ^ (ρ - i.val), Sum.inr ⟨i.val, by omega⟩, by simp [map_mul, map_pow, hs, hx],
    fun r => (h2 i _ rfl r).symm, ?_, Sum.inr ⟨2 * ρ - 1 - i.val, by omega⟩, ?_⟩
  · rintro (a | j)
    · have e0 : ∑ r, F.β r (Sum.inl a) * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) = 0 := by
        simp_rw [h1, Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun b _ => ?_
        have := pair_col p J.W.gram J.d.i₀ J.d.e b i
        rw [J.d.i₀e, Matrix.zero_apply, star_zero, pr_zero] at this
        calc ∑ r, p.pr (J.d.i₀ r b) * F₀.β b a * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r))
            = F₀.β b a * ∑ r, p.pr (J.d.i₀ r b) * p.pr (star ((J.W.gram *ᵥ fun r => J.d.e r i) r)) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
          _ = 0 := by rw [this, mul_zero]
      rw [e0]
      exact zero_mem _
    · by_cases hj : j.val < ρ
      · rw [inrLo j hj]
        exact zero_mem _
      · rw [inrHi j (by omega), Valuation.mem_integer_iff, map_mul, vt, one_mul]
        split_ifs <;> simp
  · rw [inrHi _ (by simp only; omega), map_mul, vt, one_mul, if_pos (Fin.ext (by simp only; omega)), map_one]

end GlobalTheory.JacFramePair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsKFinOfMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.CommIs

open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt GlobalTheory.Core.Mi

theorem isKFin_of_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {x : M.H τ}
    (hx : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) : Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) x := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ v hv => by
      rw [(Submodule.mem_bot _).1 hv, map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    obtain ⟨S₂, k1, k2, k3⟩ := hy
    refine ⟨S₁ ⊔ S₂, inferInstance, Submodule.add_mem_sup h2 k2, fun g hg v hv => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (h3 g hg a ha) (k3 g hg b hb)
  | smul c x _ hx =>
    obtain ⟨S₁, h1, h2, h3⟩ := hx
    exact ⟨S₁, h1, S₁.smul_mem c h2, h3⟩

theorem itSpans_of (hDS : GlobalTheory.Published.DiscreteSeriesCover) (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V W : HSp D}
    {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
    (aS aT : D.what₂.Tau → ℚ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ)
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hθ : IsInfFam θ) (hw : IsWeilExp ψ V W aS aT ω)
    (hv : IsVacVec ψ θ M M' f) (hi : IsItW θ M M' ω (ptOf ψ θ M M' f) It) : GlobalTheory.Core.Mi.ItSpans M M' It := by
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D V W S S' M M' θ ψ aS aT ω f It hθ hw hv hi
  intro v hv
  have hv' := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv τ), rfl⟩)
  refine (Submodule.span_le.2 ?_) hv'
  rintro w ⟨P, u, hu, rfl⟩
  have hu' : u ∈ Submodule.comap (It P) (Submodule.span ℂ
      {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), GlobalTheory.Core.Mi.KVecP M' y ∧ x = It P (PiTensorProduct.tprod ℂ y)}) := by
    refine (Submodule.span_le.2 ?_) hu
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨P, y, fun τ => isKFin_of_mem _ _ (hy τ), rfl⟩
  exact hu'

end GlobalTheory.Fam.CommIs

open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt in

theorem GlobalTheory.Fam.commOf_is : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ g : GlobalTheory.Fam.Geo D, GeoMeas (pk W) g → (∀ j, j ≤ D.R.m → (g.x j).Is) → (commOf (pk W) u g).Is := by
  intro hDS hHC D L hT Gi Gl Kc Yd cX ex W u hp g hm hx
  have hC : W.Q.Rl.Char3 W.Q.F := hp.bot.hyp.2.2.2.1
  have hS : StepsOK (pk W) := GlobalTheory.Chain.StepVac.stepsOK _ _ _ _ _ _ (pk W) hC.lev hC.models.inf hC.chain.ωY hC.chain.ωX
    hC.chain.vY hC.chain.vX
  have hθ : IsInfFam (pk W).θ := hC.models.inf
  have hm1 : D.R.m - 1 < D.R.m := Nat.sub_lt (lt_of_lt_of_le two_pos D.R.two_le_m) one_pos
  have hY : ∀ j, j + 1 < D.R.m → GlobalTheory.Core.Mi.ItSpans ((pk W).MY j) ((pk W).MY (j + 1)) ((pk W).ItY j) := by
    intro j hj
    have h := hS.1 W.P.A3.A.μ0 ⟨j, by omega⟩ hj
    obtain ⟨χS, χT, hω, he⟩ := h.1
    exact GlobalTheory.Fam.CommIs.itSpans_of hDS hHC _ _ _ _ _ _ _ _ _ hθ ⟨χS, χT, hω, he⟩ h.2 (hC.chain.ItY W.P.A3.A.μ0 j hj)
  have hX : GlobalTheory.Core.Mi.ItSpans ((pk W).MY (D.R.m - 1)) (pk W).MX (pk W).ItX := by
    have h := hS.2 W.P.A3.A.μ0 ⟨D.R.m - 1, hm1⟩ rfl
    obtain ⟨χS, χT, hω, he⟩ := h.1
    exact GlobalTheory.Fam.CommIs.itSpans_of hDS hHC _ _ _ _ _ _ _ _ _ hθ ⟨χS, χT, hω, he⟩ h.2 (hC.chain.ItX W.P.A3.A.μ0)
  have hXc : ∀ n (e : D.R.m - 1 = n), GlobalTheory.Core.Mi.ItSpans ((pk W).MY n) (pk W).MX
      (Eq.rec (motive := fun n _ => PolF D D.sp.X'.rank (Yc D n).rank →ₗ[ℂ] SmT (pk W).MX →ₗ[ℂ] SmT ((pk W).MY n))
        (pk W).ItX e) := by
    intro n e
    subst e
    exact hX
  refine ⟨W.Q.stdChar, hθ, hx, GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite D.sp.X'_sig fun τ => Or.inl (D.X'_posDef τ), hm.μf, hm.ρJ,
    hm.ρB, fun j hj => hY j hj, fun j h => hXc (j + 1) (idx_top h)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTypePlacesOfLevCh
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.ComCols

variable {D : D7}

theorem isTypePlaces_of_levCh {L : LevCh D Unit} (hL : L.Is ()) : GlobalTheory.Core.Mi.IsTypePlaces L.Pg := by
  classical
  refine ⟨fun PP hPP => ?_, fun v hv => ?_⟩
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := L.C.P.overP hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h1
    · exact Ideal.mul_mem_left _ _ h1
  · have := v.isMaximal
    obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    let W : Formalism.L2.DIV.Pl D.host.E := ⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
    have hW : W.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQ'.over.symm
    have hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal := by
      rw [← hW] at hv
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ W.asIdeal := hv
      rw [map_natCast, Nat.cast_mul] at h2
      exact (W.isPrime.mem_or_mem h2).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    have hS := GlobalTheory.ChainOnto.Model.mem_S hL (GlobalTheory.Member.exists_isInfFam_family D).choose 1 L.triv k W hk
    unfold GlobalTheory.ChainOnto.Com.S at hS
    obtain ⟨P, hP, e⟩ := Finset.mem_image.1 hS
    refine ⟨P, ⟨hP, e.trans hW⟩, ?_⟩
    rintro P' ⟨hP', e'⟩
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (e'.trans (e.trans hW).symm) with h | h
    · exact h
    · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 h) (GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hP) (Or.inl hP'))

theorem com_is_of_levCh {L : LevCh D Unit} (hL : L.Is ()) (c : GlobalTheory.ChainOnto.Com D) (hθ : IsInfFam c.θ) (hψ : IsStdChar D c.ψ (-1))
    (hP : c.Pg = L.Pg) (hμ : ∀ j : Fin D.R.m, ChrEq (c.μ ((j : ℕ) + 1)) (L.C.mu0 j)) (hη : ChrEq c.η L.C.eta)
    (hχ : ∀ j : Fin D.R.m, ∀ PP ∈ c.Pg, IsRes (L.C.mu0 j) PP (c.chi ((j : ℕ) + 1) PP)⁻¹) : c.Is := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D c.η L.C.eta hη L.C.isEta
  have hS : ∀ (k : Fin 2) (Q : Formalism.L2.DIV.Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      Q.under (𝓞 D.host.F) ∈ c.S := fun k Q hk => by
    have := GlobalTheory.ChainOnto.Model.mem_S hL c.θ c.ψ L.triv k Q hk
    unfold GlobalTheory.ChainOnto.Com.S at this ⊢
    rw [hP]
    exact this
  refine ⟨hθ, hψ, ⟨hη.1, GlobalTheory.Mem.TupChar.unramEverywhere hη L.C.isEta.unr, ⟨⟨_, hres⟩, fun η h a => ?_⟩, fun τ => ?_,
    fun j hj => ?_⟩, fun j τ => ?_, fun j w hw => ?_, fun j => ⟨_, hμ j, hχ j⟩, ?_⟩
  · rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h hres, pow_one, MonoidHom.comp_apply]
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hη
      (GlobalTheory.InnerSteps.hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hi : i < D.R.m := by omega
    refine ⟨(hμ ⟨i, hi⟩).1, ⟨_, hres⟩, fun η _ a => ?_⟩
    show c.μ (i + 1) (idF D a) = _
    rw [pow_zero]
    exact GlobalTheory.GridWeil.triv_base (hμ ⟨i, hi⟩) (L.C.isMu0 ⟨i, hi⟩).triv a
  · have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hμ j) (GlobalTheory.InnerSteps.hasInfQ_tauE (L.C.isMu0 j).inf) τ
    simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
    exact h1
  · exact (GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ j) w).2 ((L.C.isMu0 j).unr w fun k hk => hw (hS k w hk))
  · rw [hP]
    exact GlobalTheory.CentralShift.exists_idemSum _ fun Q hQ Q' hQ' => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hQ) (Or.inl hQ')

end GlobalTheory.SeeSaw.ComCols
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JoinSubspaceRealDataExists
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Mem.SJ

namespace GlobalTheory.Mem.KJoinLat

theorem exists_read_of_latTie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → ∀ (S0 : IndefData (A3.side3 F.P0 F.ψ0 (R.toCx3 F).zs)) (p0 : BaseLevelRowSide D) (Sp : SPer (F.Dc (R.toCx3 F).zs)) (C : ColData (F.Dc (R.toCx3 F).zs) Sp ((R.toCx3 F).data F.cr true)) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin ((F.Dc (R.toCx3 F).zs).a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 (F.Dc (R.toCx3 F).zs)), DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → ∃ Rd : Read D (R.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0), HEq Rd.wU I.wU ∧ HEq Rd.eNu I.eNu ∧ HEq Rd.eRR I.eRR ∧ (∀ y, HEq (Rd.jV y) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) ∧ Rd.ReadingFormsSpanGoodSubspace ∧ Rd.IotaRd F.cr ∧ Rd.NuTie ∧ (HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (A3.indefDown ((R.toCx3 F).data F.cr true)).RR (A3.indefDown ((R.toCx3 F).data F.cr true)).XE I.eRR → Rd.RRTie F.cr) ∧ ((∀ (u : D.what₂.Word) (x : Fin ((F.Dc (R.toCx3 F).zs).a (I.wU u)) → D.what₂.LL) (y : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV A3.A.μ0) → D.what₂.LL), D.what₂.embLL ((F.Dc (R.toCx3 F).zs).Pt (I.wU u) A3.A.μ0 x y) = D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) → Rd.DcPt) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F n hOk S0 p0 Sp C NuC I h
  obtain ⟨Rd, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    exists_read_of_matrix_tie D (R.toCx3 F) F.fc F.cr (I.tup A3.A.μ0) h.tup.mu0 h.tup.v0 (I.jA A3.A.μ0)
      (rH D A3.A F.P1 F.ψ1 A3.A.μ0) (rE D A3.A F.P1 F.ψ1 A3.A.μ0) (rV0 D A3.A F.P1 F.ψ1 A3.A.μ0) I.wU I.eNu I.eRR
      (h.sharp.forms A3.A.μ0) (GlobalTheory.range_goodProjector_eq_range_goodCoordinates D A3.A n hOk.ok2 F.P1 F.ψ1 A3.A.μ0) (h.sharp.iota A3.A.μ0)
      (fun u => ⟨_, h.cols.Nu u⟩)
  exact ⟨Rd, h1, h2, h3, h4, h5, h6, h7, fun hR => h8 ⟨_, hR⟩, h9⟩

theorem kernelJoin_thetaSurjective_goodPart_latticeCondition : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → SchurAll D → (D.sp.Y 0).SigOK → ∀ (S0 : IndefData (A3.side3 F.P0 F.ψ0 (R.toCx3 F).zs)) (p0 : BaseLevelRowSide D) (C : ColData (F.Dc (R.toCx3 F).zs) (F.Sp (R.toCx3 F).zs) ((R.toCx3 F).data F.cr true)) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin ((F.Dc (R.toCx3 F).zs).a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 (F.Dc (R.toCx3 F).zs)), DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (A3.indefDown ((R.toCx3 F).data F.cr true)).RR (A3.indefDown ((R.toCx3 F).data F.cr true)).XE I.eRR → (∀ (u : D.what₂.Word) (x : Fin ((F.Dc (R.toCx3 F).zs).a (I.wU u)) → D.what₂.LL) (y : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV A3.A.μ0) → D.what₂.LL), D.what₂.embLL ((F.Dc (R.toCx3 F).zs).Pt (I.wU u) A3.A.μ0 x y) = D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) → ∃ (Rd : Read D (R.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0)) (M : Seam Rd F.cr), HEq Rd.wU I.wU ∧ M.ChainTie ∧ M.GoodPartHasComplexCoordinates ∧ M.RowTie (F.eV (R.toCx3 F).zs) ∧ M.ColNorm ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ ∧ ∀ (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (F.Dc (R.toCx3 F).zs).Mem → D.what₂.Word) (bR : ∀ x, Fin ((F.Dc (R.toCx3 F).zs).a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (I.wU u) = u) → F.Sp (R.toCx3 F).zs = spOf (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (I.wU u) i) (D.eMu u (D.jN u (I.eNu u (Pi.single i 1))))) → ∀ (t : GA D (D.sp.Y 0)) (c : ℝ), EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c → ∀ (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ), HEq sEE sEEc → κS ≠ 0 → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c ⟨R.HE.e (Tw.out x), hx⟩)) → ∀ (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, eE (D.jEE (I.eRR y)) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y))) → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St Gd) (v₀ : (R.MY 0).Vec) (a : ℂ), (∀ x, ((j x : EEC St Gd) : L2X St) =ᵐ[muX St] fun g => a * ev (R.MY 0) v₀ (R.HE.e (eE x)) ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm g * t)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (x : D.what₂.EE) (φ : D.what₂.Mu u) (T' : Cu St u hK), colDictL St (pw u).Tr hK T' = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR x), (F.fc (R.toCx3 F).zs).Sp.Pu (Rd.wU u) (cjv (twAt D.what₂.embLL A3.A.v0) (M.cφ u φ))⟫_ℂ = cj (twAt D.what₂.embLL A3.A.v0) (κ * ⟪((conjHH St Gd (j x) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T'⟫_ℂ) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F n hOk hSep hCW hPR hSchur hSig S0 p0 C NuC I hDef hLat hPer
  obtain ⟨Rd, hwU, heNu, heRR, hjV, hV0, hIota, hNu, hRR, hDc⟩ :=
    exists_read_of_latTie D G Pl0 I0 T A3 Ks R F n hOk S0 p0 _ C NuC I hDef
  obtain ⟨M⟩ := seam_nonempty D _ _ _ _ _ Rd F.cr
  have hCx := cxFacts_of_prims D G Pl0 I0 T A3 Ks R F n hOk hSep hCW hPR
  have hRow := rows_eq_rows_level D _ _ _ _ _ Rd F.cr M _ hCx (hRR hLat)
  have hCV := chainTie_and_v0Onto D _ _ _ _ _ Rd F.cr M
  refine ⟨Rd, M, hwU, hCV.1 (hDc hPer), hCV.2 hV0,
    ⟨hRow.1, hRow.2.1, ⟨_, Real.sqrt_pos.2 (hCx.pos.2.2 true), hRow.2.2⟩, 1, one_ne_zero, fun y => by
      rw [one_smul]; exact RowB.theta_eq D _ _ _ _ _ Rd F.cr M _ hCx hIota y⟩,
    colNorm_of_nuTie D _ _ _ _ _ Rd F.cr M hNu, thetaMap_referenceTuple_goodPart_onto_rows D _ _ _ _ _ Rd F.cr _ hCx hIota hV0, ?_⟩
  intro St h Gd hK pw wdD bR hwd hSp hbR t c hEv sEE sEEc κS hS hκS hsEEc eE heE j v₀ a hj u
  have hwUe : Rd.wU = I.wU := eq_of_heq hwU
  have heRRe : Rd.eRR = I.eRR := eq_of_heq heRR
  have hME : ∀ x, M.eR x = Tw.mkL (twAt D.what₂.embLL A3.A.v0) R.HE.H (eE x) := by
    have hsp : Submodule.span ℂ (Set.range fun i => D.jEE (D.div.RR.b i)) = ⊤ := D.jEE_basis.2
    have hext := LinearMap.ext_on_range hsp (f := M.eR)
      (g := (Tw.mkL (twAt D.what₂.embLL A3.A.v0) R.HE.H).comp eE) (fun i => ?_)
    · exact fun x => LinearMap.congr_fun hext x
    · obtain ⟨y, hy⟩ := Rd.eRR.surjective (D.div.RR.b i)
      have h1 := heE y
      rw [← heRRe] at h1
      rw [← hy, M.eR_eq y]
      exact (congrArg (Tw.mkL (twAt D.what₂.embLL A3.A.v0) R.HE.H) h1).symm
  have hmem : ∀ x, R.HE.e (eE x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) := fun x => by
    have h1 := hRow.1 x
    rw [hME x] at h1
    exact h1
  let e : D.what₂.EE →ₗ[ℂ] R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) :=
    LinearMap.codRestrict _ (R.HE.e ∘ₗ eE) hmem
  have hSch := SchurMove.schur_iotaX D _ (R.MY 0) (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St h R.θ _ _ t
    hSchur hSig hCW.base.models.inf (goodPart_le _ _ _ _ _)
  obtain ⟨κ₀, hκ₀, hκe⟩ := sEEofTT_eq_smul_conjHH D _ (R.MY 0) _ St Gd R.ν0 R.fd0
    (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c hSch hEv e j v₀ a hj
  have hkey : ∀ x, (sEEc (M.eR x)).out = (κS * κ₀) • conjHH St Gd (j x) := fun x => by
    have hx : R.HE.e (Tw.out (M.eR x)) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) :=
      (congrArg (fun z => R.HE.e (Tw.out z) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) (hME x)).mpr (hmem x)
    have h2 : (⟨R.HE.e (Tw.out (M.eR x)), hx⟩ : R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) = e x :=
      Subtype.ext (congrArg (fun z => R.HE.e (Tw.out z)) (hME x))
    exact (congrArg Tw.out (hsEEc (M.eR x) hx)).trans
      (GlobalTheory.Mem.SJ.KernelJoin.smul_apply_eq_of_eq _ h2 κS κ₀ (hκe x))
  have hwd' : ∀ u, wdD (Rd.wU u) = u := fun u => (congrArg wdD (congrFun hwUe u)).trans (hwd u)
  have hbR' := GlobalTheory.Mem.SJ.KernelJoin.heq_of_reindex _ bR (fun u v => D.eMu u (D.jN u v)) Rd.wU I.wU Rd.eNu I.eNu
    hwUe heNu hbR
  exact GlobalTheory.Mem.SJ.PairMain.pair_step D _ _ _ _ _ Rd F.cr M St Gd hK pw wdD bR hwd' hSp hbR' sEE sEEc hS j (κS * κ₀)
    (mul_ne_zero hκS hκ₀) hkey u

section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
  {R : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem core_latTie {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    (Rl : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ) (hOk : A3.fam3.Ok3 n) (hSep : A3.fam3.TypesSep3)
    (hCh : Rl.WeakCharacterisation F) (hPrim : PrimRows3 Rl F) (hSchur : SchurAll D) (hSig : (D.sp.Y 0).SigOK)
    (Zs : DefSub A3.fam3.amb3) (hzs : (Rl.toCx3 F).zs = Zs)
    (S0 : IndefData (A3.side3 F.P0 F.ψ0 Zs)) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs))
    (hs1 : HEq ((Rl.toCx3 F).data F.cr true) S1)
    (Dc : DefCols (A3.side3 F.P1 F.ψ1 Zs)) (hdc : F.Dc Zs = Dc) (Sp : SPer Dc) (hsp : HEq (F.Sp Zs) Sp)
    (p0 : BaseLevelRowSide D) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 Dc)
    (hDef : DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 C NuC I)
    (hLat : HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (A3.indefDown S1).RR (A3.indefDown S1).XE I.eRR)
    (hPt : ∀ (u : D.what₂.Word) (x : Fin (Dc.a (I.wU u)) → D.what₂.LL)
      (y : Fin ((A3.side3 F.P1 F.ψ1 Zs).nV A3.A.μ0) → D.what₂.LL),
      D.what₂.embLL (Dc.Pt (I.wU u) A3.A.μ0 x y) =
        D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y)))
    (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter)
    (pw : ∀ u, PerW St hK u) (wdD : Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)
    (hwdD : ∀ u, wdD (I.wU u) = u)
    (hSp : HEq Sp (spOf (twAt D.what₂.embLL A3.A.v0) Dc hK Gd wdD (fun x => pw (wdD x)) bR))
    (hbR : ∀ u i, HEq (bR (I.wU u) i) (D.eMu u (D.jN u (I.eNu u (Pi.single i 1)))))
    (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hEv : EvalTieT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true)) St Gd
      (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c)
    (sEE : (Rl.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (Rl.toCx3 F).zs).Sp.HH)
    (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) Rl.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ)
    (hsE : HEq sEE sEEc) (hκ : κS ≠ 0)
    (hsee : ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) Rl.HE.H)
      (hx : Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true))),
      sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (Rl.MY 0) Rl.ν0 Rl.fd0
        (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c
        ⟨Rl.HE.e (Tw.out x), hx⟩))
    (eE : D.what₂.EE →ₗ[ℂ] Rl.HE.H)
    (hRead : ∀ y y', HEq y y' → eE (D.jEE (I.eRR y)) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := Rl.HE.H)
      ((Rl.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y'))) :
    ∃ (Rd : GlobalTheory.Mem.SJ.Read D (Rl.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0)) (M : GlobalTheory.Mem.SJ.Seam Rd F.cr),
      HEq Rd.wU I.wU ∧ M.ChainTie ∧ M.GoodPartHasComplexCoordinates ∧ M.RowTie (F.eV (Rl.toCx3 F).zs) ∧ M.ColNorm ∧
      (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ ∧
      ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St Gd) (v₀ : (Rl.MY 0).Vec) (a : ℂ),
        (∀ x, ((j x : EEC St Gd) : L2X St) =ᵐ[muX St]
          fun g => a * ev (Rl.MY 0) v₀ (Rl.HE.e (eE x)) ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm g * t)) →
        ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (x : D.what₂.EE) (φ : D.what₂.Mu u) (T' : Cu St u hK),
          colDictL St (pw u).Tr hK T' = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) →
          ⟪sEE (M.eR x), (F.fc (Rl.toCx3 F).zs).Sp.Pu (Rd.wU u)
              (GlobalTheory.Mem.SJ.cjv (twAt D.what₂.embLL A3.A.v0) (M.cφ u φ))⟫_ℂ =
            cj (twAt D.what₂.embLL A3.A.v0) (κ * ⟪((conjHH St Gd (j x) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T'⟫_ℂ) := by
  subst hzs
  subst hdc
  obtain rfl := eq_of_heq hs1
  obtain rfl := eq_of_heq hsp
  obtain ⟨Rd, M, hw, h1, h2, h3, h4, hon, hT⟩ :=
    kernelJoin_thetaSurjective_goodPart_latticeCondition D G Pl0 I0 T A3 Ks Rl F n hOk hSep hCh hPrim hSchur hSig S0 p0 C NuC I hDef hLat hPt
  exact ⟨Rd, M, hw, h1, h2, h3, h4, hon, fun j v₀ a hj => hT St h Gd hK pw wdD bR hwdD (eq_of_heq hSp) hbR t c hEv
    sEE sEEc κS hsE hκ hsee eE (fun y => hRead y y HEq.rfl) j v₀ a hj⟩

theorem join_subspace_lattice_condition (Q : RealT R P Dcf Spf Zscf S Ks) (hPin : RealPins Q) (hSee : SeeEx Q) (n : ℕ)
    (hOk : P.A3.fam3.Ok3 n) (hSep : P.A3.fam3.TypesSep3) (hPrim : PrimRows3 Q.Rl Q.F)
    (hLat : HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (P.A3.indefDown P.S1).RR (P.A3.indefDown P.S1).XE P.I.eRR)
    (hDc : RowsHoldDcPt3 P) (hSchur : SchurAll D) (hSig : (D.sp.Y 0).SigOK) (hJ : GlobalTheory.Mem.JTop.JoinPin Q) :
    Nonempty (Formalism.L2.SG.JoinSI.JoinSI R S Q) ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  obtain ⟨eE, hRead, hRow⟩ := hJ
  have hι : Q.ιS = (Formalism.L2.SG.RowsJoinPinned.iotaX S.X S.inst).toMulEquiv :=
    (GlobalTheory.Mem.JIota.heq_iota_iff D S.X S.inst Q.ιS).1 Q.ιS_eq
  have hEv := Q.seeEval (by obtain ⟨-, c', hc'⟩ := hSee; exact ⟨c', hc'⟩)
  rw [hι] at hEv
  have hκ : Q.uS * (Q.κS : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · intro h0
      have := Q.uS_norm
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    · exact_mod_cast Q.seeK.1.ne'
  obtain ⟨Rd, M, hw, h1, h2, h3, h4, hon, hT⟩ :=
    core_latTie Q.Rl Q.F n hOk hSep Q.charW hPrim hSchur hSig P.Zs Q.zs P.S0 P.S1 Q.s1 P.Dc Q.dc P.Sp Q.sp ex.p0 P.C P.NuC
      P.I P.tied.div hLat (fun u x y => hDc u P.A3.A.μ0 x y) S.X S.inst S.G S.Y.hK (pwOf S Q.hin) Q.wdD Q.bR Q.wdD_wU
      Q.spPin (GlobalTheory.Mem.JTop.bR_heq Q hPin) Q.tS Q.cS hEv Q.sEE Q.sEEc _ Q.sEEj hκ
      (fun x hx => (Q.seeDef x hx).trans (by rw [hι])) eE hRead
  refine ⟨⟨⟨Rd.wU, hw, M.cφ, M.cF, M.eR, h1, h2, h3, h4, fun hF => ?_⟩⟩, hon⟩
  obtain ⟨v₀, -, a, -, hj⟩ := hRow hF
  exact hT (Formalism.L2.SG.JoinSI.jOf S hF) v₀ a hj

end

theorem join_subspace_real_data_lattice : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : Formalism.L2.RecT ex) (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (y : RealIn x Rc (S.toSTiesR Rc)) (c : ℝ), ∀ n : ℕ, SchurAll D → RealPins (realTOf y) → Holds x.R x.F → x.A3.fam3.Ok3 n → x.A3.fam3.TypesSep3 → HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).RR (x.A3.indefDown (divisionPairOfAdelicFormsFaceColumnsData x).S1).XE (divisionPairOfAdelicFormsFaceColumnsData x).I.eRR → RowsHoldDcPt3 (divisionPairOfAdelicFormsFaceColumnsData x) → SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS → EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G (iotaX P.X P.inst).toMulEquiv y.tS c → RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j → Nonempty (Formalism.L2.SG.JoinSI.JoinSI Rc (S.toSTiesR Rc) (realTOf y)) ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D L hT Gi Gl K Yd cX ex x Rc P S y c n hSchur hPins hH hOk hSep hLat hDc hSee hEv hRow
  obtain ⟨hSx, hJ⟩ := GlobalTheory.Mem.JPin.seeEx_joinPin D L hT Gi Gl K Yd cX ex x Rc P S y c hH hSee hEv hRow
  exact join_subspace_lattice_condition (realTOf y) hPins hSx n hOk hSep (Holds.prim hH) hLat hDc hSchur (D.sp.Y_sig 0) hJ

end GlobalTheory.Mem.KJoinLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LamEqOfRed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZero

theorem lam_eq_of_red : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt G.q.e PP → ∀ (x : G.S.P.J) (g : GL (Fin D.R.r) (kP PP)), GlobalTheory.LevZero.Red G PP x g → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = edgeSum (GlobalTheory.chainEdge D.R.k) g → ((G.S.P.lam x : ℂˣ) : ℂ) = (G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (ofSplit G.q).pr (z : D.host.E)) : ℂ) := by
  intro D c v G PP _ x g hx z hz
  have hadd : ∀ a b : D.host.E, (ofSplit G.q).pr (a + b) = (ofSplit G.q).pr a + (ofSplit G.q).pr b := by
    intro a b
    simp only [GlobalTheory.LocMod.Place.pr, map_add]
  have hr : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  exact GlobalTheory.ChainChar.char_of_red PP.asIdeal
    (AddMonoidHom.mk' (fun y : 𝓞 D.host.E => (ofSplit G.q).pr (y : D.host.E))
      fun a b => by rw [← hadd]; rfl) hr G.S x g hx z hz

end GlobalTheory.LevZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSpaceMovedLevelClassPointsRepresentativesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_space_moved_level_class_points_representatives : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → IsReps (I.rec7 l Z).sp.X' UT h ∧ ∀ c, stabOrd UT (h c) = Nat.card ((I.fm l u a).stabilizer₂ c) := by
  first | exact @GlobalTheory.ClassPtReps.isReps_stabOrd_top | exact GlobalTheory.ClassPtReps.isReps_stabOrd_top | (intros; apply GlobalTheory.ClassPtReps.isReps_stabOrd_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCombinationsComposeFinitelyManyPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCombinations_compose_finitely_many_places : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ i, P (L i).q.v) → ∃ o' : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt P o' ∧ ∀ F, comb ψ S T o' F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F := by
  first | exact @GlobalTheory.LocComp.main | exact GlobalTheory.LocComp.main | (intros; apply GlobalTheory.LocComp.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantRationalFinitePartsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedVacuum_invariant_rationalFiniteParts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∀ c₀ g h, g ∈ GfC _ → h ∈ GfC _ → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (g) (h) → ∀ r r', IsRatFin _ r → IsRatFin _ r' → GlobalTheory.AdForm.VacAll.MoveT I l Z θ i hi c₀ μ om vac (r * g) (r' * h) := by
  first | exact @GlobalTheory.AdForm.VacAllRat.moveT_rat | exact GlobalTheory.AdForm.VacAllRat.moveT_rat | (intros; apply GlobalTheory.AdForm.VacAllRat.moveT_rat <;> assumption)
end

