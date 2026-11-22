import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsPairMass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumReads
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesAtOfMovesAtOpenSet
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem movesAt_of_movesAt_open : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' k'' : (uAt r v i).Comp) (a c : GL (Fin D.R.r) D.host.E) (hma : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (hmc : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k'') c) (W : Set (Frame ((uAt r v i).X k).Ψ D.R.r)), IsOpen W → W.Nonempty → W ⊆ ((uAt r v i).X k).dom → (∀ (z : Frame ((uAt r v i).X k).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k).dom), z ∈ W → MovesAt p r i v γ k k' a hma z hz ∧ MovesAt p r i v γ k k'' c hmc z hz) → ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k'' c hmc x hx → MovesAt p r i v γ k k' a hma x hx := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v γ k k' k'' a c hma hmc W hWo hWn hWd hW x hx hcx
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hU : IsUnf (uAt r v i) := (h.laws v).p.toLawsCore.unf _ hj _ (r.used v).full.toCore.good_σ₀
  obtain ⟨-, htr, hsy, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid D.host.E _ _ _
    ((r.used v).full.Q.Xo ((i : ℕ) + 1)) (r.used v).full.Q.c (CAt (r.used v).full.σ₀)

  have step : ∀ z (hz : z ∈ ((uAt r v i).X k).dom), z ∈ W →
      ∃ γ' ∈ ((uAt r v i).X k').Γ, ∃ b ∈ Bor ((uAt r v i).X k').Ψ D.R.r,
        (⟨k'', castFrame hmc.psi (lact c z)⟩ : Σ k, Frame ((uAt r v i).X k).Ψ D.R.r) =
          ⟨k', rmul (lact γ' (castFrame hma.psi (lact a z))) b⟩ := by
    intro z hz hzW
    obtain ⟨⟨hy₁, t₁, f₁⟩, ⟨hy₂, t₂, f₂⟩⟩ := hW z hz hzW
    have hb := htr _ _ _ _ _ f₁ (hsy _ _ _ f₂)
    exact (hU.2.2.2.1 k' k'' ⟨_, hy₁⟩ ⟨_, hy₂⟩).1 ⟨_, hb⟩
  obtain ⟨z₀, hz₀⟩ := hWn
  have hk : k'' = k' := by
    obtain ⟨g₀, -, b₀, -, e₀⟩ := step z₀ (hWd hz₀) hz₀
    exact (Sigma.mk.inj_iff.1 e₀).1
  subst hk
  have hcast : ∀ z (b : Frame ((uAt r v i).X k'').Ψ D.R.r) (γ' : GL (Fin D.R.r) D.host.E),
      castFrame hmc.psi (lact c z) = rmul (lact γ' (castFrame hma.psi (lact a z))) b →
      lact c z = rmul (lact γ' (lact a z)) (castFrame hma.psi.symm b) := by
    intro z b γ' e
    funext τ
    have := congrFun e ⟨τ.1, hma.psi ▸ τ.2⟩
    exact this
  have hborc : ∀ b ∈ Bor ((uAt r v i).X k'').Ψ D.R.r, castFrame hma.psi.symm b ∈ Bor ((uAt r v i).X k).Ψ D.R.r := by
    intro b hb τ
    exact hb ⟨τ.1, hma.psi ▸ τ.2⟩
  obtain ⟨γ', hγ', V, hVo, hVn, hVd, hV⟩ := GlobalTheory.T.exists_candidate_borel_move_open_frames_baire ((uAt r v i).X k) ((uAt r v i).X k'').Γ a c W hWo ⟨z₀, hz₀⟩ hWd
    (fun z hz => by
      obtain ⟨γ', hγ', b, hb, e⟩ := step z (hWd hz) hz
      exact ⟨γ', hγ', _, hborc b hb, hcast z b γ' (eq_of_heq (Sigma.mk.inj_iff.1 e).2)⟩)
  obtain ⟨s, hs⟩ := GlobalTheory.T.scalar_of_borel_moves_open_frames ((uAt r v i).X k) _ V hVo hVn hVd hV
  set m : GL (Fin D.R.r) D.host.E := (γ' * a)⁻¹ * c with hm_def
  have hcm : (c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) =
      (γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) * (a : Matrix _ _ _) * (m : Matrix _ _ _) := by
    have : c = γ' * a * m := by rw [hm_def]; group
    rw [this]; simp [Units.val_mul]
  obtain ⟨hy₂, t₂, f₂⟩ := hcx
  have hy₁ : castFrame hma.psi (lact a x) ∈ ((uAt r v i).X k'').dom := hma.mem_dom hx
  let bm : Frame ((uAt r v i).X k'').Ψ D.R.r := fun τ => (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1
  have hbm : bm ∈ Bor ((uAt r v i).X k'').Ψ D.R.r := by
    intro τ
    refine ⟨?_, fun p q hpq => ?_⟩
    · show ((m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1).det ≠ 0
      rw [show (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = τ.1.mapMatrix (m : Matrix _ _ _) from rfl,
        ← RingHom.map_det]
      have hu : IsUnit (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det :=
        (Matrix.isUnit_iff_isUnit_det _).1 m.isUnit
      exact (map_ne_zero τ.1).2 hu.ne_zero
    · show (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 p q = 0
      rw [hs, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (ne_of_lt hpq).symm, map_zero]
  have heq : castFrame hmc.psi (lact c x) = rmul (lact γ' (castFrame hma.psi (lact a x))) bm := by
    funext τ
    show (c : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * mat x ⟨τ.1, _⟩ =
      ((γ' : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 * ((a : Matrix _ _ _).map τ.1 * mat x ⟨τ.1, _⟩)) *
        (m : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1
    rw [hcm, hs, Matrix.map_mul, Matrix.map_mul]
    have hsc : (Matrix.scalar (Fin D.R.r) s).map τ.1 = Matrix.scalar (Fin D.R.r) (τ.1 s) := by
      ext p q; by_cases hpq : p = q <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hpq]
    rw [hsc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    congr 2
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
  have hb := (hU.2.2.2.1 k'' k'' ⟨_, hy₁⟩ ⟨_, hy₂⟩).2 ⟨γ', hγ', bm, hbm, congrArg (Sigma.mk k'') heq⟩
  obtain ⟨t', ht'⟩ := hb
  exact ⟨hy₁, _, htr _ _ _ _ _ ht' f₂⟩

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCharacterRationalValues
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.LevVal

theorem envV_chi_mem {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (h : R.Char F)
    (j : Fin D.R.m) (t : T0) (k : (GlobalTheory.TraceIncl.envV R j t).J) :
    ∃ a : D.what₂.LL, D.what₂.embLL a = (((GlobalTheory.TraceIncl.envV R j t).χ k : ℂˣ) : ℂ) := by
  obtain ⟨a, ha⟩ := hχ_of R j t
    (fun PP hP u => let ⟨a, ha⟩ := GlobalTheory.ConjForms.chi_mem R h.grp.chiW j PP hP u; ⟨a, ha.symm⟩)
    (fun PP hP u => let ⟨a, ha⟩ := GlobalTheory.PinsOverField.xiR_mem R h.lev h.fam t PP hP u; ⟨a, ha.symm⟩) k
  exact ⟨a, ha.symm⟩

theorem chi_val : AtTw fun Fm x hx i p w j => ∀ k, ∃ a : (Fm.D x i).what₂.LL,
  (Fm.D x i).what₂.embLL a = (((GlobalTheory.TraceIncl.envV (R2 p) j ((R2 p).mu ((Fm.D x i).plEq w))).χ k : ℂˣ) : ℂ) :=
  AtTw.of_forall fun _ _ _ _ p hr hm _ _ j k =>
    envV_chi_mem (R2 p) (F2 p) (GlobalTheory.BigOn.links2_of_rows _ _ _ _ _ _ _ _ _ _ p hr hm.1).1 j _ k

end GlobalTheory.BigOn.LevVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelClassScalarIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

namespace GlobalTheory.ClassScalarIntegral

set_option maxHeartbeats 1000000 in

theorem class_scalar_integral : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h yd → Nat.card (Fin (Vc D i).rank → LevQ (T.Q.Dw ((i : ℕ) + 1)) (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂) ≠ 0 → ∀ a : D.what₂.LL, D.what₂.embLL a = (((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹ * (((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 yd : Circle) : ℂ) * (Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ)) → ∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * a) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hO v hv hmu hQG hF0 hV0 hdel hMb hRun ℓ' hLev hAct χ ξR ω φ hK Λ h N hU hTb hTM hLN hΛ e Ps yd hh he hPs hs hy hcard a ha lam hTl
  have lemL1 := GlobalTheory.T.exists_coprime_mul_inv_genusLatticeScalar_integral
  have lemHV := GlobalTheory.T.exists_isIntegral_absNorm_pow_mul_onId_of_coprime
  have lemCC := GlobalTheory.T.exists_detIdeal_coprime_splitSupportedPoint
  have lemPSI := GlobalTheory.T.twistedKernelCharacter_isTameHecke_unramified
  obtain ⟨ψ, b, I, _, φs, n, hb0, hbP, hc, hu, hr, htame, hinf⟩ :=
    lemPSI D G Pl0 T0 A T R F κ v₀ fw O hT hC i hO v hv hmu hQG hF0 hV0 hdel hMb hRun ℓ' hLev hAct χ ξR ω φ hK Λ h N hU hTb hTM
      hLN hΛ e Ps yd hh he hPs
  have hp := Formalism.EigenvalueLevelCeiling.plc_prime lam
  obtain ⟨cc, c0, cb, cl, cv⟩ := lemCC D (Vc D i) hO.2.lift.std.1 hO.2.lift.std.2 h e Ps yd he hs hy b hbP _ ψ hc hu hr Λ hΛ
    (Formalism.EigenvalueLevelCeiling.plc lam) hp hTl
  obtain ⟨K, hK1⟩ := lemHV D.host.E ψ I φs n hinf htame b hb0 hu cc c0 cb
  obtain ⟨m, hm, hm1⟩ := lemL1 D T hT ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ Λ (O i).s0 (Formalism.EigenvalueLevelCeiling.plc lam) hp hU hTb hTl
  refine ⟨((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL), ?_, ?_⟩
  · intro hmem
    have hco : Nat.Coprime (m * Ideal.absNorm cc ^ K) (Formalism.EigenvalueLevelCeiling.plc lam) := Nat.Coprime.mul hm (Nat.Coprime.pow_left _ cl)
    have h1 : ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) ∈ lam.asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem lam
    obtain ⟨u, w, huw⟩ : IsCoprime ((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL) ((Formalism.EigenvalueLevelCeiling.plc lam : ℕ) : 𝓞 D.what₂.LL) :=
      Nat.Coprime.cast hco
    exact lam.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (huw ▸ lam.asIdeal.add_mem (lam.asIdeal.mul_mem_left _ hmem) (lam.asIdeal.mul_mem_left _ h1)))
  · have hinj : Function.Injective D.what₂.embLL.toIntAlgHom := D.what₂.embLL.injective
    refine (isIntegral_algHom_iff _ hinj).1 ?_
    have e1 : D.what₂.embLL.toIntAlgHom (((((m * Ideal.absNorm cc ^ K : ℕ) : 𝓞 D.what₂.LL)) : D.what₂.LL) * a) =
        ((m : ℂ) * ((O i).s0 (betaH (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ))⁻¹) *
        (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ)) *
        ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℝ) : ℂ) := by
      rw [RingHom.toIntAlgHom_apply, map_mul, ha, ← cv]
      push_cast
      rw [map_mul, map_pow, map_natCast, map_natCast]
      ring
    rw [e1]
    refine (hm1.mul hK1).mul ?_
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), ← Nat.cast_pow, Complex.ofReal_natCast]
    exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ^ D.R.r : ℕ) : ℤ)))

end GlobalTheory.ClassScalarIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularMatricesPreserveFrameLatticesStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_matrices_preserve_frame_lattices : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n), Function.Injective F.emb → (∀ τ, Antitone (res n (lamW τ))) → ∀ u : ι → GL (Fin n) (PadicAlgCl l), (∀ τ a b, (u τ).val a b ∈ Set.range F.emb ∧ (u τ)⁻¹.val a b ∈ Set.range F.emb) → ∀ z, (z ∈ F.latN lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latN lamW) ∧ (z ∈ F.latD lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latD lamW) := by
  first | exact @GlobalTheory.FrameRead.lamG_mem_lattices | exact GlobalTheory.FrameRead.lamG_mem_lattices | (intros; apply GlobalTheory.FrameRead.lamG_mem_lattices <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueMaximal
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweNonsplit

open GlobalTheory.HoweAdelic

theorem unique_maximal : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
      ∀ N N', Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) N → Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) N' → N = N' := by
  intro hP hHD F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hηX hηW hHX hHW hWeil v hv N N' hN hN'
  obtain ⟨om', hom'⟩ := GlobalTheory.LocOpsW.locRep F E σ n d X W M ψ χX χW om hψ hWeil v
  have hHDv := GlobalTheory.HoweNonsplit.howeDualityFor_locOps hP hHD F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hηX hηW hHX hHW hWeil v hv om' hom'
  have hpres : ∀ x, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' x φ ∈ SB (Fin n × Fin d → Fv F v) :=
    fun x φ hφ => (hom' x.1 x.2 φ hφ).1
  have key : ∀ (g : UAtGrp σ X (evFin F v)) (h : UAtGrp σ W (evFin F v)) (φ : (Fin n × Fin d → Fv F v) → ℂ),
      φ ∈ SB (Fin n × Fin d → Fv F v) → ∀ φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) →
      Acts (evFin F v) (om (g.1, h.1)) φ φ₁ → φ₁ = om' (g, h) φ := fun g h φ hφ φ₁ _ hA =>
    GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr => (hA r hr).symm.trans ((hom' g h φ hφ).2 r hr)
  have haug : augAt om v = locAug om' := by
    apply le_antisymm
    · rw [augAt, Submodule.span_le]
      rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
      have e := key ⟨g, hg⟩ 1 φ hφ φ₁ hφ₁ hA
      exact Submodule.subset_span ⟨⟨g, hg⟩, φ, hφ, by rw [e]⟩
    · rw [locAug, Submodule.span_le]
      rintro z ⟨g, φ, hφ, rfl⟩
      exact Submodule.subset_span ⟨g.1, g.2, φ, hφ, om' (g, 1) φ, (hom' g 1 φ hφ).1, (hom' g 1 φ hφ).2, rfl⟩
  have hiff : ∀ P, ThetaSub om v P ↔ IsLocSub om' P := by
    intro P
    rw [ThetaSub, IsLocSub, haug]
    refine and_congr_right fun _ => and_congr_right fun hle => ⟨fun hs h φ hφ => ?_, fun hs h hh φ hφ φ₁ hφ₁ hA => ?_⟩
    · exact hs h.1 h.2 φ hφ _ (hom' 1 h φ (hle hφ)).1 (hom' 1 h φ (hle hφ)).2
    · rw [key 1 ⟨h, hh⟩ φ (hle hφ) φ₁ hφ₁ hA]
      exact hs _ φ hφ
  have hM : ∀ P, Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) P →
      Maximal (fun P => IsLocSub om' P ∧ P ≠ SB (Fin n × Fin d → Fv F v)) P := by
    intro P hP'
    simpa only [hiff] using hP'
  replace hN := hM N hN
  replace hN' := hM N' hN'
  have hsup : IsLocSub om' (N ⊔ N') := isLocSub_sup hN.1.1 hN'.1.1
  have hne : N ⊔ N' ≠ SB (Fin n × Fin d → Fv F v) :=
    GlobalTheory.HoweAdelic.sup_ne_SB_of_howeDuality om' hHDv hpres N N' hN.1.1 hN'.1.1 hN.1.2 hN'.1.2
  have h1 : N ⊔ N' ≤ N := hN.2 ⟨hsup, hne⟩ le_sup_left
  have h2 : N ⊔ N' ≤ N' := hN'.2 ⟨hsup, hne⟩ le_sup_right
  exact le_antisymm (le_sup_left.trans h2) (le_sup_right.trans h1)

end GlobalTheory.HoweNonsplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruenceDetEqOneOfThreeLeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCongruence_det_eq_one_of_three_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E), 3 ≤ M → G.det ≠ 0 → Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → IsUStab G Λ γ → (∀ x ∈ Λ, ∃ y ∈ Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = M • y) → (γ : Matrix (Fin r) (Fin r) E).det = 1 := by
  first | exact @GlobalTheory.UnitaryCongruenceDetAny.det_eq_one | exact GlobalTheory.UnitaryCongruenceDetAny.det_eq_one | (intros; apply GlobalTheory.UnitaryCongruenceDetAny.det_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VariableMatrixDetPolyPowMulMemDualWeylStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.variableMatrixDetPoly_pow_mul_mem_dualWeyl : ∀ (R : Type) [CommRing R] (n k : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R), f ∈ dualWeyl R n n ν → detPol R n ^ k * f ∈ dualWeyl R n n fun a => ν a + k := by
  first | exact @GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl | exact GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl | (intros; apply GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFinitePartMovesVacuumAsThetaModel
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacMoveFin

theorem mulStep : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  ∀ (x₁ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₁ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₁ : GA D S) (h₁ : GA D T)
    (x₂ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₂ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₂ : GA D S) (h₂ : GA D T) (c₁ c₂ : ℂ),
    IsFinPt S g₁ x₁ → IsFinPt T h₁ y₁ → IsFinPt S g₂ x₂ → IsFinPt T h₂ y₂ →
    Reads ψ θ hS hT cc δ r (c₁ • W.Om x₁ y₁ e0) (om (g₁, h₁) f₀) → Reads ψ θ hS hT cc δ r (c₂ • W.Om x₂ y₂ e0) (om (g₂, h₂) f₀) →
    Reads ψ θ hS hT cc δ r ((c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0) (om (g₁ * g₂, h₁ * h₂) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀ x₁ y₁ g₁ h₁ x₂ y₂ g₂ h₂ c₁ c₂ hg₁ hh₁ hg₂ hh₂ hr₁ hr₂
  have he := GlobalTheory.NormSum.Model.vac_mem_TT hSet.crv hodd.1
  have hG := GlobalTheory.NormSum.RatExtend.TT_smul c₂ (W.maps x₂ y₂ e0 he)
  have key := GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hodd.1 x₁ y₁ g₁ h₁ hg₁ hh₁ c₁ f₀ hf₀ hr₁ _ hG _ hr₂
  have h1 : om (g₁ * g₂, h₁ * h₂) f₀ = om (g₁, h₁) (om (g₂, h₂) f₀) := by
    rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]
  have h2 : (c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0 = c₁ • W.Om x₁ y₁ (c₂ • W.Om x₂ y₂ e0) := by
    rw [W.smul _ _ _ _ (W.maps x₂ y₂ e0 he), ← W.mul _ _ _ _ _ he, smul_smul]
  rw [h1, h2]; exact key

theorem vacuum_move_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ → Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT x y g h hg hh f₀ hf₀
  exact GlobalTheory.T.movedVacuum_constant_trivial_finite_pairs ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀
    (GlobalTheory.VacLine.moved_vacuum_reads ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀)
    (mulStep ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀)
    (GlobalTheory.SplitVacMove.reads_om_split ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀)
    (GlobalTheory.T.inertIntegralPoints_fix_adelic_classical_vacuum ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀) x y g h hg hh

end GlobalTheory.VacMoveFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.XiAwayIm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.XiAway

theorem xi_awayIm : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ t : T, LocIn D.what₂.embLL (L.xiH t) →
      ∀ (m : ℕ) (y : (AE D)ˣ), GlobalTheory.KappaArith.AwayIm D m ((L.xi t y : Circle) : ℂ) := by
  intro D T L μ₀ hL t hx m y
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h := hL.xi t
  have h1 : L.xi t y ^ n = 1 := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (L.xi t ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D _ _ h n ho) y
  obtain ⟨ζ, hζ⟩ := GlobalTheory.TwistValues.char_mem (L.xi t) (L.xiH t) h hn ho D.what₂.embLL.fieldRange
    (fun P k => hx P (Formalism.L2.Host.atFin P k)) y
  have h2 : ζ ^ n = 1 := D.what₂.embLL.injective (by
    rw [map_pow, map_one]
    erw [hζ]
    have := congrArg (fun w : Circle => (w : ℂ)) h1
    simpa using this)
  exact ⟨ζ, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one m hn h2, hζ⟩

end GlobalTheory.XiAway
end

