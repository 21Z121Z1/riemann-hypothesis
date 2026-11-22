import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0753
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterEqOfCommonUnipotentLevelEigenve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0771
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0769
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0330
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0755
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0735
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0013
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0754

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActionReadAtMemberStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.action_read_at_member : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.ActRead t.r.Y := by
  first | exact @GlobalTheory.CenLocAt.actRead_at | exact GlobalTheory.CenLocAt.actRead_at | (intros; apply GlobalTheory.CenLocAt.actRead_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterEqOfCommonUnipotentLevelEigenveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveCharacter_eq_of_common_unipotentLevel_eigenvector : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (p m : ℕ) (θ : GAf L n ≃* GAf L n) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (F : GAf L n → V) (F' : GAf L n → V') (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (ψ₀ ψ₀' : AddChar (s.v.adicCompletion (maximalRealSubfield L)) ℂ) (ξ ξ' : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), p.Prime → s.Above p → m.Coprime p → 2 ≤ r → r ≤ n → FrameAut θ → F ≠ 0 → F' ≠ 0 → NG.IsPsi0 s ψ₀ → NG.IsPsi0 s ψ₀' → NG.LevelUni J χ s r ψ₀ ξ → NG.LevelUni J' χ' s r ψ₀' ξ' → (∀ κ : J, Eig F κ (χ κ : ℂˣ)) → (∀ κ : J', Eig F' κ (χ' κ : ℂˣ)) → (∀ κ, TrivOutside {s.v} κ → NG.UniRT s r (s.loc n κ) → ∃ c c' : ℂ, Eig F (θ κ) c ∧ Eig F' (θ κ) c' ∧ c ^ m = c' ^ m) → ∀ y, Valued.v y ≤ 1 → ψ₀ y = ψ₀' y := by
  first | exact @GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq | exact GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq | (intros; apply GlobalTheory.PsiCmp.fractionFieldToGenericStalk_algebraMap_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleAndLamUsedAllStatesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_and_lam_used_all_states : PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ _ _ _ x => SumRepresentations.adm8 (Dof x) ∧ GlobalTheory.NRows.LamUsed (Dof x) := by
  first | exact @GlobalTheory.HeightCounting.Up.RowsAtStates.parts_lam_allSt | exact GlobalTheory.HeightCounting.Up.RowsAtStates.parts_lam_allSt | (intros; apply GlobalTheory.HeightCounting.Up.RowsAtStates.parts_lam_allSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormKillsGrassmannianRelationCopi
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GrassTop

theorem ren_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) :
    ren τ (rel k) = GlobalTheory.PointChern.relPoly τ k := by
  simp [ren, rel, GlobalTheory.PointChern.relPoly, map_sum, renVar]

theorem admissibleChernForm_kills_grassmannianRelationCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), GlobalTheory.Schubert.admitted H Dw Θ →
    ∀ (τ : GlobalTheory.AllWt.Psi H) (j : MvPolynomial (Bool × ℕ) ℝ), j ∈ GlobalTheory.GrassTop.J Dw.p Dw.q →
    ∀ r : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (r * GlobalTheory.GrassTop.ren τ j) = 0 := by
  intro E _ _ _ H Dw Θ hA τ j hj
  obtain ⟨h1, h2, h3, -⟩ := hA
  unfold J at hj
  induction hj using Submodule.span_induction with
  | mem x hx =>
    intro r
    rcases hx with ⟨k, hk, rfl⟩ | ⟨b, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · rw [ren_rel, mul_comm]; exact h1 τ k hk r
    · rw [mul_comm]
      simp only [ren, map_sub, rename_X, map_one]
      exact h2 _ r
    · rw [mul_comm]
      simp only [ren, rename_X]
      have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
      exact h3 _ _ (by simp only [renVar, if_true]; omega) r
    · rw [mul_comm]
      simp only [ren, rename_X]
      have hm : Dw.mult (conjEmb τ.1) = Dw.q := GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)
      exact h3 _ _ (by simp only [renVar]; simp only [Bool.false_eq_true, if_false]; omega) r
  | zero => intro r; simp
  | add x y _ _ hx hy => intro r; rw [map_add, mul_add, map_add, hx, hy, add_zero]
  | smul a x _ hx => intro r; rw [smul_eq_mul, map_mul (ren τ) a x, ← mul_assoc]; exact hx _

end GlobalTheory.GrassTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormProdGrassmannianBasisCopies
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.GrassTopProd

theorem wt_add {ι : Type} (a b : ι × ℕ →₀ ℕ) :
    GlobalTheory.GrassTop.wt (a + b) = GlobalTheory.GrassTop.wt a + GlobalTheory.GrassTop.wt b := by
  unfold GlobalTheory.GrassTop.wt
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem wt_sum {ι κ : Type} (s : Finset κ) (d : κ → ι × ℕ →₀ ℕ) :
    GlobalTheory.GrassTop.wt (∑ k ∈ s, d k) = ∑ k ∈ s, GlobalTheory.GrassTop.wt (d k) := by
  induction s using Finset.induction_on with
  | empty => simp [GlobalTheory.GrassTop.wt]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, wt_add, ih]

theorem wt_mapDomain {ι κ : Type} (f : ι × ℕ → κ × ℕ) (hf : ∀ x, (f x).2 = x.2) (d : ι × ℕ →₀ ℕ) :
    GlobalTheory.GrassTop.wt (d.mapDomain f) = GlobalTheory.GrassTop.wt d := by
  unfold GlobalTheory.GrassTop.wt
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
  simp [hf]

theorem adm_apply_prod_ren_eq_ite_mul_pointPoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ), (∀ τ, g τ ∈ GlobalTheory.GrassTop.basis Dw.p Dw.q) →
    ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ →
    Θ (∏ τ, GlobalTheory.GrassTop.ren τ (g τ)) = (if ∀ τ, g τ = X (true, Dw.p) ^ Dw.q then
      (-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H)) else 0) * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  intro E _ _ _ H Dw g hg Θ hΘ
  have hm : ∀ τ : GlobalTheory.AllWt.Psi H, Dw.mult τ.1 = Dw.p := fun τ => GlobalTheory.PointChern.mult_of_mem Dw τ.2
  split_ifs with hall
  · have h1 : ∏ τ, GlobalTheory.GrassTop.ren τ (g τ) = ∏ τ : GlobalTheory.AllWt.Psi H, X (τ.1, Dw.p) ^ Dw.q := by
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hall τ, map_pow]
      simp [GlobalTheory.GrassTop.ren, GlobalTheory.GrassTop.renVar]
    have h2 : GlobalTheory.LieBase.pointPoly H Dw = C ((-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H))) *
        ∏ τ : GlobalTheory.AllWt.Psi H, X (τ.1, Dw.p) ^ Dw.q := by
      unfold GlobalTheory.LieBase.pointPoly
      rw [Finset.prod_congr rfl (fun τ _ => by rw [hm τ])]
      rw [show Dw.p + Dw.q - Dw.p = Dw.q by omega]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← C_pow, ← pow_mul]
    rw [h1, h2, ← smul_eq_C_mul, LinearMap.map_smul, smul_eq_mul, ← mul_assoc, ← mul_pow]
    norm_num
  · push_neg at hall
    obtain ⟨σ, hσ⟩ := hall
    have key : ∀ τ, ∃ d : Bool × ℕ →₀ ℕ, GlobalTheory.GrassTop.wt d ≤ Dw.p * Dw.q ∧
        (g τ ≠ X (true, Dw.p) ^ Dw.q → GlobalTheory.GrassTop.wt d < Dw.p * Dw.q) ∧ g τ = monomial d 1 := by
      intro τ
      rcases hg τ with ⟨d, hd, he⟩ | he
      · exact ⟨d, hd.le, fun _ => hd, he⟩
      · refine ⟨Finsupp.single (true, Dw.p) Dw.q, ?_, fun h => absurd he h, ?_⟩
        · simp [GlobalTheory.GrassTop.wt, Finsupp.sum_single_index, mul_comm]
        · rw [he, X_pow_eq_monomial]
    choose d hd1 hd2 hd3 using key
    have hprod : ∏ τ, GlobalTheory.GrassTop.ren τ (g τ) =
        monomial (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) 1 := by
      rw [monomial_sum_one]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hd3 τ, GlobalTheory.GrassTop.ren, rename_monomial]
    have hw : GlobalTheory.GrassTop.wt (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) <
        Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by
      rw [wt_sum]
      calc ∑ τ, GlobalTheory.GrassTop.wt ((d τ).mapDomain (GlobalTheory.GrassTop.renVar τ))
          = ∑ τ, GlobalTheory.GrassTop.wt (d τ) :=
            Finset.sum_congr rfl fun τ _ => wt_mapDomain (GlobalTheory.GrassTop.renVar τ) (fun _ => rfl) (d τ)
        _ < ∑ _τ : GlobalTheory.AllWt.Psi H, Dw.p * Dw.q :=
            Finset.sum_lt_sum (fun τ _ => hd1 τ) ⟨σ, Finset.mem_univ _, hd2 σ hσ⟩
        _ = Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) := by simp
    have h0 : Θ (monomial (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) 1) = 0 :=
      hΘ.2.2.2 (∑ τ, (d τ).mapDomain (GlobalTheory.GrassTop.renVar τ)) hw.ne
    rw [hprod, h0, zero_mul]

end GlobalTheory.GrassTopProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AgreeOfData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.HeightCounting.Up.ThirdAgree

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.Up.RealOfReading

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem agree_of_data (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) {cf : CharFrame D} {nch : NChoice D}
    (tp : TupTied D cf nch) (hC : R.C = cf) (Xd : DivX D) (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (hb htup hg hf)
    (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hrep : ∀ σ, (rep σ).Iso (principalLevelFrame.rowRepR R.θ (Y.eFT σ)))
    (c : ∀ i, CoefA (Vc D i)) (hc : R.cV = c) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (std : ∀ i, R3.StdFrame Y.hF (PV i))
    (eW : ∀ μ, Used0 D μ → ∀ i : Fin D.R.m, (M μ (i.1 + 1) (by omega) (by omega)).wt.W ≃ₗ[ℂ] (c i).W)
    (jm : ∀ μ, Used0 D μ → ∀ i : Fin D.R.m, D.what₂.Mt μ (i.1 + 1) → GA D (Vc D i) → (c i).W)
    (hj : ∀ μ h i x, HEq (Y.IL.jMt μ h i x).1 (jm μ h i x))
    (read : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.Mt μ (i.1 + 1)) (g : GAf D.host.E D.R.nV),
      eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = jm μ h i x ((PV i).ψ g))
    (rat : ∀ (i : Fin D.R.m) (g : GAf D.host.E D.R.nV), g ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
      ∃ γ ∈ Formalism.L2.Theta.GQ (Vc D i), finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g))
    (wt : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (g : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D i),
      finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g) → ∀ v,
        eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).wt.ρ g v) = (c i).ρ γ (eW μ h i v)) :
    Nonempty (GlobalTheory.NJoin.Agree (realOfRead R.toRealDat F.lv2 Y tp hC Xd E labPi hb htup hg hf) M rep) := by
  subst hc
  refine ⟨⟨Y.hF, PV, fun j => (StandardFrameAgreement.stdFrame_iff _ _).1 (std j), fun j => (StandardFrameAgreement.stdFrame_iff _ _).1 (Y.stdPsi.2 j),
    fun _ => 1, ?_, fun μ hμ j => (eW μ hμ j).symm, ?_, ?_, hrep⟩⟩
  · intro j h
    simp only [inv_one, one_mul, mul_one]
    exact rat j h
  · intro μ hμ j h γ hγ he v
    have he' := he
    simp only [inv_one, one_mul, mul_one] at he'
    have key := wt μ hμ j h γ hγ he' ((eW μ hμ j).symm v)
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    refine Eq.trans ?_ key.symm
    exact congrArg _ (LinearEquiv.apply_symm_apply _ v).symm
  · intro μ hμ j x h
    refine (LinearEquiv.eq_symm_apply _).2 ?_
    refine (read μ hμ j x h).trans ?_
    simp only [inv_one, one_mul]
    exact (congrFun (eq_of_heq (hj μ hμ j x)) _).symm

theorem heq_apply {Mt : D.what₂.Tup → ℕ → Hs} {c c' : ∀ i, CoefA (Vc D i)} (h : c = c')
    (j : ∀ μ (i : Fin D.R.m), (Mt μ ((i : ℕ) + 1)).T →ₗ[ℂ] (GA D (Vc D i) → (c i).W))
    (j' : ∀ μ (i : Fin D.R.m), (Mt μ ((i : ℕ) + 1)).T →ₗ[ℂ] (GA D (Vc D i) → (c' i).W)) (hj : HEq j j') (μ i x) :
    HEq (j μ i x) (j' μ i x) := by
  subst h
  cases hj
  rfl

end Gen

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : TwDat B}
  {Wt : Set B.places.Pl}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Pj.instCMHost (@Late.st B C a).toD7) (@Pj.Par.H (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.l (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.c (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Pj.instCMHost (@Late.st B C a).toD7) (@Pj.Par.H (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.l (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.c (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

def cpV (c : ∀ i, CoefA (Vc a.D i)) : ∀ i, CoefA (Vc b.D i) := fun i => (by with_unfolding_all exact ((coefA b (c ((by with_unfolding_all exact (i :))))) :))

theorem cV_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) : z.R.cV = cpV b z₀.R.cV := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  exact (by with_unfolding_all exact ((Eq.refl (cpV b z₀.R.cV)) :))

theorem cV_two (b' : Late B C) {c₀ : ∀ i, CoefA (Vc a.D i)} {c : ∀ i, CoefA (Vc b.D i)} {c' : ∀ i, CoefA (Vc b'.D i)}
    (h : c = cpV b c₀) (h' : c' = cpV b' c₀) : c' = cpV b' c := by
  subst h h'
  exact (by with_unfolding_all exact ((Eq.refl (cpV b' c₀)) :))

end Copy

section Main

theorem iso_of_eq {Lf : Type} [Field Lf] [NumberField Lf] [IsCMField Lf] {n : ℕ} {π π' : NG.FinTyp Lf n} (h : π = π') : π.Iso π' :=
  h ▸ NG.IsoRep.refl _

set_option maxHeartbeats 4000000 in

theorem agree_third : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ T w P x => ∀ (l : LC hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), GlobalTheory.CoefDuty.Built l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∀ (hC : m.z.R.C = cfL L (cfOf x)) (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd) (labPi : E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) hb htup hg hf (rep : (withLoc L).what₂.FT → NG.FinTyp (withLoc L).host.E (withLoc L).R.r), HEq rep (repOf x.r.Y) → Nonempty (GlobalTheory.NJoin.Agree (GlobalTheory.HeightCounting.Up.RealOfReading.realOfRead m.z.R.toRealDat m.z.F.lv2 r.Y (tpL L l.c.tp) hC Xd E labPi hb htup hg hf) (mtL L l.mt.M) rep) := by
  intro hL _ _
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l big L _ _ m hcp hco s r hpin hC Xd E labPi hb htup hg hf rep hrep
  have c1 := cV_copy (B := B) (C := w.C) (a := P.Z₀) (GlobalTheory.HeightCounting.Fin3.oL x L).Z P.z m.z m.Xg m.tr ((by with_unfolding_all exact (hcp.core :))) ((by with_unfolding_all exact (hcp.R :)))
  have c0 := cV_copy (B := B) (C := w.C) (a := P.Z₀) x.o.Z P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :)))
  have ecV := cV_two (a := P.Z₀) x.o.Z (GlobalTheory.HeightCounting.Fin3.oL x L).Z c0 c1
  have hJ : HEq m.t.lf.jMt x.m.t.lf.jMt := hco.jMt.trans x.coh.jMt.symm
  have kJ : ∀ μ (i : Fin (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7.R.m) y,
      HEq (m.t.lf.jMt μ i y) (x.m.t.lf.jMt ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :)))) := fun μ i y => (by with_unfolding_all exact ((heq_apply (D := (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7) (Mt := fun μ j => (P.q.p.sL μ j).A) ecV
      ((by with_unfolding_all exact (m.t.lf.jMt :))) ((by with_unfolding_all exact (x.m.t.lf.jMt :))) ((by with_unfolding_all exact (hJ :))) μ i y) :))
  have eR1 : m.t.rep = (by with_unfolding_all exact (P.q.t.rep :)) := (by with_unfolding_all exact ((eq_of_heq hco.rep) :))
  have eR0 : x.m.t.rep = (by with_unfolding_all exact (P.q.t.rep :)) := (by with_unfolding_all exact ((eq_of_heq x.coh.rep) :))
  have eRep : rep = (by with_unfolding_all exact ((repOf x.r.Y) :)) := (by with_unfolding_all exact ((eq_of_heq hrep) :))
  have hrep' : ∀ σ, (rep σ).Iso (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT σ)) := by
    intro σ
    have a1 : (rep σ).Iso ((by with_unfolding_all exact ((repOf x.r.Y σ) :))) := (by with_unfolding_all exact ((iso_of_eq (congrFun eRep σ)) :))
    have a2 := x.pin.rep ((by with_unfolding_all exact (σ :)))
    have a3 : ((by with_unfolding_all exact ((x.m.t.rep σ) :)) : NG.FinTyp (withLoc L).host.E (withLoc L).R.r).Iso ((by with_unfolding_all exact ((m.t.rep σ) :))) := (by with_unfolding_all exact ((iso_of_eq ((congrFun eR0 σ).trans (congrFun eR1 σ).symm)) :))
    have a4 := NG.IsoRep.symm (principalLevelFrame.rowRepR m.z.R.θ (r.Y.eFT σ)).stable (hpin.rep σ)
    exact (by with_unfolding_all exact ((NG.IsoRep.trans a1 (NG.IsoRep.trans a2 (NG.IsoRep.trans a3 a4))) :))
  let DL := (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z).toD7
  let jm : ∀ μ, Used0 DL μ → ∀ i : Fin DL.R.m, DL.what₂.Mt μ (i.1 + 1) → GA DL (Vc DL i) →
      (cpV (GlobalTheory.HeightCounting.Fin3.oL x L).Z x.m.z.R.cV i).W :=
    fun μ h i y => (by with_unfolding_all exact ((x.r.Y.IL.jMt ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact (h :))) ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (y :)))).1 :))
  have hj : ∀ μ h i y, HEq (r.Y.IL.jMt μ h i y).1 (jm μ h i y) := fun μ h i y => (by with_unfolding_all exact (((hpin.jMt μ h i y).trans ((kJ μ i y).trans (x.pin.jMt μ h i y).symm)) :))
  exact (by with_unfolding_all exact ((agree_of_data (D := DL) (R := m.z.R) (F := m.z.F) r.Y (cf := (by with_unfolding_all exact ((cfL L (cfOf x)) :))) (nch := (by with_unfolding_all exact ((chL L l.c.ch) :)))
    ((by with_unfolding_all exact ((tpL L l.c.tp) :))) ((by with_unfolding_all exact (hC :))) ((by with_unfolding_all exact (Xd :))) ((by with_unfolding_all exact (E :))) ((by with_unfolding_all exact (labPi :))) ((by with_unfolding_all exact (hb :))) ((by with_unfolding_all exact (htup :))) ((by with_unfolding_all exact (hg :))) ((by with_unfolding_all exact (hf :))) ((by with_unfolding_all exact ((mtL L l.mt.M) :))) ((by with_unfolding_all exact (rep :)))
    ((by with_unfolding_all exact (hrep' :))) _ ecV (GlobalTheory.HeightCounting.Fin3.pvL L l) ((by with_unfolding_all exact (l.mt.ad.std :))) ((by with_unfolding_all exact (l.mt.ad.eW :))) jm hj ((by with_unfolding_all exact (l.mt.ad.read :))) ((by with_unfolding_all exact (l.mt.ad.rat :)))
    ((by with_unfolding_all exact (l.mt.ad.wt :)))) :))

end Main

end GlobalTheory.HeightCounting.Up.ThirdAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicChartLiftHolomorphicPeriodMapsStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicChart_lift_holomorphic_periodMaps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V X.dim)) (P : ReciprocityTheory.L2DbarEstimates.V X.dim → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B ∧ c'.e y ∈ B ∧ B ⊆ c'.e.target ∧ (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) ∧ (∀ x, DifferentiableOn ℂ (fun b => P b x) B) ∧ ∀ b ∈ B, ∃ q : FrPt Xo c (Formalism.L2.Pj.CAt σ), cxPt T.Z q = cxOf e σ hj (c'.e.symm b) ∧ Fu.u i (P b) = q.x := by
  first | exact @GlobalTheory.ShFam.chart_lift_periods_of_openPart | exact GlobalTheory.ShFam.chart_lift_periods_of_openPart | (intros; apply GlobalTheory.ShFam.chart_lift_periods_of_openPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanInputsImply
section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory

theorem hypA_of_artinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCoverExists → GlobalTheory.Published.BesselUniquenessReal → GlobalTheory.Published.FormalDegreeCompactDual → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → HypA :=
fun ar cm we hm cd cw hf cl ce bu fd sw =>
  have c := GlobalTheory.DiscreteSeriesConsequences.of_classification cl
  have u : GlobalTheory.Published.DiscreteSeriesUpqUnique := GlobalTheory.Published.discreteSeriesUpqUnique_of_classification cl
  have d := GlobalTheory.discreteSeries_three_of_hypotheses ce c.2.2.2.2 u
  ⟨ar.rayClassFieldSt, ar.principalIdealSt, cm, hm, cd, cw, GlobalTheory.weilRepresentationUnitaryPair, c.2.2.1, hf, c.2.1, u,
    GlobalTheory.rowsFinDim_link, sw, GlobalTheory.BesselMapOne.besselMapUniq_of_besselUniqueness bu, c.2.2.2.2, fd, GlobalTheory.Mass.massRatio_all_unramified_cmFields,
    d.1, d.2.1, d.2.2, ar, we⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BadPlacesSubOfAdmissibleTwistStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bad_places_sub_of_admissible_twist : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → NX.badV (Dof x) i (QOf P v) ⊆ gPl (Dof x) ∪ qPl (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) := by
  first | exact @GlobalTheory.LevCmp.BadV.badV_sub_gPl_qPl | exact GlobalTheory.LevCmp.BadV.badV_sub_gPl_qPl | (intros; apply GlobalTheory.LevCmp.BadV.badV_sub_gPl_qPl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormBaseChangeDvr
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TraitCmp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), IsCN R → P.TorsionIso →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (g : R →+* W), Function.Injective g → ¬ IsLocalHom g →
    ∀ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap g)) (P' : PELUnif (maximalIdeal W) t'),
      ∃ ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X, Function.Surjective ρ ∧
        ∀ (y : P.D.toPre.X) (r : R) (r' : W), PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (ρ y) r' → Associated (g r) r' := by
  intro E _ _ _ H R _ _ _ t P hR hT W _ _ _ hW g hg hnl t' m P'
  obtain ⟨ρ, hs, hτ⟩ := GlobalTheory.T.characters_restrict_linear_to_trait_uniformisation E H R t P hR hT W hW g hg hnl t' m P'
  exact ⟨ρ, hs, GlobalTheory.T.associated_psi_coordinates_of_tau_units E H R t P W g hg t' P' ρ hτ⟩

end GlobalTheory.TraitCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BwitFrameTwists
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowEx.FrmW

open GlobalTheory.Mem.R3 Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Col2

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}

set_option maxHeartbeats 1000000 in

theorem frame_of_args (a : TwArgs ex t) (x : TwIn ex) (hx : HEq a.x x) :
    x.R.toRealDat.C = Fr.at (w.st Z) f ∧ TwistPlacesOffPrimeQZero x.R.toRealDat.toLevCh ∧
      ∀ u, ∃ ξ ∈ T.set f, HEq (x.R.toRealDat.toLevCh.xiH u) ξ := by
  obtain rfl := eq_of_heq hx
  have hz := GlobalTheory.RowEx.twisted_data_off_base_level B f T w Z _ _ t.r.z
  have e := congrArg (fun s => match s with
    | ⟨_, _, _, _, _, _, _, _, _, R, _, _⟩ => R.toRealDat.C = Fr.at (w.st Z) f ∧ TwistPlacesOffPrimeQZero R.toRealDat.toLevCh ∧
        ∀ u, ∃ ξ ∈ T.set f, HEq (R.toRealDat.toLevCh.xiH u) ξ) a.pack
  exact e.mpr ⟨hz.2.1, hz.1, fun u => ⟨_, hz.2.2.2 u, HEq.rfl⟩⟩

end GlobalTheory.RowEx.FrmW

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.RowEx.bwit_frame_twists : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL) (K : Ctx) (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c), BWit q b → b.B.Q.Rl.toRealDat.C = Fr.at (q.w.st q.Z) q.f ∧ TwistPlacesOffPrimeQZero b.B.Q.Rl.toRealDat.toLevCh ∧ ∀ u, ∃ ξ ∈ q.T.set q.f, HEq (b.B.Q.Rl.toRealDat.toLevCh.xiH u) ξ := by
  intro hL p K q c b w
  have h2 := GlobalTheory.RowEx.FrmW.frame_of_args w.a w.x w.ax
  have e := congrArg (fun r : RPk b.R b.S => r.B.Q.Rl.toRealDat.C = Fr.at (q.w.st q.Z) q.f ∧ TwistPlacesOffPrimeQZero r.B.Q.Rl.toRealDat.toLevCh ∧
      ∀ u, ∃ ξ ∈ q.T.set q.f, HEq (r.B.Q.Rl.toRealDat.toLevCh.xiH u) ξ) w.y.eq
  exact e.mpr h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellPlacesMembershipTwistStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_places_membership_twist : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → (eta (D := Dof x) (cfOf x) w.I.xi v j).TameAt P' := by
  first | exact @GlobalTheory.TwTameCell.eta_tameAt | exact GlobalTheory.TwTameCell.eta_tameAt | (intros; apply GlobalTheory.TwTameCell.eta_tameAt <;> assumption)
end

